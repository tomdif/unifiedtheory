"""Real-text byte language-model comparison: QueryTriad vs Transformer.

Dataset: the canonical WikiText-2 raw train/valid/test files used by the
PyTorch language-model example.  Raw bytes are tokens, so neither model gets a
tokenizer advantage and the metric is bits per byte (BPC).

Protocol fixed before execution
-------------------------------
* train context: 128 bytes
* identical batches, updates, optimizer, schedule, and training tokens
* parameter counts within roughly 10 percent
* evaluation at contexts 128, 256, and 512

Promotion requires either:
1. test BPC at context 256 lower by >= 0.02 while context-128 BPC is no more
   than 0.02 worse; or
2. BPC within 0.01 at context 256 and >= 1.25x training-token throughput.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import time
import urllib.request
from pathlib import Path

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F


VOCAB = 256
TRAIN_CONTEXT = 128
EVAL_CONTEXTS = (128, 256, 512)
DATA_URLS = {
    "train": "https://raw.githubusercontent.com/pytorch/examples/main/word_language_model/data/wikitext-2/train.txt",
    "valid": "https://raw.githubusercontent.com/pytorch/examples/main/word_language_model/data/wikitext-2/valid.txt",
    "test": "https://raw.githubusercontent.com/pytorch/examples/main/word_language_model/data/wikitext-2/test.txt",
}


def parameter_count(model):
    return sum(parameter.numel() for parameter in model.parameters())


def download_dataset(directory: Path):
    directory.mkdir(parents=True, exist_ok=True)
    metadata = {}
    tensors = {}
    for split, url in DATA_URLS.items():
        path = directory / f"{split}.txt"
        if not path.exists():
            urllib.request.urlretrieve(url, path)
        payload = path.read_bytes()
        metadata[split] = {
            "url": url,
            "bytes": len(payload),
            "sha256": hashlib.sha256(payload).hexdigest(),
        }
        tensors[split] = torch.from_numpy(
            np.frombuffer(payload, dtype=np.uint8).copy().astype(np.int64)
        )
    return tensors, metadata


class QueryTriadLayer(nn.Module):
    def __init__(self, width=64, max_delay=512, ff=128):
        super().__init__()
        self.width = width
        self.max_delay = max_delay
        self.query = nn.Linear(width, width)
        self.key = nn.Linear(width, width)
        self.value = nn.Linear(width, width)
        self.delay_bias = nn.Parameter(torch.zeros(3, max_delay + 1))
        self.mix = nn.Linear(4 * width, width)
        self.norm1 = nn.LayerNorm(width)
        self.ff = nn.Sequential(
            nn.Linear(width, ff), nn.GELU(), nn.Linear(ff, width)
        )
        self.norm2 = nn.LayerNorm(width)

    def forward(self, sequence):
        _, length, width = sequence.shape
        query = self.query(sequence)
        key = self.key(sequence)
        value = self.value(sequence)
        content = torch.matmul(query, key.transpose(1, 2)) / math.sqrt(width)
        positions = torch.arange(length, device=sequence.device)
        delay = positions[:, None] - positions[None, :]
        causal = delay >= 0
        delay_index = delay.clamp(0, self.max_delay)
        bias = self.delay_bias[:, delay_index]
        scores = content[:, None] + bias[None]
        scores = scores.masked_fill(~causal[None, None], float("-inf"))
        weights = scores.softmax(dim=-1)
        reads = torch.einsum("bstu,bud->btsd", weights, value)
        common = reads.mean(dim=2)
        q1 = (2.0 * reads[:, :, 0] - reads[:, :, 1] - reads[:, :, 2]) / math.sqrt(6.0)
        q2 = (reads[:, :, 1] - reads[:, :, 2]) / math.sqrt(2.0)
        state = self.norm1(sequence + self.mix(
            torch.cat([sequence, common, q1, q2], dim=-1)
        ))
        return self.norm2(state + self.ff(state))


class QueryTriadLM(nn.Module):
    def __init__(self, width=64, layers=2):
        super().__init__()
        self.embedding = nn.Embedding(VOCAB, width)
        self.layers = nn.ModuleList([QueryTriadLayer(width) for _ in range(layers)])
        self.head = nn.Linear(width, VOCAB)

    def forward(self, tokens):
        state = self.embedding(tokens)
        for layer in self.layers:
            state = layer(state)
        return self.head(state)

    def delay_diagnostics(self):
        rows = []
        for layer_index, layer in enumerate(self.layers):
            sheets = []
            for sheet in range(3):
                values, indices = layer.delay_bias[sheet].topk(8)
                sheets.append({
                    "sheet": sheet,
                    "top_delays": indices.tolist(),
                    "biases": values.tolist(),
                })
            rows.append({"layer": layer_index, "sheets": sheets})
        return rows


def sinusoidal_positions(max_length, width):
    position = torch.arange(max_length, dtype=torch.float32)[:, None]
    frequency = torch.exp(
        torch.arange(0, width, 2, dtype=torch.float32)
        * (-math.log(10000.0) / width)
    )
    encoding = torch.zeros(max_length, width)
    encoding[:, 0::2] = torch.sin(position * frequency)
    encoding[:, 1::2] = torch.cos(position * frequency)
    return encoding


class TransformerLM(nn.Module):
    def __init__(self, width=64, layers=3, heads=4, ff=128, max_length=1024):
        super().__init__()
        self.embedding = nn.Embedding(VOCAB, width)
        self.register_buffer(
            "position", sinusoidal_positions(max_length, width), persistent=False
        )
        block = nn.TransformerEncoderLayer(
            d_model=width, nhead=heads, dim_feedforward=ff,
            dropout=0.0, activation="gelu", batch_first=True, norm_first=True,
        )
        self.encoder = nn.TransformerEncoder(block, num_layers=layers)
        self.norm = nn.LayerNorm(width)
        self.head = nn.Linear(width, VOCAB)

    def forward(self, tokens):
        length = tokens.shape[1]
        state = self.embedding(tokens) + self.position[:length].to(
            dtype=self.embedding.weight.dtype
        )
        mask = torch.triu(
            torch.full((length, length), float("-inf"),
                       device=tokens.device, dtype=state.dtype),
            diagonal=1,
        )
        return self.head(self.norm(self.encoder(state, mask=mask)))


def random_batch(data, batch, context, device, generator):
    starts = torch.randint(
        0, len(data) - context - 1, (batch,),
        device=device, generator=generator,
    )
    offsets = torch.arange(context + 1, device=device)
    chunks = data[starts[:, None] + offsets[None, :]]
    return chunks[:, :-1], chunks[:, 1:]


def cosine_learning_rate(step, total_steps, base, warmup=100):
    if step < warmup:
        return base * (step + 1) / warmup
    progress = (step - warmup) / max(1, total_steps - warmup)
    return base * 0.1 + base * 0.9 * 0.5 * (1.0 + math.cos(math.pi * progress))


def train(model, data, steps, batch, learning_rate, seed, device):
    generator = torch.Generator(device=device)
    generator.manual_seed(seed + 1000)
    optimizer = torch.optim.AdamW(model.parameters(), lr=learning_rate,
                                  weight_decay=0.01)
    model.train()
    trace = []
    torch.cuda.reset_peak_memory_stats()
    torch.cuda.synchronize()
    started = time.perf_counter()
    for step in range(steps):
        lr = cosine_learning_rate(step, steps, learning_rate)
        for group in optimizer.param_groups:
            group["lr"] = lr
        inputs, targets = random_batch(
            data, batch, TRAIN_CONTEXT, device, generator
        )
        optimizer.zero_grad(set_to_none=True)
        with torch.autocast("cuda", dtype=torch.bfloat16):
            logits = model(inputs)
            loss = F.cross_entropy(logits.reshape(-1, VOCAB), targets.reshape(-1))
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        optimizer.step()
        if step in (0, steps // 4, steps // 2, 3 * steps // 4, steps - 1):
            trace.append({"step": step + 1, "loss_nats": float(loss.item()),
                          "bpc": float(loss.item() / math.log(2.0))})
    torch.cuda.synchronize()
    seconds = time.perf_counter() - started
    tokens = steps * batch * TRAIN_CONTEXT
    return {
        "seconds": seconds,
        "tokens": tokens,
        "tokens_per_second": tokens / seconds,
        "peak_mib": torch.cuda.max_memory_allocated() / (1024 * 1024),
        "trace": trace,
    }


@torch.inference_mode()
def evaluate(model, data, context, batch, max_tokens, device):
    model.eval()
    usable = min(len(data) - context - 1, max_tokens)
    starts = torch.arange(0, usable, context, device=device)
    offsets = torch.arange(context + 1, device=device)
    loss_sum = 0.0
    count = 0
    for cursor in range(0, len(starts), batch):
        selected = starts[cursor:cursor + batch]
        chunks = data[selected[:, None] + offsets[None, :]]
        inputs, targets = chunks[:, :-1], chunks[:, 1:]
        with torch.autocast("cuda", dtype=torch.bfloat16):
            logits = model(inputs)
            loss = F.cross_entropy(
                logits.reshape(-1, VOCAB), targets.reshape(-1), reduction="sum"
            )
        loss_sum += float(loss.item())
        count += targets.numel()
    nats = loss_sum / count
    return {"nats_per_byte": nats, "bits_per_byte": nats / math.log(2.0),
            "bytes": count}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seeds", type=int, default=2)
    parser.add_argument("--steps", type=int, default=3000)
    parser.add_argument("--batch", type=int, default=64)
    parser.add_argument("--eval-batch", type=int, default=16)
    parser.add_argument("--eval-bytes", type=int, default=524288)
    parser.add_argument("--smoke", action="store_true")
    args = parser.parse_args()
    if not torch.cuda.is_available():
        raise SystemExit("CUDA required")
    if args.smoke:
        args.seeds = 1
        args.steps = 3
        args.batch = 4
        args.eval_batch = 2
        args.eval_bytes = 4096
    device = torch.device("cuda")
    dataset, dataset_metadata = download_dataset(
        Path(__file__).with_name("wikitext2_raw")
    )
    dataset = {key: value.to(device) for key, value in dataset.items()}
    runs = []
    partial = Path(__file__).with_name("real_text_delay_lm_partial.json")

    for seed_index in range(args.seeds):
        for model_name, constructor in (
            ("query_triad", QueryTriadLM),
            ("transformer", TransformerLM),
        ):
            seed = 17000 + seed_index
            torch.manual_seed(seed)
            model = constructor().to(device)
            training = train(
                model, dataset["train"], args.steps, args.batch,
                2.0e-3, seed, device,
            )
            evaluation = {}
            for split in ("valid", "test"):
                evaluation[split] = {
                    f"context_{context}": evaluate(
                        model, dataset[split], context, args.eval_batch,
                        args.eval_bytes, device,
                    )
                    for context in EVAL_CONTEXTS
                }
            row = {
                "seed": seed_index,
                "model": model_name,
                "parameters": parameter_count(model),
                "training": training,
                "evaluation": evaluation,
            }
            if model_name == "query_triad":
                row["delay_diagnostics"] = model.delay_diagnostics()
            runs.append(row)
            partial.write_text(json.dumps({"runs": runs}, indent=2))
            print(
                f"seed={seed_index} {model_name:11s} params={row['parameters']:,} "
                f"train_bpc={training['trace'][-1]['bpc']:.3f} "
                f"test128={evaluation['test']['context_128']['bits_per_byte']:.3f} "
                f"test256={evaluation['test']['context_256']['bits_per_byte']:.3f} "
                f"tok/s={training['tokens_per_second']:,.0f}"
            )
            del model
            torch.cuda.empty_cache()

    promotion = None
    if not args.smoke:
        means = {}
        for model_name in ("query_triad", "transformer"):
            selected = [row for row in runs if row["model"] == model_name]
            means[model_name] = {
                f"test_bpc_{context}": float(np.mean([
                    row["evaluation"]["test"][f"context_{context}"]["bits_per_byte"]
                    for row in selected
                ]))
                for context in EVAL_CONTEXTS
            }
            means[model_name]["tokens_per_second"] = float(np.mean([
                row["training"]["tokens_per_second"] for row in selected
            ]))
        q, t = means["query_triad"], means["transformer"]
        loss_win = (q["test_bpc_256"] <= t["test_bpc_256"] - 0.02
                    and q["test_bpc_128"] <= t["test_bpc_128"] + 0.02)
        efficient_tie = (q["test_bpc_256"] <= t["test_bpc_256"] + 0.01
                         and q["tokens_per_second"] >= 1.25 * t["tokens_per_second"])
        promotion = {
            "means": means,
            "loss_win": loss_win,
            "efficient_tie": efficient_tie,
            "real_text_promotion_passed": loss_win or efficient_tie,
        }

    output = {
        "status": "real-text byte language-model experiment",
        "dataset": dataset_metadata,
        "protocol": vars(args),
        "gpu": torch.cuda.get_device_name(0),
        "torch": torch.__version__,
        "promotion_criterion": (
            "test BPC256 >=0.02 lower with BPC128 no >0.02 worse, "
            "or within0.01 and >=1.25x faster"
        ),
        "runs": runs,
        "promotion": promotion,
    }
    path = Path(__file__).with_name("real_text_delay_lm_results.json")
    path.write_text(json.dumps(output, indent=2))
    print(json.dumps({"promotion": promotion}, indent=2))
    print("results:", path)


if __name__ == "__main__":
    main()
