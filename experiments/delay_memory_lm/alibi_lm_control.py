"""Strong relative-position control for the real-text QueryTriad experiment."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F

from real_text_delay_lm_experiment import (
    EVAL_CONTEXTS,
    TRAIN_CONTEXT,
    VOCAB,
    download_dataset,
    evaluate,
    parameter_count,
    train,
)


def alibi_slopes(heads):
    if heads & (heads - 1):
        raise ValueError("this compact implementation requires power-of-two heads")
    start = 2.0 ** (-2.0 ** -(math.log2(heads) - 3.0))
    return torch.tensor([start ** (index + 1) for index in range(heads)])


class AlibiLayer(nn.Module):
    def __init__(self, width=64, heads=4, ff=128):
        super().__init__()
        self.width = width
        self.heads = heads
        self.head_width = width // heads
        self.norm1 = nn.LayerNorm(width)
        self.qkv = nn.Linear(width, 3 * width)
        self.output = nn.Linear(width, width)
        self.norm2 = nn.LayerNorm(width)
        self.ff = nn.Sequential(
            nn.Linear(width, ff), nn.GELU(), nn.Linear(ff, width)
        )
        self.register_buffer("slopes", alibi_slopes(heads), persistent=False)

    def _fused_alibi_attention(self, query, key, value):
        """Compute exact causal ALiBi attention through fused SDPA.

        For causal positions j <= i, the usual bias is
        ``-slope * (i - j)``.  The ``-slope * i`` term is constant across
        every row and therefore cancels in softmax.  We encode the remaining
        ``slope * j`` term as one extra query/key dot-product coordinate.  We
        pad to 32 dimensions so CUDA can retain its fused attention kernel.
        """
        batch, heads, length, head_width = query.shape
        padded_width = 32
        if head_width + 1 > padded_width:
            raise ValueError("increase padded_width for this head size")

        query_scale = math.sqrt(padded_width / head_width)
        bias_scale = math.sqrt(padded_width)
        positions = torch.arange(
            length, device=query.device, dtype=query.dtype
        )
        q_bias = query.new_full((batch, heads, length, 1), bias_scale)
        k_bias = (
            self.slopes.to(device=key.device, dtype=key.dtype)[None, :, None, None]
            * positions[None, None, :, None]
        ).expand(batch, -1, -1, -1)
        tail = padded_width - head_width - 1
        q_tail = query.new_zeros((batch, heads, length, tail))
        k_tail = key.new_zeros((batch, heads, length, tail))
        v_tail = value.new_zeros((batch, heads, length, padded_width - head_width))
        query_augmented = torch.cat(
            (query * query_scale, q_bias, q_tail), dim=-1
        )
        key_augmented = torch.cat((key, k_bias, k_tail), dim=-1)
        value_augmented = torch.cat((value, v_tail), dim=-1)
        attended = F.scaled_dot_product_attention(
            query_augmented,
            key_augmented,
            value_augmented,
            dropout_p=0.0,
            is_causal=True,
        )
        return attended[..., :head_width]

    def forward(self, sequence):
        batch, length, _ = sequence.shape
        state = self.norm1(sequence)
        qkv = self.qkv(state).view(
            batch, length, 3, self.heads, self.head_width
        )
        query, key, value = qkv.unbind(dim=2)
        query = query.transpose(1, 2)
        key = key.transpose(1, 2)
        value = value.transpose(1, 2)
        attended = self._fused_alibi_attention(query, key, value)
        attended = attended.transpose(1, 2).reshape(batch, length, self.width)
        sequence = sequence + self.output(attended)
        return sequence + self.ff(self.norm2(sequence))


class AlibiTransformerLM(nn.Module):
    def __init__(self, width=64, layers=3, heads=4):
        super().__init__()
        self.embedding = nn.Embedding(VOCAB, width)
        self.layers = nn.ModuleList([
            AlibiLayer(width, heads) for _ in range(layers)
        ])
        self.norm = nn.LayerNorm(width)
        self.head = nn.Linear(width, VOCAB)

    def forward(self, tokens):
        state = self.embedding(tokens)
        for layer in self.layers:
            state = layer(state)
        return self.head(self.norm(state))


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
        args.seeds, args.steps, args.batch = 1, 3, 4
        args.eval_batch, args.eval_bytes = 2, 4096
    device = torch.device("cuda")
    dataset, metadata = download_dataset(Path(__file__).with_name("wikitext2_raw"))
    dataset = {key: value.to(device) for key, value in dataset.items()}
    runs = []
    partial = Path(__file__).with_name("alibi_lm_partial.json")
    for seed_index in range(args.seeds):
        seed = 17000 + seed_index
        torch.manual_seed(seed)
        model = AlibiTransformerLM().to(device)
        training = train(
            model, dataset["train"], args.steps, args.batch,
            2.0e-3, seed, device,
        )
        evaluation = {
            split: {
                f"context_{context}": evaluate(
                    model, dataset[split], context, args.eval_batch,
                    args.eval_bytes, device,
                )
                for context in EVAL_CONTEXTS
            }
            for split in ("valid", "test")
        }
        row = {
            "seed": seed_index,
            "model": "alibi_transformer",
            "parameters": parameter_count(model),
            "training": training,
            "evaluation": evaluation,
        }
        runs.append(row)
        partial.write_text(json.dumps({"runs": runs}, indent=2))
        print(
            f"seed={seed_index} params={row['parameters']:,} "
            f"test128={evaluation['test']['context_128']['bits_per_byte']:.3f} "
            f"test256={evaluation['test']['context_256']['bits_per_byte']:.3f} "
            f"test512={evaluation['test']['context_512']['bits_per_byte']:.3f} "
            f"tok/s={training['tokens_per_second']:,.0f}"
        )
    output = {
        "status": "ALiBi relative-position control",
        "dataset": metadata,
        "protocol": vars(args),
        "runs": runs,
        "means": {
            f"test_bpc_{context}": float(np.mean([
                row["evaluation"]["test"][f"context_{context}"]["bits_per_byte"]
                for row in runs
            ]))
            for context in EVAL_CONTEXTS
        } | {
            "tokens_per_second": float(np.mean([
                row["training"]["tokens_per_second"] for row in runs
            ]))
        },
    }
    path = Path(__file__).with_name("alibi_lm_results.json")
    path.write_text(json.dumps(output, indent=2))
    print(json.dumps(output["means"], indent=2))
    print("results:", path)


if __name__ == "__main__":
    main()
