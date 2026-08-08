# Real-text delay-memory LM verdict

Date: 2026-08-08  
Hardware: NVIDIA GeForce RTX 4090  
Software: PyTorch 2.4.1+cu124, BF16

## Protocol

- Dataset: canonical raw WikiText-2 files from the PyTorch examples repository.
- Tokenization: raw bytes (vocabulary size 256).
- Training context: 128 bytes.
- Training budget: 3,000 updates x 64 sequences x 128 bytes = 24,576,000 bytes per model and seed.
- Optimizer, learning-rate schedule, clipping, batches, seeds, and evaluation bytes were held fixed.
- Two seeds per model.
- Test contexts: 128, 256, and 512 bytes.
- Lower bits per byte (BPC) is better.

The original predeclared promotion criterion was:

1. QueryTriad BPC at context 256 is at least 0.02 lower, while its BPC at context 128 is no more than 0.02 worse; or
2. BPC at context 256 is within 0.01 and QueryTriad is at least 1.25x faster.

## Mean results

| Model | Parameters | BPC 128 | BPC 256 | BPC 512 | Train bytes/s |
|---|---:|---:|---:|---:|---:|
| QueryTriad | 127,622 | 2.2359 | 2.3720 | 2.7790 | 441,114 |
| Absolute sinusoidal Transformer | 133,568 | 2.0997 | 3.7780 | 4.8016 | 530,890 |
| ALiBi Transformer | 133,568 | 2.1127 | 2.0980 | 2.1535 | 538,519 |

Against the strong relative-position control, QueryTriad is worse by 0.1231,
0.2740, and 0.6256 BPC at contexts 128, 256, and 512 respectively. It also
runs at 81.9% of ALiBi throughput. It therefore fails both promotion clauses.

## Verdict

The earlier apparent long-context advantage over the absolute-position
Transformer does **not** survive the ALiBi control. The absolute baseline's
out-of-distribution collapse was a positional-encoding artifact. This
experiment supplies no evidence that the three-sheet delay carrier improves
real-text language modeling at this scale.

What survives is narrower:

- the QueryTriad implementation is a functioning GPU language model;
- its learned delay biases extrapolate more gracefully than absolute
  sinusoidal positions in this setup;
- an ordinary relative-position Transformer achieves better loss and higher
  throughput, so relative timing alone does not justify the new architecture.

This is a useful falsification result. Further LLM-scale investment should be
conditional on a revised mechanism that predicts an advantage beyond relative
position bias, followed by another parameter-, token-, and kernel-matched
test.

## Reproducibility artifacts

- `real_text_delay_lm_experiment.py`: QueryTriad and absolute Transformer.
- `alibi_lm_control.py`: exact ALiBi control. Its fused formulation was
  checked against the explicit bias matrix in float64 with maximum absolute
  error 7.32e-16.
- `results/real_text_delay_lm_results.json`: raw two-seed
  QueryTriad/absolute results.
- `results/alibi_lm_results.json`: raw two-seed ALiBi results.

Dataset checksums are embedded in both result JSON files.

On a CUDA host, reproduce the two runs from this directory with:

```bash
python3 -u real_text_delay_lm_experiment.py \
  --seeds 2 --steps 3000 --batch 64 --eval-batch 16 --eval-bytes 524288
python3 -u alibi_lm_control.py \
  --seeds 2 --steps 3000 --batch 64 --eval-batch 16 --eval-bytes 524288
```
