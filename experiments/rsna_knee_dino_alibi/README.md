# RSNA knee: DINO + physical ALiBi

This is a reproducible test of one narrow hypothesis for the RSNA Knee MRI
abnormality-detection competition:

> Aggregating frozen DINO slice features with attention biased by **physical
> DICOM slice separation** improves scanner-grouped 12-target macro AUC over
> both mean pooling and ordinal/index ALiBi.

It is not a claim that ALiBi plus DINO is automatically leaderboard-leading.
Public work already establishes DINO as a useful baseline; report-label quality,
MRI orientation, site leakage, ensembling, and full-data retraining are at least
as important as the aggregator.  This module isolates the aggregator before
spending time on those additions.

## What is built

The pipeline is hierarchical:

1. DICOM files are ordered by the projection of `ImagePositionPatient` onto
   the slice normal from `ImageOrientationPatient`. Filename order is never
   used as geometry.
2. A fixed physical field of view is cropped. Right knees are put into a
   common orientation. Adjacent slices form a 2.5-D pseudo-RGB image.
3. A frozen DINOv2 or DINOv3 encoder emits `CLS || mean(patch)` per slice.
4. Each series is summarized by masked mean, ordinal ALiBi, or bidirectional
   physical-distance ALiBi.
5. A study transformer fuses all series with plane/fluid/fat-suppression
   metadata. Twelve learned target queries produce the competition logits.

The feature cache makes the three aggregators use exactly the same images,
DINO features, labels, folds, and optimization budget. Optional confidence
columns weight report-derived labels, and optional report embeddings support
image/report contrastive distillation without using reports at test time.

## Data boundary

The competition data are not downloaded by this repository. Join the
competition, accept its rules yourself, and mount the files so the root contains:

```text
train.csv
train_series.csv
train_series/<StudyInstanceUID>/<SeriesInstanceUID>/*.dcm
test.csv
test_series.csv
test_series/<StudyInstanceUID>/<SeriesInstanceUID>/*.dcm
sample_submission.csv
```

Training requires a separate CSV containing `StudyInstanceUID` and all 12
target columns listed in `constants.py`. Missing values are masked. Optional
`<target>__conf` columns are confidence weights. This explicit interface keeps
weak report labels, the small expert-labeled subset, and any pseudo-labels from
being silently conflated.

Test reports are not assumed or consumed. A model that needs report text at
inference is invalid for this pipeline.

## Install and smoke test

```bash
cd experiments/rsna_knee_dino_alibi
python -m pip install -r requirements.txt
python smoke_test.py
python dicom_smoke.py
python pipeline_smoke.py
```

The smoke test is CPU-only and checks:

- permutation equivariance of physical slice attention;
- invariance to masked padding;
- sensitivity to irregular physical gaps;
- tensor-cache/collator compatibility;
- end-to-end gradient flow through both hierarchy levels.

For a full-size synthetic workload on an ordinary CUDA GPU:

```bash
python gpu_benchmark.py --batch 8 --series 8 --slices 64 --feature-dim 1536
```

The checked RunPod RTX 4090 result is in `results/gpu_benchmark_4090.json`.
Physical ALiBi processed about 1,719 studies/s in this cached-feature inference
benchmark and peaked at 0.087 GiB allocated. These are aggregator-only numbers;
DINO encoding and DICOM I/O dominate an end-to-end run.

Validate the actual Hugging Face backbone interface separately with:

```bash
HF_HOME=/workspace/hf_cache python backbone_smoke.py --model-name facebook/dinov2-base
```

The checked DINOv2-base result is in
`results/backbone_smoke_dinov2_base.json`: five synthetic images produced a
finite `[5, 1536]` `CLS || mean(patch)` tensor on the RTX 4090.

## Extract DINO features

DINOv2 is the primary backbone because its public licensing and current public
competition evidence make it the cleanest baseline. DINOv3 should be treated
as an ensemble-diversity experiment and its model-specific license checked
before redistribution.

```bash
python extract_features.py \
  --data-root /workspace/rsna-knee \
  --split train \
  --output /workspace/cache/dinov2-base/train \
  --model-name facebook/dinov2-base \
  --max-slices 64 \
  --batch-size 64

python extract_features.py \
  --data-root /workspace/rsna-knee \
  --split test \
  --output /workspace/cache/dinov2-base/test \
  --model-name facebook/dinov2-base \
  --max-slices 64 \
  --batch-size 64
```

On an internet-disabled Kaggle inference notebook, mount the pretrained model
as a dataset and pass its local path with `--local-files-only`.

## Preregistered ablation

Use scanner/vendor/model/field-strength groups from the generated cache index,
or supply externally audited fold assignments in the labels file. Random folds
are implemented only as a loudly marked fallback and are not evidence for
generalization.

```bash
python run_ablation.py \
  --cache-index /workspace/cache/dinov2-base/train/train_cache_index.csv \
  --labels-csv /workspace/labels/train_targets.csv \
  --output /workspace/runs/dinov2_alibi \
  --seeds 2026 2027 2028 \
  --folds 5 \
  --batch-size 12

python summarize_ablation.py /workspace/runs/dinov2_alibi
```

Promotion is predeclared as at least **+0.010 scanner-grouped macro AUC** for
physical ALiBi over the stronger of mean pooling and ordinal ALiBi, averaged
over complete paired fold/seed runs. Anything smaller is treated as negative or
inconclusive, not re-described as a win.

The sequence of escalation is:

1. frozen DINOv2-base, three aggregation controls;
2. only if promoted: DINOv2-large and partial backbone unfreezing;
3. only then: DINOv3 as a separately cached ensemble member;
4. five-fold OOF blend and full-data refit for submission.

## Inference

```bash
python infer.py \
  --cache-index /workspace/cache/dinov2-base/test/test_cache_index.csv \
  --sample-submission /workspace/rsna-knee/sample_submission.csv \
  --checkpoints /workspace/runs/dinov2_alibi/seed*/physical_alibi_fold*.pt \
  --ensemble rank \
  --output /workspace/submission.csv
```

Rank averaging is the default because the competition metric is macro AUC.

## RunPod handoff

Copy this directory to the pod, install dependencies in its persistent volume,
and run the smoke test before feature extraction. The expensive work is DINO
encoding; the cached hierarchy trains quickly on an ordinary CUDA GPU.

The current code does not accept Kaggle rules, fetch private data, submit to a
leaderboard, or claim a score that has not been measured.
