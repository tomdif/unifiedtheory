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
3. A DINOv2 or DINOv3 encoder emits `CLS || mean(patch)` plus an optional
   compact spatial patch grid per slice.
4. Each pathology has its own spatial patch query, so ACL, meniscus, marrow,
   and fluid targets need not attend to the same anatomy.
5. Each series is summarized by masked mean, ordinal ALiBi, or bidirectional
   physical-distance ALiBi.
6. A study transformer fuses all series with plane/fluid/fat-suppression
   metadata. Twelve learned target queries produce the competition logits.

The stage-two model can train a zero-initialized residual adapter in cached
DINO token space. This is substantially cheaper than repeatedly decoding the
full DICOM corpus while still testing lightweight representation adaptation. A
separate end-to-end DINO adapter is included for the final fine-tuning
experiment and has been checked against the real DINOv2-base CUDA backbone.

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
python stage2_smoke.py
python ensemble_smoke.py
python pipeline_smoke.py
```

The smoke test is CPU-only and checks:

- permutation equivariance of physical slice attention;
- invariance to masked padding;
- sensitivity to irregular physical gaps;
- tensor-cache/collator compatibility;
- end-to-end gradient flow through both hierarchy levels.

The stage-two tests additionally check multilingual report polarity, gold-label
override, scanner-group integrity, patch and slice permutation invariance,
token-adapter training, target-wise nested OOF blending, and both ensemble
inference paths.

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
HF_HOME=/workspace/hf_cache python adapter_smoke.py \
  --model-name facebook/dinov2-base --local-files-only
```

The checked DINOv2-base result is in
`results/backbone_smoke_dinov2_base.json`: five synthetic images produced a
finite `[5, 1536]` `CLS || mean(patch)` tensor on the RTX 4090.
The adapter test also completed a CUDA forward/backward pass with all frozen
DINO tensors gradient-free and 51,488 adapter parameters receiving gradients;
see `results/adapter_smoke_dinov2_base.json`.

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
  --patch-grid 4 \
  --max-slices 64 \
  --batch-size 64

python extract_features.py \
  --data-root /workspace/rsna-knee \
  --split test \
  --output /workspace/cache/dinov2-base/test \
  --model-name facebook/dinov2-base \
  --patch-grid 4 \
  --max-slices 64 \
  --batch-size 64
```

On an internet-disabled Kaggle inference notebook, mount the pretrained model
as a dataset and pass its local path with `--local-files-only`.

## Leakage-safe labels and folds

First freeze whole scanner groups into folds. The greedy assignment balances
the 12 observed positive masses without ever splitting a scanner group:

```bash
python folds.py \
  --cache-index /workspace/cache/dinov2-base/train/train_cache_index.csv \
  --labels-csv /workspace/labels/raw_targets.csv \
  --output /workspace/labels/folded_targets.csv \
  --group-column scanner_group --folds 5
```

Reports are train-only privileged information. The inspectable multilingual
rule teacher produces soft targets, optional NLI scores provide an independent
channel, calibration is fitted out of fold, and expert labels always override
weak labels:

```bash
python score_reports_nli.py \
  --train-csv /workspace/labels/folded_reports.csv \
  --output /workspace/labels/report_nli.csv

python report_teacher.py \
  --train-csv /workspace/labels/folded_reports.csv \
  --nli-csv /workspace/labels/report_nli.csv \
  --output /workspace/labels/train_targets.csv
```

Checkpoint selection uses only expert (`__gold`) validation entries whenever
both classes are available. Weak labels can increase training coverage but can
never make their own teacher look good in validation.

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
2. target-specific `4 x 4` patch hierarchy with a 64-wide cached token adapter;
3. DINOv2-large and an end-to-end final-block/adapter fine-tune only if stage
   two improves gold OOF AUC;
4. DINOv3 as a separately cached ensemble member, subject to its license;
5. nested target-wise OOF blend and fold ensemble for submission.

All stage-two folds are trained with:

```bash
python run_stage2.py \
  --cache-index /workspace/cache/dinov2-base/train/train_cache_index.csv \
  --labels-csv /workspace/labels/train_targets.csv \
  --output /workspace/runs/dinov2_patch \
  --aggregator physical_alibi --token-adapter-bottleneck 64 \
  --folds 5 --batch-size 8 \
  --extra --series-dropout 0.15
```

Repeat folds 0 through 4 for each promoted backbone. Do not tune on the public
leaderboard; grouped OOF validation is the model-selection surface.

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

For a heterogeneous ensemble, fit convex weights separately for each target
using OOF predictions, and report the nested-fold score (not the optimistic
refit score):

```bash
python fit_oof_ensemble.py \
  --labels-csv /workspace/labels/train_targets.csv \
  --member 'summary=/workspace/runs/base/physical_alibi_fold*_oof.csv' \
  --member 'patch=/workspace/runs/patch/patch_physical_alibi_fold*_oof.csv' \
  --output /workspace/runs/blend.json

python ensemble_infer.py \
  --cache-index /workspace/cache/dinov2-base/test/test_cache_index.csv \
  --sample-submission /workspace/rsna-knee/sample_submission.csv \
  --blend /workspace/runs/blend.json \
  --member 'summary=/workspace/runs/base/physical_alibi_fold*.pt' \
  --member 'patch=/workspace/runs/patch/patch_physical_alibi_fold*.pt' \
  --output /workspace/submission.csv
```

This is a serious leaderboard pipeline, not a guarantee of first place. The
go/no-go evidence is five-fold scanner-grouped gold OOF AUC, target-level
stability, and ensemble diversity. No architectural claim substitutes for
those measurements.

## RunPod handoff

Copy this directory to the pod, install dependencies in its persistent volume,
and run the smoke test before feature extraction. The expensive work is DINO
encoding; the cached hierarchy trains quickly on an ordinary CUDA GPU.

The current code does not accept Kaggle rules, fetch private data, submit to a
leaderboard, or claim a score that has not been measured.
