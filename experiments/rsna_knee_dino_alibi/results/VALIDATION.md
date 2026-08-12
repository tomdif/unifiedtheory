# Validation record

Date: 2026-08-09

## Structural CPU test

`python smoke_test.py` passed locally and on the RunPod environment.

| Check | Result |
|---|---:|
| joint slice-permutation max error | 3.73e-8 |
| masked-padding max error | 3.73e-8 |
| irregular-gap attention-bias delta | 0.75 |
| tiny overfit loss | 0.6964 -> 0.0074 |

## DICOM test

`python dicom_smoke.py` generated four shuffled MR DICOM slices. Filename order
had z positions `[12, 0, 8, 4]` mm; the extractor recovered
`[0, 4, 8, 12]` mm from orientation and position tags, then emitted four
`24 x 24 x 3` adjacent-slice images.

## Real backbone test

On an NVIDIA GeForce RTX 4090, `facebook/dinov2-base` encoded five synthetic
images into a finite `[5, 1536]` `CLS || mean(patch)` tensor. See
`backbone_smoke_dinov2_base.json`.

## Full-size cached-feature benchmark

On the same RTX 4090, the physical-ALiBi model processed a synthetic batch of
8 studies x 8 series x 64 slices x 1536 features at 4.65 ms/batch and peaked
at 0.0865 GiB allocated. This excludes DINO and DICOM I/O. See
`gpu_benchmark_4090.json`.

## Pipeline integration

`python pipeline_smoke.py` generated 18 cached studies, trained one physical
ALiBi fold over all 12 targets, reloaded the 45,451-byte checkpoint, ran rank
ensemble inference, and emitted a complete 18 x 13 submission table.

The expanded integration also trained and reloaded the target-specific patch
hierarchy with a zero-initialized cached token adapter (52,053-byte smoke
checkpoint), and exercised OOF-fitted rank-ensemble inference.

## Weak supervision and fold audit

`python stage2_smoke.py` passed the following structural checks:

| Check | Result |
|---|---:|
| report positive / uncertain / negative | 0.93 / 0.55 / 0.06 |
| scanner groups split across folds | 0 |
| patch permutation max error | 4.47e-8 |
| physical slice permutation max error | 2.98e-8 |
| patch+adapter tiny overfit loss | 0.6975 -> 0.0041 |

Checkpoint selection now uses gold validation masks rather than scoring the
weak report teacher against itself.

## OOF ensemble audit

`python ensemble_smoke.py` used three held-out folds and two synthetic model
families whose usefulness alternated by target. Target-wise convex rank
stacking selected the correct member for all 12 targets and achieved 0.9022
nested OOF macro AUC. `pipeline_smoke.py` separately exercised the fitted-blend
submission path.

## Real adapter test

On the RTX 4090, the end-to-end `facebook/dinov2-base` adapter completed a CUDA
forward/backward pass. All frozen backbone parameters remained gradient-free;
six adapter tensors received gradients. See `adapter_smoke_dinov2_base.json`.

## Real competition-data ablation

The rules-authorized RunPod execution extracted all 4,407 training studies.
Two malformed pixel frames were skipped while retaining the remaining valid
slices and series in their studies. The restart-safe index retained scanner
metadata for every cached study.

The fold optimizer produced five complete scanner-group folds with both expert
classes available in all 60 fold/target cells. All 45 preregistered fits
(three aggregators x five folds x three seeds) completed:

| Aggregator | Mean gold OOF macro AUC |
|---|---:|
| mean pooling | **0.66910** |
| index ALiBi | 0.65869 |
| physical ALiBi | 0.65682 |

Physical ALiBi missed its predeclared +0.010 promotion threshold and instead
lost 0.01228 to mean pooling. It is therefore not promoted.

## Fixed mean-pooling ensemble audit

`audit_mean_ensemble.py` retained every mean checkpoint for every target, with
no target-wise model selection. Fold-local rank averaging reached **0.67897**
macro AUC across the same 60 expert fold/target cells: +0.00987 over the average
single-seed cell AUC and +0.00243 over the best single seed. It improved 36
cells, tied 5, and worsened 19.

| Target | Fold-mean gold AUC |
|---|---:|
| ACL | 0.62994 |
| MCL | 0.65222 |
| Medial Meniscus | 0.64667 |
| Lateral Meniscus | 0.67249 |
| Medial OA | 0.75238 |
| Lateral OA | 0.67667 |
| PF OA | 0.72521 |
| Effusion | **0.47545** |
| Synovitis | 0.70079 |
| Baker's | 0.76889 |
| Contusion | 0.69278 |
| Fracture | 0.75417 |

Effusion is the clear failure channel. The rank ensemble is a valid promoted
baseline but not a plausible top-leaderboard endpoint.

## Three-source public-label transfer

A fixed equal arithmetic mean of three independently published LLM report
label tables replaced the original local report teacher. The architecture,
seed, scanner-group folds, and checkpoint-selection rule were held fixed. On
all 60 expert fold-target cells, macro OOF AUC increased from **0.67634** to
**0.75166** (+0.07532); 37 cells improved, 4 tied, and 19 worsened. The largest
gains were Effusion (+0.2730) and ACL (+0.2386). MCL and Medial Meniscus
regressed, so final target-wise family choice remains nested rather than
assuming uniform transfer. See `llm_consensus_teacher_transfer.json` and CSV.

An early nested rank blend of the old and consensus-supervised patch members
scored 0.72622, below the consensus member alone. It is not promoted; the
blend audit will be repeated after the raw DINO/CNN specialists finish.

## Offline inference execution

The complete `kaggle_offline_infer.py` path ran with local DINO weights,
offline Hugging Face flags, all 15 mean checkpoints, fresh image extraction,
and exact submission validation. It took 19.58 seconds on the three-study
public placeholder test and reproduced the direct inference CSV byte-for-byte.
This runtime is a wiring check, not an estimate for the hidden test and not a
leaderboard score.

## Post-submission improvement scouts

Four warm-started fold-0 controls used the promoted consensus checkpoint
(`0.76312` macro AUC) as their fixed anchor. None cleared the predeclared
`+0.005` promotion margin, so none is included in a submission:

| Scout | Best fold-0 macro AUC | Gain | Decision |
|---|---:|---:|---|
| residual target-conditioned slice attention | 0.76399 | +0.00086 | reject |
| multilingual report-embedding distillation | 0.75437 | -0.00875 | reject |
| 64x expert-label weight | 0.75821 | -0.00491 | reject |
| v4 fixed equal-source teacher refresh | 0.75486 | -0.00826 | reject |

The v4 report consensus itself improved gold macro AUC from `0.89187` to
`0.89481`, but that small teacher gain did not transfer in the image-model
scout. The audits therefore point to representation resolution rather than
loss weighting or another teacher blend as the next credible bottleneck.

A higher-resolution extractor was consequently added with a controlled
compute trade: `336x336` DINOv2 inputs, an `8x8` retained token grid, and at
most 24 slices per series. A real-study smoke produced five valid series with
64 patch tokens per slice. Full extraction is an experiment in progress, not
yet a promoted model or score.

## Knee-native SSL and conservative routing

Target-wise routing of the completed 224/336 OOF members was tested with a
nested, expert-only router. Each held-out fold used model choices made on the
other four folds, with a paired stratified-bootstrap support requirement.
Nested macro AUC fell from `0.74847` to `0.74001` (`-0.00846`), so the router
reverted every target to the anchor. The non-nested target oracle is therefore
not a defensible estimate of deployable gain.

A competition-only knee-native DINO-LoRA pretrainer passed its systems
contract. A four-study, batch-two GPU run produced finite invariance, variance,
covariance, masked-reconstruction, cross-series, and metadata losses; used
`5.51 GiB`; and emitted a backbone checkpoint with complete diagnostic-model
key coverage. A limited 32-study supervised compatibility run then completed
with clinical plane masking and zero-initialized pathology specialists at
finite loss `1.16836` and `5.27 GiB` peak memory. The limited expert split has
undefined AUC by design, so neither run is promotion evidence.

The next score-bearing gate is one complete paired fold. Knee-native
pretraining must improve macro expert AUC by at least `0.02`, with no more than
four materially worsened targets, before full cross-validation.
