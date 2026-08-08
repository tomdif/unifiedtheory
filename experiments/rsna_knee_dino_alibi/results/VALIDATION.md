# Validation record

Date: 2026-08-08

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

## Unexecuted boundary

No competition data were present on the RunPod volume. Therefore no real
cross-validation or leaderboard score is claimed. The preregistered ablation
begins only after the user mounts data obtained under the competition rules and
provides an auditable 12-target label table.
