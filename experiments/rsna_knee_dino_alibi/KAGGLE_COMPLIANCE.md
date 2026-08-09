# Kaggle competition compliance boundary

Audited against the official RSNA Knee Abnormality Detection rules and
evaluation pages on 2026-08-09:

- https://www.kaggle.com/competitions/rsna-knee-abnormality-detection/rules
- https://www.kaggle.com/competitions/rsna-knee-abnormality-detection/overview/evaluation

This pipeline is designed around the following hard constraints:

- hidden-test inference is image-only, internet-disabled, and time-budgeted;
- report text and the public NLI teacher are used only for training labels;
- no validation or test image is manually labeled or manually predicted;
- scanner groups never cross folds;
- weak labels never select their own checkpoints: selection uses available
  expert validation masks only;
- external pretrained assets are public and listed with licenses in
  `external_assets.json`;
- `kaggle_offline_infer.py` validates the exact sample-submission schema,
  study order, finite probabilities, and the nine-hour notebook boundary;
- competition data and derived private artifacts must not be committed or
  shared outside a team whose members have accepted the competition rules.

The repository is public. Competition-specific code must not be pushed as a
private competitive advantage: if published, the applicable rules require it
to be made available to all competitors through the competition's associated
Kaggle forum or notebook under a permissive license. Publication and any
leaderboard submission remain explicit user actions.

This file is an engineering audit, not legal advice. The official rules remain
authoritative.
