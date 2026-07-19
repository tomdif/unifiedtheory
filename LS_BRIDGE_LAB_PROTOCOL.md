# LSBridge — Photonic Waveguide Lab Protocol (one-page)

**Goal.** Test the LSBridge prediction that a Gaussian wavepacket in a
1D dispersive system spreads anomalously slowly compared to free
Schrödinger evolution. **Observable**:
`R(σ_0) = T_measured(σ_0) / T_free,predicted(σ_0)`.

---

## Setup

| Item | Spec |
|---|---|
| **Platform** | 1D coupled-waveguide array (femtosecond-laser-written silica or photorefractive) |
| **Lattice spacing** | `a = 10–20 μm` |
| **Hopping** | `t ≈ 1 mm⁻¹` (set by waveguide spacing / index contrast) |
| **Diffraction coefficient** | `D = t · a² ≈ 100–400 μm² / mm` |
| **Chip length** | 100–200 mm |
| **Wavelength** | 633–810 nm (single-mode for the channel) |
| **Input shaping** | Beam-shaping optics for Gaussian σ_0 ∈ [1, 50] μm |
| **Output** | CCD/CMOS imaging of multiple z-cleaved slices, or in-line 3D scan |

**Test schedule.** For each of the σ_0 values below, image σ(z) at ≥ 5
propagation distances. Fit each profile to a Gaussian; extract σ(z);
determine the doubling distance z* where σ(z*) = 2σ_0.

| σ_0 (μm) | z*_free (mm) | LSBridge prediction (μm-natural ℓ ≈ 1) |
|---|---|---|
| 1 | 0.017 | 1.77× slower (also 0.03 mm) |
| 2 | 0.069 | 2.12× slower |
| 3 | 0.156 | 4.30× slower |
| 5 | 0.43 | **57× slower (24.7 mm)** ← cleanest signal |
| 7 | 0.85 | 545× slower (462 mm — beyond chip) |
| 10 | 1.73 | 10⁵× slower (NOT observable — beam frozen on chip) |

The σ_0 = 5 μm point is the **sweet spot**: free Schrödinger doubles in
0.43 mm, LSBridge predicts 24.7 mm — both fit on a 50 mm chip and the
predicted slowdown is a factor 57× which is well above any plausible
systematic.

---

## Definitions

- **σ(z) extraction.** Fit each transverse intensity profile I(x; z) to
  `A · exp(-(x − x_c)² / (2σ²)) + B`. Use a linear-background fit to
  remove scattered light.
- **Doubling distance.** Smallest z* such that σ(z*) = 2σ_0.
  Interpolate from the {z, σ(z)} pairs.
- **R_measured(σ_0)** := `z*_measured / z*_free,predicted`, where
  `z*_free,predicted = √3 · σ_0² / D` and D is calibrated independently.

---

## Independent calibration of D

Run a CONTROL measurement at the smallest σ_0 (e.g. σ_0 = 1 μm) where
LSBridge predicts only a 1.77× slowdown. Use a beam with `σ_0 < ℓ` (if
ℓ has any reasonable scale) where LSBridge is in its `σ_dim < 1` regime
and the slowdown is mild. Match against the predicted shape across the
whole sweep.

Alternatively, characterize `D = t · a²` directly from single-site-input
spreading measurements which are well understood and not affected by
LSBridge in the same regime (since they don't have a well-defined initial Gaussian σ_0).

---

## Falsification matrix

| Measurement outcome | LSBridge verdict |
|---|---|
| `R_measured ≈ 1 ± 5%` across all σ_0 ∈ [3, 10] μm | **FALSIFIED** (or natural length ℓ ≪ 1 μm) |
| `R_measured = 1.5–3×` for σ_0 = 5 μm | borderline — repeat with finer σ_0 sweep |
| `R_measured > 5×` at σ_0 = 5 μm, growing to > 100× at σ_0 = 7–8 μm | **strong evidence**: ℓ ≈ 1 μm |
| `R(σ_0)` follows the proved curve shape `≈ exp(σ_0)/σ_0²` across multiple σ_0 | **definitive**: LSBridge confirmed at this length scale |

For a quantitative fit, hand the `(σ_0, R_measured, R_err)` triples to
`scripts/lsbridge_ell_inference.py`. The fit reports:
- best-fit `ℓ` with 1σ confidence interval,
- reduced χ² (consistent fit if ≲ 5, in tension if ≫ 1),
- or a clear falsification if no `ℓ ∈ [1 nm, 100 μm]` makes the data
  consistent.

---

## Confounds to control

1. **Loss / scattering** broadens σ(z) classically. Subtract via control with low-loss material.
2. **Kerr nonlinearity** in glass; use low input power (≤ μW).
3. **Coupling losses** at the input face — affect σ_0 calibration. Characterize via near-field imaging.
4. **Next-nearest-neighbor hopping** modifies effective D. Characterize via single-site discrete diffraction measurements.
5. **Imperfect Gaussian shaping** of the input beam — verify by fitting input profile.
6. **Polarization effects** if the array has birefringence — fix polarization at input.

## Confounder discrimination — uniquely-LSBridge σ_0 windows

Each plausible confounder predicts a **distinct shape** for `R(σ_0)`. The
LSBridge prediction is `R(σ_0) ≈ exp(σ_0)/σ_0²`, a smoothly-growing
exponential. Comparison (`scripts/lsbridge_confounder_discrimination.py`):

| Mechanism | R(σ_0) shape | Discriminator |
|---|---|---|
| **LSBridge** | smooth exp(σ_0)/σ_0², 1.77→57→238 over σ_0 = 1→5→6 μm | this protocol's target |
| Linear loss | R ≡ 1 (independent of σ_0) | flat = NOT LSBridge |
| Kerr self-focusing | R < 1, decreases with σ_0 | acceleration = NOT LSBridge |
| Anderson localization | R = 1 below threshold ξ_loc, sharp blow-up above | sharp threshold = NOT LSBridge |
| NNN hopping | R = 1/(1+ε)² ≈ const < 1 | constant ≠ 1 = NNN, not LSBridge |

**Uniquely-LSBridge measurement window:** σ_0 ∈ [3, 7] μm. In this range
the LSBridge prediction exceeds **every plausible confounder by ≥ 5×**.
The tightest 50× discrimination is at σ_0 ∈ [4.9, 6.5] μm.

**Recommended discrimination measurement schedule:**
- σ_0 = 3 μm: LSBridge R ≈ 4.9. Loss/Kerr/AL/NNN all R ≤ 1.0.
- σ_0 = 5 μm: LSBridge R ≈ 57. All confounders R ≤ 1.0 (Kerr: 0.53).
- σ_0 = 6 μm: LSBridge R ≈ 239. AL with ξ = 10 μm starts to contribute (R = 2.7).
- σ_0 = 7 μm: LSBridge R ≈ 1100. AL ξ = 10 grows to 54 — still distinguishable.

If the shape of measured `R(σ_0)` across these four points matches the
LSBridge exponential curve (not flat, not decreasing, not threshold-like),
the prediction is **uniquely identified**.

## Precision requirements (from sensitivity analysis)

`scripts/lsbridge_sensitivity_analysis.py` Monte Carlo recovery shows:

| Parameter | Requirement |
|---|---|
| Measurement noise | ≤ 5% per R measurement gives < 0.5% ℓ recovery error |
| Number of σ_0 values | N ≥ 6 saturates verdict reliability |
| σ_0 range | [1, 7] μm gives sub-1% ℓ accuracy if ℓ ~ 1 μm |
| Verdict robustness | Even at 20% noise, 100% trials give CONSISTENT verdicts |

The test is **highly forgiving** of measurement noise thanks to the
exponential lever arm at the upper σ_0 end: even crude (~10%) measurements
yield order-of-magnitude verdicts.

---

## Deliverables (from the run)

1. A CSV `measurements.csv` with columns `sigma_0_um, R_measured, R_err`.
2. The output of `python3 scripts/lsbridge_ell_inference.py --csv measurements.csv`, which yields:
   - best-fit ℓ + 1σ range, OR
   - falsification verdict + reduced χ².
3. Plots: σ(z) at each σ_0 + R(σ_0) curve overlaid with the proved
   theoretical bounds.

Predictions and proved bounds are in
`UnifiedTheory/LayerB/LohmillerSlotineGaussianWidthDynamics.lean`.
Numerical curves in `results/lsbridge_predictions/`.
