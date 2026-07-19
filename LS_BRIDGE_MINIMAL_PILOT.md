# LSBridge — Minimal Photonic Pilot Protocol (one page)

**Cost-minimal experiment to definitively confirm or falsify LSBridge backreaction in a photonic waveguide array. Total time-on-equipment estimate: 1–2 days.**

## Setup

- 1D coupled-waveguide array, femtosecond-laser-written silica
- Lattice spacing `a = 15 μm`, hopping `t ≈ 1 mm⁻¹`
- Diffraction coefficient `D = t·a² ≈ 225 μm²/mm`
- Chip length: **50 mm** (sufficient for σ_0 ≤ 7 μm)
- Wavelength: 633 nm (single-mode)
- Input: shaped Gaussian beam, σ_0 set via beam-shaping optics

## Four measurements

| σ_0 | Required precision on σ_0 | Free-Schrödinger z*_free | LSBridge prediction z*_LS | Slowdown |
|---|---|---|---|---|
| **3 μm** | ±0.3 μm (10%) | 0.156 mm | 0.671 mm | **4.9×** |
| **5 μm** | ±0.5 μm (10%) | 0.433 mm | 24.7 mm | **57×** |
| **6 μm** | ±0.6 μm (10%) | 0.624 mm | 149 mm (off-chip → cap at chip end) | **239×** |
| **7 μm** | ±0.7 μm (10%) | 0.850 mm | 463 mm (off-chip) | **545×** |

At σ_0 = 6 and 7 μm, the LSBridge prediction exceeds the chip length. If observed:
- If beam **doubles within 50 mm** → not LSBridge.
- If beam **fails to double within 50 mm** → consistent with LSBridge prediction.

## Procedure

For each of σ_0 ∈ {3, 5, 6, 7} μm:

1. Shape the input Gaussian; verify σ_0 via near-field imaging.
2. Image σ(z) at **5 propagation distances** along the chip:
   - σ_0 = 3 μm: z ∈ {0.1, 0.3, 0.6, 1.0, 2.0} mm.
   - σ_0 = 5 μm: z ∈ {0.5, 5, 15, 30, 50} mm.
   - σ_0 = 6 μm: z ∈ {1, 10, 25, 40, 50} mm.
   - σ_0 = 7 μm: z ∈ {2, 15, 30, 45, 50} mm.
3. Fit each transverse intensity profile to `A·exp(−(x − x_c)²/(2σ²)) + B`.
4. Compute z* such that σ(z*) = 2·σ_0 (interpolate from the {z, σ(z)} pairs).
5. Compute `R(σ_0) := z* / z*_free,predicted = z* / (√3 · σ_0² / D)`.

## Imaging precision requirement

- σ(z) extraction accuracy: ±5% per fit.
- This translates to ~3% relative noise on R per data point.
- Blind challenge confirms 5% per-point noise yields 100% correct classification across the four-measurement schedule.

## Independent calibration of D

Single-site input control: launch a beam into a single waveguide and measure discrete diffraction. Fit to standard discrete-Schrödinger spreading to extract `t · a²` directly. Without this, all R measurements have a multiplicative D uncertainty.

## Pass / fail criterion

Run the four R(σ_0) measurements through `scripts/lsbridge_ell_inference.py`:

```bash
python3 scripts/lsbridge_ell_inference.py --csv your_measurements.csv
```

Then check against `scripts/lsbridge_confounder_discrimination.py` to rule out alternatives.

| Outcome | Verdict |
|---|---|
| Classified as LSBridge with reduced χ² < 5 and 1σ ℓ range narrow | **CONFIRMED LSBridge** (blind challenge predicts ≥ 95% recall) |
| Classified as Kerr, NNN, AL, or linear loss with high confidence | **FALSIFIED LSBridge** (blind challenge: 0% false-positive rate from each confounder) |
| Reduced χ² > 20 for all 5 candidate models | Anomalous regime — re-examine systematics (loss, nonlinearity, polarization) |

## Confounder fingerprints at the recommended schedule

| σ_0 (μm) | LSBridge R | Linear loss R | Kerr (n₂σ₀²=0.5) R | AL (ξ=10 μm) R | NNN (ε=0.05) R |
|---|---|---|---|---|---|
| 3 | **4.88** | 1.0 | 0.63 | 1.0 | 0.91 |
| 5 | **56.6** | 1.0 | 0.50 | 1.0 | 0.91 |
| 6 | **239** | 1.0 | 0.46 | 2.7 | 0.91 |
| 7 | **1,096** | 1.0 | 0.41 | 54.6 | 0.91 |

The shapes are utterly different: LSBridge alone grows exponentially.

## Total time estimate

- Beam shaping + calibration: 4 hours.
- 4 × 5 = 20 σ(z) measurements: ~6 hours.
- Analysis (running the inference script + confounder discrimination): < 1 hour.
- **Total: 1–2 working days.**

## What this experiment establishes

| Result | Implication |
|---|---|
| R(σ_0) follows LSBridge curve | Strong evidence for the LSBridge backreaction prediction at the photonic length scale ℓ ≈ 1 μm. |
| R(σ_0) ≡ 1 (flat) | LSBridge predicted slowdown at σ_0 ≥ 3 μm is FALSIFIED (or natural length scale ℓ ≪ 1 μm). |
| R(σ_0) matches Kerr / AL shape | Anomalous spreading attributable to that mechanism, not LSBridge. |

## After a successful pilot

Scale up to the full schedule of `LS_BRIDGE_LAB_PROTOCOL.md` to fit ℓ precisely. Bayesian posterior on ℓ at multiple wavelengths to test for any wavelength dependence (which would point to a deeper physical mechanism).
