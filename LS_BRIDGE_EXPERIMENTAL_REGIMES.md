# LSBridge experimental regimes — falsifiability map

**Companion to:** `LS_BRIDGE_WRITEUP.md` (theorem stack),
`scripts/lsbridge_predictions.py`, `scripts/lsbridge_experimental_regimes.py`,
and `results/lsbridge_predictions/`.

**Status:** the LSBridge Lean program closes a complete theorem stack
(A, B, C.1–C.3, D.1–D.5 + D dynamics 1–3, full E prediction suite, σ(t)
Parts 1–8). At zero `sorry`, standard axioms only, 3011-job UnifiedTheory
build. This document does **not** prove anything new; it maps the proved
predictions to candidate experimental platforms and identifies the regimes
where they could be falsified.

---

## 1. What is predicted

### 1.1 The Gaussian-width ODE

From the matter–geometry coupled system at the proper Gaussian + quadratic
phase ansatz (Backreaction file, Part 12), the leading-order curved
HJ-with-Bohm reduces to

```
σ̈ · σ + (σ − 1) · σ̇² = 0.            (LSBridge backreaction ODE)
```

The first integral (`gaussian_width_first_integral`) gives the conserved
quantity `σ̇ · eˢ / σ = C`, hence

```
σ̇ = C · σ · exp(−σ).                  (implicit solution form)
```

### 1.2 Three falsifiable predictions (Gaussian sector)

The three signatures below are *Gaussian-sector* predictions. The sech-curved
counterpart has been derived in Lean (Backreaction Part 17): it shares the
same structural LHS `ξ·ξ_pp + ξ_prime²·(ξ−1)` but with a nonzero source
`ℏ²/(m²·ξ)`. Therefore **frozen states are forbidden for sech**
(`sech_curved_rejects_frozen`) and the qualitative LSBridge signatures
below are Gaussian-specific, not family-level.

1. **Frozen solutions are admissible (Gaussian-specific).** The trivial
   `σ ≡ σ_const` solves the LSBridge ODE for any `σ_const > 0`
   (with `C = 0`). Free Schrödinger forbids this: `σ̈ = ℏ²/(m²σ³) ≠ 0`.
   So the LSBridge framework allows **non-spreading Gaussian wavepackets**
   that free QM does not. The same coupling on sech profiles forbids the
   frozen state.
   *(Lean: `gaussian_width_dynamics_differs_from_free_schrodinger`,
   `sech_curved_rejects_frozen`.)*

2. **Exponentially-slow doubling time.** The time to double `σ` from
   `σ_0` to `2σ_0` satisfies the two-sided bound
   ```
   exp(σ_0)/(2C)  ≤  T_LS(σ_0)  ≤  exp(2σ_0)/C.
   ```
   In contrast, free Schrödinger gives `T_free(σ_0) = √3 · σ_0² · m / ℏ`.
   *(Lean: `doubling_time_two_sided_bound`.)*

3. **Optimal spreading width at σ = 1.** The spreading rate
   `σ̇ = C · σ · exp(−σ)` is maximized at `σ = 1` with value `C/e`. The
   LSBridge framework predicts a **unique fastest-spreading width**;
   wider or narrower wavepackets spread more slowly.
   *(Lean: `lsbridge_spreading_rate_max_at_one`.)*

### 1.3 The universal observable

The cleanest dimensionless observable to test is

```
R(σ_0) := T_doubling,measured(σ_0) / T_doubling,free(σ_0).
```

The numerical predictions for `R(σ_0)` (computed by
`scripts/lsbridge_predictions.py` and confirmed against the proved bounds):

| σ_0 (dimensionless) | R(σ_0) | Proved bound |
|---|---|---|
| 0.5 | 3.33 | [1.90, 6.28] |
| 1.0 | 1.77 | [0.79, 4.27] |
| 2.0 | 2.12 | [0.53, 7.88] |
| 5.0 | 56.6 | [1.7, 5.1×10²] |
| 10.0 | 1.48 × 10⁵ | [64, 2.8×10⁶] |
| 20.0 | ~10¹³ | exponential blow-up |

**Headline regime**: at `σ_0 ≈ 5` the slowdown is ~57×; at `σ_0 ≈ 10` it
is ~10⁵×. **Broad initial wavepackets are the sweet spot for detection.**

---

## 2. Which platforms can measure it

The mapping from dimensionless `(σ, C)` to physical parameters factors
through a single platform-specific natural length scale `ℓ`. The
dimensionless width is `σ_dim = σ_phys / ℓ`. The observable `R(σ_0)` is
universal — only its physical-units σ_0 axis depends on `ℓ`.

### 2.1 Photonic waveguide arrays (best near-term candidate)

**System.** Femtosecond-laser-written waveguide arrays in glass realize
the discrete Schrödinger equation `i∂_z ψ_n = −t(ψ_{n+1} + ψ_{n−1})`
along propagation distance `z`. The continuous limit is
`i∂_z ψ = −D ∂_x² ψ` with diffraction coefficient `D = t·a²`. Typical
values: `t ~ 1 mm⁻¹`, `a ~ 15 μm`, so `D ~ 200 μm²/mm`.

**Observable.** Beam-profile imaging gives `σ(z)` directly. The
free-diffraction doubling distance is `T_free = √3 · σ_0² / D`. For
`σ_0 = 10 μm`: `T_free ≈ 0.87 mm` — easy to measure on a 10–200 mm chip.

**LSBridge prediction (assuming ℓ = 1 μm, C = 1):**

| σ_0 (μm) | T_free | LSBridge T_LS | R(σ_0) |
|---|---|---|---|
| 1 | 0.008 mm | 0.014 mm | 1.77× |
| 5 | 0.19 mm | 10.9 mm | 56.6× |
| 10 | 0.77 mm | **114 m** | 1.5 × 10⁵× |
| 25 | 4.8 mm | 4.7 × 10¹⁷ mm | astronomical |

**Critical threshold:** at `σ_0 ≈ 5 μm` (5 dimensionless units), LSBridge
predicts the beam to spread **~57× slower** than standard diffraction.
That is a clean factor-of-50 falsifiable signal in a regime where chip
lengths still resolve it: free spreads to 2σ_0 in 0.2 mm, LSBridge predicts
10.9 mm — both fit on a 50 mm chip.

**Why this is the fastest route:**
- 1D geometry naturally matches the LSBridge prediction.
- Direct width imaging via end-face cameras.
- Broad initial Gaussians (`σ_0 ~ 50–200 μm`) are routine.
- Loss budget and integration times are not the bottleneck.

### 2.2 Exciton-polariton propagation

**System.** Polaritons in semiconductor microcavities propagate with
effective mass `m_eff ~ 10⁻⁴ m_e`, giving `ℏ/m_eff ≈ 1160 μm²/ps`.
Lifetime: ~10–100 ps. Direct space-time imaging via photoluminescence
gives `σ(t)`.

**LSBridge prediction (assuming ℓ = 1 μm, C = 1):**

| σ_0 (μm) | T_free | LSBridge T_LS | Within lifetime (30 ps)? |
|---|---|---|---|
| 1 | 0.0015 ps | 0.0026 ps | yes |
| 2 | 0.006 ps | 0.013 ps | yes |
| 5 | 0.037 ps | **2.1 ps** | yes |
| 10 | 0.15 ps | 22 ns | **NO** (polariton dies) |

**Critical regime:** `σ_0 ≈ 5 μm` is the sweet spot — free spreads in
0.04 ps (essentially instantaneous), LSBridge predicts 2.1 ps spread time
(comfortably within the ~30 ps polariton lifetime). A factor-of-50 slowdown
turns "instant" into "easily resolved." Above `σ_0 ~ 10 μm` the LSBridge
spreading exceeds the polariton lifetime and the experiment becomes
impossible.

**Caveats:**
- Polariton–polariton interactions confound the measurement; need a low-density regime.
- Cavity Q sets the effective hopping; need to characterize this independently.
- The natural-length-scale assumption (ℓ ~ 1 μm) is unfalsifiable a priori — if `ℓ` is much smaller, even `σ_0 = 1 μm` gives huge slowdown.

### 2.3 Quasi-1D ultracold-atom (BEC) expansion

**System.** ⁸⁷Rb in a highly anisotropic trap (tightly confined
transverse, loose axial). Release the trap, image the cloud width via
absorption imaging vs hold time. `ℏ/m_{Rb} ≈ 0.73 μm²/ms`.

**LSBridge prediction (assuming ℓ = 1 μm, C = 1):**

| σ_0 (μm) | T_free | LSBridge T_LS | Within typical experimental window (100 ms)? |
|---|---|---|---|
| 1 | 2.4 ms | 4.2 ms | yes |
| 2 | 9.5 ms | 20 ms | yes |
| 5 | 59 ms | 3,360 ms | borderline — 3.4 s expansion needed |
| 10 | 237 ms | 3.5 × 10⁷ ms | **no** (~10 hours) |

**Critical regime:** `σ_0 ≈ 2–5 μm` gives factor 2–57 slowdown in
experimentally accessible 20–60 ms windows.

**Caveats:**
- Residual mean-field interactions even after release (need very dilute BEC or post-release Feshbach tuning).
- Trap-release imperfections affect initial σ_0 calibration.
- Gravity-induced drift over 100+ ms hold times complicates imaging.

### 2.4 Cross-platform comparison

The universal observable `R(σ_0)` has the **same dimensionless shape on
every platform** (because the rescaling factors cancel in the ratio). The
factor-of-5 threshold sits at `σ_0 ≈ 5 ℓ` in all three platforms; the
factor-of-100 threshold at `σ_0 ≈ 10 ℓ`. The detection question reduces to:

| Platform | Resolvable σ_0 range (μm) | Best LSBridge regime | Detector limits |
|---|---|---|---|
| Photonic waveguides | 1–200 | σ_0 ~ 5–25 μm | chip length |
| Polaritons | 1–10 | σ_0 ~ 5 μm | lifetime |
| BEC 1D expansion | 1–50 | σ_0 ~ 2–5 μm | interactions + drift |

If the natural length scale `ℓ` is **much smaller** than 1 μm
(say nanometer-scale), even modest physical widths give large dimensionless
`σ_dim`, and the slowdown would already be visible at `σ_0 ~ 1 μm`.
**The experiment would constrain `ℓ` if no anomaly is seen, falsify the
prediction if anomalous slowing is seen.**

---

## 3. Experimental protocol (suggested for photonic waveguide arrays)

### 3.1 Setup
- Femtosecond-laser-written silica waveguide array.
- Lattice spacing `a = 10–20 μm`, hopping `t ~ 1 mm⁻¹` (set by waveguide
  spacing and refractive-index contrast).
- Total chip length: 100–200 mm.
- Input coupling: shaped Gaussian beam, σ_0 tunable from 5 μm to 200 μm
  via beam-shaping optics.
- Output: CCD imaging of the output face at multiple z values via
  longitudinal sampling (cleaved chip slices or 3D scan).

### 3.2 Measurement
For each chosen input σ_0:
1. Image σ(z) at 5–10 propagation distances z ∈ [0, L_chip].
2. Fit each profile to a Gaussian; extract σ(z).
3. Determine the smallest z* such that σ(z*) = 2σ_0 — the doubling
   propagation distance.
4. Compute R_measured(σ_0) = z*(σ_0) / z*_free(σ_0) where z*_free is
   the standard-diffraction prediction `√3 · σ_0² / D`.

### 3.3 Falsification thresholds

| Result | Interpretation |
|---|---|
| `R_measured(σ_0) ≈ 1` for all σ_0 ∈ [5 μm, 100 μm] | LSBridge prediction is **falsified** (or natural length `ℓ << 1 μm`) |
| `R_measured(σ_0) > 5` for σ_0 = 5 μm | Order-50 prediction borderline-confirmed |
| `R_measured(σ_0) > 100` for σ_0 = 10 μm | Order-10⁵ prediction confirmed — strong evidence for LSBridge |
| `R_measured(10 μm) > 10⁵`, `R_measured(20 μm) > 10¹³` | Universal shape confirmed across multiple widths — definitive evidence |

### 3.4 Confounds to control
- **Material loss / scattering:** broadens the beam by classical mechanisms; need to subtract a control measurement with low-loss propagation.
- **Nonlinearity:** Kerr effects in glass; use low input power.
- **Coupling losses at input:** affect σ_0 calibration; characterize via near-field imaging.
- **Lattice nonidealities (next-neighbor hopping):** affects effective `D`; characterize via single-site excitation reference measurements.

---

## 4. What the experiment would establish

**Positive result (R_measured matches LSBridge prediction):**
- Strong constraint on the natural length scale `ℓ` (since the
  predicted-R-vs-σ_0 curve has a specific shape).
- Evidence that quantum wavepacket spreading has corrections at the
  ~`exp(σ_0/ℓ)` scale beyond standard Schrödinger.
- Motivates re-examining other quantum systems for analogous slowdowns.

**Null result (R_measured ≈ 1):**
- Falsifies LSBridge **as a description of photonic-waveguide-array
  wavepacket dynamics with `ℓ ~ 1 μm`.**
- Does NOT falsify LSBridge in general — `ℓ` could be much smaller
  (sub-Angstrom?), making the predicted slowdown invisible at optical
  scales.
- Pushes further tests toward smaller-scale matter systems.

**Crossover result (R_measured > 1 but < LSBridge prediction):**
- Suggests LSBridge captures part of the correct dynamics but with a
  different functional form or modified coupling constant `C`.

---

## 5. Honest caveats

1. **The natural length scale `ℓ` is a free parameter.** LSBridge proves
   a dimensionless ODE; the physical-units mapping requires `ℓ`. The
   theory doesn't (yet) predict `ℓ`. Photonic experiments at multiple
   σ_0 would fit `ℓ` if any deviation is seen.

2. **The Gaussian ansatz (now bounded by a theorem).** The σ(t) ODE was
   derived under the proper Gaussian + quadratic phase ansatz at leading
   order. The sech-profile counterpart is now derived in Lean
   (Backreaction Part 17): same structural LHS `ξ·ξ_pp + ξ_prime²·(ξ−1)`,
   different source term `ℏ²/(m²·ξ)`, with `sech_curved_rejects_frozen`
   ruling out the frozen state for sech. The headline U-shape /
   exponential / frozen signatures are therefore **Gaussian-sector**
   predictions, not universal. A separate shape-dependence experiment
   (Gaussian vs sech) would test the deeper structural prediction.

3. **The matter-coupling assumption (a² = r²).** LSBridge's coupled
   matter–geometry system assumes the metric conformal factor equals
   the matter amplitude squared. This is a self-consistent choice in
   the framework but is one specific coupling among many.

4. **Optical analogs vs matter.** Photonic waveguide arrays implement
   the same PDE structure as quantum particles but with photons playing
   the role. If LSBridge backreaction is fundamentally a matter
   phenomenon, optical analogs may not test it — they would test only
   that the PDE structure (and the ansatz) makes the prediction.

5. **Polariton + BEC have additional confounders** (interactions,
   lifetime, trap effects) that may mask or mimic the predicted signal.

---

## 6. Summary

| Question | Answer |
|---|---|
| What is the cleanest observable? | `R(σ_0) = T_LS / T_free` (dimensionless ratio of doubling times) |
| What does the theory predict? | `R(σ_0) ≈ 1` near `σ_0 ~ 1`, `R(σ_0) ~ exp(σ_0)/σ_0²` for broad packets |
| Where can it be measured first? | Photonic waveguide arrays at `σ_0 = 5–25 μm` |
| What would falsify it? | `R_measured(σ_0) ≈ 1` for all tested `σ_0` |
| What would confirm it? | `R_measured(σ_0)` follows the LSBridge curve shape across multiple `σ_0` |

The **fastest credible test** is a photonic waveguide-array measurement of
σ(z) for a sequence of input Gaussian widths in the 5–50 μm range, looking
for an anomalous slowdown that grows superlinearly with σ_0.

All numerical predictions, regime tables, and plots are in
`results/lsbridge_predictions/` and `results/lsbridge_predictions/experimental_regimes/`.
The underlying theorems are proved in
`UnifiedTheory/LayerB/LohmillerSlotine*.lean`.
