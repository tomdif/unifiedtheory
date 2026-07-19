# LSBridge — Photonic Falsification Protocol (send-to-experimentalist)

**The ask.** ~1–2 days of beam time on a 1D coupled photonic waveguide array. The measurement is the **doubling propagation distance** of input Gaussian beams of varying widths.

## What is being tested

**Gaussian-sector LSBridge prediction.** Under the framework's matter-coupling rule `a² = r²`, a Gaussian wavepacket of width `σ_0` should exhibit a non-standard spreading dynamics with a characteristic length scale `ℓ`:

1. **U-shaped** ratio `R(σ_0) = T_LS / T_free`, with minimum at `σ_0 ≈ ℓ`.
2. **Frozen-narrow** regime: `σ_0 << ℓ` wavepackets are dynamically suppressed from spreading.
3. **Exponential broad-packet slowdown**: `R(σ_0) ~ exp(σ_0/ℓ)` for `σ_0 >> ℓ`.

**Important scope note.** This experiment tests the **Gaussian-sector** prediction. The same LSBridge coupling applied to a sech profile produces a *different* width-ODE source term — the source-term difference is a separate, theorem-backed prediction (see "Experiment B" below for the shape-dependence test).

Both ansätze share the same structural width-ODE LHS function `ξ·ξ_pp + ξ_prime²·(ξ−1)`, but the Gaussian has zero source while the sech has source `ℏ²/(m²·ξ)`. The frozen / U-shape / exponential signatures are Gaussian-specific; the structural LHS is family-level.

**CRITICAL CAVEAT — added 2026-05-25 after Phase 2 numerical PDE study.** The U-shape, frozen-narrow, and exponential-slowdown signatures above are **reduced-ODE predictions** derived under the Gaussian + quadratic-phase variational ansatz. A 1D full-PDE numerical study with a tail-mask formulation found that the reduced ODE **does not faithfully describe the full LSBridge curved Schrödinger PDE** for physically realizable real-Gaussian initial conditions:
- Mode discrimination σ_S/σ_G observed in PDE: ≤ 1.094 across σ_0 ∈ [0.3, 2.0] (reduced ODE predicts up to 3.58).
- Frozen-narrow regime not realized: at σ_0 = 0.3, PDE σ(1) = 1.70, matching free Schrödinger (1.69); reduced ODE predicted 0.58.
- PDE σ ≥ free σ everywhere — sign of "slowdown" is inverted relative to the reduced-ODE narrative.

The reduced-ODE Lean theorems are correct as mathematical statements about a specific variational reduction; they do not predict the behavior of real wavepackets in the full PDE. Until a PDE-level prediction has been established (which would require either Crank-Nicolson simulation of the un-masked equation or a direct PDE-level theorem), the photonic protocol below is testing a signal that may not be present even if LSBridge is the right physics.

> **Current full-PDE numerical evidence does not support the reduced-ODE Gaussian frozen-packet or Gaussian/sech mode-discrimination predictions. The null outcome is presently the expected result unless future unmasked/implicit PDE simulations overturn it.**

Details: `results/lsbridge_predictions/phase2_pde_shape_fidelity/sigma0_sweep_tau0.050.json` and the project memory entry `project_lsbridge_phase2_pde_divergence.md`.

---

## Pre-experiment gate (5 minutes)

Run a single discrete-diffraction calibration: launch into one waveguide, image the spreading at multiple z, fit the localization length.

**Pass condition:** `ξ_loc ≥ 50 μm`.

| Outcome | Action |
|---|---|
| ξ_loc ≥ 50 μm | Proceed to Stage A. |
| 20 μm ≤ ξ_loc < 50 μm | Shrink Stage A upper bound to σ_0 ≤ ξ_loc/2. |
| ξ_loc < 20 μm | Disorder confound exceeds LSBridge window; pick a different chip or chain to a longer chip. |

Rationale: Anderson localization is the only confounder our blind-classification challenge mis-identified as LSBridge, and only when ξ_loc is comparable to the σ_0 window.

---

## Stage A — broad scan to find the U-shape minimum (~4 hours)

Launch Gaussian beams at the following nominal widths and image σ(z) at 3 z-values per beam:

```
σ_0 ∈ {0.5, 1, 2, 3, 5, 7, 10} μm     (or as platform allows)
```

For each σ_0, compute `z*_measured` (where σ(z*) = 2σ_0) and the dimensionless ratio:

```
R(σ_0) = z*_measured / (√3 · σ_0² / D)
```

where D = t·a² is the diffraction coefficient (calibrate from the discrete-diffraction precheck).

**Look for: U-shape with minimum at some σ_0* ∈ [0.5, 10] μm.**

| Observed shape of R(σ_0) | Interpretation |
|---|---|
| **U-shape, minimum at σ_0* > 0**, R_min > 1 | **LSBridge candidate** — σ_0* ≈ ℓ (the framework's natural length). Proceed to Stage B at σ_0 ≈ σ_0*. |
| R ≈ 1 across the entire scan | LSBridge falsified at ℓ in this range, or ℓ is below platform resolution. |
| Monotonically decreasing R (R < 1 at large σ_0) | Kerr self-focusing dominant; lower input power and re-check. |
| Sharp blow-up at one σ_0 with R = 1 below | Residual Anderson localization despite the precheck; chip is too disordered. |
| Constant R < 1 | Next-nearest-neighbor hopping or D miscalibration. |

---

## Stage B — focused discrimination at σ_0 ≈ ℓ (~6 hours)

Pick four widths bracketing σ_0*:

```
σ_0 ∈ {σ_0*/2, σ_0*, 1.5·σ_0*, 2·σ_0*}     (or {3, 5, 6, 7} μm if σ_0* ≈ 5 μm)
```

For each σ_0, image σ(z) at **5 z-values** spanning the predicted doubling regime. Aim for ≤ 5% relative error on σ extraction (translates to ~3% error on R).

This produces 4 (σ_0, R, error) triples.

---

## Two independent signatures

### Signature A — overall U-shape fit

Hand the Stage A + Stage B (σ_0, R, error) data to:

```
python3 scripts/lsbridge_bayesian_inference.py --csv your_measurements.csv
```

Reports: MAP ℓ, 95% credible interval, log Bayes factor vs R ≡ 1.

| BF outcome | Verdict |
|---|---|
| log BF > 100 with tight CI on ℓ | DECISIVE evidence for LSBridge |
| log BF in [3, 100] | POSITIVE evidence, weaker fit |
| log BF in [−3, 3] | Inconclusive — collect more data |
| log BF < −3 | Evidence against LSBridge |

Also run:
```
python3 scripts/lsbridge_confounder_discrimination.py
```

This compares the observed R(σ_0) shape to four alternative mechanisms (linear loss, Kerr, AL, NNN). The blind-challenge sweep showed 0% false-positive rate for confounder data being labeled as LSBridge.

### Signature B — single-trajectory conserved quantity

For ONE trajectory (the best-imaged one), estimate `dσ/dz` from the {z, σ(z)} pairs. Compute at each measured z:

```
I(z) = (dσ/dz) · exp(σ/ℓ_MAP) / (σ/ℓ_MAP)
```

with ℓ_MAP from Signature A.

**Pass condition:** I(z) is approximately constant within measurement error along the trajectory.

This is independent of any comparison to free Schrödinger. It is a within-trajectory consistency check derived from the proved LSBridge conservation law `σ̇·exp(σ)/σ = C`.

---

## Pass / fail decision

| Signatures | Verdict |
|---|---|
| **A** (BF decisive) AND **B** (invariant constant) | LSBridge confirmed at the photonic length scale ℓ_MAP |
| **A** only | LSBridge curve fits but single trajectories inconsistent — possible artifact, re-check |
| **B** only | One trajectory consistent but scan inconclusive — gather more data points |
| Neither | LSBridge falsified at this length scale on this platform |

---

## What the answer means

| If Gaussian-sector LSBridge confirmed | Cross-platform test with polariton (cleanest near-term match) or BEC expansion at the same σ_0 in physical units. If both platforms infer the same ℓ, the effect is platform-independent — a fundamental physical mechanism. If different ℓ, an effective platform-tuned theory. |
| If Gaussian-sector LSBridge falsified | The framework is excluded at the photonic length scale (≥ ℓ_min equal to the smallest σ_0 you reached). Sub-wavelength platforms (e.g., plasmonic waveguides) would be needed to probe smaller ℓ. |

---

## Experiment B — Shape-dependence validation (optional second-round test)

If Experiment A confirms the Gaussian-sector U-shape, a much stronger follow-up is to vary the **profile shape** of the launched beam and check whether the spreading dynamics changes in the framework-predicted way.

**The proved prediction.** Gaussian and sech profiles share the same width-ODE LHS function
`ξ·ξ_pp + ξ_prime²·(ξ−1)` but with different source terms:
- Gaussian: source = 0 (frozen-state admissible, U-shape, exponential slowdown).
- Sech: source = `ℏ²/(m²·ξ)` (frozen state forbidden, source-driven dynamics, polynomial spreading).

**The test.** Use beam-shaping optics to prepare a sech-profile input at the same characteristic width and image the spreading. The framework predicts:
- A sech profile should NOT exhibit a frozen-narrow regime.
- A sech profile should NOT exhibit exponential broad-packet slowdown.
- Both profiles should exhibit the same conservation law structure (continuity-derived `α = m·ξ'/(2ℏ·ξ)`) but with different time-evolution.

**What it would establish.** A confirmed shape-dependence signature establishes that LSBridge encodes a **profile-sensitive spreading law**, not a universal frozen-soliton behavior. It is arguably more compelling than Experiment A alone, because it tests the *structural* prediction (shared LHS + ansatz-specific source) rather than only the headline Gaussian signature.

**Scope of the original Gaussian-sector claim.** Experiment A tests one specific theorem-backed prediction (the Gaussian sector). Generalizing to "all wavepackets" is NOT what the theorems support and is NOT what's claimed.

---

## Time + cost estimate

| Activity | Time |
|---|---|
| Pre-experiment ξ_loc precheck | 0.5 hour |
| Stage A broad scan (7 σ_0 × 3 z) | 4 hours |
| Stage B focused scan (4 σ_0 × 5 z) | 6 hours |
| Analysis (Bayesian + confounder + Signature B) | 1 hour |
| **Total beam time** | **~1.5 working days** |

Cost: standard femtosecond-laser-written silica waveguide array (~50 mm chip, $5–10k), single-mode CW laser (often already in lab), CCD camera + microscope.

---

## Theoretical backing (one-line each)

**Gaussian-sector (Experiment A targets):**
- σ-ODE `σ̇ = C·σ·exp(−σ)` — proved in `LohmillerSlotineBackreaction.lean` Part 12.
- Two-sided doubling bound `exp(σ_0)/(2C) ≤ T_LS ≤ exp(2σ_0)/C` — proved in `LohmillerSlotineGaussianWidthDynamics.lean` Parts 7–8.
- Optimal width at σ = 1 — proved in same file (`lsbridge_spreading_rate_max_at_one`).
- Single-trajectory invariant `σ̇·exp(σ)/σ = C` — proved as `gaussian_width_first_integral`.

**Family-level structural (both sectors):**
- Continuity-identity (Gaussian + sech) — proved in `LohmillerSlotineBackreaction.lean` Parts 12 + 16.
- Shared width-ODE LHS structure `ξ·ξ_pp + ξ_prime²·(ξ−1)` — implicit in Parts 11 + 17.

**Sech-sector (Experiment B targets):**
- Sech curved ODE `ξ·ξ_pp + ξ_prime²·(ξ−1) = ℏ²/(m²·ξ)` — proved in `LohmillerSlotineBackreaction.lean` Part 17 (`sech_curved_leading_order_sigma_ode`).
- Sech curved REJECTS frozen state — proved as `sech_curved_rejects_frozen`.
- Sech curved DISTINCT from Gaussian curved at the source term — proved as `sech_curved_distinct_from_gaussian_curved`.

All theorems: 3011-job Lean build, zero `sorry`, standard axioms only.

**Scope and limitations explicitly proved:**
- The headline U-shape / frozen / exponential signatures hold for Gaussian. They do NOT hold for sech (rejected by `sech_curved_rejects_frozen`).
- The natural length scale `ℓ` is a FREE parameter; the framework predicts the dimensionless dynamical law, not the absolute scale. The experiment measures `ℓ` directly via the position of the R(σ_0) minimum.

Numerical predictions, sensitivity bounds, confounder discrimination data, and Bayesian inference tools in `scripts/lsbridge_*.py` and `results/lsbridge_predictions/`.

---

**Author contact / responsibility for analysis:** [your name + email]
**Underlying theory writeup:** `LS_BRIDGE_WRITEUP.md` (in this repo / Zenodo DOI).
