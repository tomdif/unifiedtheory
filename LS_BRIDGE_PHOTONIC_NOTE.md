# LSBridge — Photonic Falsification Note (2 pages)

The LSBridge (Lohmiller–Slotine) framework predicts a small, sharp
modification to **Gaussian** wavepacket spreading. A photonic
waveguide-array experiment with a Gaussian input beam at σ_0 ≈ 5 μm
either confirms or falsifies this prediction with a factor-of-50
signal, on a standard 50 mm chip.

**Scope.** The three signatures below (frozen-admissible, exponential
slowdown, optimal width at σ = 1) are *Gaussian-sector* predictions.
A separate Lean theorem (`sech_curved_rejects_frozen` in Backreaction
Part 17) proves that the same LSBridge coupling applied to a sech
profile *forbids* the frozen state — its width-ODE has a nonzero
source term `ℏ²/(m²·ξ)`. Both ansätze share the same structural
LHS function `ξ·ξ_pp + ξ_prime²·(ξ−1)` but their qualitative dynamics
differs. The protocol below tests the Gaussian sector.

**CRITICAL CAVEAT — added 2026-05-25 after Phase 2 numerical PDE study.**
The signatures above are *reduced-ODE* predictions from the Gaussian +
quadratic-phase variational ansatz. A 1D full-PDE numerical study
(`scripts/lsbridge_phase2_pde_shape_fidelity.py`, tail-masked
formulation) found that the reduced ODE **does not faithfully describe
the full LSBridge curved Schrödinger PDE** for real-Gaussian initial
conditions:
  • At σ_0 = 0.3, PDE σ(1) = 1.70, matching free Schrödinger (1.69)
    rather than the reduced-ODE frozen prediction (0.58).
  • PDE σ exceeds free σ everywhere — the sign of "slowdown" is
    inverted relative to the reduced-ODE narrative.
  • Gaussian/sech mode discrimination σ_S/σ_G ≤ 1.094 in the PDE
    versus 3.58 predicted by the reduced ODE.
The Lean theorems are correct math about a variational reduction; the
reduction does not capture the full PDE dynamics of physically realizable
ICs.

> **Current full-PDE numerical evidence does not support the reduced-ODE
> Gaussian frozen-packet or Gaussian/sech mode-discrimination
> predictions. The null outcome is presently the expected result unless
> future unmasked/implicit PDE simulations overturn it.**

See memory entry `project_lsbridge_phase2_pde_divergence.md` for details.

## What the theory says

**Setting.** Polar Madelung-Bohm form of the Schrödinger equation, with
the amplitude `r` allowed to source an emergent 1+1-dim metric `g = r²·diag(−1,1)`.
For a Gaussian wavepacket with quadratic phase, the coupled
matter–geometry system reduces to a first-order ODE for the width:

  σ̇ = C · σ · exp(−σ),

where σ is dimensionless and C is a dimensionless coupling. This is a
**proved consequence** of the static and dynamic backreaction theorems
in the Lean formalization
(`UnifiedTheory/LayerB/LohmillerSlotine*.lean`). The theorem stack is
closed at zero sorry, standard axioms only.

**Three concrete predictions (Gaussian sector):**

1. **Frozen wavepackets are admissible (Gaussian-specific)**. A
   constant-σ Gaussian satisfies the LSBridge ODE for any σ > 0
   (with C = 0). Free Schrödinger forbids this since
   σ̈ = ℏ²/(m²σ³) ≠ 0. The same coupling applied to a sech profile
   forbids the frozen state — see `sech_curved_rejects_frozen`.

2. **Exponentially-slow doubling.** Free-Schrödinger doubling time is
   `T_free(σ_0) = √3 · σ_0² · m / ℏ` (polynomial). LSBridge predicts
   `exp(σ_0)/(2C) ≤ T_LS(σ_0) ≤ exp(2σ_0)/C` (exponential — both bounds
   proved in Lean as `doubling_time_two_sided_bound`).

3. **Characteristic spreading width at σ = 1.** The spreading rate
   `σ̇ = C·σ·exp(−σ)` is maximized at σ = 1 with value `C/e`. Wider OR
   narrower wavepackets spread more slowly than at this critical width
   (`lsbridge_spreading_rate_max_at_one`).

**The observable.** All three predictions condense into one
dimensionless ratio:

  R(σ_0) := T_doubling, measured / T_doubling, free.

Free Schrödinger predicts R ≡ 1 by definition. LSBridge predicts:

| σ_0 (dimensionless) | R(σ_0) |
|---|---|
| 1 | 1.77 |
| 2 | 2.12 |
| **5** | **57** |
| **7** | **548** |
| **10** | **1.5 × 10⁵** |

(Numerical from `scripts/lsbridge_predictions.py`; both upper and lower
bounds are proved theorems.)

The physical σ_0 is `σ_0,phys / ℓ` where `ℓ` is an unknown natural
length scale. The shape of R as a function of dimensionless σ_0 is
universal across platforms.

## What experiment to do

**Recommended platform: 1D coupled-waveguide array.** This realizes
the discrete Schrödinger equation directly along the propagation
direction. Beam-profile imaging gives σ(z).

**Setup.** Standard femtosecond-written silica array, `a = 15 μm`
spacing, `t ≈ 1 mm⁻¹`, chip length ~50–200 mm. Diffraction coefficient
`D = t·a² ≈ 225 μm²/mm`.

**Procedure.** Inject a Gaussian beam with σ_0 = {1, 2, 3, 5, 7} μm.
At each σ_0, image σ(z) at five or more z values; extract the doubling
distance z* where σ(z*) = 2σ_0. Compute `R(σ_0) = z*_measured / z*_free`
where `z*_free = √3 · σ_0² / D`.

**Critical row of the protocol.**

| σ_0 | z*_free | LSBridge predicted z*_LS | Slowdown |
|---|---|---|---|
| 1 μm | 7.7 μm | 14 μm | 1.77× |
| 5 μm | 0.43 mm | **24.7 mm** | **57×** |
| 7 μm | 0.85 mm | 463 mm (off-chip) | 548× |

The σ_0 = 5 μm point is the cleanest single test: both free and
LSBridge doubling distances fit on a 50 mm chip; the predicted factor-50
slowdown is well above experimental systematics.

## Falsification matrix

| Outcome | Verdict |
|---|---|
| R ≈ 1 ± 5% for all σ_0 ∈ [3, 10] μm | **LSBridge falsified** (or `ℓ ≪ 1 μm` — would need shorter-wavelength platform) |
| 1.5 ≤ R ≤ 3 at σ_0 = 5 μm | Borderline; repeat with finer sweep |
| R > 5 at σ_0 = 5 μm and rising at σ_0 = 7 μm | Strong evidence for LSBridge |
| R(σ_0) traces the predicted exp(σ_0)/σ_0² curve across multiple σ_0 | **Definitive evidence** + best-fit ℓ |

Quantitative fit and rule-out: `scripts/lsbridge_ell_inference.py`
takes a CSV of `(σ_0, R_measured, R_err)` and returns either:
- best-fit `ℓ` with 1σ confidence interval (consistent case), OR
- reduced χ² with the verdict `FALSIFIED_or_BAD_MODEL` (no `ℓ ∈ [1 nm, 100 μm]`
  matches the data).

A synthetic demonstration in `results/lsbridge_predictions/ell_inference/`
recovers `ℓ = 1.001 μm` (truth 1.000 μm) from 3% noise on 8 measurements
in the σ_0 = 1–8 μm range; reduced χ² = 1.005.

## Honest caveats

1. **The natural length scale ℓ is a free parameter** of the
   prediction; the experiment constrains it. If `ℓ ≪ 1 μm`, optical
   platforms cannot resolve the predicted slowdown.

2. **Photonic waveguides are an analog of Schrödinger evolution**, not
   matter wavepackets. If LSBridge backreaction is fundamentally a
   matter-side phenomenon, an optical null result would not falsify it.
   But the PDE-level test still constrains the model.

3. **Loss, nonlinearity, and next-nearest-neighbor hopping** are the
   confounders. Standard calibration (Section "Confounds" of
   `LS_BRIDGE_LAB_PROTOCOL.md`) controls them.

4. **The ODE is for Gaussian profiles** with quadratic phase. The Lean
   stack now proves the sech-profile counterpart has the **same
   structural LHS but a different source term** (Backreaction Part 17),
   so frozen states are forbidden and the exponential slowdown is
   Gaussian-specific. Non-Gaussian inputs evolve under a profile-specific
   law, not this ODE.

## Theory status

- Substrate → Madelung-Bohm bridge: closed (Phase A, B).
- Geometry ladder (conformal → diagonal → chartwise SPD): closed
  (Phase C.1–C.3).
- Coupled matter–geometry system, general-covariant form: closed
  (Phase D).
- Constant-R classification + impossibility for R < 0: closed (Phase E
  suite).
- σ(t) dynamics: conservation, monotonicity, asymptotics, doubling-time
  two-sided bounds, optimal-width theorem (σ(t) Parts 1–8).

3011 jobs in the UnifiedTheory Lean build, zero `sorry`, only standard
axioms `propext`, `Classical.choice`, `Quot.sound`.

Detailed lab protocol: `LS_BRIDGE_LAB_PROTOCOL.md`.
Numerical artifacts: `results/lsbridge_predictions/`.
Underlying theorems: `UnifiedTheory/LayerB/LohmillerSlotine*.lean`.
