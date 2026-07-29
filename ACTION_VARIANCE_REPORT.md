# (a) The Action Variance, Evaluated — and (b) the DESI Confrontation-Lite

**2026-07-29.** Execution of the two neck-out moves from FIVE_TESTS_REPORT.md:
(a) evaluate the BD action variance (the object MYZ 2407.03395 formalized but
never evaluated), (b) run the resulting everpresent-Λ law against DESI DR2
shape targets. Companion artifacts: `action_variance_mc.py` (+ JSON),
`everpresent_desi.py`, `exact_smeared_moment.py`. Tags: [LEAN] machine-checked,
[MC] direct sprinkling simulation here, [NUM] numerics, [PHYS] assembly/model.

**Executive summary: the smeared BD action variance is SUPER-POISSONIAN —
Var S ≈ κ²[c_N·N + (π/4)M(ε)·g·N·T̂²] with the ε-dependence of the exact mass
M(ε) confirmed by direct simulation (predicted damping ratio 0.018 vs measured
0.016) and g ≈ 0.7. Consequence: the everpresent-Λ amplitude GROWS with epoch,
Λ ∝ 1/T (not Sorkin's 1/T²). This law is automatically CMB-safe (Ω_Λ(z=1100)
~ 4×10⁻⁵ vs the classic law's fatal ~0.6), lands on the DESI-preferred thawing
side (w₀ > −1, drift w ≈ −0.5…−0.67 vs DESI w₀ = −0.752 ± 0.057), and its
amplitude calibrated to Λ_obs today pins the gravitational nonlocality scale to
ℓ_k ≈ 2.5–3.8 femtometers.**

## (a) The evaluation

Object: S = κ(N − D), κ = 4/√6, D = Σ_{y≺x} ε·f(n_xy, ε) — the smeared 4D BD
action on a flat causal diamond, unit density.

**Analytic structure [PHYS with exact ingredients].** The pair-diagonal
(Campbell) term of Var D is the per-point variance summed over elements; our
variance-rate machinery gives its exact edge form: per point of causal depth τ̂
(units ℓ_c = (24/π)^{1/4}ℓ_p), Var_pt = (π/4)·M(ε)·τ̂², where M(ε) =
(105/4)√π·ε^{3/2}(ε²+2ε+3)/(2−ε)^{13/2} is the exact smeared mass (validated
both ends: ε→0 ↔ [LEAN] `mesoscale_suppression`; ε=1 ↔ [LEAN]
`f4Dsq_mass_half` — sharp check: (π/4)M(1) = 219.3 vs MC cone integral 219.25).
Hence

    Var S = κ²·[ c_N·N  +  (π/4)·M(ε)·g·N·T̂² ]  + (short-range off-diag),

with g the diamond depth-average geometry factor and c_N·N the Poisson floor
(partially suppressed by N–D covariance cancellation).

**Direct simulation [MC].** Poisson sprinklings of 4D diamonds (N = 1000–8000,
5 ε values, interval counts via causal-matrix products, sharp limit recovers
(1,−9,16,−8)):
- Super-Poissonian growth at every ε (effective exponent ≈ 1.5–2.0 vs 1.0).
- ε-scaling of the dominant term matches M(ε): Var(ε=0.5)/Var(1) = 0.0162
  measured vs M(0.5)/M(1) = 0.018 predicted; fitted g ≈ 0.7 consistent
  across ε; at strong damping the measured variance dips BELOW the Poisson
  floor at small V (the N–D cancellation) before the edge term takes over.

**The parameter-free amplitude.** With Var S per element growing as T̂², the
per-element everpresent amplitude is not constant:

    α_eff(T, ε) = κ·√((π/4)·M(ε)·g)·(T/ℓ_c)/(8π)  ∝  T·√M(ε)  —

the fluctuating part of the action grows like √N·T̂, i.e. **δΛ ∝ 1/T**, one
power of T slower than Sorkin's 1/T². This is the exact-constants answer to
MYZ's motivating question, and it CHANGES the everpresent-Λ phenomenology.

## (b) The DESI confrontation-lite

Perturbative overlay on the ΛCDM background (no back-reaction — honest for
shape statistics only; not a likelihood analysis), 600 realizations per law,
amplitudes calibrated to median |ρ_Λ| = 0.69ρ_c today:

| diagnostic | CLASSIC (Λ ∝ y/√V) | ACTION (Λ ∝ y/V^{1/4}) | DESI DR2 target |
|---|---|---|---|
| Ω_Λ(z=1100) median | **0.63 (fatal)** | **4.3×10⁻⁵ (safe)** | ≪ 1 (CMB) |
| w₀ median [16,84] | +0.17 [−1.10, +1.86] | **−0.51 [−1.27, +0.53]** | −0.752 ± 0.057 |
| deterministic drift w | −1 (flat) + noise | **−1/2 → −2/3 (thawing)** | w₀ > −1 favored |
| wa median | −1.06 (huge scatter) | +0.08 (scatter) | −0.86 +0.23/−0.20 |
| in DESI-like box | 5% | 9% | — |

Readings:
1. **The classic law at today's amplitude is CMB-dead** (Ω_Λ(rec) ~ 0.6) —
   reproducing DNY's finding from first principles, and explaining why their
   fitted α had to be ~50× below "natural."
2. **The action law fixes the CMB problem automatically**: Λ ∝ 1/T is
   suppressed by ~t_rec/t₀ ≈ 3×10⁻⁵ at recombination while O(1) today — the
   "why now" structure comes out of the boost-edge growth, not tuning.
3. Its deterministic drift gives w_eff ≈ −1/2 (matter era) → −2/3 (Λ era):
   **thawing-like, on DESI's preferred w₀ > −1 side, within ~1.5σ-equivalent
   of the DESY5 w₀** — but it does not produce the phantom-crossing wa < 0
   median (only stochastically, ~9% of realizations). A genuine likelihood run
   (DESI BAO + SN + CMB distance priors, realization-marginalized) is the
   publishable next step and could fail the model.
4. **The mesoscale lands at the femtometer.** Calibrating α_eff(T₀) to the
   observed Λ: ℓ_k = 2.5–3.8 fm across the systematic range (g ∈ [0.5,1],
   T ∈ [age, conformal horizon]). Distinct from both the per-point channel
   (~100 m, demoted) and the B-noise/DNY-matching channel (~6 ℓ_p): the
   action channel is the everpresent-relevant one, and it says the
   gravitational nonlocality scale is nuclear-sized.

## Caveats (all flagged, in order of bite)

- **ℓ_k ≈ fm vs the LHC matter-sector bound ℓ_k ≤ 10⁻¹⁹ m**: 4 orders of
  tension IF matter and gravity share one nonlocality scale. Either the
  scales are sector-dependent (gravity-only smearing — allowed, untested), or
  this calibration falsifies the single-scale version. That is a sharp,
  stated stake.
- The overlay is not a likelihood analysis; back-reaction is neglected; the
  independent-increment assumption for S(V) is a model choice [PHYS].
- g ≈ 0.7 is MC-calibrated, not yet derived; the ASS 4D operator instability
  (complex zeros) remains an open structural caveat for the whole family.
- MC at N ≤ 8000 probes T̂ ≤ 7.9; the T̂² law is theory-extrapolated 60 orders
  beyond (backed by the exact edge integral, but stated plainly).

## Status of the chain

[LEAN] kernel masses → [NUM exact] M(ε) closed form → [MC] Var S structure
validated at 5 ε values → [PHYS] Λ ∝ 1/T law + CMB safety + thawing w + fm
mesoscale. The next decisive steps: formalize the edge term of Var S in Lean
(diagonal-Campbell reduction is `variance_rate`-shaped); the DESI likelihood
run; and a sector-dependence analysis for the fm-scale tension.

## LOCK-IN ADDENDUM (2026-07-29, later same day)

**(i) The diamond coefficient is now DERIVED — no fitted g.** Two exact
integrals close it: the angular average of the squared null-exit radius for a
point at height u, offset b in the diamond is ⟨r_exit²⟩_Ω = (u²−b²)/4 (the
1/(u+bc)² angular integral collapses), and the diamond average is
⟨u²−b²⟩ = (2/3)T². Hence the leading law is exactly

    Var S = 2·κ²·M(ε)·N·T̂²,   T̂ = T/ℓ_c,

parameter-free. MC agreement 0.7–0.9 at ε = 1, 0.5 where the edge dominates
(finite-size and the N–D cancellation account for the deficit); subleading
floor terms visible at small ε as expected. The Λ-closure then gives the exact
Károlyházy identity **ℓ_k = 3.9·(ℓ_p²T)^{1/3} = 12.7 fm** (coefficient now
derived: 3.92 = [(24/π)^{1/4}√v/(8πκ√(2M̂)·Λ̂)]^{1/3}-chain, Λ̂ = Λ(cT)² = 1.89).

**(iii) The trichotomy is formalized.** `KFCausalMinkowski4DCriticalLine.lean`
(axiom-clean, root green): `critical_line_dichotomy` — the mean kernel's s = ½
zero in both guises (Mellin moment and null-boundary w-mass) conjoined with
the strict positivity of the intensity mass — and `intensity_zero_impossible`
(all admissible finite layer families). One zero, two jobs, machine-checked.

**(ii) The DESI DR2 BAO likelihood run — a decisive negative.** Verbatim DR2
Table 4 (13 measurements, correlations), profiled over (Ωm, h·rd). Pipeline
validated: ΛCDM χ² = 10.55/11 (DESI: 10.2), Ωm = 0.2970 (DESI: 0.2975), CPL
χ² = 5.81 ≈ DESI's Δχ² = −4.7 corner. Verdicts:

| model | Δχ² vs ΛCDM |
|---|---|
| deterministic action drift (fixed ℓ_k, Λ ∝ V^{−1/4}) | **+15.2 — excluded** |
| stochastic action realizations (150) | best +25.5, median +1058 — excluded |
| stochastic classic realizations (150) | best +35.8, median +1408 — excluded |

The thawing w → −2/3 drift is too far from ΛCDM for DR2 BAO; typical
stochastic realizations are far too rough across z ∈ [0, 2.3] — quantifying
at BAO level exactly the seed-rarity DNY found for SN (16/90,000). **An O(1)
everpresent-Λ component with this correlation structure is dead against DESI
DR2.**

**What survives is sharper than what died: a new observational bound.** If Λ
itself is (mostly) constant, the BAO smoothness caps the action-channel noise
at a fraction x of Λ_obs, and the derived amplitude chain inverts to

    ℓ_k(gravity) ≥ (1/x)^{1/3}·3.9·(ℓ_p²T)^{1/3}  ≈ 30 fm  (x = 0.1).

Combined with the LHC matter-sector bound ℓ_k ≤ 10⁻¹⁹ m, the causal-set noise
mechanism now REQUIRES a ≥ 5-order sector split between gravitational and
matter nonlocality — or it is falsified outright. Either way the program has
done its job: DESI DR2 + machine-checked kernel constants = the first
cosmological lower bound on a quantum-gravity nonlocality scale, and a
mechanism that stuck its neck out and (in its O(1)-amplitude form) lost.

Caveats: BAO-only (no SN/CMB joint), ΛCDM background V(a), flatness enforced,
independent-increment correlation structure (ZAS Model-2-style smoother
correlations would soften the stochastic exclusion — the deterministic drift
exclusion is correlation-independent).
