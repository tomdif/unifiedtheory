# LSBridge — Adversarial Assumption Audit

**Companion to:** `LS_BRIDGE_WRITEUP.md`, `LS_BRIDGE_LAB_PROTOCOL.md`,
`LS_BRIDGE_MINIMAL_PILOT.md`, and the scripts in `scripts/`.

**Purpose:** every claim the LSBridge program makes is tagged here as
**theorem-backed**, **model choice**, **platform mapping**, or **confounder**.
If an outsider wants to attack the falsifiability claim, this audit shows
which arrows to aim at.

---

## A. Theorem-backed (proved in Lean, standard axioms only)

These survive any methodological challenge that does not also reject the
underlying definitions.

| Claim | Lean theorem | What's proved |
|---|---|---|
| **σ-ODE under Gaussian + quadratic phase ansatz** | `gaussian_curved_leading_order_sigma_ode` | At the `x²` coefficient match, the coupled matter–geometry system reduces to `σ̈·σ + σ̇²·(σ−1) = 0` |
| **First integral** | `gaussian_width_first_integral` | `σ̇·exp(σ)/σ` is constant under the ODE |
| **Implicit solution** | `gaussian_width_solution_implicit` | First-integral form `σ̇ = C·σ·exp(−σ)` |
| **Exact time parameterization** | `gaussian_width_exact_time_parameterization` | `∫_{σ(0)}^{σ(t)} (e^s/s) ds = C·t` (Ei integral identity) |
| **Doubling-time bounds** | `doubling_time_two_sided_bound` | `e^{σ_0}/(2C) ≤ T_LS ≤ e^{2σ_0}/C` |
| **Optimal-width theorem** | `lsbridge_spreading_rate_max_at_one` | `σ̇ ≤ C/e`, attained at σ = 1 |
| **Frozen-solution admissibility** | `gaussian_width_dynamics_differs_from_free_schrodinger` | LSBridge admits `σ ≡ const`; free Schrödinger does not |
| **Continuity identically zero** | `gaussian_continuity_identically_zero` | Continuity eq is satisfied identically under the ansatz; σ is dynamical only via HJ-with-Bohm |
| **Constant-R classification** | `LSBridge_no_global_smooth_bounded_negative_R` + E4 + E-Gen-Sech | R = 0 (exponential), R > 0 (sech), R < 0 impossible for bounded profiles |
| **Free Schrödinger reduction at a² = 1** | `flat_limit_recovers_standard_quantum_dynamics` | Standard QM is the flat-metric limit |
| **Static Einstein-like identity** | `static_limit_recovers_einstein_identity` | `R + (4m/ℏ²)·V = (2/r⁴)·r_x²` at equilibrium |

**Attack surface:** none, modulo trust in Lean + the standard axioms. If a
reviewer rejects classical logic or `Classical.choice`, the entire stack
falls — but no other proved math is more secure.

---

## B. Model choices (intrinsic to the LSBridge framework, can be revisited)

These are choices encoded in the **definitions**, not consequences of
deeper principles. A different choice gives a different theory.

| Choice | Definition file | Alternative |
|---|---|---|
| **Matter-coupling rule `a² = r²`** | `LohmillerSlotineBackreaction.lean` (Phase D.4) | Alternative couplings `a² = f(r)` for any positive function `f`. Choice of `f(r) = r²` is motivated by dimensional and dressing-curvature arguments but is not unique. |
| **1+1 conformal metric `g = a²·diag(−1,1)`** | `Conformal1p1Metric` structure | Any of the C.3 chartwise SPD metrics. The 1+1 conformal choice is the simplest; a multi-dimensional or non-conformal version exists in the framework but is not the σ-ODE setting. |
| **Gaussian + quadratic phase ansatz** | `gaussianAmplitudeNormalized`, `gaussianPhaseQuadratic` | Any other smooth ansatz family (sech, exponential, etc.). The σ-ODE derivation is specific to Gaussian. **The sech-curved ODE is now proved (Backreaction Part 17): same structural LHS `ξ·ξ_pp + ξ_prime²·(ξ−1)`, different source `ℏ²/(m²·ξ)`. Frozen states are forbidden for sech (`sech_curved_rejects_frozen`). The qualitative LSBridge signatures (frozen-admissible, U-shape, exponential slowdown) are Gaussian-specific.** |
| **Continuity-fixed α = m·σ'/(2ℏσ)** | `continuity_alpha_relation` | Without the continuity constraint, α is a free function. The framework imposes continuity, which uniquely fixes α. |
| **Bohm potential `Q = -(ℏ²/2m)·(r_xx/r)`** | `bohmQuantumPotential` | Standard Madelung-Bohm Q. Alternative quantum potentials exist but would not give standard QM in the flat limit. |
| **Free particle (V = 0)** in the σ-ODE | Derivation chapter | The σ-ODE assumes no external potential. A trapped wavepacket would have a modified ODE — not derived here. |

**Attack surface:**
- *"`a² = r²` is ad hoc."* Reply: it is the unique simple identification that produces matter-coupled curved equilibrium with `V = (ℏ²/(2m·r²))·dressingCurvature`. Other couplings give other equilibria — testable but not done here.
- *"The Gaussian ansatz is restrictive."* Reply (corrected, 2026-05-25): the sech-curved ODE has been derived in Lean (Backreaction Part 17, `sech_curved_leading_order_sigma_ode`). It shares the same structural LHS function `ξ·ξ_pp + ξ_prime²·(ξ−1)` as the Gaussian, but acquires a nonzero source term `ℏ²/(m²·ξ)`. The frozen-state admissibility, U-shape, and exponential slowdown are therefore **Gaussian-specific**, NOT family-level. The earlier heuristic-script "robustness" claim is retracted; what survives across both families is the kinematic/structural LHS, not the qualitative dynamics.
- *"Trapped wavepackets are not addressed."* Reply: correct. The σ-ODE is for free spreading. Trapped systems would need a separate derivation.

---

## C. Platform mapping (assumptions when applying to photonic waveguides)

These convert the theorem variables to lab observables and are the most
vulnerable to "wrong assumption" attacks.

| Mapping | Assumption | Vulnerability |
|---|---|---|
| **Natural length scale `ℓ`** | `ℓ ≈ 1 μm` is a guess; the theory does not predict it. | If `ℓ ≪ 0.1 μm`, all photonic-wavelength tests give `R ≈ 1` regardless. The test is consistent with LSBridge with `ℓ → 0`, just not informative. |
| **Diffraction coefficient `D = t·a²`** | Standard waveguide-array model with hopping `t` and lattice `a`. | Higher-order terms (next-nearest-neighbor hopping, curvature of the dispersion) modify `D`. Must calibrate `D` independently via single-site diffraction. |
| **Photonic Schrödinger ≃ matter Schrödinger** | Both implement the same PDE structure (free-particle dispersion). | LSBridge backreaction is fundamentally a matter-amplitude effect (`a² = r²`). For photons, the "matter amplitude" is the field amplitude — but the physical interpretation of `a² = |E|²` as an emergent metric is by analogy, not derived. **This is the deepest mapping assumption.** |
| **Single-mode propagation** | Beam stays in one transverse mode. | Multi-mode coupling broadens the beam classically — must use single-mode arrays with adiabatic input coupling. |
| **No waveguide nonlinearity** | Linear-medium regime, low input power. | Kerr nonlinearity modifies dispersion at high intensity — `confounder_discrimination.py` shows this gives R < 1 (opposite sign from LSBridge), so distinguishable. |
| **Gaussian beam shaping** | The launched beam is well-described by a Gaussian. | Non-Gaussian beams would test a different sector of the theory. Verify via near-field imaging. |
| **σ_0 calibration** | Input width measured ±10% via near-field imaging. | Calibration errors propagate to R errors via D-uncertainty. |
| **Time = propagation distance z** | `z` plays role of `t` in the analog Schrödinger equation. | True for adiabatic propagation; backscattering or strong group-velocity dispersion would break this. |

**Attack surface:**
- *"`ℓ ~ 1 μm` is a guess."* Reply: yes; a null result at this scale bounds `ℓ`. Multiple wavelengths or platforms (BEC, polariton) could fit `ℓ` independently.
- *"Photonic analog is not matter."* Reply: the photonic test verifies the PDE structure of the prediction. A matter-side test (BEC) would test the ontological claim more directly but with greater experimental complexity.
- *"D-calibration uncertainty masks LSBridge signal."* Reply: in the σ_0 ∈ [3, 7] μm regime the predicted slowdown is 5×–1000×, far exceeding ~10% D-uncertainty.

---

## D. Possible confounders / failure modes

What could mimic an LSBridge signal (or hide a real one)?

| Confounder | Effect | Mitigation |
|---|---|---|
| **Linear loss** | Attenuates uniformly; does NOT affect width evolution. | None needed; predicts `R ≡ 1`, fully distinguishable. |
| **Kerr self-focusing** | Causes accelerated spreading or beam compression. | Predicts `R < 1` for all σ_0; opposite sign from LSBridge. Use low input power. |
| **Anderson localization** | Halts spreading above the localization length `ξ_loc`. | Threshold behavior; can mimic LSBridge at σ_0 ≥ ξ_loc. Calibrate `ξ_loc` via long-z scrambling measurements. |
| **NNN hopping** | Modifies effective D by factor `(1+ε)`. | Predicts `R ≈ const` (not σ_0-dependent). Calibrate via single-site discrete diffraction reference. |
| **Coupling losses at input** | Affect σ_0 calibration. | Near-field imaging; verify σ_0 with fitted Gaussian profile. |
| **Polarization effects** | If array is birefringent, beam can drift between modes. | Fix polarization at input. |
| **Multi-mode coupling** | Spurious mode mixing broadens beam classically. | Single-mode arrays only. |
| **Chip thermal effects** | Temperature gradients alter refractive index. | Temperature-stabilize the chip. |
| **Imperfect Gaussian shaping** | Initial beam not strictly Gaussian. | Verify via near-field imaging; fit input profile to Gaussian and report residuals. |
| **Photonic backscattering** | Reflections at chip end-faces. | Anti-reflection coatings or angle-polished input/output. |
| **Detector saturation** | Bright Gaussian peaks saturate the CCD/CMOS sensor. | Use neutral-density filters or dynamic-range stitching. |

### What could mimic an LSBridge signal?

The blind-classification challenge (`scripts/lsbridge_blind_challenge.py`)
tested 1,000 synthetic classifications across 5 mechanisms × 4 scenarios.
**Zero false-positive LSBridge verdicts** were found from any confounder.

The mechanism that came closest is **Anderson localization at large `ξ_loc`**:
- AL with `ξ_loc = 10 μm` predicts R ~ 8000 at σ_0 = 8 μm.
- LSBridge predicts R ~ 5400 at σ_0 = 8 μm.
- These differ by < 2× — *potentially confusable at high σ_0*.

**However**, at σ_0 ∈ [3, 7] μm:
- AL with `ξ_loc = 10 μm` predicts R = 1 (below threshold).
- LSBridge predicts R = 4.9, 56.6, 239, 1096.
- These differ by 5×–1100×.

**Recommendation:** the σ_0 ∈ [3, 7] μm window is uniquely-LSBridge.
Measurements OUTSIDE this window (e.g., σ_0 = 8–10 μm) could be ambiguous
between LSBridge and AL.

---

## E. Critical "if wrong" failure modes

What MUST be true for the LSBridge prediction to be testable?

1. **`ℓ` is not too small.** If `ℓ ≪ optical wavelength`, photonic tests
   probe σ_0 ≫ ℓ regime where R is astronomical — the test reduces to "did
   the beam fail to spread at all?" If `ℓ ≫ chip length`, no slowdown is
   visible. The sweet spot `ℓ ~ 0.1–10 μm` is what photonic platforms cover.

2. **The matter-coupling `a² = r²` is the right identification.** A
   different `f(r)` would give a different σ-ODE. Cross-platform tests
   (photonic + polariton + BEC) would distinguish if `f` is universal or
   not.

3. **The Gaussian ansatz captures the dominant dynamics.** Non-Gaussian
   beam shapes evolve under a *profile-specific* law. The Lean stack
   now proves (Backreaction Part 17) that sech profiles share the same
   structural width-ODE LHS but with a different source term, forbidding
   frozen states. So the headline R(σ_0) shape is Gaussian-sector. For
   a clean falsification test, restrict experiment to Gaussian inputs.
   A separate shape-dependence test (Gaussian vs sech vs other) is
   theoretically motivated and would test the deeper structural
   prediction.

4. **Photonic analog is faithful to matter.** Photonic waveguides
   implement the SAME PDE as matter Schrödinger. If LSBridge backreaction
   is intrinsically a matter ontology effect (not a PDE-structure effect),
   the photonic test could give a null result even if LSBridge is "true"
   for matter.

5. **No unmodeled systematics dominate.** Loss, nonlinearity, NNN hopping,
   AL, etc. are all distinguishable from LSBridge in the recommended
   measurement window. But other unforeseen systematics could give false
   positives.

---

## F. What a null result means

| Outcome | Conclusion |
|---|---|
| `R_measured ≈ 1` for all σ_0 ∈ [3, 10] μm at 5% noise | LSBridge with `ℓ ≳ 1 μm` is **FALSIFIED**. Either `ℓ < 0.3 μm` or the model is wrong. |
| `R_measured ≈ 1` for σ_0 ≤ 7 μm at extremely low noise (< 1%) | LSBridge with `ℓ ≳ 0.5 μm` is FALSIFIED. The natural-length lower bound is tightened. |
| `R_measured(σ_0)` follows the predicted curve | **LSBridge with the fitted `ℓ` is consistent.** The matter-coupling rule `a² = r²` is plausible at the photonic length scale. Cross-platform tests can confirm. |
| `R_measured ≈ Anderson localization shape` | Anderson localization, not LSBridge. The chip has too much disorder. |
| `R_measured` decreases with σ_0 (Kerr-like) | Self-focusing or other nonlinearity. Lower the input power. |

---

## G. What a positive result establishes

If the photonic pilot confirms LSBridge:
- The natural length `ℓ` is bracketed (Bayesian posterior gives 95% CI).
- The matter-coupling structure is verified at the photonic PDE level.
- The framework deserves cross-platform testing (BEC, polariton) to test
  whether `ℓ` is platform-independent (suggesting deeper physical
  significance) or platform-specific (suggesting an effective theory).

A confirmed photonic signal would NOT yet establish:
- That LSBridge is the deepest description (could be effective).
- That the matter-coupling `a² = r²` is unique (could be one of a family).
- That LSBridge applies to matter as well as photonic analogs.

These follow-up questions are well-defined but require multi-platform
verification.

---

## H. Hand-off recommendation

The audit above identifies **three vulnerability tiers**:

| Tier | Failure mode | Mitigation |
|---|---|---|
| **Tier 1 (most concerning)** | Photonic ≠ matter analog | Cross-platform test (photonic → polariton or BEC) needed for ontological claim |
| **Tier 2 (concerning)** | `ℓ ≪ 1 μm` | Multi-wavelength tests to constrain `ℓ` from below |
| **Tier 3 (manageable)** | Confounders (Kerr, AL, loss, NNN) | Already discriminated by `scripts/lsbridge_confounder_discrimination.py` |

**Net assessment:** the LSBridge predictions are testable, distinguishable
from known alternatives, and the photonic pilot would constrain `ℓ` (positive)
or set a lower bound on `ℓ` (null). The framework's deeper ontological claim
requires multi-platform verification.

The minimal photonic pilot in `LS_BRIDGE_MINIMAL_PILOT.md` is the cheapest
single test that respects all the vulnerabilities above.
