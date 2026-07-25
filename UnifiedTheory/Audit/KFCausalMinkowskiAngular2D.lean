/-
  Audit/KFCausalMinkowskiAngular2D.lean   (Volume sector → the 2D angular/moment computation)

  The first genuinely Lorentzian-geometry step, in 2D -- and its honest verdict.

  ATTEMPTING the naive angular integral exposes MORE bundling, as the interface predicted.
  In 2D the past shell is a hyperbola parametrized by rapidity θ ∈ ℝ (non-compact), so the
  raw angular integral `∫ ξ^μ ξ^ν dθ` over the full shell DIVERGES.  Even the zeroth
  moment `∫_{J⁻} f(ρV) dy` diverges (infinite past), which is why the causal-set
  d'Alembertian on a CONSTANT field diverges and must be regularized by its own moment
  structure.  So there is no clean finite "angular integral = box coefficient"; the finite
  content lives in the smearing function's MOMENTS, which encode the divergence cancellation.

  WHAT IS FINITE AND COMPUTED HERE (unconditional).  For the standard 2D BDG smearing
  function `f(μ) = e^{-μ}(1 - 2μ + ½μ²)`, using `∫_0^∞ e^{-μ} μ^k dμ = k!`:

      ∫_0^∞ f(μ) dμ   = 0!  - 2·1! + ½·2!  = 1 - 2 + 1  = 0,   (annihilates constants)
      ∫_0^∞ μ f(μ) dμ = 1!  - 2·2! + ½·3!  = 1 - 4 + 3  = 0,   (annihilates linear fields)
      ∫_0^∞ μ² f(μ)dμ = 2!  - 2·3! + ½·4!  = 2 - 12 + 12 = 2.   (the surviving 2nd moment)

  These are NECESSARY cancellation conditions for locality; they do NOT yet prove the
  `□`-normalization.  The surviving value `2` becomes the `□φ` coefficient only after the
  null-coordinate Jacobian, the operator's exterior normalization and local counterterm,
  compact support/decay of `φ`, cancellation of the noncompact rapidity/light-cone
  contribution, and the justified `ρ → ∞` limit.  The two zeros are the necessary moment
  conditions; the `2` is the surviving second moment, not (yet) the operator normalization.

  MECHANISM (`f2D_kernel_second_deriv`).  The reason the two moments vanish is structural:

      f(μ) = e^{-μ}(1 - 2μ + ½μ²) = ½ (μ² e^{-μ})''.

  A `k=0,1` moment of a second derivative of a rapidly-decaying kernel vanishes by parts;
  this identity is also the integration-by-parts mechanism that transfers derivatives from
  the singular kernel onto the test field in the distributional limit.

  Still bundled (the informative residue): the ANGULAR divergence and its cancellation
  against a compactly-supported test field, and the passage to the ρ→∞ limit, are the
  remaining regularization the abstract interface hides.  The moments below are the part
  that is genuinely finite and now proved.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecLaplaceScaling

set_option autoImplicit false

open MeasureTheory Real Set
open UnifiedTheory.Audit.KFCausalCSpecLaplaceScaling

namespace UnifiedTheory.Audit.KFCausalMinkowskiAngular2D

/-- `e^{-x} x^n` is integrable on `(0,∞)` (nat-power form of the Gamma integrand). -/
theorem integrable_exp_pow (n : ℕ) :
    IntegrableOn (fun x => Real.exp (-x) * x ^ n) (Ioi (0 : ℝ)) := by
  refine IntegrableOn.congr_fun
    (Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity)) ?_ measurableSet_Ioi
  intro x hx
  rw [mem_Ioi] at hx
  dsimp only
  rw [show ((n : ℝ) + 1 - 1) = (n : ℝ) by ring, Real.rpow_natCast]

/-- The standard 2D BDG smearing function `f(μ) = e^{-μ}(1 - 2μ + ½μ²)`. -/
noncomputable def f2D (μ : ℝ) : ℝ := Real.exp (-μ) * (1 - 2 * μ + (1 / 2) * μ ^ 2)

/-- **Zeroth moment (annihilates constants).**  `∫_0^∞ f(μ) dμ = 0`. -/
theorem f2D_moment0 : ∫ μ in Ioi (0 : ℝ), f2D μ = 0 := by
  have ie0 : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    simpa using integrable_exp_pow 0
  have ie1 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x) (Ioi 0) := by
    simpa using integrable_exp_pow 1
  have ve0 : ∫ x in Ioi (0 : ℝ), Real.exp (-x) = 1 := by rw [integral_exp_neg_Ioi]; simp
  have ve1 : ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x = 1 := by simpa using gamma_monomial_integral 1
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun μ => Real.exp (-μ) - 2 * (Real.exp (-μ) * μ) + (1 / 2) * (Real.exp (-μ) * μ ^ 2))
    (fun μ _ => by unfold f2D; ring)]
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, ve0, ve1,
    gamma_monomial_integral 2]
  · norm_num [Nat.factorial]
  all_goals (first
    | exact ie0
    | exact ie1.const_mul 2
    | exact (integrable_exp_pow 2).const_mul (1 / 2)
    | exact ie0.sub (ie1.const_mul 2))

/-- **First moment (annihilates linear fields).**  `∫_0^∞ μ f(μ) dμ = 0`. -/
theorem f2D_moment1 : ∫ μ in Ioi (0 : ℝ), μ * f2D μ = 0 := by
  have ie1 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x) (Ioi 0) := by
    simpa using integrable_exp_pow 1
  have ve1 : ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x = 1 := by simpa using gamma_monomial_integral 1
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun μ => Real.exp (-μ) * μ - 2 * (Real.exp (-μ) * μ ^ 2)
      + (1 / 2) * (Real.exp (-μ) * μ ^ 3)) (fun μ _ => by unfold f2D; ring)]
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, ve1,
    gamma_monomial_integral 2, gamma_monomial_integral 3]
  · norm_num [Nat.factorial]
  all_goals (first
    | exact ie1
    | exact (integrable_exp_pow 2).const_mul 2
    | exact (integrable_exp_pow 3).const_mul (1 / 2)
    | exact ie1.sub ((integrable_exp_pow 2).const_mul 2))

/-- **Second moment (the `□φ` normalization).**  `∫_0^∞ μ² f(μ) dμ = 2`.  This surviving
second-order coefficient is what becomes the flat-space d'Alembertian `□φ`. -/
theorem f2D_moment2 : ∫ μ in Ioi (0 : ℝ), μ ^ 2 * f2D μ = 2 := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun μ => Real.exp (-μ) * μ ^ 2 - 2 * (Real.exp (-μ) * μ ^ 3)
      + (1 / 2) * (Real.exp (-μ) * μ ^ 4)) (fun μ _ => by unfold f2D; ring)]
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul,
    gamma_monomial_integral 2, gamma_monomial_integral 3, gamma_monomial_integral 4]
  · norm_num [Nat.factorial]
  all_goals (first
    | exact integrable_exp_pow 2
    | exact (integrable_exp_pow 3).const_mul 2
    | exact (integrable_exp_pow 4).const_mul (1 / 2)
    | exact (integrable_exp_pow 2).sub ((integrable_exp_pow 3).const_mul 2))

/-- **Kernel first derivative.**  `d/dμ (μ² e^{-μ}) = e^{-μ}(2μ - μ²)`. -/
theorem f2D_kernel_first_deriv (μ : ℝ) :
    HasDerivAt (fun x => x ^ 2 * Real.exp (-x)) (Real.exp (-μ) * (2 * μ - μ ^ 2)) μ := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * μ) μ := by simpa using hasDerivAt_pow 2 μ
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-μ)) μ := by
    simpa using (Real.hasDerivAt_exp (-μ)).comp μ (hasDerivAt_neg μ)
  convert h1.mul h2 using 1
  ring

/-- **Kernel second derivative = 2·f (the mechanism).**  `d²/dμ² (μ² e^{-μ}) = 2 f(μ)`,
i.e. `f(μ) = ½ (μ² e^{-μ})''`.  The first slot is the first derivative `e^{-μ}(2μ - μ²)`
from `f2D_kernel_first_deriv`, so this is genuinely the second derivative of `μ² e^{-μ}`.
This is why the `k=0,1` moments vanish and is the integration-by-parts kernel identity for
the distributional continuum limit. -/
theorem f2D_kernel_second_deriv (μ : ℝ) :
    HasDerivAt (fun x => Real.exp (-x) * (2 * x - x ^ 2)) (2 * f2D μ) μ := by
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-μ)) μ := by
    simpa using (Real.hasDerivAt_exp (-μ)).comp μ (hasDerivAt_neg μ)
  have h3 : HasDerivAt (fun x : ℝ => 2 * x - x ^ 2) (2 - 2 * μ) μ := by
    simpa using ((hasDerivAt_id μ).const_mul 2).sub (hasDerivAt_pow 2 μ)
  convert h2.mul h3 using 1
  unfold f2D; ring

#print axioms f2D_moment0
#print axioms f2D_moment1
#print axioms f2D_moment2
#print axioms f2D_kernel_first_deriv
#print axioms f2D_kernel_second_deriv

end UnifiedTheory.Audit.KFCausalMinkowskiAngular2D
