/-
  Cosmology/QQG/Couplings.lean
  ───────────────────────────────────

  Quadratic-gravity couplings (ξ, λ) and their 1-loop "physical" β-functions
  as given in eq (2) of Liu–Quintin–Afshordi, arXiv:2510.18733v2:

      β_ξ  = − (1/(4π)²) · ( ξ² − 36 λ ξ − 2520 λ² ) / 36
      β_λ  = − (1/(4π)²) · ( (1617 + 90 N) λ − 20 ξ ) · λ / 90

  Here N is the matter-multiplicity weight of eq (3):

      N = (1/60) N_scalar + (1/5) N_vector + (1/20) N_fermion .

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. Both β-functions vanish at the origin (ξ,λ) = (0,0).
       This is the formal statement of "UV asymptotic freedom" for QQG
       in the sense that the origin is a fixed point of the RG flow.
    2. β_ξ on the ξ = 0 axis equals (70/(4π)²) λ², so β_ξ ≥ 0 there.
    3. β_λ on the λ = 0 axis vanishes identically.
    4. The discriminant of β_ξ viewed as a quadratic in ξ at fixed λ is
       (36² + 4·2520) λ² = 11376 λ² ≥ 0, so the separatrices ξ = ξ_±(λ)
       always exist when λ ≠ 0.

  WHAT IS NOT PROVEN HERE:
    Anything about the validity of the eq (2) scheme itself.  The paper
    flags refs [51–54] as ongoing debate about the "physical" β-functions;
    we encode eq (2) as a *definition*, not as a derived fact.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.Cosmology.QQG

open Real

/-! ## 1. The QQG coupling pair (ξ, λ) -/

/-- The pair of dimensionless couplings of quadratic gravity:
    `ξ` multiplies the `R²` term and `λ` multiplies the Weyl-squared term
    in the bare action of eq (1).  Both real, sign-unconstrained. -/
structure QQGCouplings where
  ξ : ℝ
  /-- Field name `lam` to avoid clashing with Lean's `λ` lambda binder. -/
  lam : ℝ

/-- The origin (ξ, λ) = (0, 0): the UV fixed point. -/
def QQGCouplings.origin : QQGCouplings := ⟨0, 0⟩

/-! ## 2. Matter-multiplicity weight N (eq 3) -/

/-- The matter weight of eq (3): a positive real combination of the
    counts of scalar, vector, and fermion fields. -/
noncomputable def matterMultiplicity
    (N_scalar N_vector N_fermion : ℕ) : ℝ :=
  (N_scalar : ℝ) / 60 + (N_vector : ℝ) / 5 + (N_fermion : ℝ) / 20

/-- The matter weight is non-negative. -/
theorem matterMultiplicity_nonneg (Ns Nv Nf : ℕ) :
    0 ≤ matterMultiplicity Ns Nv Nf := by
  unfold matterMultiplicity
  have h1 : (0 : ℝ) ≤ (Ns : ℝ) / 60 := by positivity
  have h2 : (0 : ℝ) ≤ (Nv : ℝ) / 5 := by positivity
  have h3 : (0 : ℝ) ≤ (Nf : ℝ) / 20 := by positivity
  linarith

/-! ## 3. The 1-loop "physical" β-functions of eq (2) -/

/-- The 1-loop β-function for ξ (eq 2, top line). -/
noncomputable def betaXi (c : QQGCouplings) : ℝ :=
  -(1 / (4 * Real.pi)^2) * (c.ξ^2 - 36 * c.lam * c.ξ - 2520 * c.lam^2) / 36

/-- The 1-loop β-function for λ (eq 2, bottom line, with matter weight N). -/
noncomputable def betaLambda (N : ℝ) (c : QQGCouplings) : ℝ :=
  -(1 / (4 * Real.pi)^2)
    * ((1617 + 90 * N) * c.lam - 20 * c.ξ) * c.lam / 90

/-! ## 4. The origin is a fixed point: asymptotic freedom -/

/-- β_ξ vanishes at the origin. -/
theorem betaXi_at_origin : betaXi QQGCouplings.origin = 0 := by
  simp [betaXi, QQGCouplings.origin]

/-- β_λ vanishes at the origin, for any matter content. -/
theorem betaLambda_at_origin (N : ℝ) :
    betaLambda N QQGCouplings.origin = 0 := by
  simp [betaLambda, QQGCouplings.origin]

/-- **UV asymptotic freedom (formal statement).**  The RG flow has the
    origin as a fixed point: both β-functions vanish there, so trajectories
    that approach (ξ, λ) = (0, 0) in the UV do so asymptotically. -/
theorem origin_is_RG_fixed_point (N : ℝ) :
    betaXi QQGCouplings.origin = 0
      ∧ betaLambda N QQGCouplings.origin = 0 :=
  ⟨betaXi_at_origin, betaLambda_at_origin N⟩

/-! ## 5. β-functions on the coordinate axes -/

/-- On the ξ = 0 axis, β_ξ = (70/(4π)²) λ² ≥ 0.  Hence in this regime
    ξ is driven away from zero as λ grows. -/
theorem betaXi_on_xi_axis (lam : ℝ) :
    betaXi ⟨0, lam⟩ = (70 / (4 * Real.pi)^2) * lam^2 := by
  simp only [betaXi]
  ring

/-- On the ξ = 0 axis, β_ξ ≥ 0. -/
theorem betaXi_nonneg_on_xi_axis (lam : ℝ) : 0 ≤ betaXi ⟨0, lam⟩ := by
  rw [betaXi_on_xi_axis]
  have h_pi : (0 : ℝ) < (4 * Real.pi)^2 := by
    have : (0 : ℝ) < 4 * Real.pi := by positivity
    positivity
  have h_lam : 0 ≤ lam^2 := sq_nonneg lam
  positivity

/-- On the λ = 0 axis, β_λ vanishes identically. -/
theorem betaLambda_on_lambda_axis (N ξ : ℝ) :
    betaLambda N ⟨ξ, 0⟩ = 0 := by
  simp [betaLambda]

/-! ## 6. Separatrix discriminant -/

/-- The β_ξ function viewed as a quadratic in ξ (at fixed λ) has roots
    where ξ² − 36 λ ξ − 2520 λ² = 0.  The discriminant of this quadratic
    is 36² + 4·2520 = 11376, all multiplied by λ². -/
noncomputable def separatrixDiscriminant (lam : ℝ) : ℝ := 11376 * lam^2

/-- The separatrix discriminant is non-negative for all λ; hence the
    two separatrices of the RG flow (the red dashed lines of Fig. 1)
    exist for every λ. -/
theorem separatrixDiscriminant_nonneg (lam : ℝ) :
    0 ≤ separatrixDiscriminant lam := by
  unfold separatrixDiscriminant
  have : (0 : ℝ) ≤ lam^2 := sq_nonneg lam
  linarith

/-- Algebraic identity: the polynomial ξ² − 36 λ ξ − 2520 λ², evaluated
    at the larger separatrix root ξ = 18 λ + √(11376 λ²)/2, factors away.
    We give the *unfactored* identity that recovers the discriminant. -/
theorem betaXi_quadratic_discriminant (ξ lam : ℝ) :
    (ξ - 18 * lam)^2 - separatrixDiscriminant lam / 4
      = ξ^2 - 36 * lam * ξ - 2520 * lam^2 := by
  unfold separatrixDiscriminant
  ring

end UnifiedTheory.Cosmology.QQG
