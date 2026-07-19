/-
  LayerB/BochnerConcavityLift.lean
  ─────────────────────────────────

  **Bochner-integration concavity lift on `Matrix (Fin n) (Fin n) ℂ`** —
  the Layer C named gate `Bochner_Concavity_Lift_Target` from
  `LayerB/RpowOperatorConcavity.lean`, discharged unconditionally.

  ## What this file ships

    • `bochner_concavity_lift` — for a Bochner-integrable family
      `f : ℝ → Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ`
      that is a.e. operator-concave on `Ici 0`, the integral
      `A ↦ ∫ t, f t A ∂ν` is operator-concave on `Ici 0`.

      Direct application of Mathlib's
      `MeasureTheory.integral_concaveOn_of_integrand_ae`
      after assembling the required typeclass infrastructure
      (`PartialOrder`, `IsOrderedAddMonoid`, `IsOrderedModule ℝ`,
      `ClosedIciTopology`) on `Matrix (Fin n) (Fin n) ℂ`.

    • `bochnerConcavityLift_holds` — `Bochner_Concavity_Lift_Target`
      discharged unconditionally.

  ## Typeclass infrastructure

  The Mathlib lemma `integral_concaveOn_of_integrand_ae` requires
  (besides the standard normed-space and integration setup):

    [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    [ClosedIciTopology E]

  For `E = Matrix (Fin n) (Fin n) ℂ` with `Matrix.Norms.L2Operator`:

    • `PartialOrder` and `IsOrderedAddMonoid`
      ← `MatrixOrder` (scoped instances in `Mathlib/Analysis/Matrix/Order.lean`).
    • `IsOrderedModule ℝ`
      ← derived from `StarOrderedRing` + `StarModule ℝ` via the
        instance in `Mathlib/Algebra/Order/Star/Basic.lean` (line 400).
    • `ClosedIciTopology`
      ← inherited from `OrderClosedTopology` on the CStar-algebra
        (instance in `Mathlib/Analysis/CStarAlgebra/.../Order.lean`
        line 474) ; `OrderClosedTopology` implies `ClosedIciTopology`
        (instance in `Mathlib/Topology/Order/OrderClosed.lean` line 609).
    • `NormedSpace ℝ` ← from `NormedSpace ℂ` via `RestrictScalars`.
    • `CompleteSpace` ← from `Pi.complete` on the underlying finite
        function space.

  All instances above are inferred automatically once the relevant
  scoped namespaces are opened.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-01.
-/

import UnifiedTheory.LayerB.RpowOperatorConcavity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.OrderClosed

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.BochnerConcavityLift

open Matrix Complex MeasureTheory Set
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open UnifiedTheory.LayerB.RpowOperatorConcavity

/-! ## 1. The general Bochner-lift lemma. -/

/-- **Bochner integration preserves operator concavity on
    `Matrix (Fin n) (Fin n) ℂ`.**

    For a measurable family `f : ℝ → Matrix (Fin n) (Fin n) ℂ →
    Matrix (Fin n) (Fin n) ℂ`, if

      (i)  `f t` is operator-concave on `Ici 0` for almost every `t`,
      (ii) for every `A ∈ Ici 0`, `t ↦ f t A` is Bochner-integrable,

    then the functional `A ↦ ∫ t, f t A ∂ν` is operator-concave on
    `Ici 0`.

    This is a direct application of Mathlib's
    `MeasureTheory.integral_concaveOn_of_integrand_ae`, with the
    required typeclass infrastructure for matrices supplied by
    `MatrixOrder` (partial order, ordered add-monoid, star-ordered
    ring → IsOrderedModule ℝ) and `Matrix.Norms.L2Operator` (CStar
    algebra → OrderClosedTopology → ClosedIciTopology). -/
theorem bochner_concavity_lift {n : ℕ} {ν : Measure ℝ}
    (f : ℝ → Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (h_concave : ∀ᵐ t ∂ν,
      ConcaveOn ℝ (Set.Ici (0 : Matrix (Fin n) (Fin n) ℂ)) (f t))
    (h_int : ∀ A ∈ Set.Ici (0 : Matrix (Fin n) (Fin n) ℂ),
      Integrable (fun t => f t A) ν) :
    ConcaveOn ℝ
      (Set.Ici (0 : Matrix (Fin n) (Fin n) ℂ))
      (fun A => ∫ t, f t A ∂ν) := by
  have hs : Convex ℝ (Set.Ici (0 : Matrix (Fin n) (Fin n) ℂ)) :=
    convex_Ici _
  exact MeasureTheory.integral_concaveOn_of_integrand_ae
    (β := Matrix (Fin n) (Fin n) ℂ) hs h_concave h_int

/-! ## 2. Discharge of `Bochner_Concavity_Lift_Target`. -/

/-- **`Bochner_Concavity_Lift_Target` discharged unconditionally.**

    Specialises `bochner_concavity_lift` to the measure
    `μ.restrict (Set.Ioi 0)` and the integrand
    `t ↦ cfcₙ (Real.rpowIntegrand₀₁ p t)`. -/
theorem bochnerConcavityLift_holds : Bochner_Concavity_Lift_Target := by
  intro m p _hp μ h_ae h_int
  -- Apply the general lift with `ν = μ.restrict (Set.Ioi 0)` and
  -- `f t A = cfcₙ (Real.rpowIntegrand₀₁ p t) A`.
  exact bochner_concavity_lift
    (n := m)
    (ν := μ.restrict (Set.Ioi 0))
    (fun t A => cfcₙ (Real.rpowIntegrand₀₁ p t) A)
    h_ae h_int

/-! ## 3. Corollary: full unconditional discharge of the Layer-D
        rpow-concavity assembly. -/

/-- **`Rpow_Operator_Concavity_Target` discharged conditional only on
    the remaining per-`t` gate.**

    Combines this file's unconditional Bochner-lift discharge with
    the Layer-D assembly in
    `UnifiedTheory.LayerB.RpowOperatorConcavity` to remove
    `Bochner_Concavity_Lift_Target` from the gate list. -/
theorem rpow_operator_concavity_target_modulo_per_t
    (h_per_t : RpowIntegrand_Per_t_Operator_Concavity_Target) :
    UnifiedTheory.LayerB.LiebRpowRoute.Rpow_Operator_Concavity_Target :=
  rpow_operator_concavity_target_from_gates h_per_t bochnerConcavityLift_holds

end UnifiedTheory.LayerB.BochnerConcavityLift
