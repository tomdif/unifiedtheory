/- Bounded-time rectangle data determine spacetime measures finite on
bounded time windows. Global finite total mass is not assumed. -/
import UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSpacetimeMeasureSeparation
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalSpacetimeExhaustion

def timeSection (μ : Measure (ℝ × ℝ)) (A : Set ℝ) : Measure ℝ :=
  (μ.restrict (univ ×ˢ A)).map Prod.fst

theorem timeSection_apply (μ : Measure (ℝ × ℝ)) (A S : Set ℝ) (hS : MeasurableSet S) :
    timeSection μ A S = μ (S ×ˢ A) := by
  rw [timeSection,Measure.map_apply measurable_fst hS,
    Measure.restrict_apply (measurable_fst hS)]
  congr 1
  ext z
  simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,true_and]

theorem finite_ext_of_time_rectangles (μ ν : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a b : ℝ, a ≤ b → ∀ A : Set ℝ, MeasurableSet A →
      μ (Icc a b ×ˢ A) = ν (Icc a b ×ˢ A)) : μ = ν := by
  apply Measure.ext_prod
  intro S A hS hA
  letI : IsFiniteMeasure (timeSection μ A) := by unfold timeSection; infer_instance
  have he : timeSection μ A = timeSection ν A := by
    apply Measure.ext_of_Icc
    intro a b hab
    simpa only [timeSection_apply _ _ _ measurableSet_Icc] using h a b hab A hA
  have hx := congrArg (fun m : Measure ℝ => m S) he
  simpa only [timeSection_apply _ _ _ hS] using hx

theorem restrict_window_rectangle (μ : Measure (ℝ × ℝ)) (b c u v : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    μ.restrict (Icc b c ×ˢ univ) (Icc u v ×ˢ A) =
      μ (Icc (max u b) (min v c) ×ˢ A) := by
  rw [Measure.restrict_apply (measurableSet_Icc.prod hA)]
  congr 1
  ext z
  simp only [mem_inter_iff,mem_prod,mem_Icc,mem_univ,and_true,max_le_iff,le_min_iff]
  tauto

theorem ext_of_finite_windows (μ ν : Measure (ℝ × ℝ))
    (hμ : ∀ b c : ℝ, IsFiniteMeasure (μ.restrict (Icc b c ×ˢ univ)))
    (hν : ∀ b c : ℝ, IsFiniteMeasure (ν.restrict (Icc b c ×ˢ univ)))
    (h : ∀ a b : ℝ, a ≤ b → ∀ A : Set ℝ, MeasurableSet A →
      μ (Icc a b ×ˢ A) = ν (Icc a b ×ˢ A)) : μ = ν := by
  apply Measure.ext_of_iUnion_eq_univ (window_cover 0)
  intro n
  change μ.restrict (Icc (left 0 n) (right 0 n) ×ˢ univ) =
    ν.restrict (Icc (left 0 n) (right 0 n) ×ˢ univ)
  letI := hμ (left 0 n) (right 0 n)
  letI := hν (left 0 n) (right 0 n)
  apply finite_ext_of_time_rectangles
  intro u v _ A hA
  change μ.restrict (Icc (left 0 n) (right 0 n) ×ˢ univ) (Icc u v ×ˢ A) =
    ν.restrict (Icc (left 0 n) (right 0 n) ×ˢ univ) (Icc u v ×ˢ A)
  rw [restrict_window_rectangle μ _ _ _ _ A hA,restrict_window_rectangle ν _ _ _ _ A hA]
  by_cases hab : max u (left 0 n) ≤ min v (right 0 n)
  · exact h _ _ hab A hA
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab),empty_prod,measure_empty,measure_empty]

#print axioms timeSection_apply
#print axioms finite_ext_of_time_rectangles
#print axioms restrict_window_rectangle
#print axioms ext_of_finite_windows
end
end UnifiedTheory.Audit.KFCausalSpacetimeMeasureSeparation
