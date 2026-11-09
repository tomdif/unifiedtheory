/- A real probability tail gives frequency control without a moment
assumption. The resulting modulus is uniform in the base frequency. -/
import UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalProbabilityFrequencyTail
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar scalar_add scalar_norm scalar_sub_one)

theorem scalar_difference (v w x : ℝ) :
    ‖scalar (v*x)-scalar (w*x)‖ ≤ |v-w| *|x| := by
  have he : scalar (v*x)-scalar (w*x) =
      (scalar ((v-w)*x)-1)*scalar (w*x) := by
    rw [sub_mul,one_mul,← scalar_add]
    congr 2
    ring
  rw [he,norm_mul,scalar_norm,mul_one]
  exact (scalar_sub_one _).trans_eq (abs_mul _ _)

theorem characteristic_scalar (μ : ProbabilityMeasure ℝ) (v : ℝ) :
    charFun (μ : Measure ℝ) v = ∫ x, scalar (v*x) ∂(μ : Measure ℝ) := by
  rw [charFun_apply_real]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [scalar,Complex.ofReal_mul]
  congr 1
  ring

theorem characteristic_difference_tail (μ : ProbabilityMeasure ℝ) (v w R : ℝ) (hR : 0 ≤ R) :
    ‖charFun (μ : Measure ℝ) v-charFun (μ : Measure ℝ) w‖ ≤
      |v-w| *R+2*(μ : Measure ℝ).real {x | R < |x|} := by
  classical
  let A : Set ℝ := {x | R < |x|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (by fun_prop)
  have hi (u : ℝ) : Integrable (fun x : ℝ => scalar (u*x)) (μ : Measure ℝ) :=
    (integrable_const (1:ℝ)).mono' (by unfold scalar; fun_prop)
      (ae_of_all _ (fun x => (scalar_norm (u*x)).le))
  have hg : Integrable (fun x : ℝ => |v-w| *R+2*A.indicator (fun _ => (1:ℝ)) x)
      (μ : Measure ℝ) :=
    (integrable_const _).add (((integrable_const (1:ℝ)).indicator hA).const_mul 2)
  rw [characteristic_scalar,characteristic_scalar,← integral_sub (hi v) (hi w)]
  calc
    _ ≤ ∫ x, ‖scalar (v*x)-scalar (w*x)‖ ∂(μ : Measure ℝ) := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (|v-w| *R+2*A.indicator (fun _ => (1:ℝ)) x) ∂(μ : Measure ℝ) := by
      apply integral_mono_ae ((hi v).sub (hi w)).norm hg
      filter_upwards [] with x
      change ‖scalar (v*x)-scalar (w*x)‖ ≤ _
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        have hb : ‖scalar (v*x)-scalar (w*x)‖ ≤ 2 := by
          simpa only [scalar_norm,one_add_one_eq_two] using norm_sub_le (scalar (v*x)) (scalar (w*x))
        nlinarith [mul_nonneg (abs_nonneg (v-w)) hR]
      · rw [Set.indicator_of_notMem hx,mul_zero,add_zero]
        exact (scalar_difference v w x).trans
          (mul_le_mul_of_nonneg_left (le_of_not_gt hx) (abs_nonneg (v-w)))
    _ = _ := by
      rw [integral_add (integrable_const _) (((integrable_const (1:ℝ)).indicator hA).const_mul 2),
        integral_const_mul (2:ℝ),integral_indicator_const _ hA]
      simp only [integral_const,probReal_univ,smul_eq_mul,mul_one,one_mul]
      rfl

theorem frequency_window (μ : ℕ → ℝ → ProbabilityMeasure ℝ) (s T : ℝ)
    (ht : ∀ η : ℝ, 0 < η → ∃ R : ℝ, 0 < R ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T → (μ n t : Measure ℝ).real {x | R < |x|} < η)
    (η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t v w : ℝ,
      |t-s| ≤ T → |v-w| ≤ ρ →
      ‖charFun (μ n t : Measure ℝ) v-charFun (μ n t : Measure ℝ) w‖ < η := by
  obtain ⟨R,hR,N,hN⟩ := ht (η/4) (by positivity)
  refine ⟨η/(4*(R+1)),by positivity,N,?_⟩
  intro n hn t v w htt hv
  have hb := characteristic_difference_tail (μ n t) v w R hR.le
  have htail := hN n hn t htt
  have hx := (le_div_iff₀ (by positivity : 0 < 4*(R+1))).mp hv
  nlinarith [abs_nonneg (v-w)]

#print axioms scalar_difference
#print axioms characteristic_scalar
#print axioms characteristic_difference_tail
#print axioms frequency_window

end
end UnifiedTheory.Audit.KFCausalProbabilityFrequencyTail
