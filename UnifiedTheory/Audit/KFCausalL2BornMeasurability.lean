/- The unnormalised Born measure is measurable in its actual L2 state.
This supplies a kernel, including at the zero state, without choosing
pointwise representatives jointly in two variables. -/
import UnifiedTheory.Audit.KFCausalL2BornLaw
import UnifiedTheory.Audit.KFCausalContractiveMultiplier
import Mathlib.MeasureTheory.Measure.GiryMonad

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalL2BornMeasurability
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalL2BornLaw
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def cut (A : Set X) (hA : MeasurableSet A) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  multiplyL (A.indicator (fun _ => (1 : ℂ))) (measurable_const.indicator hA)
    (fun x => by by_cases hx : x ∈ A <;> simp [hx])

theorem law_cut (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 μ) :
    law μ f A = ENNReal.ofReal (‖cut μ A hA f‖^2) := by
  rw [law_apply μ f A hA,l2_norm_square]
  congr 1
  rw [← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [multiplyL_coe (A.indicator (fun _ => (1 : ℂ)))
    (measurable_const.indicator hA) (fun x => by by_cases hx : x ∈ A <;> simp [hx]) f] with x hx
  change A.indicator (fun x => ‖f x‖^2) x = ‖cut μ A hA f x‖^2
  rw [show cut μ A hA f x = A.indicator (fun _ => (1 : ℂ)) x*f x from hx]
  by_cases ha : x ∈ A <;> simp [ha]

theorem law_eval_continuous (A : Set X) (hA : MeasurableSet A) :
    Continuous (fun f : Lp ℂ 2 μ => law μ f A) := by
  simp_rw [law_cut μ A hA]
  exact ENNReal.continuous_ofReal.comp (((cut μ A hA).continuous.norm).pow 2)

theorem law_measurable :
    @Measurable (Lp ℂ 2 μ) (Measure X) (borel _) _ (law μ) := by
  letI : MeasurableSpace (Lp ℂ 2 μ) := borel _
  letI : BorelSpace (Lp ℂ 2 μ) := ⟨rfl⟩
  exact Measure.measurable_of_measurable_coe _ (fun A hA => (law_eval_continuous μ A hA).measurable)

theorem law_finite (f : Lp ℂ 2 μ) : IsFiniteMeasure (law μ f) where
  measure_univ_lt_top := by rw [law_total]; exact ENNReal.ofReal_lt_top

#print axioms law_cut
#print axioms law_eval_continuous
#print axioms law_measurable
#print axioms law_finite
end
end UnifiedTheory.Audit.KFCausalL2BornMeasurability
