/- Born measures under sharp projections, measure-preserving coordinates
and tensor products. All statements concern arbitrary L2 vectors. -/
import UnifiedTheory.Audit.KFCausalL2BornLaw
import UnifiedTheory.Audit.KFCausalL2TensorEmbedding
import UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
import UnifiedTheory.Audit.KFCausalContractiveMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalBornLocalization
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalL2BornLaw
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y)

def mask (A : Set X) (hA : MeasurableSet A) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  multiplyL (A.indicator (fun _ => (1 : ℂ))) (measurable_const.indicator hA)
    (fun x => by
      classical
      by_cases hx : x ∈ A <;> simp [hx])

theorem mask_coe (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 μ) :
    mask μ A hA f =ᵐ[μ] A.indicator f := by
  classical
  filter_upwards [multiplyL_coe (μ := μ) (A.indicator (fun _ => (1 : ℂ)))
    (measurable_const.indicator hA) (fun x => by by_cases hx : x ∈ A <;> simp [hx]) f]
    with x hx
  change mask μ A hA f x = _ at hx
  rw [hx]
  by_cases h : x ∈ A <;> simp [h]

theorem mask_norm_square (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 μ) :
    ‖mask μ A hA f‖^2 = ∫ x in A, ‖f x‖^2 ∂μ := by
  classical
  rw [l2_norm_square,← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [mask_coe μ A hA f] with x hx
  rw [hx]
  by_cases h : x ∈ A <;> simp [h]

theorem law_mask (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 μ) :
    law μ f A = ENNReal.ofReal (‖mask μ A hA f‖^2) := by
  rw [law_apply μ f A hA,mask_norm_square]

theorem law_pullback (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (f : Lp ℂ 2 ν) :
    law μ (unitaryPullback e he f) = (law ν f).map e.symm := by
  ext A hA
  rw [law_apply μ _ A hA,Measure.map_apply e.symm.measurable hA,
    law_apply ν f _ (hA.preimage e.symm.measurable)]
  congr 1
  calc
    _ = ∫ x in A, ‖f (e x)‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (unitaryPullback_coe e he f)] with x hx
      rw [hx]
      rfl
    _ = _ := by
      have ht := setIntegral_map_equiv e.symm (fun x => ‖f (e x)‖^2) A (μ := ν)
      rw [he.symm.map_eq] at ht
      simpa only [MeasurableEquiv.apply_symm_apply] using ht

theorem law_product [SFinite μ] [SFinite ν] (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    law (μ.prod ν) (productState μ ν f g) = (law μ f).prod (law ν g) := by
  rw [law,law,law,prod_withDensity
    ((Lp.stronglyMeasurable f).measurable.norm.pow_const 2 |>.ennreal_ofReal)
    ((Lp.stronglyMeasurable g).measurable.norm.pow_const 2 |>.ennreal_ofReal)]
  apply withDensity_congr_ae
  filter_upwards [productState_coe μ ν f g] with z hz
  rw [hz,norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _)]

#print axioms mask_coe
#print axioms mask_norm_square
#print axioms law_mask
#print axioms law_pullback
#print axioms law_product

end
end UnifiedTheory.Audit.KFCausalBornLocalization
