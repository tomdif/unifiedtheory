/- Weighted homeomorphism pullback on compactly supported continuous
configuration tests. The inverse is constructed from the nonzero weight;
the actual model's norm preservation is proved in a separate module. -/
import UnifiedTheory.Audit.KFCausalConfigurationTestSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalWeightedConfigurationTests
noncomputable section
open scoped CompactlySupported
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace

def weighted (e : Configuration ≃ₜ Configuration) (w : Configuration → ℂ)
    (hw : Continuous w) (f : Test) : Test :=
  ⟨⟨fun x => w x*f (e x),hw.mul (f.continuous.comp e.continuous)⟩,
    (f.hasCompactSupport.comp_homeomorph e).mul_left⟩

theorem weighted_apply (e : Configuration ≃ₜ Configuration) (w : Configuration → ℂ)
    (hw : Continuous w) (f : Test) (x : Configuration) : weighted e w hw f x = w x*f (e x) := rfl

theorem inverseWeight_continuous (e : Configuration ≃ₜ Configuration) (w : Configuration → ℂ)
    (hw : Continuous w) (hn : ∀ x, w x ≠ 0) : Continuous (fun y => (w (e.symm y))⁻¹) :=
  (hw.comp e.symm.continuous).inv₀ (fun y => hn (e.symm y))

def weightedEquiv (e : Configuration ≃ₜ Configuration) (w : Configuration → ℂ)
    (hw : Continuous w) (hn : ∀ x, w x ≠ 0) : Test ≃ₗ[ℂ] Test where
  toFun := weighted e w hw
  invFun := weighted e.symm (fun y => (w (e.symm y))⁻¹) (inverseWeight_continuous e w hw hn)
  left_inv f := by
    apply DFunLike.ext
    intro x
    simp only [weighted_apply,e.apply_symm_apply]
    rw [← mul_assoc,inv_mul_cancel₀ (hn (e.symm x)),one_mul]
  right_inv f := by
    apply DFunLike.ext
    intro x
    simp only [weighted_apply,e.symm_apply_apply]
    rw [← mul_assoc,mul_inv_cancel₀ (hn x),one_mul]
  map_add' f g := by
    apply DFunLike.ext
    intro x
    simp only [weighted_apply,CompactlySupportedContinuousMap.add_apply]
    ring
  map_smul' c f := by
    apply DFunLike.ext
    intro x
    simp only [weighted_apply,CompactlySupportedContinuousMap.smul_apply,RingHom.id_apply,smul_eq_mul]
    ring

theorem weightedEquiv_apply (e : Configuration ≃ₜ Configuration) (w : Configuration → ℂ)
    (hw : Continuous w) (hn : ∀ x, w x ≠ 0) (f : Test) (x : Configuration) :
    weightedEquiv e w hw hn f x = w x*f (e x) := rfl

theorem weightedEquiv_symm_apply (e : Configuration ≃ₜ Configuration) (w : Configuration → ℂ)
    (hw : Continuous w) (hn : ∀ x, w x ≠ 0) (f : Test) (x : Configuration) :
    (weightedEquiv e w hw hn).symm f x = (w (e.symm x))⁻¹*f (e.symm x) := rfl

#print axioms weighted
#print axioms weightedEquiv
#print axioms weightedEquiv_symm_apply

end
end UnifiedTheory.Audit.KFCausalWeightedConfigurationTests
