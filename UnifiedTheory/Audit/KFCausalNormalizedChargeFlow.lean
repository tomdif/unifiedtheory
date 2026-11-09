/- The frequency-normalized standing-wave rotation. A scale lambda != 0
converts antisymmetric Fourier frequencies to momenta before rotation.
The conjugated rotation preserves volume even when |lambda| != 1. -/
import UnifiedTheory.Audit.KFCausalPairedRotation
import UnifiedTheory.Audit.KFCausalHaarConjugation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalPairedRotation
open UnifiedTheory.Audit.KFCausalHaarConjugation

def dilate (c : ℝ) (x : Space) : Space := WithLp.toLp 2 fun
  | .inl i => c*x (.inl i)
  | .inr i => x (.inr i)

theorem dilate_compose (c κ : ℝ) (x : Space) : dilate c (dilate κ x) = dilate (c*κ) x := by
  ext i
  rcases i with i | i <;> simp [dilate, mul_assoc]

theorem dilate_one (x : Space) : dilate 1 x = x := by
  ext i
  rcases i with i | i <;> simp [dilate]

def dilationEquiv (c : ℝ) (hc : c ≠ 0) : Space ≃ₗ[ℝ] Space where
  toFun := dilate c
  invFun := dilate c⁻¹
  left_inv x := by rw [dilate_compose, inv_mul_cancel₀ hc, dilate_one]
  right_inv x := by rw [dilate_compose, mul_inv_cancel₀ hc, dilate_one]
  map_add' x y := by
    ext i
    rcases i with i | i <;> simp [dilate, mul_add]
  map_smul' c x := by
    ext i
    rcases i with i | i <;> simp [dilate]
    ring

def flowEquiv (c : ℝ) (hc : c ≠ 0) (θ : ℝ) : Space ≃ᵐ Space :=
  conjugate (dilationEquiv c hc).toContinuousLinearEquiv
    (rotationIsometry θ).toMeasurableEquiv

theorem flow_apply (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    flowEquiv c hc θ x = dilate c⁻¹ (rotate θ (dilate c x)) := rfl

theorem flow_preserves_volume (c : ℝ) (hc : c ≠ 0) (θ : ℝ) :
    MeasurePreserving (flowEquiv c hc θ) :=
  conjugate_preserves volume _ _ (rotation_preserves_volume θ)

theorem flow_zero (c : ℝ) (hc : c ≠ 0) (x : Space) : flowEquiv c hc 0 x = x := by
  rw [flow_apply, rotate_zero, dilate_compose, inv_mul_cancel₀ hc, dilate_one]

theorem flow_compose (c : ℝ) (hc : c ≠ 0) (θ φ : ℝ) (x : Space) :
    flowEquiv c hc θ (flowEquiv c hc φ x) = flowEquiv c hc (θ+φ) x := by
  simp only [flow_apply, dilate_compose, mul_inv_cancel₀ hc, dilate_one, rotate_compose]

theorem flow_reverse (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    flowEquiv c hc (-θ) (flowEquiv c hc θ x) = x := by
  rw [flow_compose, neg_add_cancel, flow_zero]

theorem flow_period (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    flowEquiv c hc (θ+2*Real.pi) x = flowEquiv c hc θ x := by
  simp only [flow_apply, rotate_period]

theorem flow_clock (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    flowEquiv c hc θ x (.inr 0) = x (.inr 0) := rfl

theorem flow_neutral (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    flowEquiv c hc θ x (.inr 3) = x (.inr 3) := rfl

theorem flow_first_plane (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    (flowEquiv c hc θ x (.inl 0), flowEquiv c hc θ x (.inr 1)) =
      (Real.cos θ*x (.inl 0)-Real.sin θ*x (.inr 1)/c,
       c*Real.sin θ*x (.inl 0)+Real.cos θ*x (.inr 1)) := by
  ext <;> simp [flow_apply, dilate, rotate] <;> field_simp

theorem flow_second_plane (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    (flowEquiv c hc θ x (.inl 1), flowEquiv c hc θ x (.inr 2)) =
      (Real.cos θ*x (.inl 1)-Real.sin θ*x (.inr 2)/c,
       c*Real.sin θ*x (.inl 1)+Real.cos θ*x (.inr 2)) := by
  ext <;> simp [flow_apply, dilate, rotate] <;> field_simp

theorem flow_continuous (c : ℝ) (hc : c ≠ 0) :
    Continuous (fun p : ℝ × Space => flowEquiv c hc p.1 p.2) := by
  have hS := (dilationEquiv c hc).toContinuousLinearEquiv.continuous
  have hI := (dilationEquiv c hc).toContinuousLinearEquiv.symm.continuous
  exact hI.comp (rotate_continuous.comp (continuous_fst.prodMk (hS.comp continuous_snd)))

def momentumScale (hbar : ℝ) : ℝ := 2*Real.pi*hbar

theorem momentumScale_ne_zero (hbar : ℝ) (hh : hbar ≠ 0) : momentumScale hbar ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hh

#print axioms dilate_compose
#print axioms dilate_one
#print axioms flow_apply
#print axioms flow_preserves_volume
#print axioms flow_zero
#print axioms flow_compose
#print axioms flow_reverse
#print axioms flow_period
#print axioms flow_clock
#print axioms flow_neutral
#print axioms flow_first_plane
#print axioms flow_second_plane
#print axioms flow_continuous
#print axioms momentumScale_ne_zero

end
end UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
