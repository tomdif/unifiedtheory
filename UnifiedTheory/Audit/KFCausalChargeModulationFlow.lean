/- Modulation parameters for the actual standing-charge rotation.
Using dilated coordinates makes their orbit an ordinary orthogonal
rotation, so the parameter norm is constant around the entire circle. -/
import UnifiedTheory.Audit.KFCausalChargeGaussianGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalChargeModulationFlow
noncomputable section
open UnifiedTheory.Audit.KFCausalPairedRotation
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry

theorem dilate_inner (c : ℝ) (x k : Space) :
    inner ℝ (dilate c x) k = inner ℝ x (dilate c k) := by
  simp only [PiLp.inner_apply,Fintype.sum_sum_type,dilate,
    RCLike.inner_apply,conj_trivial]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rotate_inner_move (θ : ℝ) (x k : Space) :
    inner ℝ (rotate θ x) k = inner ℝ x (rotate (-θ) k) := by
  have h := rotation_inner θ x (rotate (-θ) k)
  change inner ℝ (rotate θ x) (rotate θ (rotate (-θ) k)) = _ at h
  simpa only [rotate_compose,add_neg_cancel,rotate_zero] using h

def parameter (θ : ℝ) (k : Space) : Space := rotate (-θ) k

theorem flow_phase (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x k : Space) :
    inner ℝ (flowEquiv c hc θ x) (dilate c k) =
      inner ℝ x (dilate c (parameter θ k)) := by
  rw [← dilate_inner,dilate_flow,rotate_inner_move,dilate_inner]
  rfl

theorem parameter_norm (θ : ℝ) (k : Space) : ‖parameter θ k‖ = ‖k‖ :=
  (rotationIsometry (-θ)).norm_map k

theorem parameter_zero (k : Space) : parameter 0 k = k := by
  simp only [parameter,neg_zero,rotate_zero]

theorem parameter_compose (θ φ : ℝ) (k : Space) :
    parameter φ (parameter θ k) = parameter (θ+φ) k := by
  simp only [parameter,rotate_compose,neg_add_rev]

theorem parameter_period (θ : ℝ) (k : Space) :
    parameter (θ+2*Real.pi) k = parameter θ k := by
  unfold parameter
  have h := rotate_period (-(θ+2*Real.pi)) k
  simpa only [show -(θ+2*Real.pi)+2*Real.pi = -θ by ring] using h.symm

theorem parameter_continuous : Continuous (fun p : ℝ × Space => parameter p.1 p.2) := by
  unfold parameter
  exact rotate_continuous.comp (f := fun p : ℝ × Space => (-p.1,p.2))
    (show Continuous (fun p : ℝ × Space => (-p.1,p.2)) from
      continuous_fst.neg.prodMk continuous_snd)

#print axioms dilate_inner
#print axioms rotate_inner_move
#print axioms flow_phase
#print axioms parameter_norm
#print axioms parameter_zero
#print axioms parameter_compose
#print axioms parameter_period
#print axioms parameter_continuous

end
end UnifiedTheory.Audit.KFCausalChargeModulationFlow
