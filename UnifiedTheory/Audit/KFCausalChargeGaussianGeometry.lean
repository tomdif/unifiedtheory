/- The invariant Gaussian radius for the actual frequency-normalized
standing rotation, and the hbar-dependent physical oscillator width. -/
import UnifiedTheory.Audit.KFCausalMixedCircleAction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedRotation
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow

def radius (c : ℝ) (x : Joint 2 4) : ℝ :=
  ‖dilate c x‖^2-(x (.inr 0))^2-(x (.inr 3))^2

theorem radius_coordinates (c : ℝ) (x : Joint 2 4) :
    radius c x = c^2*((x (.inl 0))^2+(x (.inl 1))^2)+
      (x (.inr 1))^2+(x (.inr 2))^2 := by
  simp [radius,EuclideanSpace.norm_sq_eq,Fintype.sum_sum_type,Fin.sum_univ_succ,
    dilate,Real.norm_eq_abs,sq_abs]
  ring

theorem dilate_flow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Joint 2 4) :
    dilate c (flowEquiv c hc θ x) = rotate θ (dilate c x) := by
  rw [flow_apply,dilate_compose,mul_inv_cancel₀ hc,dilate_one]

theorem radius_flow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Joint 2 4) :
    radius c (flowEquiv c hc θ x) = radius c x := by
  have hn : ‖rotate θ (dilate c x)‖ = ‖dilate c x‖ := (rotationIsometry θ).norm_map _
  simp only [radius,dilate_flow,flow_clock,flow_neutral,hn]

def profile (α β c : ℝ) (g : ℝ → ℂ) (x : Joint 2 4) : ℂ :=
  g (x (.inr 0))*Complex.exp (-((α*radius c x+β*(x (.inr 3))^2:ℝ):ℂ))

theorem profile_flow (α β c : ℝ) (hc : c ≠ 0) (g : ℝ → ℂ) (θ : ℝ) (x : Joint 2 4) :
    profile α β c g (flowEquiv c hc θ x) = profile α β c g x := by
  simp only [profile,flow_clock,radius_flow,flow_neutral]

theorem action_fixed_of_profile (α β c : ℝ) (hc : c ≠ 0) (g : ℝ → ℂ) (d : ℂ)
    (f : JointHilbert 2 4) (hf : f =ᵐ[volume] fun x => d*profile α β c g x) (θ : ℝ) :
    KFCausalMixedCircleAction.action c hc θ f = f := by
  apply Lp.ext
  filter_upwards [KFCausalMixedCircleAction.action_coe c hc θ f,
    (flow_preserves_volume c hc θ).quasiMeasurePreserving.ae hf,hf] with x hx hy hz
  simp only [Function.comp_apply] at hx
  rw [hx,hy,profile_flow,hz]

def groundWidth (hbar : ℝ) : ℝ := 1/(2*|hbar|)

theorem groundWidth_positive (hbar : ℝ) (hh : hbar ≠ 0) : 0 < groundWidth hbar := by
  have hp := abs_pos.mpr hh
  unfold groundWidth
  positivity

theorem groundWidth_matching (hbar : ℝ) (hh : hbar ≠ 0) :
    Real.pi^2/groundWidth hbar = groundWidth hbar*(momentumScale hbar)^2 := by
  have hn := abs_ne_zero.mpr hh
  unfold groundWidth momentumScale
  rw [show (2*Real.pi*hbar)^2 = 4*Real.pi^2*hbar^2 by ring,← sq_abs hbar]
  field_simp
  ring

#print axioms radius_coordinates
#print axioms dilate_flow
#print axioms radius_flow
#print axioms profile_flow
#print axioms action_fixed_of_profile
#print axioms groundWidth_positive
#print axioms groundWidth_matching

end
end UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
