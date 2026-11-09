/- Exact square completion of the charged-neutral diffusion after the
neutral integral. The quartic logarithmic-curvature term is retained
with its charged Y weight; it is not replaced by a uniform energy bound. -/
import UnifiedTheory.Audit.KFCausalJointFourierDissipationMixedBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointFourierDissipationMixedSquare
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalNeutralLineDomain
open KFCausalQuarticPlaneDomination (potential)
open KFCausalQuarticNeutralDefect
open KFCausalNeutralQuarticBoundary
open KFCausalNeutralQuarticFormBound (energy second energy_nonnegative)
open KFCausalNeutralQuarticTransportForms (acceleration)
open KFCausalJointFourierDissipationMixedBoundary

def curvature (f : ℝ → ℂ) : ℝ := ∫ x, logCurvature x*‖f x‖^2

def reducedDensity (u v Y η L x : ℝ) (f g k C Cg : ℂ) : ℝ :=
  Y*(4*(u^2+v^2)*potential x*‖C‖^2+
    v*mixed η L x f g C Cg+acceleration η L x f g k/4)

theorem curvature_integrable (f : ℝ → ℂ) (hf : Regular f) :
    Integrable (fun x => logCurvature x*‖f x‖^2) := by
  have he (x : ℝ) : logCurvature x*‖f x‖^2 =
      potentialSecond x*‖f x‖^2-4*(potential x*‖(connection x:ℂ)*f x‖^2) := by
    have hs := square_completion 0 1 x (f x) 0
    norm_num [secondDensity,boundaryDensity,direction] at hs
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    linarith
  simp_rw [he]
  exact (weight_norm_integrable f hf 2).sub
    ((weight_norm_integrable _ (connection_regular f hf) 0).const_mul 4)

theorem curvature_lower (f : ℝ → ℂ) (hf : Regular f) :
    -4*energy f ≤ curvature f := by
  have h := integral_mono ((weight_norm_integrable f hf 0).const_mul (-4))
    (curvature_integrable f hf) (fun x =>
      by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (logCurvature_lower x) (sq_nonneg ‖f x‖))
  simpa only [integral_const_mul,curvature,energy] using h

theorem second_exact_square (η L : ℝ) (f g : ℝ → ℂ)
    (hf : Regular f) (hg : Regular g) (hd : ∀ x, HasDerivAt f (g x) x) :
    second η L f g =
      4*energy (fun x => direction η L x (f x) (g x))+(L^2+η^2)*curvature f := by
  have hiS := second_integrable η L f g hf hg
  have hiB := (boundary_integrable f g hf hg).const_mul (2*η^2)
  have hiK := (weight_norm_integrable _ (direction_regular η L f g hf hg) 0).const_mul 4
  have hiC := (curvature_integrable f hf).const_mul (L^2+η^2)
  have he := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall
    (fun x => square_completion η L x (f x) (g x)))
  have hiKB : Integrable (fun x => 4*potential x*‖direction η L x (f x) (g x)‖^2) := by
    simpa only [mul_assoc] using hiK
  have hiCC : Integrable (fun x => (L^2+η^2)*logCurvature x*‖f x‖^2) := by
    simpa only [mul_assoc] using hiC
  rw [integral_add hiS hiB,integral_add hiKB hiCC,integral_const_mul,
    boundary_integral f g hf hg hd,mul_zero,add_zero] at he
  simp_rw [mul_assoc] at he
  rw [integral_const_mul,integral_const_mul] at he
  exact he

theorem acceleration_integrable (η L : ℝ) (f g k : ℝ → ℂ)
    (hf : Regular f) (hg : Regular g) (hk : Regular k) :
    Integrable (fun x => acceleration η L x (f x) (g x) (k x)) := by
  simp_rw [KFCausalNeutralQuarticTransportForms.acceleration_expansion]
  exact (((weight_norm_integrable g hg 0).const_mul (2*(L^2+η^2))).add
    ((weight_re_integrable f k hf hk 0).const_mul (2*(L^2-η^2)))).add
    ((weight_im_integrable f k hf hk 0).const_mul (4*L*η))

theorem acceleration_exact_square (η L : ℝ) (f g k : ℝ → ℂ)
    (hf : Regular f) (hg : Regular g) (hk : Regular k)
    (hd : ∀ x, HasDerivAt f (g x) x) (he : ∀ x, HasDerivAt g (k x) x) :
    (∫ x, acceleration η L x (f x) (g x) (k x)) =
      4*energy (fun x => direction η L x (f x) (g x))+(L^2+η^2)*curvature f := by
  rw [KFCausalNeutralQuarticTransportForms.acceleration_integral η L f g k hf hg hk hd he]
  exact second_exact_square η L f g hf hg hd

theorem energy_add_exact (v : ℝ) (K C : ℝ → ℂ) (hK : Regular K) (hC : Regular C) :
    energy (fun x => K x+(2*(v:ℂ))*C x) =
      energy K+4*v^2*energy C+4*v*(∫ x, potential x*(conj (K x)*C x).re) := by
  have he (x : ℝ) : potential x*‖K x+(2*(v:ℂ))*C x‖^2 =
      potential x*‖K x‖^2+4*v^2*(potential x*‖C x‖^2)+
        4*v*(potential x*(conj (K x)*C x).re) := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_ofNat,Complex.im_ofNat,Complex.conj_re,Complex.conj_im]
    ring
  unfold energy
  simp_rw [he]
  have h0 : Integrable (fun x => potential x*‖K x‖^2) := weight_norm_integrable K hK 0
  have h1 : Integrable (fun x => 4*v^2*(potential x*‖C x‖^2)) :=
    (weight_norm_integrable C hC 0).const_mul (4*v^2)
  have h2 : Integrable (fun x => 4*v*(potential x*(conj (K x)*C x).re)) :=
    (weight_re_integrable K C hK hC 0).const_mul (4*v)
  have hs := integral_add (h0.add h1) h2
  simp only [Pi.add_apply] at hs
  rw [hs,integral_add h0 h1,integral_const_mul,integral_const_mul]

theorem reducedDensity_integrable (u v Y η L : ℝ) (f g k C Cg : ℝ → ℂ)
    (hf : Regular f) (hg : Regular g) (hk : Regular k) (hC : Regular C) (hCg : Regular Cg) :
    Integrable (fun x => reducedDensity u v Y η L x (f x) (g x) (k x) (C x) (Cg x)) := by
  have h0 := (weight_norm_integrable C hC 0).const_mul (4*(u^2+v^2))
  have h1 := (mixed_integrable η L f g C Cg hf hg hC hCg).const_mul v
  have h2 := (acceleration_integrable η L f g k hf hg hk).div_const 4
  simpa only [reducedDensity,mul_assoc] using ((h0.add h1).add h2).const_mul Y

theorem complete_mixed_square (u v Y η L : ℝ) (f g k C Cg : ℝ → ℂ)
    (hf : Regular f) (hg : Regular g) (hk : Regular k) (hC : Regular C) (hCg : Regular Cg)
    (hdf : ∀ x, HasDerivAt f (g x) x) (hdg : ∀ x, HasDerivAt g (k x) x)
    (hdC : ∀ x, HasDerivAt C (Cg x) x) :
    (∫ x, reducedDensity u v Y η L x (f x) (g x) (k x) (C x) (Cg x)) =
      Y*(energy (fun x => direction η L x (f x) (g x)+(2*(v:ℂ))*C x)+
        4*u^2*energy C+(L^2+η^2)/4*curvature f) := by
  have h0 : Integrable (fun x => 4*(u^2+v^2)*potential x*‖C x‖^2) := by
    convert (weight_norm_integrable C hC 0).const_mul (4*(u^2+v^2)) using 1
    funext x
    change 4*(u^2+v^2)*potential x*‖C x‖^2 = 4*(u^2+v^2)*(potential x*‖C x‖^2)
    ring
  have h1 := (mixed_integrable η L f g C Cg hf hg hC hCg).const_mul v
  have h2 := (acceleration_integrable η L f g k hf hg hk).div_const 4
  have hs := integral_add (h0.add h1) h2
  simp only [Pi.add_apply] at hs
  unfold reducedDensity
  rw [integral_const_mul,hs,integral_add h0 h1,
    integral_const_mul,integral_div,mixed_integral η L f g C Cg hf hg hC hCg hdf hdC,
    acceleration_exact_square η L f g k hf hg hk hdf hdg,
    energy_add_exact v _ C (direction_regular η L f g hf hg) hC]
  simp only [completedMixed,mul_assoc,integral_const_mul]
  unfold energy
  ring

theorem complete_mixed_lower (u v Y η L : ℝ) (hY : 0 ≤ Y) (f g k C Cg : ℝ → ℂ)
    (hf : Regular f) (hg : Regular g) (hk : Regular k) (hC : Regular C) (hCg : Regular Cg)
    (hdf : ∀ x, HasDerivAt f (g x) x) (hdg : ∀ x, HasDerivAt g (k x) x)
    (hdC : ∀ x, HasDerivAt C (Cg x) x) :
    -(L^2+η^2)*Y*energy f ≤
      ∫ x, reducedDensity u v Y η L x (f x) (g x) (k x) (C x) (Cg x) := by
  rw [complete_mixed_square u v Y η L f g k C Cg hf hg hk hC hCg hdf hdg hdC]
  have hc := mul_le_mul_of_nonneg_left (curvature_lower f hf)
    (show 0 ≤ (L^2+η^2)/4 by positivity)
  have h0 := energy_nonnegative (fun x => direction η L x (f x) (g x)+(2*(v:ℂ))*C x)
  have h1 : 0 ≤ 4*u^2*energy C := mul_nonneg (by positivity) (energy_nonnegative C)
  have h := mul_le_mul_of_nonneg_left (show -(L^2+η^2)*energy f ≤
      energy (fun x => direction η L x (f x) (g x)+(2*(v:ℂ))*C x)+
        4*u^2*energy C+(L^2+η^2)/4*curvature f by nlinarith) hY
  nlinarith

#print axioms curvature_integrable
#print axioms curvature_lower
#print axioms second_exact_square
#print axioms acceleration_integrable
#print axioms acceleration_exact_square
#print axioms energy_add_exact
#print axioms reducedDensity_integrable
#print axioms complete_mixed_square
#print axioms complete_mixed_lower
end
end UnifiedTheory.Audit.KFCausalJointFourierDissipationMixedSquare
