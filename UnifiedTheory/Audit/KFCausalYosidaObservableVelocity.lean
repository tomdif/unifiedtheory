/- Exact observable pairing through a positive resolvent, and the
corresponding bounded Schrodinger expectation derivative. -/
import UnifiedTheory.Audit.KFCausalYosidaSignedPairing
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalYosidaObservableVelocity
noncomputable section
open UnifiedTheory.Audit.KFCausalPositiveResolventBounds
open UnifiedTheory.Audit.KFCausalYosidaApproximation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def smoothedPoint (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves T R a) (f : H) : T.domain := a • point T R a hr f

theorem smoothedPoint_coe (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves T R a) (f : H) : (smoothedPoint T R a hr f:H) = a • R f := rfl

theorem smoothedPoint_value (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves T R a) (f : H) : T (smoothedPoint T R a hr f) = yosida R a f := by
  change T.toFun (a • point T R a hr f) = _
  rw [T.toFun.map_smul_of_tower]
  change a • T (point T R a hr f) = _
  rw [point_value,smul_sub,yosida_apply]

theorem smoothed_pairing (T : H →ₗ.[ℂ] H) (R M : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves T R a) (hm : ∀ f, (inner ℂ f (M f)).im = 0) (f : H) :
    (inner ℂ (yosida R a f) (M f)).im =
      (inner ℂ (T (smoothedPoint T R a hr f)) (M (smoothedPoint T R a hr f))).im := by
  let u := point T R a hr f
  have hv : T u = f-a • (u:H) := point_value T R a hr f
  have hy : yosida R a f = a • T u := by rw [hv,smul_sub,yosida_apply]; rfl
  have hx : f = T u+a • (u:H) := by rw [hv]; abel
  have hM : M f = M (T u)+a • M (u:H) := by
    conv_lhs => rw [hx]
    rw [map_add,ContinuousLinearMap.map_smul_of_tower]
  rw [smoothedPoint_value,hy,hM,smoothedPoint_coe,ContinuousLinearMap.map_smul_of_tower]
  simp only [inner_add_right,inner_smul_left_eq_smul,inner_smul_right_eq_smul]
  change (a • inner ℂ (T u) (M (T u))+a • (a • inner ℂ (T u) (M (u:H)))).im =
    (a • (a • inner ℂ (T u) (M (u:H)))).im
  simp only [Complex.add_im,Complex.real_smul,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,hm,mul_zero,zero_add]

theorem expectation_derivative (M : H →L[ℂ] H)
    (hm : ∀ x y, inner ℂ (M x) y = inner ℂ x (M y))
    (v : ℝ → H) (w : H) (hbar t : ℝ)
    (hv : HasDerivAt v ((-Complex.I*((1/hbar:ℝ):ℂ)) • w) t) :
    HasDerivAt (fun r => (inner ℂ (v r) (M (v r))).re)
      ((-2/hbar)*(inner ℂ w (M (v t))).im) t := by
  have hd := (M.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have hi := hv.inner ℂ hd
  have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hi
  convert hh using 1
  change (-2/hbar)*(inner ℂ w (M (v t))).im =
    (inner ℂ (v t) (M ((-Complex.I*((1/hbar:ℝ):ℂ)) • w))+
      inner ℂ ((-Complex.I*((1/hbar:ℝ):ℂ)) • w) (M (v t))).re
  rw [map_smul,inner_smul_right,inner_smul_left]
  rw [← hm (v t) w]
  have hs : (inner ℂ (M (v t)) w).im = -(inner ℂ w (M (v t))).im :=
    inner_im_symm (𝕜 := ℂ) _ _
  simp [Complex.mul_re,Complex.mul_im,hs]
  ring

theorem smoothed_energy_le (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 ≤ a)
    (hr : Resolves T R a) (f : H) :
    (inner ℂ (T (smoothedPoint T R a hr f)) (smoothedPoint T R a hr f:H)).re ≤
      (inner ℂ (yosida R a f) f).re := by
  rw [smoothedPoint_value,smoothedPoint_coe]
  have hy : yosida R a f = a • (f-a • R f) := by rw [smul_sub,yosida_apply]
  have hp : 0 ≤ (inner ℂ (yosida R a f) (f-a • R f)).re := by
    rw [hy,inner_smul_left_eq_smul]
    have hs : (inner ℂ (f-a • R f) (f-a • R f)).re = ‖f-a • R f‖^2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) _
    change 0 ≤ (a • inner ℂ (f-a • R f) (f-a • R f)).re
    rw [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hs]
    positivity
  rw [inner_sub_right,Complex.sub_re] at hp
  linarith

#print axioms smoothedPoint_coe
#print axioms smoothedPoint_value
#print axioms smoothed_pairing
#print axioms expectation_derivative
#print axioms smoothed_energy_le

end
end UnifiedTheory.Audit.KFCausalYosidaObservableVelocity
