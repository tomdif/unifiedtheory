/- Construct all positive shifted inverses from an identified positive
contractive inverse at shift one. Every inverse equation is proved on
the original partial-operator domain. -/
import UnifiedTheory.Audit.KFCausalResolventHamiltonian
import UnifiedTheory.Audit.KFCausalYosidaApproximation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalShiftedResolventFromOne
noncomputable section
open KFCausalCoerciveInverse KFCausalResolventHamiltonian
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def shift (R : H →L[ℂ] H) (a : ℝ) : H →L[ℂ] H := 1+(a-1) • R

theorem shift_apply (R : H →L[ℂ] H) (a : ℝ) (x : H) :
    shift R a x = x+(a-1) • R x := rfl

theorem shift_coercive (R : H →L[ℂ] H) (a : ℝ)
    (hp : ∀ x, 0 ≤ (inner ℂ (R x) x).re) (hc : ∀ x, ‖R x‖ ≤ ‖x‖) (x : H) :
    min 1 a*‖x‖^2 ≤ (inner ℂ (shift R a x) x).re := by
  have hb : (inner ℂ (R x) x).re ≤ ‖x‖^2 :=
    (re_inner_le_norm (𝕜 := ℂ) _ _).trans
      ((mul_le_mul_of_nonneg_right (hc x) (norm_nonneg x)).trans_eq (pow_two _).symm)
  have he : (inner ℂ (shift R a x) x).re = ‖x‖^2+(a-1)*(inner ℂ (R x) x).re := by
    rw [shift_apply,inner_add_left,inner_smul_left_eq_smul,KFCausalShiftedForm.complex_inner_square]
    simp only [Complex.add_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
  rw [he]
  by_cases ha : 1 ≤ a
  · rw [min_eq_left ha,one_mul]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr ha) (hp x))
  · rw [min_eq_right (le_of_not_ge ha)]
    nlinarith [mul_nonneg (show 0 ≤ 1-a by linarith) (sub_nonneg.mpr hb)]

theorem shift_symmetric (R : H →L[ℂ] H) (a : ℝ) (hs : R.toLinearMap.IsSymmetric) :
    (shift R a).toLinearMap.IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe,shift_apply,inner_add_left,inner_add_right,
    inner_smul_left_eq_smul,inner_smul_right_eq_smul]
  exact congrArg (fun z : ℂ => inner ℂ x y+(a-1) • z) (hs x y)

theorem shift_isUnit [CompleteSpace H] (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hp : ∀ x, 0 ≤ (inner ℂ (R x) x).re) (hc : ∀ x, ‖R x‖ ≤ ‖x‖)
    (hs : R.toLinearMap.IsSymmetric) : IsUnit (shift R a) :=
  coercive_isUnit (shift R a) (min 1 a) (lt_min zero_lt_one ha)
    (shift_coercive R a hp hc) (shift_symmetric R a hs)

def resolvent (R : H →L[ℂ] H) (a : ℝ) : H →L[ℂ] H := R.comp (Ring.inverse (shift R a))

def point (R : H →L[ℂ] H) (hi : Function.Injective R) (a : ℝ) (f : H) :
    (inverseShift R hi).domain := rangeVector R hi (Ring.inverse (shift R a) f)

theorem point_coe (R : H →L[ℂ] H) (hi : Function.Injective R) (a : ℝ) (f : H) :
    (point R hi a f : H) = resolvent R a f := rfl

private theorem shift_algebra (a : ℝ) (x y : H) :
    x-y+a • y = x+(a-1) • y := by rw [sub_smul,one_smul]; abel

theorem right_inverse (R : H →L[ℂ] H) (hi : Function.Injective R) (a : ℝ)
    (hu : IsUnit (shift R a)) (f : H) :
    inverseShift R hi (point R hi a f)+a • resolvent R a f=f := by
  change inverseShift R hi (rangeVector R hi (Ring.inverse (shift R a) f))+
    a • R (Ring.inverse (shift R a) f)=f
  rw [inverseShift_apply_range,shift_algebra]
  exact inverse_apply_right (shift R a) hu f

theorem left_inverse (R : H →L[ℂ] H) (hi : Function.Injective R) (a : ℝ)
    (hu : IsUnit (shift R a)) (x : (inverseShift R hi).domain) :
    resolvent R a (inverseShift R hi x+a • (x:H))=x := by
  have he : shift R a (inverseShift R hi x+(x:H)) = inverseShift R hi x+a • (x:H) := by
    rw [shift_apply,inverseShift_resolvent,sub_smul,one_smul]
    abel
  change R (Ring.inverse (shift R a) (inverseShift R hi x+a • (x:H)))=(x:H)
  rw [← he,inverse_apply_left (shift R a) hu]
  exact inverseShift_resolvent R hi x

theorem resolves (R : H →L[ℂ] H) (hi : Function.Injective R) (a : ℝ)
    (hu : IsUnit (shift R a)) :
    KFCausalPositiveResolventBounds.Resolves (inverseShift R hi) (resolvent R a) a := by
  intro f
  refine ⟨(point R hi a f).property,?_⟩
  exact eq_sub_iff_add_eq.mpr (right_inverse R hi a hu f)

private theorem inverse_commutes (F L : H →L[ℂ] H) (hu : IsUnit F) (hc : L*F=F*L) :
    Ring.inverse F*L=L*Ring.inverse F := by
  calc
    _ = (Ring.inverse F*L)*(F*Ring.inverse F) := by rw [Ring.mul_inverse_cancel F hu,mul_one]
    _ = Ring.inverse F*(L*F)*Ring.inverse F := by simp only [mul_assoc]
    _ = Ring.inverse F*(F*L)*Ring.inverse F := by rw [hc]
    _ = _ := by rw [← mul_assoc,Ring.inverse_mul_cancel F hu,one_mul]

theorem resolvent_commutes_one (R : H →L[ℂ] H) (a : ℝ) (hu : IsUnit (shift R a)) :
    resolvent R a*R=R*resolvent R a := by
  have hc : R*shift R a=shift R a*R := by
    ext x
    simp only [ContinuousLinearMap.mul_apply,shift_apply,map_add,ContinuousLinearMap.map_smul_of_tower]
  change (R*Ring.inverse (shift R a))*R=R*(R*Ring.inverse (shift R a))
  rw [mul_assoc,inverse_commutes _ _ hu hc]

theorem resolvents_commute (R : H →L[ℂ] H) (a b : ℝ)
    (ha : IsUnit (shift R a)) (hb : IsUnit (shift R b)) :
    resolvent R a*resolvent R b=resolvent R b*resolvent R a := by
  have hFa : R*shift R a=shift R a*R := by
    ext x
    simp only [ContinuousLinearMap.mul_apply,shift_apply,map_add,ContinuousLinearMap.map_smul_of_tower]
  have hFb : R*shift R b=shift R b*R := by
    ext x
    simp only [ContinuousLinearMap.mul_apply,shift_apply,map_add,ContinuousLinearMap.map_smul_of_tower]
  have hRia : Commute R (Ring.inverse (shift R a)) := (inverse_commutes _ _ ha hFa).symm
  have hRib : Commute R (Ring.inverse (shift R b)) := (inverse_commutes _ _ hb hFb).symm
  have hFab : Commute (shift R a) (shift R b) := by
    ext x
    simp only [ContinuousLinearMap.mul_apply,shift_apply,map_add,ContinuousLinearMap.map_smul_of_tower]
    module
  have hii := hFab.ringInverse_ringInverse
  exact ((Commute.refl R).mul_right hRib).mul_left (hRia.symm.mul_right hii)

#print axioms shift_apply
#print axioms shift_coercive
#print axioms shift_symmetric
#print axioms shift_isUnit
#print axioms point_coe
#print axioms right_inverse
#print axioms left_inverse
#print axioms resolves
#print axioms resolvent_commutes_one
#print axioms resolvents_commute
end
end UnifiedTheory.Audit.KFCausalShiftedResolventFromOne
