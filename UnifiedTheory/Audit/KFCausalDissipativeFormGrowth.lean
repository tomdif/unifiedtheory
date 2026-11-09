/- A shifted energy form has a cutoff-independent forward growth bound
for any strong trajectory of a dissipative bounded generator. -/
import UnifiedTheory.Audit.KFCausalWeightedMassEnergy
import UnifiedTheory.Audit.KFCausalSplitTargetShiftedForm
import UnifiedTheory.Audit.KFCausalSchrodingerEnergyEstimate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDissipativeFormGrowth
noncomputable section
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
variable {V H K : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem shifted_form_derivative_bound (J : V →L[ℂ] H) (A B : V →L[ℂ] K)
    (a t : ℝ) (ha : 0 ≤ a) (x : V) :
    energy ((2*Real.exp (2*t)) • gram B) x ≤
      2*energy (KFCausalSplitTargetShiftedForm.shiftForm J A B a t) x := by
  have he : energy (KFCausalSplitTargetShiftedForm.shiftForm J A B a t) x =
      a*‖J x‖^2+(‖A x‖^2+Real.exp (2*t)*‖B x‖^2) :=
    (inner_re_symm (𝕜 := ℂ) x _).trans
      (KFCausalSplitTargetShiftedForm.shiftForm_diagonal J A B a t x)
  have hd : energy ((2*Real.exp (2*t)) • gram B) x = 2*Real.exp (2*t)*‖B x‖^2 := by
    change (inner ℂ x ((2*Real.exp (2*t)) • B.adjoint (B x))).re = _
    rw [inner_smul_right_eq_smul,B.adjoint_inner_right,
      KFCausalShiftedForm.complex_inner_square]
    simp only [Complex.real_smul,← Complex.ofReal_mul,Complex.ofReal_re]
  rw [he,hd]
  have hp := mul_nonneg ha (sq_nonneg ‖J x‖)
  nlinarith [sq_nonneg ‖A x‖]

theorem growth_bound (E D : ℝ → ℝ) (hd : ∀ t, HasDerivAt E (D t) t)
    (hb : ∀ t, D t ≤ 2*E t) (s t : ℝ) (hst : s ≤ t) :
    E t ≤ Real.exp (2*(t-s))*E s := by
  have hw : ∀ x, HasDerivAt (fun r => Real.exp (-2*r)*E r)
      (Real.exp (-2*x)*(D x-2*E x)) x := by
    intro x
    have he := (Real.hasDerivAt_exp (-2*x)).comp x ((hasDerivAt_id x).const_mul (-2))
    convert he.mul (hd x) using 1
    simp only [Function.comp_apply]
    ring
  have hm : Antitone (fun r => Real.exp (-2*r)*E r) :=
    antitone_of_hasDerivAt_nonpos hw (fun x => mul_nonpos_of_nonneg_of_nonpos
      (Real.exp_pos _).le (sub_nonpos.mpr (hb x)))
  have hh := mul_le_mul_of_nonneg_left (hm hst) (Real.exp_pos (2*t)).le
  have hself : Real.exp (2*t)*Real.exp (-2*t) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  have hshift : Real.exp (2*t)*Real.exp (-2*s) = Real.exp (2*(t-s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [← mul_assoc,hself,one_mul,hshift] using hh

omit [CompleteSpace V] in
theorem dissipative_growth (F D A : ℝ → V →L[ℂ] V)
    (hF : ∀ t, (F t).toLinearMap.IsSymmetric) (hD : ∀ t, HasDerivAt F (D t) t)
    (hb : ∀ t x, energy (D t) x ≤ 2*energy (F t) x)
    (ha : ∀ t x, (inner ℂ x (F t (A t x))).re ≤ 0)
    (u : ℝ → V) (hu : ∀ t, HasDerivAt u (A t (u t)) t)
    (s t : ℝ) (hst : s ≤ t) :
    energy (F t) (u t) ≤ Real.exp (2*(t-s))*energy (F s) (u s) := by
  apply growth_bound (fun t => energy (F t) (u t))
    (fun t => energy (D t) (u t)+2*(inner ℂ (u t) (F t (A t (u t)))).re)
    (fun t => energy_derivative F (D t) u (A t (u t)) t (hF t) (hD t) (hu t)) _ s t hst
  intro t
  linarith [hb t (u t),ha t (u t)]

#print axioms shifted_form_derivative_bound
#print axioms growth_bound
#print axioms dissipative_growth
end
end UnifiedTheory.Audit.KFCausalDissipativeFormGrowth
