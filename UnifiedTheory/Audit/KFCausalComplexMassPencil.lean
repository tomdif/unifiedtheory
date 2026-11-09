/- The complex mass/form pencil has a constructed inverse. Rotating
its diagonal makes the existing positive shifted form coercivity apply. -/
import UnifiedTheory.Audit.KFCausalAccretiveInverse
import UnifiedTheory.Audit.KFCausalMassFormOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalComplexMassPencil
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def phase (h : ℝ) : ℂ := -Complex.I*((1/h:ℝ):ℂ)
def rotation (h : ℝ) : ℂ := 1-Complex.I*(h:ℂ)
def pencil (M Q : V →L[ℂ] V) (h b : ℝ) : V →L[ℂ] V := b • M-phase h • Q

theorem phase_ne_zero (h : ℝ) (hh : h ≠ 0) : phase h ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr (one_div_ne_zero hh))

theorem phase_real (h : ℝ) : (phase h).re = 0 := by simp [phase]

theorem rotation_ne_zero (h : ℝ) : rotation h ≠ 0 := by
  intro hz
  have he := congrArg Complex.re hz
  simp [rotation] at he

omit [CompleteSpace V] in
theorem rotated_diagonal (M Q : V →L[ℂ] V)
    (hM : M.toLinearMap.IsSymmetric) (hQ : Q.toLinearMap.IsSymmetric)
    (h b : ℝ) (hh : h ≠ 0) (x : V) :
    (inner ℂ ((rotation h • pencil M Q h b) x) x).re =
      (inner ℂ ((b • M+Q) x) x).re := by
  have hm : (inner ℂ (M x) x).im = 0 := hM.im_inner_apply_self x
  have hq : (inner ℂ (Q x) x).im = 0 := hQ.im_inner_apply_self x
  simp only [pencil,rotation,phase,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,inner_sub_left,
    inner_add_left,inner_smul_left,inner_smul_left_eq_smul]
  simp_all [Complex.mul_re,Complex.mul_im,Complex.real_smul]

theorem pencil_isUnit (M Q : V →L[ℂ] V)
    (hM : M.toLinearMap.IsSymmetric) (hQ : Q.toLinearMap.IsSymmetric)
    (h b d : ℝ) (hh : h ≠ 0) (hd : 0 < d)
    (hc : ∀ x, d*‖x‖^2 ≤ (inner ℂ ((b • M+Q) x) x).re) :
    IsUnit (pencil M Q h b) := by
  have hu := KFCausalAccretiveInverse.coercive_isUnit (rotation h • pencil M Q h b) d hd
    (fun x => (hc x).trans_eq (rotated_diagonal M Q hM hQ h b hh x).symm)
  obtain ⟨hi,hs⟩ := ContinuousLinearMap.isUnit_iff_bijective.mp hu
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  constructor
  · intro x y he
    exact hi (congrArg (fun v : V => rotation h • v) he)
  · intro y
    obtain ⟨x,hx⟩ := hs (rotation h • y)
    exact ⟨x,smul_right_injective V (rotation_ne_zero h) hx⟩

#print axioms phase_ne_zero
#print axioms phase_real
#print axioms rotation_ne_zero
#print axioms rotated_diagonal
#print axioms pencil_isUnit
end
end UnifiedTheory.Audit.KFCausalComplexMassPencil
