/- Shifted-form energy identities on the lifted Hamiltonian graph.
They yield resolvent contraction and dissipative bounded approximations. -/
import UnifiedTheory.Audit.KFCausalMassFormOperator
import UnifiedTheory.Audit.KFCausalShiftedForm
import UnifiedTheory.Audit.KFCausalHilbertStateEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalWeightedMassEnergy
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def energy (F : V →L[ℂ] V) (x : V) : ℝ := (inner ℂ x (F x)).re

theorem weighted_symmetric (M Q : V →L[ℂ] V)
    (hM : M.toLinearMap.IsSymmetric) (hQ : Q.toLinearMap.IsSymmetric)
    (a : ℝ) (w v x y : V) (hw : Q w = M v) (hx : Q x = M y) :
    inner ℂ v ((a • M+Q) x) = inner ℂ w ((a • M+Q) y) := by
  have hm (u z : V) : inner ℂ (M u) z = inner ℂ u (M z) := hM u z
  have hq (u z : V) : inner ℂ (Q u) z = inner ℂ u (Q z) := hQ u z
  have h₁ : inner ℂ v (M x) = inner ℂ w (M y) := by
    rw [← hm v x,← hw,hq w x,hx]
  have h₂ : inner ℂ v (Q x) = inner ℂ w (Q y) := by
    rw [hx,← hm v y,← hw,hq w y]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    inner_add_right,inner_smul_right_eq_smul,h₁,h₂]

theorem weighted_diagonal_real (M Q : V →L[ℂ] V)
    (hM : M.toLinearMap.IsSymmetric) (hQ : Q.toLinearMap.IsSymmetric)
    (a : ℝ) (w v : V) (hw : Q w = M v) :
    (inner ℂ w ((a • M+Q) v)).im = 0 := by
  have hm (u z : V) : inner ℂ (M u) z = inner ℂ u (M z) := hM u z
  have hq (u z : V) : inner ℂ (Q u) z = inner ℂ u (Q z) := hQ u z
  have hF : (a • M+Q).toLinearMap.IsSymmetric := by
    intro x y
    simp only [ContinuousLinearMap.coe_coe,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,inner_add_left,inner_add_right,
      inner_smul_left_eq_smul,inner_smul_right_eq_smul,hm x y,hq x y]
  have he := weighted_symmetric M Q hM hQ a w v w v hw hw
  have hc : star (inner ℂ w ((a • M+Q) v)) = inner ℂ w ((a • M+Q) v) := by
    exact (inner_conj_symm (𝕜 := ℂ) ((a • M+Q) v) w).trans ((hF v w).trans he)
  have hi := congrArg Complex.im hc
  simp only [Complex.star_def,Complex.conj_im] at hi
  linarith

theorem energy_real_smul (F : V →L[ℂ] V) (r : ℝ) (x : V) :
    energy F (r • x) = r^2*energy F x := by
  simp only [energy,ContinuousLinearMap.map_smul_of_tower,inner_smul_left_eq_smul,
    inner_smul_right_eq_smul,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem energy_skew_split (F : V →L[ℂ] V) (hF : F.toLinearMap.IsSymmetric)
    (x y : V) (c : ℂ) (hc : c.re = 0) (hxy : (inner ℂ x (F y)).im = 0) (b : ℝ) :
    energy F (b • x-c • y) = b^2*energy F x+Complex.normSq c*energy F y := by
  have hyx : (inner ℂ y (F x)).im = 0 := by
    have he : inner ℂ y (F x) = star (inner ℂ x (F y)) :=
      (hF y x).symm.trans (inner_conj_symm (𝕜 := ℂ) (F y) x).symm
    rw [he]
    change -(inner ℂ x (F y)).im = 0
    rw [hxy,neg_zero]
  simp only [energy,map_sub,ContinuousLinearMap.map_smul_of_tower,map_smul,
    inner_sub_left,inner_sub_right,inner_smul_left_eq_smul,inner_smul_right_eq_smul,
    inner_smul_left]
  simp [Complex.real_smul,Complex.mul_re,Complex.mul_im,
    Complex.normSq_apply,hc,hxy,hyx]
  ring

theorem resolvent_energy_bound (F : V →L[ℂ] V) (hF : F.toLinearMap.IsSymmetric)
    (hpos : ∀ x, 0 ≤ energy F x) (x y : V) (c : ℂ) (hc : c.re = 0)
    (hxy : (inner ℂ x (F y)).im = 0) (b : ℝ) :
    energy F (b • x) ≤ energy F (b • x-c • y) := by
  rw [energy_real_smul,energy_skew_split F hF x y c hc hxy b]
  exact le_add_of_nonneg_right (mul_nonneg (Complex.normSq_nonneg c) (hpos y))

theorem energy_norm_upper (F : V →L[ℂ] V) (x : V) :
    energy F x ≤ ‖F‖*‖x‖^2 := by
  calc
    energy F x ≤ ‖x‖*‖F x‖ := re_inner_le_norm (𝕜 := ℂ) x (F x)
    _ ≤ ‖x‖*(‖F‖*‖x‖) := mul_le_mul_of_nonneg_left (F.le_opNorm x) (norm_nonneg x)
    _ = _ := by ring

theorem energy_norm_comparison (F : V →L[ℂ] V) (d : ℝ) (hd : 0 < d)
    (hco : ∀ z, d*‖z‖^2 ≤ energy F z) (x y : V) (he : energy F x ≤ energy F y) :
    ‖x‖ ≤ Real.sqrt (‖F‖/d)*‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (div_nonneg (norm_nonneg _) hd.le)]
  calc
    ‖x‖^2 = (d*‖x‖^2)/d := by field_simp
    _ ≤ (‖F‖*‖y‖^2)/d := div_le_div_of_nonneg_right
      ((hco x).trans (he.trans (energy_norm_upper F y))) hd.le
    _ = _ := by ring

theorem resolvent_dissipation (F : V →L[ℂ] V) (x y : V) (c : ℂ)
    (hc : c.re = 0) (hxy : (inner ℂ x (F y)).im = 0) (b : ℝ) :
    (inner ℂ (b • x-c • y) (F (b • (c • y)))).re =
      -b*Complex.normSq c*energy F y := by
  simp only [ContinuousLinearMap.map_smul_of_tower,map_smul,inner_sub_left,
    inner_smul_left_eq_smul,inner_smul_right_eq_smul,inner_smul_left]
  simp [energy,Complex.real_smul,Complex.mul_re,Complex.mul_im,
    Complex.normSq_apply,hc,hxy]
  ring

theorem energy_derivative (F : ℝ → V →L[ℂ] V) (D : V →L[ℂ] V)
    (u : ℝ → V) (v : V) (t : ℝ) (hF : (F t).toLinearMap.IsSymmetric)
    (hD : HasDerivAt F D t) (hu : HasDerivAt u v t) :
    HasDerivAt (fun r => energy (F r) (u r))
      (energy D (u t)+2*(inner ℂ (u t) (F t v)).re) t := by
  have hp := hu.inner ℂ (KFCausalHilbertStateEvolution.operator_apply_derivative F u D v t hD hu)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hp
  apply hr.congr_deriv
  change (inner ℂ (u t) (D (u t)+F t v)+inner ℂ v (F t (u t))).re =
    energy D (u t)+2*(inner ℂ (u t) (F t v)).re
  have he : (inner ℂ v (F t (u t))).re = (inner ℂ (u t) (F t v)).re :=
    (inner_re_symm (𝕜 := ℂ) _ _).trans (congrArg Complex.re (hF (u t) v))
  simp only [energy,inner_add_right,Complex.add_re,he]
  ring

#print axioms energy_norm_upper
#print axioms energy_norm_comparison
#print axioms resolvent_dissipation
#print axioms energy_derivative
#print axioms weighted_symmetric
#print axioms weighted_diagonal_real
#print axioms energy_real_smul
#print axioms energy_skew_split
#print axioms resolvent_energy_bound
end
end UnifiedTheory.Audit.KFCausalWeightedMassEnergy
