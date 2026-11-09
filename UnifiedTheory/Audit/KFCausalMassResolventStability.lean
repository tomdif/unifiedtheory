/- Uniform shifted-form contraction and dissipation for the lifted
Schrodinger resolvent. The bounded generator approximates the imaginary
Hamiltonian generator, rather than the positive Hamiltonian itself. -/
import UnifiedTheory.Audit.KFCausalComplexMassResolvent
import UnifiedTheory.Audit.KFCausalWeightedMassEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMassResolventStability
noncomputable section
open UnifiedTheory.Audit.KFCausalComplexMassPencil
open UnifiedTheory.Audit.KFCausalComplexMassResolvent
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def approximation (M Q : V →L[ℂ] V) (h b : ℝ) : V →L[ℂ] V :=
  b • (b • resolvent M Q h b-1)

theorem shift_symmetric (M Q : V →L[ℂ] V)
    (hM : M.toLinearMap.IsSymmetric) (hQ : Q.toLinearMap.IsSymmetric) (a : ℝ) :
    (a • M+Q).toLinearMap.IsSymmetric := by
  have hm (u z : V) : inner ℂ (M u) z = inner ℂ u (M z) := hM u z
  have hq (u z : V) : inner ℂ (Q u) z = inner ℂ u (Q z) := hQ u z
  intro x y
  simp only [ContinuousLinearMap.coe_coe,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,inner_add_left,inner_add_right,
    inner_smul_left_eq_smul,inner_smul_right_eq_smul,hm x y,hq x y]

theorem energy_contraction (M Q : V →L[ℂ] V)
    (hM : M.toLinearMap.IsSymmetric) (hQ : Q.toLinearMap.IsSymmetric)
    (h b a : ℝ) (hh : h ≠ 0) (hu : IsUnit (pencil M Q h b))
    (hp : ∀ x, 0 ≤ energy (a • M+Q) x) (f : V) :
    energy (a • M+Q) (b • resolvent M Q h b f) ≤ energy (a • M+Q) f := by
  have hxy := weighted_diagonal_real M Q hM hQ a _ _ (output_equation M Q h b hh hu f)
  have hb := resolvent_energy_bound (a • M+Q) (shift_symmetric M Q hM hQ a) hp
    (resolvent M Q h b f) (output M Q h b f) (phase h) (phase_real h) hxy b
  exact hb.trans_eq (congrArg (energy (a • M+Q)) (resolvent_right M Q h b hh f))

theorem scaled_norm_bound (M Q : V →L[ℂ] V)
    (hM : M.toLinearMap.IsSymmetric) (hQ : Q.toLinearMap.IsSymmetric)
    (h b a d : ℝ) (hh : h ≠ 0) (hu : IsUnit (pencil M Q h b)) (hd : 0 < d)
    (hco : ∀ x, d*‖x‖^2 ≤ energy (a • M+Q) x) (f : V) :
    ‖b • resolvent M Q h b f‖ ≤ Real.sqrt (‖a • M+Q‖/d)*‖f‖ :=
  energy_norm_comparison _ d hd hco _ _ (energy_contraction M Q hM hQ h b a hh hu
    (fun x => (mul_nonneg hd.le (sq_nonneg ‖x‖)).trans (hco x)) f)

theorem approximation_action (M Q : V →L[ℂ] V) (h b : ℝ) (hh : h ≠ 0) (f : V) :
    approximation M Q h b f = b • (phase h • output M Q h b f) := by
  have he : phase h • output M Q h b f = b • resolvent M Q h b f-f := by
    rw [output,smul_smul,mul_inv_cancel₀ (phase_ne_zero h hh),one_smul]
  exact congrArg (fun z : V => b • z) he.symm

theorem approximation_dissipation (M Q : V →L[ℂ] V)
    (hM : M.toLinearMap.IsSymmetric) (hQ : Q.toLinearMap.IsSymmetric)
    (h b a : ℝ) (hh : h ≠ 0) (hu : IsUnit (pencil M Q h b)) (f : V) :
    (inner ℂ f ((a • M+Q) (approximation M Q h b f))).re =
      -b*Complex.normSq (phase h)*energy (a • M+Q) (output M Q h b f) := by
  have hxy := weighted_diagonal_real M Q hM hQ a _ _ (output_equation M Q h b hh hu f)
  have he := resolvent_dissipation (a • M+Q) (resolvent M Q h b f)
    (output M Q h b f) (phase h) (phase_real h) hxy b
  rw [resolvent_right M Q h b hh f,← approximation_action M Q h b hh f] at he
  exact he

theorem approximation_nonpositive (M Q : V →L[ℂ] V)
    (hM : M.toLinearMap.IsSymmetric) (hQ : Q.toLinearMap.IsSymmetric)
    (h b a : ℝ) (hh : h ≠ 0) (hb : 0 ≤ b) (hu : IsUnit (pencil M Q h b))
    (hp : ∀ x, 0 ≤ energy (a • M+Q) x) (f : V) :
    (inner ℂ f ((a • M+Q) (approximation M Q h b f))).re ≤ 0 := by
  rw [approximation_dissipation M Q hM hQ h b a hh hu f]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (Complex.normSq_nonneg _)) (hp _)

#print axioms shift_symmetric
#print axioms energy_contraction
#print axioms scaled_norm_bound
#print axioms approximation_action
#print axioms approximation_dissipation
#print axioms approximation_nonpositive
end
end UnifiedTheory.Audit.KFCausalMassResolventStability
