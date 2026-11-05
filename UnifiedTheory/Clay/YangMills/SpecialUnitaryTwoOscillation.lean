/- Determinant-one refinement of the local trace perturbation in dimension two.
The two spectral phases are changed inversely, so the perturbation stays in
SU(2). This algebraic oscillation theorem still needs conditional Wilson and
Haar-cap estimates before any variance or continuum claim follows. -/
import UnifiedTheory.Clay.YangMills.UnitaryTraceLocalOscillation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Clay.YangMills.SpecialUnitaryTwoOscillation
noncomputable section
open Matrix UnitaryTraceLocalOscillation

abbrev TwoMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev TwoUnitary := Matrix.unitaryGroup (Fin 2) ℂ

theorem trace_square (P : TwoMatrix) : trace (P*P) = (trace P)^2-2*det P := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.det_fin_two, Fin.sum_univ_two]
  ring

theorem projection_det (P : TwoMatrix) (hsq : P*P=P) (htr : trace P = 1) : det P = 0 := by
  have hh := trace_square P
  rw [hsq,htr] at hh
  linear_combination (1/2 : ℂ)*hh

theorem det_one_add_smul (P : TwoMatrix) (z : ℂ) :
    det (1+z • P) = 1+z*trace P+z^2*det P := by
  simp [Matrix.det_fin_two, Matrix.trace, Fin.sum_univ_two]
  ring

theorem phaseMatrix_det (P : TwoMatrix) (hsq : P*P=P) (htr : trace P = 1) (z : ℂ) :
    det (phaseMatrix P z) = z := by
  rw [phaseMatrix, det_one_add_smul, projection_det P hsq htr, htr]
  ring

theorem cayley_two (U : TwoMatrix) : U*U-(trace U) • U+(det U) • 1=0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace, Matrix.mul_apply, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring

theorem eigen_complement (U : TwoUnitary) (hdet : det (U : TwoMatrix)=1)
    (P : TwoMatrix) (ev : ℂ) (hev : ‖ev‖=1) (htr : trace P=1)
    (hUP : (U : TwoMatrix)*P=ev • P) : trace (U : TwoMatrix)-ev=star ev := by
  have heq := congrArg (fun M : TwoMatrix => trace (M*P)) (cayley_two (U : TwoMatrix))
  have hUP2 : ((U : TwoMatrix)*(U : TwoMatrix))*P=(ev*ev) • P := by
    rw [mul_assoc, hUP, mul_smul_comm, hUP, smul_smul]
  simp only [add_mul, sub_mul, smul_mul_assoc, one_mul, hUP2, hUP, hdet,
    trace_add, trace_sub, trace_smul, htr, smul_smul, mul_one, one_smul,
    zero_mul, trace_zero, smul_eq_mul] at heq
  have hevstar : ev*star ev=1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hev]
    norm_num
  have hne : ev ≠ 0 := by intro h; rw [h, norm_zero] at hev; norm_num at hev
  apply mul_right_cancel₀ hne
  change (trace (U : TwoMatrix)-ev)*ev=star ev*ev
  linear_combination -heq-hevstar

def balanced (P : TwoMatrix) (z : ℂ) : TwoMatrix :=
  phaseMatrix P z * phaseMatrix (1-P) (star z)

theorem complement_square (P : TwoMatrix) (hsq : P*P=P) : (1-P)*(1-P)=1-P := by
  noncomm_ring [hsq]

theorem complement_trace (P : TwoMatrix) (htr : trace P=1) : trace (1-P)=1 := by
  rw [trace_sub, htr]
  norm_num [Matrix.trace, Fin.sum_univ_two]

theorem balanced_unitary (P : TwoMatrix) (hstar : star P=P) (hsq : P*P=P)
    (z : ℂ) (hz : ‖z‖=1) : balanced P z ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem
    (phaseMatrix_unitary P hstar hsq z hz)
    (phaseMatrix_unitary (1-P) (by simp [star_sub,hstar])
      (complement_square P hsq) (star z) (by simpa using hz))

theorem balanced_det (P : TwoMatrix) (hsq : P*P=P) (htr : trace P=1)
    (z : ℂ) (hz : ‖z‖=1) : det (balanced P z)=1 := by
  rw [balanced, det_mul, phaseMatrix_det P hsq htr,
    phaseMatrix_det (1-P) (complement_square P hsq) (complement_trace P htr)]
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

theorem balanced_expand (P : TwoMatrix) (hsq : P*P=P) (z : ℂ) :
    balanced P z=1+(z-1) • P+(star z-1) • (1-P) := by
  have hp : P*(1-P)=0 := by rw [mul_sub,mul_one,hsq,sub_self]
  simp only [balanced,phaseMatrix,add_mul,mul_add,one_mul,mul_one,
    smul_mul_smul_comm,hp,smul_zero]
  module

theorem balanced_trace (U : TwoUnitary) (hdet : det (U : TwoMatrix)=1)
    (P : TwoMatrix) (hsq : P*P=P) (htr : trace P=1)
    (ev : ℂ) (hev : ‖ev‖=1) (hUP : (U : TwoMatrix)*P=ev • P) (z : ℂ) :
    (trace ((U : TwoMatrix)*balanced P z)).re-(trace (U : TwoMatrix)).re =
      2*((z-1)*ev).re := by
  have hcomp := eigen_complement U hdet P ev hev htr hUP
  rw [balanced_expand P hsq z]
  simp only [mul_add,mul_one,mul_smul_comm,mul_sub,hUP,trace_add,trace_sub,trace_smul,
    htr,smul_eq_mul,mul_one]
  rw [← mul_sub, hcomp]
  simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- A genuine determinant-one perturbation: no passage through U(2) outside
SU(2) is needed. This remains a finite-dimensional algebraic estimate. -/
theorem exists_nearby (U : TwoUnitary) (hdet : det (U : TwoMatrix) = 1)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ V : TwoUnitary, det (V : TwoMatrix) = 1 ∧
      (∀ i j, ‖V i j-U i j‖ ≤ 24*t) ∧
      t^2 ≤ |(trace (V : TwoMatrix)).re-(trace (U : TwoMatrix)).re| := by
  obtain ⟨ev,P,hev,hstar,hsq,htr,hP,hUP⟩ := exists_spectral_projection U
  let B (s : ℝ) : TwoUnitary :=
    ⟨balanced P (phase s), balanced_unitary P hstar hsq (phase s) (phase_norm s)⟩
  have hphase (s : ℝ) (hs : s = t ∨ s = -t) : ‖phase s-1‖ ≤ 4*t := by
    rcases hs with hs | hs
    · rw [hs]; exact phase_close t ht.le ht1
    · rw [hs]
      have he : phase (-t) = star (phase t) := by
        apply Complex.ext <;> simp [phase, neg_div]
      rw [he, ← star_one, ← star_sub, norm_star]
      exact phase_close t ht.le ht1
  have hB (s : ℝ) (hs : s = t ∨ s = -t) (i j : Fin 2) :
      ‖(B s) i j-(1 : TwoMatrix) i j‖ ≤ 12*t := by
    have hcomp : ‖(1-P) i j‖ ≤ 2 := by
      exact (norm_sub_le _ _).trans (by
        have hi := UnitaryCharacterObservables.unitary_entry_bound (1 : TwoUnitary) i j
        change ‖(1 : TwoMatrix) i j‖ ≤ 1 at hi
        change ‖(1 : TwoMatrix) i j‖ + ‖P i j‖ ≤ 2
        linarith [hP i j])
    have hz := hphase s hs
    have hzstar : ‖star (phase s)-1‖ ≤ 4*t := by
      calc
        _ = ‖star (phase s-1)‖ := by rw [star_sub, star_one]
        _ = ‖phase s-1‖ := norm_star _
        _ ≤ 4*t := hz
    change ‖(balanced P (phase s)) i j-(1 : TwoMatrix) i j‖ ≤ _
    rw [balanced_expand P hsq]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [show (1 : TwoMatrix) i j + (phase s-1)*P i j +
      (star (phase s)-1)*(1-P) i j-(1 : TwoMatrix) i j =
      (phase s-1)*P i j+(star (phase s)-1)*(1-P) i j by ring]
    calc
      _ ≤ ‖(phase s-1)*P i j‖ + ‖(star (phase s)-1)*(1-P) i j‖ := norm_add_le _ _
      _ = ‖phase s-1‖*‖P i j‖ + ‖star (phase s)-1‖*‖(1-P) i j‖ := by rw [norm_mul,norm_mul]
      _ ≤ (4*t)*1+(4*t)*2 := add_le_add
        (mul_le_mul hz (hP i j) (norm_nonneg _) (by positivity))
        (mul_le_mul hzstar hcomp (norm_nonneg _) (by positivity))
      _ = 12*t := by ring
  have hclose (s : ℝ) (hs : s = t ∨ s = -t) (i j : Fin 2) :
      ‖(U*B s) i j-U i j‖ ≤ 24*t := by
    have he : ((U*B s : TwoUnitary) : TwoMatrix)-(U : TwoMatrix) =
        (U : TwoMatrix)*((B s : TwoMatrix)-1) := by
      simp only [mul_sub, mul_one, UnitaryGroup.mul_val]
    change ‖((((U*B s : TwoUnitary) : TwoMatrix)-(U : TwoMatrix)) i j)‖ ≤ _
    rw [he]
    have hh := UnitaryEntryEstimates.left_mul_entry U ((B s : TwoMatrix)-1) (12*t) (hB s hs) i j
    norm_num at hh
    linarith
  have hd (s : ℝ) : det ((U*B s : TwoUnitary) : TwoMatrix) = 1 := by
    rw [UnitaryGroup.mul_val, det_mul, hdet, one_mul]
    exact balanced_det P hsq htr (phase s) (phase_norm s)
  have htrace (s : ℝ) :
      (trace ((U*B s : TwoUnitary) : TwoMatrix)).re-(trace (U : TwoMatrix)).re =
        2*((phase s-1)*ev).re := balanced_trace U hdet P hsq htr ev hev hUP (phase s)
  rcases phase_separation ev hev t ht ht1 with hp | hm
  · refine ⟨U*B t, hd t, hclose t (Or.inl rfl), ?_⟩
    rw [htrace,abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · refine ⟨U*B (-t), hd (-t), hclose (-t) (Or.inr rfl), ?_⟩
    rw [htrace,abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

end
end UnifiedTheory.Clay.YangMills.SpecialUnitaryTwoOscillation
