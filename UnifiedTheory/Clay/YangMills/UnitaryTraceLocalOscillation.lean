/- Local trace oscillation on the full unitary group. A rank-one spectral
phase gives nearby unitary matrices with real trace separated quadratically.
This concerns U(d), not determinant-one subgroups and not a Wilson variance
bound until the local density and Haar-cap estimates are attached. -/
import UnifiedTheory.Clay.YangMills.UnitaryExponentialPlaquette
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Clay.YangMills.UnitaryTraceLocalOscillation
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

variable {d : Type*} [Fintype d] [DecidableEq d]

def vectorSquare (v : d → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

theorem vectorSquare_pos (v : d → ℂ) (hv : v ≠ 0) : 0 < vectorSquare v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hi)⟩

theorem star_dot_self (v : d → ℂ) : star v ⬝ᵥ v = (vectorSquare v : ℂ) := by
  simp only [dotProduct, vectorSquare, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

def projection (v : d → ℂ) : Matrix d d ℂ :=
  (vectorSquare v : ℂ)⁻¹ • vecMulVec v (star v)

theorem projection_star (v : d → ℂ) : star (projection v) = projection v := by
  simp [projection, Matrix.star_eq_conjTranspose, conjTranspose_vecMulVec]

theorem projection_square (v : d → ℂ) (hv : v ≠ 0) :
    projection v * projection v = projection v := by
  have hq : (vectorSquare v : ℂ) ≠ 0 := by exact_mod_cast (vectorSquare_pos v hv).ne'
  simp only [projection, smul_mul_smul_comm, vecMulVec_mul_vecMulVec, star_dot_self,
    vecMulVec_smul, smul_smul]
  congr 1
  field_simp

theorem projection_trace (v : d → ℂ) (hv : v ≠ 0) : trace (projection v) = 1 := by
  have hq : (vectorSquare v : ℂ) ≠ 0 := by exact_mod_cast (vectorSquare_pos v hv).ne'
  rw [projection, trace_smul, trace_vecMulVec, dotProduct_comm, star_dot_self]
  simp [hq]

theorem projection_entry (v : d → ℂ) (hv : v ≠ 0) (i j : d) : ‖projection v i j‖ ≤ 1 := by
  have hq := vectorSquare_pos v hv
  have hi : ‖v i‖ ^ 2 ≤ vectorSquare v :=
    Finset.single_le_sum (fun k _ => sq_nonneg ‖v k‖) (Finset.mem_univ i)
  have hj : ‖v j‖ ^ 2 ≤ vectorSquare v :=
    Finset.single_le_sum (fun k _ => sq_nonneg ‖v k‖) (Finset.mem_univ j)
  have hij : ‖v i‖ * ‖v j‖ ≤ vectorSquare v := by nlinarith [sq_nonneg (‖v i‖ - ‖v j‖)]
  simp only [projection, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, vecMulVec_apply, Pi.star_apply, norm_star]
  calc
    (vectorSquare v)⁻¹ * (‖v i‖ * ‖v j‖) ≤ (vectorSquare v)⁻¹ * vectorSquare v :=
      mul_le_mul_of_nonneg_left hij (inv_nonneg.mpr hq.le)
    _ = 1 := inv_mul_cancel₀ hq.ne'

theorem exists_spectral_projection [Nonempty d] (U : Matrix.unitaryGroup d ℂ) :
    ∃ (ev : ℂ) (P : Matrix d d ℂ), ‖ev‖ = 1 ∧ star P = P ∧ P * P = P ∧
      trace P = 1 ∧ (∀ i j, ‖P i j‖ ≤ 1) ∧ (U : Matrix d d ℂ) * P = ev • P := by
  obtain ⟨ev, hev⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (U : Matrix d d ℂ))
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have he : (U : Matrix d d ℂ) *ᵥ v = ev • v := hv.apply_eq_smul
  have hn : ‖ev‖ = 1 := spectrum.norm_eq_one_of_unitary U.property (by
    simpa only [Matrix.spectrum_toLin'] using hev.mem_spectrum)
  refine ⟨ev, projection v, hn, projection_star v, projection_square v hv.2,
    projection_trace v hv.2, projection_entry v hv.2, ?_⟩
  simp only [projection, mul_smul_comm, mul_vecMulVec, he, smul_vecMulVec, smul_smul]
  congr 1
  ring

def phase (t : ℝ) : ℂ :=
  ⟨(1-t^2)/(1+t^2), 2*t/(1+t^2)⟩

theorem phase_re (t : ℝ) : (phase t).re = (1-t^2)/(1+t^2) := rfl

theorem phase_im (t : ℝ) : (phase t).im = 2*t/(1+t^2) := rfl

theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  have hd : 1+t^2 ≠ 0 := by positivity
  have h : ‖phase t‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, phase_re, phase_im]
    field_simp
    ring
  nlinarith [norm_nonneg (phase t)]

def phaseMatrix (P : Matrix d d ℂ) (z : ℂ) : Matrix d d ℂ := 1 + (z-1) • P

theorem phaseMatrix_unitary (P : Matrix d d ℂ) (hstar : star P = P) (hsq : P*P=P)
    (z : ℂ) (hz : ‖z‖ = 1) : phaseMatrix P z ∈ Matrix.unitaryGroup d ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hzz : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  simp only [phaseMatrix, star_add, star_one, star_smul, hstar, star_sub,
    one_mul, mul_one, add_mul, mul_add, smul_mul_smul_comm, hsq, mul_smul_comm, smul_mul_assoc, one_mul, mul_one]
  have hsc : (z-1) + (star z-1) + (z-1)*(star z-1) = 0 := by linear_combination hzz
  rw [show 1 + (z - 1) • P + (star z - 1) • (P + (z - 1) • P) =
      1 + ((z-1) + (star z-1) + (z-1)*(star z-1)) • P by module, hsc]
  simp

theorem phaseMatrix_trace (U : Matrix.unitaryGroup d ℂ) (P : Matrix d d ℂ)
    (ev : ℂ) (hUP : (U : Matrix d d ℂ)*P=ev • P) (htr : trace P = 1) (z : ℂ) :
    trace ((U : Matrix d d ℂ)*phaseMatrix P z)-trace (U : Matrix d d ℂ) = (z-1)*ev := by
  simp [phaseMatrix, mul_add, mul_smul_comm, hUP, trace_add, trace_smul, htr, mul_comm]


theorem phase_close (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖phase t - 1‖ ≤ 4*t := by
  have hd : 0 < 1+t^2 := by positivity
  have hr : (phase t-1).re = -2*t^2/(1+t^2) := by
    rw [Complex.sub_re, Complex.one_re, phase_re]
    field_simp
    ring
  have hi : (phase t-1).im = 2*t/(1+t^2) := by simp only [Complex.sub_im, Complex.one_im, sub_zero, phase_im]
  calc
    ‖phase t-1‖ ≤ |(phase t-1).re| + |(phase t-1).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = (2*t^2+2*t)/(1+t^2) := by
      rw [hr, hi, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg t]) hd.le),
        abs_of_nonneg (by positivity : 0 ≤ 2*t/(1+t^2))]
      ring
    _ ≤ 4*t := (div_le_iff₀ hd).mpr (by nlinarith [sq_nonneg t, mul_nonneg ht (sq_nonneg t)])

theorem phase_separation (ev : ℂ) (hev : ‖ev‖ = 1) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    t^2/2 ≤ |((phase t-1)*ev).re| ∨ t^2/2 ≤ |((phase (-t)-1)*ev).re| := by
  let p := ((phase t-1)*ev).re
  let q := ((phase (-t)-1)*ev).re
  have hd : 0 < 1+t^2 := by positivity
  have hsum : (1+t^2)*(p+q) = -4*t^2*ev.re := by
    dsimp [p, q]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero, phase_re, phase_im, neg_sq]
    field_simp
    ring
  have hdiff : (1+t^2)*(p-q) = -4*t*ev.im := by
    dsimp [p, q]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero, phase_re, phase_im, neg_sq]
    field_simp
    ring
  by_contra h
  push_neg at h
  change |p| < t^2/2 ∧ |q| < t^2/2 at h
  have habs : |p|+|q| < t^2 := by linarith [h.1,h.2]
  have hs : |p+q| < t^2 := (abs_add_le _ _).trans_lt habs
  have hdif : |p-q| < t^2 := (abs_sub _ _).trans_lt habs
  have hr0 : 4*t^2*|ev.re| = (1+t^2)*|p+q| := by
    have hh := congrArg abs hsum
    simpa only [abs_mul, abs_of_pos hd, abs_pow, sq_abs, abs_neg, show |(4 : ℝ)| = 4 by norm_num] using hh.symm
  have hi0 : 4*t*|ev.im| = (1+t^2)*|p-q| := by
    have hh := congrArg abs hdiff
    simpa only [abs_mul, abs_of_pos hd, abs_of_pos ht, abs_neg, show |(4 : ℝ)| = 4 by norm_num] using hh.symm
  have hr : 4*|ev.re| < 1+t^2 := by
    have hh := mul_lt_mul_of_pos_left hs hd
    rw [← hr0] at hh
    exact (mul_lt_mul_iff_right₀ (sq_pos_of_pos ht)).mp (by nlinarith [hh])
  have hi : 4*|ev.im| < (1+t^2)*t := by
    have hh := mul_lt_mul_of_pos_left hdif hd
    rw [← hi0] at hh
    exact (mul_lt_mul_iff_right₀ ht).mp (by nlinarith [hh])
  have ht2 : t^2 ≤ 1 := by nlinarith
  have hra : |ev.re| < 1/2 := by linarith
  have hia : |ev.im| < 1/2 := by
    have hh := mul_le_mul_of_nonneg_right (show 1+t^2 ≤ 2 by linarith) ht.le
    nlinarith
  have he := Complex.norm_le_abs_re_add_abs_im ev
  rw [hev] at he
  linarith

/-- Uniform quadratic real-trace oscillation, with explicit entrywise closeness.
The construction changes one spectral phase, so it belongs to the full U(d). -/
theorem exists_nearby [Nonempty d] (U : Matrix.unitaryGroup d ℂ)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ V : Matrix.unitaryGroup d ℂ,
      (∀ i j, ‖V i j-U i j‖ ≤ 4*(Fintype.card d : ℝ)*t) ∧
      t^2/2 ≤ |(trace (V : Matrix d d ℂ)).re-(trace (U : Matrix d d ℂ)).re| := by
  obtain ⟨ev, P, hev, hstar, hsq, htr, hP, hUP⟩ := exists_spectral_projection U
  let phaseUnit (s : ℝ) : Matrix.unitaryGroup d ℂ :=
    ⟨phaseMatrix P (phase s), phaseMatrix_unitary P hstar hsq (phase s) (phase_norm s)⟩
  have hclose (s : ℝ) (hs : s = t ∨ s = -t) (i j : d) :
      ‖(phaseUnit s) i j - (1 : Matrix d d ℂ) i j‖ ≤ 4*t := by
    have hphase : ‖phase s-1‖ ≤ 4*t := by
      rcases hs with hs | hs
      · rw [hs]; exact phase_close t ht.le ht1
      · rw [hs]
        have he : phase (-t) = star (phase t) := by
          apply Complex.ext <;> simp [phase, neg_div]
        rw [he, ← star_one, ← star_sub, norm_star]
        exact phase_close t ht.le ht1
    change ‖(1 + (phase s-1) • P) i j-(1 : Matrix d d ℂ) i j‖ ≤ _
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_left, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hP i j) (norm_nonneg _)).trans (by simpa using hphase)
  have hdist (s : ℝ) (hs : s=t ∨ s = -t) (i j : d) :
      ‖(U*phaseUnit s) i j-U i j‖ ≤ 4*(Fintype.card d : ℝ)*t := by
    have he : ((U*phaseUnit s : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) -
        (U : Matrix d d ℂ) =
        (U : Matrix d d ℂ)*((phaseUnit s : Matrix d d ℂ)-1) := by
      simp only [mul_sub, mul_one, UnitaryGroup.mul_val]
    change ‖((((U*phaseUnit s : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) -
      (U : Matrix d d ℂ)) i j)‖ ≤ _
    rw [he]
    have hh := UnitaryEntryEstimates.left_mul_entry U
      ((phaseUnit s : Matrix d d ℂ)-1) (4*t) (hclose s hs) i j
    convert hh using 1 <;> ring
  have htrace (s : ℝ) :
      (trace ((U*phaseUnit s : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ)).re-
        (trace (U : Matrix d d ℂ)).re = ((phase s-1)*ev).re := by
    rw [← Complex.sub_re]
    exact congrArg Complex.re (phaseMatrix_trace U P ev hUP htr (phase s))
  rcases phase_separation ev hev t ht ht1 with hp | hm
  · exact ⟨U*phaseUnit t, hdist t (Or.inl rfl), by simpa only [htrace] using hp⟩
  · exact ⟨U*phaseUnit (-t), hdist (-t) (Or.inr rfl), by simpa only [htrace] using hm⟩

end
end UnifiedTheory.Clay.YangMills.UnitaryTraceLocalOscillation
