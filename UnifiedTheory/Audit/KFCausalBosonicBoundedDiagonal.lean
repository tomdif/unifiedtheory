/- Bounded real occupation multipliers obtained by completion of the actual
finite-occupation core. These are used to construct a completed form domain. -/
import UnifiedTheory.Audit.KFCausalBosonicNumberEstimate
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalBosonicBoundedDiagonal
noncomputable section
open KFCausalBosonicOccupationSpace KFCausalBosonicNumberEstimate
open scoped BigOperators
variable {ι : Type*}

theorem diagonal_symmetric (w : Occupation ι → ℝ) (u v : Core ι) :
    inner ℂ (embed (diagonal w u)) (embed v) =
      inner ℂ (embed u) (embed (diagonal w v)) := by
  simp only [lp.inner_eq_tsum, embed_apply, diagonal_apply]
  apply tsum_congr
  intro n
  change inner ℂ ((w n : ℂ) • u n) (v n) = inner ℂ (u n) ((w n : ℂ) • v n)
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

theorem diagonal_comp (w v : Occupation ι → ℝ) (u : Core ι) :
    diagonal w (diagonal v u) = diagonal (fun n => w n*v n) u := by
  ext n
  simp only [diagonal_apply, Complex.ofReal_mul, mul_assoc]

theorem diagonal_one (u : Core ι) : diagonal (fun _ => 1) u = u := by
  ext n
  simp [diagonal_apply]

theorem core_norm_square (u : Core ι) : ‖embed u‖^2 = energy (fun _ => 1) u := by
  have he := diagonal_energy (fun _ => 1) u
  rw [diagonal_one] at he
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (embed u)).symm.trans he

theorem diagonal_norm_square (w : Occupation ι → ℝ) (u : Core ι) :
    ‖embed (diagonal w u)‖^2 = energy (fun n => (w n)^2) u := by
  have he := diagonal_symmetric w u (diagonal w u)
  rw [diagonal_comp] at he
  calc
    _ = (inner ℂ (embed (diagonal w u)) (embed (diagonal w u))).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) (embed (diagonal w u))).symm
    _ = _ := by rw [he, diagonal_energy]; simp only [pow_two]

theorem diagonal_weighted_energy (v w : Occupation ι → ℝ) (u : Core ι) :
    energy v (diagonal w u) = energy (fun n => w n*(v n*w n)) u := by
  rw [← diagonal_energy, diagonal_symmetric, diagonal_comp, diagonal_comp, diagonal_energy]
  simp only [mul_assoc]

theorem diagonal_norm_bound (w : Occupation ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ n, |w n| ≤ C) (u : Core ι) :
    ‖embed (diagonal w u)‖ ≤ C*‖embed u‖ := by
  have he : energy (fun n => (w n)^2) u ≤ C^2*energy (fun _ => 1) u := by
    simp only [energy, Finset.mul_sum, one_mul]
    apply Finset.sum_le_sum
    intro n _
    have hn := sq_le_sq₀ (abs_nonneg (w n)) hC |>.mpr (hw n)
    have hn' : (w n)^2 ≤ C^2 := by simpa only [sq_abs] using hn
    exact mul_le_mul_of_nonneg_right hn' (sq_nonneg _)
  rw [← diagonal_norm_square, ← core_norm_square] at he
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  simpa only [mul_pow] using he

def multiplier (w : Occupation ι → ℝ) : Fock ι →L[ℂ] Fock ι :=
  (embed.comp (diagonal w)).extendOfNorm embed

theorem multiplier_core (w : Occupation ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ n, |w n| ≤ C) (u : Core ι) :
    multiplier w (embed u) = embed (diagonal w u) :=
  LinearMap.extendOfNorm_eq core_dense ⟨C, diagonal_norm_bound w C hC hw⟩ u

theorem multiplier_bound (w : Occupation ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ n, |w n| ≤ C) (u : Fock ι) : ‖multiplier w u‖ ≤ C*‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le core_dense C (diagonal_norm_bound w C hC hw) u

theorem multiplier_apply (w : Occupation ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ n, |w n| ≤ C) (u : Fock ι) (n : Occupation ι) :
    multiplier w u n = (w n : ℂ)*u n := by
  have hev : Continuous (fun f : Fock ι => f n) :=
    (continuous_apply n).comp lp.uniformContinuous_coe.continuous
  refine (core_dense (ι := ι)).induction_on u ?_ ?_
  · exact isClosed_eq (hev.comp (multiplier w).continuous) (continuous_const.mul hev)
  · intro v
    rw [multiplier_core w C hC hw, embed_apply, diagonal_apply, embed_apply]

theorem multiplier_symmetric (w : Occupation ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ n, |w n| ≤ C) : (multiplier w).toLinearMap.IsSymmetric := by
  intro u v
  change inner ℂ (multiplier w u) v = inner ℂ u (multiplier w v)
  simp only [lp.inner_eq_tsum, multiplier_apply w C hC hw]
  apply tsum_congr
  intro n
  change inner ℂ ((w n : ℂ) • u n) (v n) = inner ℂ (u n) ((w n : ℂ) • v n)
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

end
end UnifiedTheory.Audit.KFCausalBosonicBoundedDiagonal
