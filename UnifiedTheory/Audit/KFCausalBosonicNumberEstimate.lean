/- The mode annihilation energy identity and number bound are derived from
the actual occupation operators. This is the core estimate needed before
comparison with the energy of the actual second-quantized Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalBosonicCCR

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalBosonicNumberEstimate
noncomputable section
open scoped BigOperators
open KFCausalBosonicOccupationSpace KFCausalBosonicCCR
variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq _

def diagonal (w : Occupation ι → ℝ) : Core ι →ₗ[ℂ] Core ι :=
  Finsupp.lsum ℂ (fun n => (w n : ℂ) • Finsupp.lsingle n)

theorem diagonal_single (w : Occupation ι → ℝ) (n : Occupation ι) (c : ℂ) :
    diagonal w (Finsupp.single n c) = Finsupp.single n ((w n : ℂ)*c) := by
  simp [diagonal, Finsupp.lsum_single, Finsupp.smul_single, smul_eq_mul]

theorem diagonal_apply (w : Occupation ι → ℝ) (u : Core ι) (n : Occupation ι) :
    diagonal w u n = (w n : ℂ)*u n := by
  have he : (Finsupp.lapply n).comp (diagonal w) =
      (w n : ℂ) • (Finsupp.lapply n : Core ι →ₗ[ℂ] ℂ) := by
    apply Finsupp.lhom_ext
    intro m c
    by_cases hm : m = n
    · subst m
      simp [diagonal_single]
    · simp [diagonal_single, Finsupp.single_apply, hm]
  exact congrArg (fun T : Core ι →ₗ[ℂ] ℂ => T u) he

theorem core_inner (u v : Core ι) :
    inner ℂ (embed u) (embed v) = ∑ n ∈ u.support, inner ℂ (u n) (v n) := by
  rw [lp.inner_eq_tsum]
  simp only [embed_apply]
  exact tsum_eq_sum (fun n hn => by simp [Finsupp.notMem_support_iff.mp hn])

def energy (w : Occupation ι → ℝ) (u : Core ι) : ℝ :=
  ∑ n ∈ u.support, w n * ‖u n‖^2

theorem diagonal_energy (w : Occupation ι → ℝ) (u : Core ι) :
    (inner ℂ (embed u) (embed (diagonal w u))).re = energy w u := by
  rw [core_inner]
  simp only [energy, Complex.re_sum, diagonal_apply]
  apply Finset.sum_congr rfl
  intro n _
  change (inner ℂ (u n) ((w n : ℂ) • u n)).re = _
  rw [inner_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact congrArg (fun r : ℝ => w n*r) (inner_self_eq_norm_sq (𝕜 := ℂ) (u n))

theorem creation_annihilation_number (i : ι) (u : Core ι) :
    creation i (annihilation i u) = diagonal (fun n => (n i : ℝ)) u := by
  have he : (creation i).comp (annihilation i) = diagonal (fun n => (n i : ℝ)) := by
    apply Finsupp.lhom_ext
    intro n c
    simp only [LinearMap.comp_apply, annihilation_single, creation_single, diagonal_single]
    by_cases hn : n i = 0
    · simp [hn]
    · have hl : lower i n i + 1 = n i := by simp [lower]; omega
      rw [raise_lower i n hn, hl, ← mul_assoc, amplitude_square]
      norm_cast
  exact congrArg (fun T : Core ι →ₗ[ℂ] Core ι => T u) he

theorem annihilation_energy (i : ι) (u : Core ι) :
    ‖embed (annihilation i u)‖^2 = energy (fun n => (n i : ℝ)) u := by
  have ha := creation_annihilation_adjoint i (annihilation i u) u
  rw [creation_annihilation_number] at ha
  calc
    _ = (inner ℂ (embed (diagonal (fun n => (n i : ℝ)) u)) (embed u)).re := by
      rw [ha]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) (embed (annihilation i u))).symm
    _ = (inner ℂ (embed u) (embed (diagonal (fun n => (n i : ℝ)) u))).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    _ = _ := diagonal_energy _ u

def particleCount (n : Occupation ι) : ℕ := n.sum (fun _ k => k)

theorem mode_le_particleCount (i : ι) (n : Occupation ι) : n i ≤ particleCount n := by
  classical
  by_cases hi : i ∈ n.support
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  · simp only [Finsupp.notMem_support_iff.mp hi]
    exact Nat.zero_le _

def numberEnergy (u : Core ι) : ℝ := energy (fun n => (particleCount n : ℝ)) u

theorem annihilation_number_bound (i : ι) (u : Core ι) :
    ‖embed (annihilation i u)‖^2 ≤ numberEnergy u := by
  rw [annihilation_energy]
  apply Finset.sum_le_sum
  intro n _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  change (n i : ℝ) ≤ (particleCount n : ℝ)
  exact_mod_cast mode_le_particleCount i n

end
end UnifiedTheory.Audit.KFCausalBosonicNumberEstimate
