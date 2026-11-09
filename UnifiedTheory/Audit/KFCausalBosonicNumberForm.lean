/- Completed number-energy form domain, realized as the range of
(1+N)^(-1/2). The annihilation map extends continuously from this form
space with its sharp number bound. No eigenbasis for H(t) is assumed. -/
import UnifiedTheory.Audit.KFCausalBosonicBoundedDiagonal

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalBosonicNumberForm
noncomputable section
open KFCausalBosonicOccupationSpace KFCausalBosonicNumberEstimate
open KFCausalBosonicBoundedDiagonal
open scoped BigOperators
variable {ι : Type*}

def weight (n : Occupation ι) : ℝ := (Real.sqrt (1 + (particleCount n : ℝ)))⁻¹

theorem weight_pos (n : Occupation ι) : 0 < weight n := by unfold weight; positivity

theorem weight_bound (n : Occupation ι) : |weight n| ≤ 1 := by
  rw [abs_of_pos (weight_pos n)]
  apply inv_le_one_of_one_le₀
  have hn : (1 : ℝ) ≤ 1+(particleCount n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn

theorem weight_identity (n : Occupation ι) :
    (1 + (particleCount n : ℝ))*(weight n)^2 = 1 := by
  have hn : 0 < 1+(particleCount n : ℝ) := by positivity
  unfold weight
  rw [inv_pow, Real.sq_sqrt hn.le, mul_inv_cancel₀ hn.ne']

def embedding : Fock ι →L[ℂ] Fock ι := multiplier weight

theorem embedding_core (u : Core ι) : embedding (embed u) = embed (diagonal weight u) :=
  multiplier_core weight 1 zero_le_one weight_bound u

theorem embedding_apply (u : Fock ι) (n : Occupation ι) :
    embedding u n = (weight n : ℂ)*u n := multiplier_apply weight 1 zero_le_one weight_bound u n

theorem embedding_contracts (u : Fock ι) : ‖embedding u‖ ≤ ‖u‖ := by
  simpa only [one_mul] using multiplier_bound weight 1 zero_le_one weight_bound u

theorem embedding_injective : Function.Injective (embedding (ι := ι)) := by
  intro u v he
  apply lp.ext
  funext n
  have hn := congrArg (fun f : Fock ι => f n) he
  simp only [embedding_apply] at hn
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (weight_pos n).ne') hn

def liftCore (u : Core ι) : Core ι := diagonal (fun n => (weight n)⁻¹) u

theorem embedding_liftCore (u : Core ι) : embedding (embed (liftCore u)) = embed u := by
  rw [embedding_core]
  congr 1
  ext n
  simp only [liftCore, diagonal_apply, Complex.ofReal_inv, ← mul_assoc]
  rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (weight_pos n).ne'), one_mul]

theorem embedding_dense : DenseRange (embedding (ι := ι)) := by
  intro u
  apply closure_mono (s := Set.range (embed (ι := ι))) _ (core_dense u)
  rintro _ ⟨v, rfl⟩
  exact ⟨embed (liftCore v), embedding_liftCore v⟩

theorem form_domain (u : Fock ι) :
    u ∈ Set.range (embedding (ι := ι)) ↔
      Memℓp (fun n => ((weight n)⁻¹ : ℂ)*u n) 2 := by
  constructor
  · rintro ⟨v, rfl⟩
    have he : (fun n => ((weight n)⁻¹ : ℂ)*embedding v n) = (fun n => v n) := by
      funext n
      rw [embedding_apply, ← mul_assoc,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (weight_pos n).ne'), one_mul]
    rw [he]
    exact v.property
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    apply lp.ext
    funext n
    change embedding (⟨_, h⟩ : Fock ι) n = u n
    rw [embedding_apply]
    change (weight n : ℂ)*(((weight n)⁻¹ : ℂ)*u n) = u n
    rw [← mul_assoc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (weight_pos n).ne'), one_mul]

theorem core_energy_identity (u : Core ι) :
    numberEnergy (diagonal weight u) + ‖embedding (embed u)‖^2 = ‖embed u‖^2 := by
  rw [embedding_core, diagonal_norm_square, core_norm_square]
  unfold numberEnergy
  rw [diagonal_weighted_energy]
  simp only [energy, ← Finset.sum_add_distrib, one_mul]
  apply Finset.sum_congr rfl
  intro n _
  calc
    _ = ((1 + (particleCount n : ℝ))*(weight n)^2)*‖u n‖^2 := by ring
    _ = _ := by rw [weight_identity, one_mul]

def annihilationCore (i : ι) : Core ι →ₗ[ℂ] Fock ι :=
  embed.comp ((annihilation i).comp (diagonal weight))

theorem annihilationCore_square_bound (i : ι) (u : Core ι) :
    ‖annihilationCore i u‖^2 ≤ ‖embed u‖^2 - ‖embedding (embed u)‖^2 := by
  have h := annihilation_number_bound i (diagonal weight u)
  have he := core_energy_identity u
  change ‖embed (annihilation i (diagonal weight u))‖^2 ≤ _
  linarith

theorem annihilationCore_bound (i : ι) (u : Core ι) : ‖annihilationCore i u‖ ≤ ‖embed u‖ := by
  have h := annihilationCore_square_bound i u
  nlinarith [norm_nonneg (annihilationCore i u), norm_nonneg (embed u),
    sq_nonneg ‖embedding (embed u)‖]

def annihilationForm (i : ι) : Fock ι →L[ℂ] Fock ι := (annihilationCore i).extendOfNorm embed

theorem annihilationForm_core (i : ι) (u : Core ι) :
    annihilationForm i (embed u) = annihilationCore i u :=
  LinearMap.extendOfNorm_eq core_dense ⟨1, by simpa using annihilationCore_bound i⟩ u

theorem annihilationForm_square_bound (i : ι) (u : Fock ι) :
    ‖annihilationForm i u‖^2 ≤ ‖u‖^2 - ‖embedding u‖^2 := by
  refine (core_dense (ι := ι)).induction_on u ?_ ?_
  · apply isClosed_le
    · exact (annihilationForm i).continuous.norm.pow 2
    · exact (continuous_norm.pow 2).sub (embedding.continuous.norm.pow 2)
  · intro v
    rw [annihilationForm_core]
    exact annihilationCore_square_bound i v

end
end UnifiedTheory.Audit.KFCausalBosonicNumberForm
