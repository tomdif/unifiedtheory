/- Universal isometric realization of a positive kernel whose canonical
vectors have an explicit Hilbert realization. This extends through the actual
null quotient and completion, rather than merely matching a formal Gram table. -/
import UnifiedTheory.Clay.YangMills.KernelHilbertCompletion
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.KernelHilbertRealization
noncomputable section
open PositiveKernelForm KernelHilbertCompletion CountableCorrelationCompactness
open scoped BigOperators

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An explicitly given vector family supplies a positive kernel. -/
def vectorKernel (v : ι → H) : PositiveKernel ι where
  value p := inner ℂ (v p.1) (v p.2)
  positive := by
    intro n index a
    have he : gramValue (fun i j => (i, j)) (fun p => inner ℂ (v p.1) (v p.2)) n index a =
        inner ℂ (∑ i, a i • v (index i)) (∑ j, a j • v (index j)) := by
      simp only [gramValue, sum_inner]
      simp only [inner_sum, inner_smul_left, inner_smul_right, Complex.star_def]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    constructor
    · exact inner_self_im (𝕜 := ℂ) (∑ i, a i • v (index i))
    · change 0 ≤ RCLike.re (inner ℂ (∑ i, a i • v (index i)) (∑ i, a i • v (index i)))
      exact inner_self_nonneg

variable (K : PositiveKernel ι) (v : ι → H)
  (hv : ∀ i j, inner ℂ (v i) (v j) = K.value (i, j))

def sumMap : Formal K →ₗ[ℂ] H := Finsupp.linearCombination ℂ v

include hv in
theorem sumMap_inner (x y : Formal K) :
    inner ℂ (sumMap K v x) (sumMap K v y) = rawForm K x y := by
  classical
  change inner ℂ (x.sum (fun i a => a • v i)) (y.sum (fun i a => a • v i)) = _
  simp only [Finsupp.sum, sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right, hv, rawForm,
    Finsupp.sum, Complex.star_def]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def sumIsometry : Formal K →ₗᵢ[ℂ] H where
  toLinearMap := sumMap K v
  norm_map' x := by
    have he : ‖sumMap K v x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), sumMap_inner K v hv]
      rfl
    nlinarith [norm_nonneg (sumMap K v x), norm_nonneg x]

def embedIsometry : Formal K →ₗᵢ[ℂ] Hilbert K where
  toLinearMap := (embed K).toLinearMap
  norm_map' x := by
    change ‖embed K x‖ = ‖x‖
    have he : ‖embed K x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), inner_embed]
      rfl
    nlinarith [norm_nonneg (embed K x), norm_nonneg x]

variable [CompleteSpace H]

def realizationCLM : Hilbert K →L[ℂ] H :=
  (sumIsometry K v hv).toContinuousLinearMap.extend (embed K)

theorem realization_embed (x : Formal K) : realizationCLM K v hv (embed K x) = sumMap K v x :=
  ContinuousLinearMap.extend_eq _ (denseRange_embed K) (embedIsometry K).isometry.isUniformInducing x

def realization : Hilbert K →ₗᵢ[ℂ] H where
  toLinearMap := (realizationCLM K v hv).toLinearMap
  norm_map' x := by
    refine (denseRange_embed K).induction_on x
      (isClosed_eq (realizationCLM K v hv).continuous.norm continuous_norm) ?_
    intro y
    change ‖realizationCLM K v hv (embed K y)‖ = ‖embed K y‖
    rw [realization_embed]
    exact ((sumIsometry K v hv).norm_map y).trans ((embedIsometry K).norm_map y).symm

@[simp] theorem realization_canonical (i : ι) : realization K v hv (canonical K i) = v i := by
  change realizationCLM K v hv (embed K (basisState K i)) = v i
  rw [realization_embed]
  change (Finsupp.linearCombination ℂ v) (Finsupp.single i 1) = v i
  rw [Finsupp.linearCombination_single, one_smul]

theorem realization_injective : Function.Injective (realization K v hv) :=
  (realization K v hv).injective

end
end UnifiedTheory.Clay.YangMills.KernelHilbertRealization
