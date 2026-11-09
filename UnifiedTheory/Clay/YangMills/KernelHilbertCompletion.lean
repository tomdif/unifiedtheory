/- Actual Hilbert reconstruction of a positive Gram kernel: finitely supported
linear combinations, quotient by zero-norm states, then completion. This is
Kolmogorov/kernel reconstruction, not full OS or quantum-field reconstruction. -/
import UnifiedTheory.Clay.YangMills.PositiveKernelForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.KernelHilbertCompletion
noncomputable section
open PositiveKernelForm
open scoped BigOperators

variable {ι : Type*}

/-- A type synonym keeps each kernel's seminorm separate. -/
def Formal (_K : PositiveKernel ι) := ι →₀ ℂ

variable (K : PositiveKernel ι)

instance formalAddCommGroup : AddCommGroup (Formal K) := inferInstanceAs (AddCommGroup (ι →₀ ℂ))
instance formalModule : Module ℂ (Formal K) := inferInstanceAs (Module ℂ (ι →₀ ℂ))
instance formalCore : PreInnerProductSpace.Core ℂ (Formal K) := preInnerCore K
instance formalSeminormed : SeminormedAddCommGroup (Formal K) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
instance formalInnerProductSpace : InnerProductSpace ℂ (Formal K) :=
  InnerProductSpace.ofCore (formalCore K)

abbrev NullQuotient := SeparationQuotient (Formal K)
abbrev Hilbert := UniformSpace.Completion (NullQuotient K)

def quotientMap : Formal K →L[ℂ] NullQuotient K := SeparationQuotient.mkCLM ℂ (Formal K)

def embed : Formal K →L[ℂ] Hilbert K :=
  (UniformSpace.Completion.toComplL : NullQuotient K →L[ℂ] Hilbert K).comp (quotientMap K)

@[simp] theorem inner_quotient (x y : Formal K) :
    inner ℂ (quotientMap K x) (quotientMap K y) = rawForm K x y := rfl

@[simp] theorem inner_embed (x y : Formal K) :
    inner ℂ (embed K x) (embed K y) = rawForm K x y := by
  change inner ℂ ((quotientMap K x : NullQuotient K) : Hilbert K)
    ((quotientMap K y : NullQuotient K) : Hilbert K) = _
  rw [UniformSpace.Completion.inner_coe, inner_quotient]

/-- The quotient removes precisely the null vectors of the kernel form. -/
theorem quotient_eq_zero_iff (x : Formal K) :
    quotientMap K x = 0 ↔ rawForm K x x = 0 := by
  rw [← inner_quotient]
  exact (inner_self_eq_zero (𝕜 := ℂ)).symm

theorem embed_eq_zero_iff (x : Formal K) :
    embed K x = 0 ↔ rawForm K x x = 0 := by
  rw [← inner_embed]
  exact (inner_self_eq_zero (𝕜 := ℂ)).symm

theorem denseRange_embed : DenseRange (embed K) :=
  UniformSpace.Completion.denseRange_coe.comp
    (SeparationQuotient.surjective_mk.denseRange)
    (UniformSpace.Completion.continuous_coe (NullQuotient K))

def basisState (i : ι) : Formal K := Finsupp.single i 1
def canonical (i : ι) : Hilbert K := embed K (basisState K i)

@[simp] theorem canonical_inner (i j : ι) :
    inner ℂ (canonical K i) (canonical K j) = K.value (i, j) := by
  simp [canonical, basisState]

theorem canonical_norm_sq (i : ι) : ‖canonical K i‖ ^ 2 = (K.value (i, i)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), canonical_inner]
  rfl

theorem embed_mem_canonical_span (x : Formal K) :
    embed K x ∈ Submodule.span ℂ (Set.range (canonical K)) := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add i c x hi hc ih =>
    rw [map_add]
    apply Submodule.add_mem _ _ ih
    have hs : (Finsupp.single i c : Formal K) = c • basisState K i := by
      change Finsupp.single i c = c • Finsupp.single i (1 : ℂ)
      simp
    rw [hs, map_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)

/-- Canonical kernel vectors have genuinely dense linear span in the completion. -/
theorem dense_canonical_span :
    Dense (Submodule.span ℂ (Set.range (canonical K)) : Set (Hilbert K)) :=
  (denseRange_embed K).mono (by
    rintro _ ⟨x, rfl⟩
    exact embed_mem_canonical_span K x)

def vacuum (unitIndex : ι) : Hilbert K := canonical K unitIndex

theorem vacuum_norm (unitIndex : ι) (hunit : K.value (unitIndex, unitIndex) = 1) :
    ‖vacuum K unitIndex‖ = 1 := by
  have h := canonical_norm_sq K unitIndex
  rw [hunit] at h
  have hn := norm_nonneg (canonical K unitIndex)
  change ‖canonical K unitIndex‖ = 1
  norm_num only [Complex.one_re] at h
  nlinarith

theorem vacuum_ne_zero (unitIndex : ι) (hunit : K.value (unitIndex, unitIndex) = 1) :
    vacuum K unitIndex ≠ 0 := by
  intro hzero
  have h := vacuum_norm K unitIndex hunit
  rw [hzero, norm_zero] at h
  norm_num at h

/-- Connected variance expressed directly in the limiting Gram kernel. -/
def connectedVariance (unitIndex i : ι) : ℝ :=
  (K.value (i, i) - K.value (i, unitIndex) * K.value (unitIndex, i)).re

def centered (unitIndex i : ι) : Hilbert K :=
  canonical K i - K.value (unitIndex, i) • vacuum K unitIndex

theorem centered_orthogonal (unitIndex i : ι)
    (hunit : K.value (unitIndex, unitIndex) = 1) :
    inner ℂ (vacuum K unitIndex) (centered K unitIndex i) = 0 := by
  simp only [centered, vacuum, inner_sub_right, inner_smul_right, canonical_inner,
    hunit, mul_one, sub_self]

theorem centered_norm_sq (unitIndex i : ι)
    (hunit : K.value (unitIndex, unitIndex) = 1) :
    ‖centered K unitIndex i‖ ^ 2 = connectedVariance K unitIndex i := by
  have hinner : inner ℂ (centered K unitIndex i) (centered K unitIndex i) =
      K.value (i, i) - K.value (i, unitIndex) * K.value (unitIndex, i) := by
    unfold centered vacuum
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left,
      inner_smul_left, inner_smul_right, inner_smul_right]
    simp only [canonical_inner, hunit, mul_one]
    rw [← kernel_hermitian K i unitIndex]
    ring
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
  rfl

theorem connectedVariance_nonneg (unitIndex i : ι)
    (hunit : K.value (unitIndex, unitIndex) = 1) : 0 ≤ connectedVariance K unitIndex i := by
  rw [← centered_norm_sq K unitIndex i hunit]
  positivity

theorem centered_ne_zero_of_variance_pos (unitIndex i : ι)
    (hunit : K.value (unitIndex, unitIndex) = 1)
    (hvar : 0 < connectedVariance K unitIndex i) : centered K unitIndex i ≠ 0 := by
  intro hz
  have h := centered_norm_sq K unitIndex i hunit
  rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  linarith

/-- Positive connected variance gives a canonical state outside the vacuum line. -/
theorem canonical_not_vacuum_span (unitIndex i : ι)
    (hunit : K.value (unitIndex, unitIndex) = 1)
    (hvar : 0 < connectedVariance K unitIndex i) :
    canonical K i ∉ Submodule.span ℂ ({vacuum K unitIndex} : Set (Hilbert K)) := by
  rintro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hcoeff : K.value (unitIndex, i) = c := by
    have hi := congrArg (fun v : Hilbert K => inner ℂ (vacuum K unitIndex) v) hc
    simpa only [vacuum, inner_smul_right, canonical_inner, hunit, mul_one] using hi.symm
  apply centered_ne_zero_of_variance_pos K unitIndex i hunit hvar
  unfold centered
  rw [hcoeff, hc]
  exact sub_self _

end
end UnifiedTheory.Clay.YangMills.KernelHilbertCompletion
