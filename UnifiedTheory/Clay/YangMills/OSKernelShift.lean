/- A reflected-kernel shift with bounded orbits constructs contractions on the
actual null quotient and Hilbert completion. Its hypotheses are kernel/test
identities and coefficient bounds, not an assumed contraction or Hamiltonian. -/
import UnifiedTheory.Clay.YangMills.OSBoundedOrbitContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSKernelShift
noncomputable section
open PositiveKernelForm KernelHilbertCompletion
open scoped NNReal BigOperators

variable {ι : Type*} (K : PositiveKernel ι)

structure ShiftData where
  shift : ℝ≥0 → ι → ι
  zero : ∀ i, shift 0 i = i
  add : ∀ s t i, shift s (shift t i) = shift (s+t) i
  symmetric : ∀ t i j, K.value (shift t i, j) = K.value (i, shift t j)
  bound : ι → ℝ
  bound_nonneg : ∀ i, 0 ≤ bound i
  kernel_bound : ∀ t i j, ‖K.value (shift t i, shift t j)‖ ≤ bound i * bound j

variable (S : ShiftData K)

def formal (t : ℝ≥0) : Formal K →ₗ[ℂ] Formal K :=
  Finsupp.linearCombination ℂ (fun i => basisState K (S.shift t i))

@[simp] theorem formal_single (t : ℝ≥0) (i : ι) (c : ℂ) :
    formal K S t (Finsupp.single i c) = Finsupp.single (S.shift t i) c := by
  change Finsupp.linearCombination ℂ (fun i => basisState K (S.shift t i)) _ = _
  rw [Finsupp.linearCombination_single]
  change (c • (Finsupp.single (S.shift t i) (1 : ℂ) : ι →₀ ℂ)) = _
  simp

@[simp] theorem formal_zero (x : Formal K) : formal K S 0 x = x := by
  classical
  induction x using Finsupp.induction with
  | zero => exact map_zero _
  | @single_add i c x hi hc ih => simp only [map_add, formal_single, S.zero, ih]

theorem formal_add (s t : ℝ≥0) (x : Formal K) :
    formal K S s (formal K S t x) = formal K S (s+t) x := by
  classical
  induction x using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add i c x hi hc ih => simp only [map_add, formal_single, S.add, ih]

theorem formal_inner (s t : ℝ≥0) (x y : Formal K) :
    inner ℂ (formal K S s x) (formal K S t y) =
      x.sum (fun i a => y.sum (fun j b => star a * b * K.value (S.shift s i, S.shift t j))) := by
  classical
  change inner ℂ (x.sum (fun i a => a • basisState K (S.shift s i)))
    (y.sum (fun j b => b • basisState K (S.shift t j))) = _
  simp only [Finsupp.sum, sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : inner ℂ (basisState K (S.shift s i)) (basisState K (S.shift t j)) =
      K.value (S.shift s i, S.shift t j) := by
    change rawForm K (Finsupp.single _ 1) (Finsupp.single _ 1) = _
    simp
  rw [he]
  simp only [Complex.star_def]
  ring

theorem formal_symmetric (t : ℝ≥0) (x y : Formal K) :
    inner ℂ (formal K S t x) y = inner ℂ x (formal K S t y) := by
  have h₁ := formal_inner K S t 0 x y
  have h₂ := formal_inner K S 0 t x y
  simp only [formal_zero, S.zero, S.symmetric] at h₁ h₂
  exact h₁.trans h₂.symm

theorem formal_orbit_bounded (x : Formal K) :
    BddAbove (Set.range (fun t => ‖formal K S t x‖)) := by
  classical
  let C := ∑ i ∈ x.support, ∑ j ∈ x.support,
    ‖star (Finsupp.toFun x i) * Finsupp.toFun x j‖ * (S.bound i * S.bound j)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (norm_nonneg _) (mul_nonneg (S.bound_nonneg i) (S.bound_nonneg j))))
  refine ⟨Real.sqrt C, ?_⟩
  rintro _ ⟨t, rfl⟩
  have he : ‖formal K S t x‖ ^ 2 ≤ C := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    change (inner ℂ (formal K S t x) (formal K S t x)).re ≤ C
    apply (Complex.re_le_norm _).trans
    rw [formal_inner]
    change ‖∑ i ∈ x.support, ∑ j ∈ x.support,
      star (Finsupp.toFun x i) * Finsupp.toFun x j * K.value (S.shift t i, S.shift t j)‖ ≤ C
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (S.kernel_bound t i j) (norm_nonneg _)
  nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C, norm_nonneg (formal K S t x)]

theorem formal_contraction (t : ℝ≥0) (x : Formal K) : ‖formal K S t x‖ ≤ ‖x‖ :=
  OSBoundedOrbitContraction.norm_le (formal K S) (formal_add K S) (formal_symmetric K S)
    (formal_orbit_bounded K S) t x

/-- This is derived null-space descent, not an assumption on the shift. -/
theorem formal_null (t : ℝ≥0) (x : Formal K) (hx : embed K x = 0) :
    embed K (formal K S t x) = 0 := by
  apply norm_eq_zero.mp
  change ‖(KernelHilbertRealization.embedIsometry K) (formal K S t x)‖ = 0
  rw [(KernelHilbertRealization.embedIsometry K).norm_map]
  have hn : ‖x‖ = 0 := by
    have he : ‖embed K x‖ = ‖x‖ := (KernelHilbertRealization.embedIsometry K).norm_map x
    rw [hx, norm_zero] at he
    exact he.symm
  exact le_antisymm (by simpa only [hn] using formal_contraction K S t x) (norm_nonneg _)

def formalCLM (t : ℝ≥0) : Formal K →L[ℂ] Formal K :=
  (formal K S t).mkContinuous 1 (fun x => by simpa only [one_mul] using formal_contraction K S t x)

def operator (t : ℝ≥0) : Hilbert K →L[ℂ] Hilbert K :=
  ((embed K).comp (formalCLM K S t)).extend (embed K)

@[simp] theorem operator_embed (t : ℝ≥0) (x : Formal K) :
    operator K S t (embed K x) = embed K (formal K S t x) :=
  ContinuousLinearMap.extend_eq _ (denseRange_embed K)
    (KernelHilbertRealization.embedIsometry K).isometry.isUniformInducing x

theorem operator_contraction (t : ℝ≥0) (v : Hilbert K) : ‖operator K S t v‖ ≤ ‖v‖ := by
  refine (denseRange_embed K).induction_on v
    (isClosed_le (operator K S t).continuous.norm continuous_norm) ?_
  intro x
  rw [operator_embed]
  change ‖(KernelHilbertRealization.embedIsometry K) (formal K S t x)‖ ≤
    ‖(KernelHilbertRealization.embedIsometry K) x‖
  simpa only [LinearIsometry.norm_map] using formal_contraction K S t x

@[simp] theorem operator_zero (v : Hilbert K) : operator K S 0 v = v := by
  refine (denseRange_embed K).induction_on v
    (isClosed_eq (operator K S 0).continuous continuous_id) ?_
  intro x
  rw [operator_embed, formal_zero]

theorem operator_add (s t : ℝ≥0) (v : Hilbert K) :
    operator K S s (operator K S t v) = operator K S (s+t) v := by
  refine (denseRange_embed K).induction_on v
    (isClosed_eq ((operator K S s).continuous.comp (operator K S t).continuous)
      (operator K S (s+t)).continuous) ?_
  intro x
  rw [operator_embed, operator_embed, operator_embed, formal_add]

@[simp] theorem operator_canonical (t : ℝ≥0) (i : ι) :
    operator K S t (canonical K i) = canonical K (S.shift t i) := by
  change operator K S t (embed K (Finsupp.single i 1)) = _
  rw [operator_embed, formal_single]
  rfl

end
end UnifiedTheory.Clay.YangMills.OSKernelShift
