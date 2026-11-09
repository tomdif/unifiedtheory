/- A kernel shift needs only subexponential coefficient growth. Reflection
symmetry and the semigroup law derive contraction, then supply the bounded
shift data consumed by the existing actual quotient/completion construction. -/
import UnifiedTheory.Clay.YangMills.OSSubexponentialContraction
import UnifiedTheory.Clay.YangMills.OSKernelShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSDampedKernelShift
noncomputable section
open Filter PositiveKernelForm KernelHilbertCompletion
open scoped Topology NNReal BigOperators

variable {ι : Type*} (K : PositiveKernel ι)

structure ShiftAlgebra where
  shift : ℝ≥0 → ι → ι
  zero : ∀ i, shift 0 i = i
  add : ∀ s t i, shift s (shift t i) = shift (s+t) i
  symmetric : ∀ t i j, K.value (shift t i,j) = K.value (i,shift t j)

variable (S : ShiftAlgebra K)

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
      x.sum (fun i a => y.sum (fun j b => star a*b*K.value (S.shift s i,S.shift t j))) := by
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
      K.value (S.shift s i,S.shift t j) := by
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

def DampedDecay : Prop := ∀ (eps : ℝ), 0 < eps → ∀ i j,
  Tendsto (fun t : ℝ≥0 => (Real.exp (-eps*(t:ℝ)) : ℂ) *
    K.value (S.shift t i,S.shift t j)) atTop (𝓝 0)

theorem damped_norm_sq_tendsto (hg : DampedDecay K S) (x : Formal K)
    (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun t : ℝ≥0 => Real.exp (-eps*(t:ℝ)) * ‖formal K S t x‖^2)
      atTop (𝓝 0) := by
  classical
  have hsum : Tendsto (fun t : ℝ≥0 =>
      ∑ i ∈ x.support, ∑ j ∈ x.support,
        (star (Finsupp.toFun x i)*Finsupp.toFun x j) *
          ((Real.exp (-eps*(t:ℝ)) : ℂ)*K.value (S.shift t i,S.shift t j))) atTop (𝓝 0) := by
    simpa only [mul_zero, Finset.sum_const_zero] using
      tendsto_finset_sum x.support (fun i _ => tendsto_finset_sum x.support
        (fun j _ => (hg eps heps i j).const_mul
          (star (Finsupp.toFun x i)*Finsupp.toFun x j)))
  have he (t : ℝ≥0) :
      (Real.exp (-eps*(t:ℝ)) : ℂ)*inner ℂ (formal K S t x) (formal K S t x) =
      ∑ i ∈ x.support, ∑ j ∈ x.support,
        (star (Finsupp.toFun x i)*Finsupp.toFun x j) *
          ((Real.exp (-eps*(t:ℝ)) : ℂ)*K.value (S.shift t i,S.shift t j)) := by
    rw [formal_inner]
    simp only [Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (Real.exp (-eps*(t:ℝ)) : ℂ) *
      (star (Finsupp.toFun x i)*Finsupp.toFun x j*K.value (S.shift t i,S.shift t j)) = _
    ring
  simp_rw [← he] at hsum
  have hr := (Complex.continuous_re.tendsto 0).comp hsum
  simpa only [Function.comp_def, norm_sq_eq_re_inner (𝕜 := ℂ), Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] using hr

/-- Contraction is a theorem of positive-kernel algebra and Schwartz-type
growth; it is not a hypothesis on the quotient dynamics. -/
theorem formal_contraction (hg : DampedDecay K S) (t : ℝ≥0) (x : Formal K) :
    ‖formal K S t x‖ ≤ ‖x‖ := by
  have hd (s : ℝ≥0) : (‖formal K S s x‖^2)^2 ≤ ‖x‖^2 * ‖formal K S (s+s) x‖^2 := by
    have he : ‖formal K S s x‖^2 ≤ ‖x‖*‖formal K S (s+s) x‖ := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), formal_symmetric, formal_add]
      exact re_inner_le_norm _ _
    have hh := pow_le_pow_left₀ (sq_nonneg ‖formal K S s x‖) he 2
    simpa only [mul_pow] using hh
  have h := OSSubexponentialContraction.subexponential_doubling
    (fun s => ‖formal K S s x‖^2) (‖x‖^2) (sq_nonneg _) (fun s => sq_nonneg _)
    hd (fun eps heps => damped_norm_sq_tendsto K S hg x eps heps) t
  nlinarith [norm_nonneg x, norm_nonneg (formal K S t x)]

theorem kernel_bound (hg : DampedDecay K S) (t : ℝ≥0) (i j : ι) :
    ‖K.value (S.shift t i,S.shift t j)‖ ≤ ‖basisState K i‖*‖basisState K j‖ := by
  have he : K.value (S.shift t i,S.shift t j) =
      inner ℂ (formal K S t (basisState K i)) (formal K S t (basisState K j)) := by
    simp only [basisState, formal_single]
    change _ = rawForm K (Finsupp.single _ 1) (Finsupp.single _ 1)
    simp
  rw [he]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul
    (formal_contraction K S hg t _) (formal_contraction K S hg t _)
    (norm_nonneg _) (norm_nonneg _))

/-- The old completion machinery now receives a derived kernel bound. -/
def boundedData (hg : DampedDecay K S) : OSKernelShift.ShiftData K where
  shift := S.shift
  zero := S.zero
  add := S.add
  symmetric := S.symmetric
  bound i := ‖basisState K i‖
  bound_nonneg _ := norm_nonneg _
  kernel_bound := kernel_bound K S hg

end
end UnifiedTheory.Clay.YangMills.OSDampedKernelShift
