/- The OS contraction mechanism: symmetry, the semigroup identity and bounded
positive-time orbits imply contraction. Neither contraction nor null-space
descent is an input. The application must prove the orbit bound and identities. -/
import UnifiedTheory.Clay.YangMills.KernelHilbertRealization
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSBoundedOrbitContraction
noncomputable section
open scoped NNReal

/-- A bounded nonnegative function with the doubling Cauchy--Schwarz inequality
cannot exceed its base norm. A supremum argument replaces repeated squaring. -/
theorem bounded_doubling {T : Type*} [Nonempty T] (f : T → ℝ) (next : T → T)
    (r : ℝ) (hr : 0 ≤ r) (hf : ∀ t, 0 ≤ f t) (hb : BddAbove (Set.range f))
    (hd : ∀ t, f t ^ 2 ≤ r * f (next t)) : ∀ t, f t ≤ r := by
  let M := sSup (Set.range f)
  have hm (t : T) : f t ≤ M := le_csSup hb ⟨t, rfl⟩
  have hM : 0 ≤ M := (hf (Classical.arbitrary T)).trans (hm _)
  have hs : ∀ t, f t ≤ Real.sqrt (r * M) := by
    intro t
    have he := (hd t).trans (mul_le_mul_of_nonneg_left (hm (next t)) hr)
    nlinarith [Real.sq_sqrt (mul_nonneg hr hM), Real.sqrt_nonneg (r * M)]
  have hMs : M ≤ Real.sqrt (r * M) := csSup_le (Set.range_nonempty f) (by
    rintro _ ⟨t, rfl⟩
    exact hs t)
  have hMr : M ≤ r := by
    nlinarith [Real.sq_sqrt (mul_nonneg hr hM), Real.sqrt_nonneg (r * M)]
  exact fun t => (hm t).trans hMr

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
  (T : ℝ≥0 → E →ₗ[ℂ] E)
  (hadd : ∀ s t x, T s (T t x) = T (s + t) x)
  (hsym : ∀ t x y, inner ℂ (T t x) y = inner ℂ x (T t y))
  (hbound : ∀ x, BddAbove (Set.range (fun t => ‖T t x‖)))

include hadd hsym hbound in
theorem norm_le (t : ℝ≥0) (x : E) : ‖T t x‖ ≤ ‖x‖ := by
  apply bounded_doubling (fun s => ‖T s x‖) (fun s => s + s) ‖x‖ (norm_nonneg x)
    (fun s => norm_nonneg _) (hbound x) _ t
  intro s
  calc
    ‖T s x‖ ^ 2 = RCLike.re (inner ℂ x (T (s + s) x)) := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), hsym, hadd]
    _ ≤ ‖x‖ * ‖T (s + s) x‖ := re_inner_le_norm _ _

include hadd hsym hbound in
/-- In particular, zero seminorm vectors remain null under every shift. -/
theorem null_preserved (t : ℝ≥0) (x : E) (hx : ‖x‖ = 0) : ‖T t x‖ = 0 :=
  le_antisymm (by simpa only [hx] using norm_le T hadd hsym hbound t x) (norm_nonneg _)

def shiftCLM (t : ℝ≥0) : E →L[ℂ] E :=
  (T t).mkContinuous 1 (fun x => by simpa only [one_mul] using norm_le T hadd hsym hbound t x)

@[simp] theorem shiftCLM_apply (t : ℝ≥0) (x : E) : shiftCLM T hadd hsym hbound t x = T t x := rfl

theorem shiftCLM_norm_le (t : ℝ≥0) : ‖shiftCLM T hadd hsym hbound t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul, shiftCLM_apply] using norm_le T hadd hsym hbound t x

end
end UnifiedTheory.Clay.YangMills.OSBoundedOrbitContraction
