/-
  Supporting finite algebra and load bounds for LOCAL_CAUSAL_CLOCK.md.
  The full operator construction, local readout theorem, continuum
  encoding, and spectral bottleneck have analytic proofs in that note.
-/
import UnifiedTheory.Audit.KFCausalOrderClock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalLocalClock
noncomputable section
open scoped BigOperators

/-- Zero-based version of the event's positive summable constraint weight. -/
def clockWeight (k : ℕ) : ℝ := 1 / (((k : ℝ)+1)*((k : ℝ)+2))

theorem clockWeight_pos (k : ℕ) : 0 < clockWeight k := by
  unfold clockWeight
  positivity

theorem clockWeight_split (k : ℕ) :
    clockWeight k = 1/((k : ℝ)+1)-1/((k : ℝ)+2) := by
  unfold clockWeight
  have h1 : (k : ℝ)+1 ≠ 0 := by positivity
  have h2 : (k : ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring

theorem clockWeight_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, clockWeight k) = 1-1/((n : ℝ)+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, clockWeight_split]
    push_cast
    ring

/-- A wire's cumulative weight stays bounded as its number of events grows. -/
theorem clockWeight_load (n : ℕ) :
    (∑ k ∈ Finset.range n, clockWeight k) ≤ 1 := by
  rw [clockWeight_sum]
  have h : 0 ≤ 1/((n : ℝ)+1) := by positivity
  linarith

theorem incoming_guard_kills_violation (a b : ℝ) (ha : a^2 = a) :
    (1-a)*b*a = 0 := by
  calc
    (1-a)*b*a = b*(a-a^2) := by ring
    _ = 0 := by rw [ha]; ring

theorem outgoing_guard_kills_violation (a b : ℝ) (hb : b^2 = b) :
    (1-a)*b*(1-b) = 0 := by
  calc
    (1-a)*b*(1-b) = (1-a)*(b-b^2) := by ring
    _ = 0 := by rw [hb]; ring

/-- A positive clock penalty excludes illegal zero modes. -/
theorem illegal_energy_lower_bound (J violations propagation : ℝ)
    (hJ : 0 ≤ J) (hv : 1 ≤ violations) (hp : 0 ≤ propagation) :
    J ≤ J*violations+propagation := by nlinarith

theorem propagation_support_bound (pre post work s : ℕ)
    (hp : pre ≤ s) (hs : post ≤ s) (hw : work ≤ s) :
    1+pre+post+work ≤ 1+3*s := by omega

/-- Positive weights change the spectrum, but leave the constraint kernel. -/
theorem weighted_history_zero_iff {E H : Type*} [Fintype E]
    [NormedAddCommGroup H] (w : E → ℝ) (r : E → H) (hw : ∀ e, 0 < w e) :
    (∑ e, w e * ‖r e‖^2) = 0 ↔ ∀ e, r e = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun e _ => mul_nonneg (le_of_lt (hw e)) (sq_nonneg ‖r e‖))]
  simp only [Finset.mem_univ, forall_true_left]
  constructor
  · intro h e
    have he := (mul_eq_zero.mp (h e)).resolve_left (ne_of_gt (hw e))
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)
  · intro h e
    simp [h e]

/-- Complementary unitary updates leave a commuting local observable fixed. -/
theorem local_observable_unchanged {R : Type*} [Monoid R]
    (U Uinv A : R) (hunit : Uinv*U = 1) (hcomm : Commute A U) :
    Uinv*A*U = A := by
  calc
    Uinv*A*U = Uinv*(A*U) := mul_assoc _ _ _
    _ = Uinv*(U*A) := by rw [hcomm.eq]
    _ = A := by rw [← mul_assoc, hunit, one_mul]

/-- Mixing over unread spectator clocks preserves a common expectation. -/
theorem local_readout_mixture {E : Type*} [Fintype E]
    (p : E → ℝ) (value : ℝ) (hp : ∑ e, p e = 1) :
    (∑ e, p e * value) = value := by
  rw [← Finset.sum_mul, hp, one_mul]

/-- The chosen tick refinement defeats the extensive product-error factor. -/
theorem clock_continuum_product_scale (sites C a : ℝ) (ha : 0 < a)
    (hn : sites ≤ C/a^3) : sites*a^4 ≤ C*a := by
  calc
    sites*a^4 ≤ (C/a^3)*a^4 :=
      mul_le_mul_of_nonneg_right hn (pow_nonneg ha.le 4)
    _ = C*a := by field_simp

#print axioms clockWeight_pos
#print axioms clockWeight_split
#print axioms clockWeight_sum
#print axioms clockWeight_load
#print axioms incoming_guard_kills_violation
#print axioms outgoing_guard_kills_violation
#print axioms illegal_energy_lower_bound
#print axioms propagation_support_bound
#print axioms weighted_history_zero_iff
#print axioms local_observable_unchanged
#print axioms local_readout_mixture
#print axioms clock_continuum_product_scale

end
end UnifiedTheory.Audit.KFCausalLocalClock
