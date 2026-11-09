/-
  Supporting formal results for CAUSAL_ORDER_CLOCK_BRIDGE.md.
  Allowed-swap invariance is formalized here. Connectivity of all linear
  extensions by such swaps and the full Hilbert-space history theorem
  have analytic proofs in the note; they are not introduced as axioms.
-/
import UnifiedTheory.Audit.KFCausalCollectiveSpacetime

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalOrderClock
noncomputable section
open scoped BigOperators

/-- Chronological list: the earliest operator acts first, on the right. -/
def evolution {E M : Type*} [Monoid M] (U : E → M) (events : List E) : M :=
  (events.reverse.map U).prod

/-- Only the two exchanged gates need commute. -/
theorem adjacent_event_swap {E M : Type*} [Monoid M]
    (U : E → M) (before after : List E) (x y : E)
    (h : Commute (U x) (U y)) :
    evolution U (before ++ x :: y :: after) =
      evolution U (before ++ y :: x :: after) := by
  simp only [evolution, List.reverse_append, List.reverse_cons, List.map_append,
    List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil,
    mul_one]
  simp only [mul_assoc]
  rw [← mul_assoc (U y) (U x), ← h.eq, mul_assoc]

def AllowedSwap {E : Type*} (independent : E → E → Prop)
    (first second : List E) : Prop :=
  ∃ before after x y, independent x y ∧
    first = before ++ x :: y :: after ∧ second = before ++ y :: x :: after

/-- All finite chains of allowed adjacent exchanges preserve evolution. -/
theorem allowed_swap_chain {E M : Type*} [Monoid M]
    (independent : E → E → Prop) (U : E → M)
    (hcomm : ∀ x y, independent x y → Commute (U x) (U y))
    {first second : List E}
    (h : Relation.ReflTransGen (AllowedSwap independent) first second) :
    evolution U first = evolution U second := by
  induction h with
  | refl => rfl
  | @tail middle last _ step ih =>
    obtain ⟨before, after, x, y, hxy, rfl, rfl⟩ := step
    exact ih.trans (adjacent_event_swap U before after x y (hcomm x y hxy))

/-- A context-dependent pure-gauge transport satisfies every diamond. -/
theorem pure_gauge_diamond {G : Type*} [Group G] (w0 wx wy wxy : G) :
    (wxy * wx⁻¹) * (wx * w0⁻¹) = (wxy * wy⁻¹) * (wy * w0⁻¹) := by
  simp [mul_assoc]

/-- One transported history edge becomes an ordinary difference. -/
theorem transported_edge {R : Type*} [Ring R] (u vi vj a b : R)
    (h : vj = u * vi) : vj * a - u * (vi * b) = vj * (a-b) := by
  rw [h, mul_sub]
  simp only [mul_assoc]

/-- Vanishing of one positive history penalty is the update equation. -/
theorem edge_penalty_zero_iff {H : Type*} [NormedAddCommGroup H] (a b : H) :
    ‖a-b‖ ^ 2 = 0 ↔ a = b := by
  simp only [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]

/-- The positive sum enforces all edge constraints, not just their average. -/
theorem history_penalty_zero_iff {E H : Type*} [Fintype E]
    [NormedAddCommGroup H] (residual : E → H) :
    (∑ e, ‖residual e‖ ^ 2) = 0 ↔ ∀ e, residual e = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun e _ => sq_nonneg ‖residual e‖)]
  simp only [Finset.mem_univ, forall_true_left, sq_eq_zero_iff, norm_eq_zero]

/-- An intrinsic scalar label cannot distinguish an order symmetry's orbit. -/
theorem invariant_clock_on_symmetry_orbit {E T : Type*}
    (clock : E → T) (symmetry : E → E) (hinv : ∀ x, clock (symmetry x) = clock x)
    (x y : E) (hxy : symmetry x = y) : clock x = clock y := by
  simpa [hxy] using (hinv x).symm

/-- Changing one common clock unit preserves frequency ratios. -/
theorem frequency_ratio_invariant (u v scale : ℝ) (hs : scale ≠ 0) :
    (u/scale)/(v/scale) = u/v := by
  by_cases hv : v = 0
  · simp [hv]
  · field_simp

/-- A common clock calibration leaves a quadratic band's ratio equal to four. -/
theorem quadratic_frequency_ratio (D k scale : ℝ)
    (hD : D ≠ 0) (hk : k ≠ 0) (hs : scale ≠ 0) :
    ((D*(2*k)^2)/scale)/((D*k^2)/scale) = 4 := by
  rw [frequency_ratio_invariant _ _ _ hs]
  field_simp
  ring

#print axioms adjacent_event_swap
#print axioms allowed_swap_chain
#print axioms pure_gauge_diamond
#print axioms transported_edge
#print axioms edge_penalty_zero_iff
#print axioms history_penalty_zero_iff
#print axioms invariant_clock_on_symmetry_orbit
#print axioms frequency_ratio_invariant
#print axioms quadratic_frequency_ratio

end
end UnifiedTheory.Audit.KFCausalOrderClock
