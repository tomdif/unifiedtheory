/-
  LayerA/DimensionTripleCoincidence.lean — Triple coincidence at d=4

  Three INDEPENDENT physical characterizations each single out d=4:

    C1  (Gauge mode count)      : n² - 1 = 15            [NoExtraDimensions]
    C2  (Trace-reversal involution) : (2 - n)² = 4, n ≥ 2  [LinearizedEinstein]
    C3  (Gauge tracelessness)   : 1 - n/4 = 0 over ℚ       [MetricGaugeCoupling]

  These come from completely different physics:
    C1 — counting traceless matrix degrees of freedom (gauge sector)
    C2 — algebraic property of the linearized Einstein operator
    C3 — vanishing trace of the Yang-Mills stress-energy tensor

  The trace-reversal operator L(h) = h - (1/2)tr(h)·I has
  tr(L(h)) = (1 - n/2)·tr(h), so L(L(h)) = h iff (1 - n/2)² = 1,
  equivalently (2 - n)² = 4 over ℤ. For n ≥ 2, the only solution is n = 4.

  The Yang-Mills trace tr(T) = (1 - n/4)|F|² vanishes for all field
  configurations iff 1 - n/4 = 0, i.e., n = 4.

  This file proves:
    1. Each predicate is satisfied ONLY by n = 4 (in appropriate domain)
    2. n = 4 is the unique n ≥ 2 satisfying all three simultaneously
    3. No other dimension satisfies even TWO of the three

  All proofs by decidable arithmetic — ZERO sorry, ZERO axioms.
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.DimensionTripleCoincidence

/-! ## The three characterizations as predicates on ℕ -/

/-- **C1: Gauge mode count.** The dressing sector (traceless n×n matrices) has
    dimension n² - 1.  Matching the SM's 15 gauge modes requires n² - 1 = 15. -/
def C1 (n : ℕ) : Prop := n ^ 2 - 1 = 15

/-- **C2: Trace-reversal involution.** The linearized Einstein operator
    L(h) = h - (1/2)tr(h)·I satisfies L∘L = id iff (1 - n/2)² = 1.
    We require n ≥ 2 (physical spacetime) and express the condition as
    (2 - n)² = 4 over ℤ (equivalent to (1 - n/2)² = 1 over ℝ). -/
def C2 (n : ℕ) : Prop := n ≥ 2 ∧ (2 - (n : ℤ)) ^ 2 = 4

/-- **C3: Gauge stress-energy tracelessness.** The Yang-Mills trace formula
    tr(T) = (1 - n/4)|F|² vanishes for all field configurations iff n = 4.
    Equivalently, 1 - n/4 = 0 forces n = 4. -/
def C3 (n : ℕ) : Prop := (1 : ℚ) - (n : ℚ) / 4 = 0

/-! ## Each characterization forces n = 4 -/

/-- C1 has the unique solution n = 4. -/
theorem C1_unique (n : ℕ) : C1 n ↔ n = 4 := by
  unfold C1
  constructor
  · intro h
    have h1 : n ^ 2 ≥ 16 := by omega
    have h2 : n ^ 2 = 16 := by omega
    have h3 : n ≥ 4 := by nlinarith
    have h4 : n ≤ 4 := by
      by_contra h5
      push_neg at h5
      have : n ≥ 5 := by omega
      nlinarith
    omega
  · intro h; subst h; norm_num

/-- C2 has the unique solution n = 4 (among n ≥ 2). -/
theorem C2_unique (n : ℕ) : C2 n ↔ n = 4 := by
  unfold C2
  constructor
  · intro ⟨hn, hsq⟩
    -- (2 - n)² = 4 in ℤ, so |2 - n| = 2, i.e., 2 - n = 2 or 2 - n = -2
    -- From (2-n)² = 4 we get (2-n)² - 4 = 0, i.e., (2-n-2)(2-n+2) = 0, i.e., -n(4-n) = 0
    have key : (n : ℤ) * ((n : ℤ) - 4) = 0 := by nlinarith
    rcases mul_eq_zero.mp key with h | h
    · -- n = 0 contradicts n ≥ 2
      have : n = 0 := by omega
      omega
    · -- n = 4
      omega
  · intro h; subst h; constructor <;> norm_num

/-- C3 characterizes n = 4: solving the rational equation 1 - n/4 = 0 over ℕ. -/
theorem C3_unique (n : ℕ) : C3 n ↔ n = 4 := by
  unfold C3
  constructor
  · intro h
    have h1 : (n : ℚ) / 4 = 1 := by linarith
    have h2 : (n : ℚ) = 4 := by linarith
    exact_mod_cast h2
  · intro h; subst h; norm_num

/-! ## The triple coincidence theorem -/

/-- **The three conditions are INDEPENDENT over ℤ.**
    They have genuinely different solution sets:
    - n = -4 satisfies C1 ((-4)²-1=15) but NOT C2 ((2-(-4))²=36≠4) or C3 (1-(-4)/4≠0)
    - n = 0 satisfies the algebraic part of C2 ((2-0)²=4) but NOT C1 (0²-1≠15)
    The coincidence at n=4 over ℕ≥2 is therefore non-trivial. -/
theorem conditions_independent_over_Z :
    -- C1 has a solution that C2 rejects
    ((-4 : ℤ) ^ 2 - 1 = 15 ∧ ¬((2 - (-4 : ℤ)) ^ 2 = 4))
    -- C2 (algebraic part) has a solution that C1 rejects
    ∧ ((2 - (0 : ℤ)) ^ 2 = 4 ∧ ¬((0 : ℤ) ^ 2 - 1 = 15))
    -- C3 rejects -4 (which C1 accepts)
    ∧ (¬((1 : ℚ) - (-4 : ℚ) / 4 = 0)) := by
  norm_num

/-- n = 4 satisfies all three characterizations simultaneously. -/
theorem four_satisfies_all : C1 4 ∧ C2 4 ∧ C3 4 := by
  refine ⟨?_, ?_, ?_⟩
  · show C1 4; unfold C1; norm_num
  · show C2 4; unfold C2; norm_num
  · show C3 4; unfold C3; norm_num

/-! ## Strengthening: no other dimension satisfies even TWO of the three -/

/-- For n ≠ 4, C1 fails. -/
theorem C1_fails_of_ne (n : ℕ) (hn : n ≠ 4) : ¬ C1 n :=
  fun h => hn ((C1_unique n).mp h)

/-- For n ≠ 4, C2 fails. -/
theorem C2_fails_of_ne (n : ℕ) (hn : n ≠ 4) : ¬ C2 n :=
  fun h => hn ((C2_unique n).mp h)

/-- For n ≠ 4, C3 fails. -/
theorem C3_fails_of_ne (n : ℕ) (hn : n ≠ 4) : ¬ C3 n :=
  fun h => hn ((C3_unique n).mp h)

/-- **No dimension other than 4 satisfies any pair of the three conditions.**

    Since each condition individually forces n = 4, any pair also forces n = 4.
    This means the triple coincidence is NOT a weakening — even two out of
    three suffice to fix the dimension.  The coincidence of all three is
    an overdetermined system with a unique solution. -/
theorem no_other_dimension_satisfies_any_pair (n : ℕ) (hn : n ≠ 4) :
    ¬ (C1 n ∧ C2 n) ∧ ¬ (C1 n ∧ C3 n) ∧ ¬ (C2 n ∧ C3 n) := by
  exact ⟨fun ⟨h, _⟩ => C1_fails_of_ne n hn h,
         fun ⟨h, _⟩ => C1_fails_of_ne n hn h,
         fun ⟨h, _⟩ => C2_fails_of_ne n hn h⟩

/-- **Over ℕ, the three independently-defined conditions happen to coincide.**
    Despite having different solution sets over ℤ (proved above), they agree
    on ℕ: each is equivalent to n = 4. -/
theorem conditions_coincide_over_N (n : ℕ) :
    (C1 n ↔ n = 4) ∧ (C2 n ↔ n = 4) ∧ (C3 n ↔ n = 4) :=
  ⟨C1_unique n, C2_unique n, C3_unique n⟩

/-! ## Explicit exclusion of other dimensions -/

/-- d = 2: fails all three. -/
theorem dim2_fails : ¬ C1 2 ∧ ¬ C2 2 ∧ ¬ C3 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [C1]
  · simp [C2]
  · simp [C3]; norm_num

/-- d = 3: fails all three. -/
theorem dim3_fails : ¬ C1 3 ∧ ¬ C2 3 ∧ ¬ C3 3 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [C1]
  · intro ⟨_, h⟩; simp at h
  · simp [C3]; norm_num

/-- d = 5: fails all three. -/
theorem dim5_fails : ¬ C1 5 ∧ ¬ C2 5 ∧ ¬ C3 5 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [C1]
  · intro ⟨_, h⟩; simp at h
  · simp [C3]; norm_num

/-- d = 10 (string theory): fails all three. -/
theorem dim10_fails : ¬ C1 10 ∧ ¬ C2 10 ∧ ¬ C3 10 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [C1]
  · intro ⟨_, h⟩; simp at h
  · simp [C3]; norm_num

/-- d = 11 (M-theory): fails all three. -/
theorem dim11_fails : ¬ C1 11 ∧ ¬ C2 11 ∧ ¬ C3 11 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [C1]
  · intro ⟨_, h⟩; simp at h
  · simp [C3]; norm_num

/-! ## Master theorem -/

/-- **The conditions are independent over ℤ but coincide over ℕ.**
    This is the full dimension selection theorem: three independent
    physics routes (with genuinely different ℤ-solution sets) all
    converge to n = 4 over the natural numbers. -/
theorem dimension_selection :
    -- Independence: different solution sets over ℤ
    ((-4 : ℤ) ^ 2 - 1 = 15 ∧ ¬((2 - (-4 : ℤ)) ^ 2 = 4))
    -- Coincidence: same solution over ℕ
    ∧ (∀ n : ℕ, C1 n ↔ n = 4)
    ∧ (∀ n : ℕ, C2 n ↔ n = 4)
    ∧ (∀ n : ℕ, C3 n ↔ n = 4) :=
  ⟨⟨by norm_num, by norm_num⟩, C1_unique, C2_unique, C3_unique⟩

end UnifiedTheory.LayerA.DimensionTripleCoincidence
