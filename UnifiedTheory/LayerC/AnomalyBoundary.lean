/-
  UnifiedTheory/LayerC/AnomalyBoundary.lean
  ──────────────────────────────────────────────

  **SM ↔ QM Bridge — the HONEST BOUNDARY of anomaly cancellation.**

  The companion file `AnomalyCancellation.lean` proves the POSITIVE
  content: quantum gauge consistency (anomaly freedom) + mass
  generation FORCE the SM hypercharges (`hypercharge_uniqueness`).

  This file proves the precise NEGATIVE content — exactly what
  anomaly cancellation does NOT force — so that the claim "quantum
  consistency forces the SM" is bounded honestly:

    1. **Anomaly additivity.**  Each of the five anomaly functionals is
       a `List.map`-then-`.sum`, hence LINEAR over `List.append`:
           A(X ++ Y) = A(X) + A(Y).
       This single fact drives every negative below.

    2. **N generations are anomaly-free for EVERY N.**  Because each
       anomaly is a linear sum, `A(N copies) = N · A(1 copy) = N·0 = 0`.
       So anomaly freedom is satisfied by 1, 2, 3, … any number of
       identical generations.

    3. **HONEST NEGATIVE: the generation count is UNCONSTRAINED.**
       The famous "why are there exactly 3 generations?" question is
       NOT answered by anomaly cancellation: every `N` is equally
       consistent.  Anomalies fix the charges WITHIN a generation but
       say nothing about HOW MANY generations there are.

    4. **Witten SU(2) parity, general content.**  For `N` integer
       generations the number of doublets is `4N`, always even — the
       global anomaly is automatically satisfied for any whole number
       of generations.  (A hypothetical half-generation would give an
       odd doublet count → genuinely inconsistent; integrality is the
       real constraint, not the generation count.)

    5. **Boundary master.**  A single bundled statement: charges YES
       (within a generation), generation number NO.

  ## Standing constraint
  Zero `sorry`, zero custom `axiom`.  Exact ℚ / ℕ arithmetic;
  the generation result is a genuine induction `N·0 = 0`.
-/

import UnifiedTheory.LayerC.AnomalyCancellation

namespace UnifiedTheory.LayerC.AnomalyBoundary

open UnifiedTheory.LayerC.AnomalyCancellation

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: ANOMALY ADDITIVITY (linearity over `++`)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Every anomaly functional has the shape `(fs.map g).sum`.  Since
    `(A ++ B).map g = A.map g ++ B.map g` and `(xs ++ ys).sum = xs.sum
    + ys.sum`, each functional is additive over `List.append`.  This
    is the exact linearity that makes "more generations" cost-free. -/

/-- `[SU(3)]²U(1)` anomaly is additive over `++`. -/
theorem su3sq_anomaly_append (A B : List WeylFermion) :
    su3sq_u1_anomaly (A ++ B) = su3sq_u1_anomaly A + su3sq_u1_anomaly B := by
  unfold su3sq_u1_anomaly
  rw [List.map_append, List.sum_append]

/-- `[SU(2)]²U(1)` anomaly is additive over `++`. -/
theorem su2sq_anomaly_append (A B : List WeylFermion) :
    su2sq_u1_anomaly (A ++ B) = su2sq_u1_anomaly A + su2sq_u1_anomaly B := by
  unfold su2sq_u1_anomaly
  rw [List.map_append, List.sum_append]

/-- `[U(1)]³` anomaly is additive over `++`. -/
theorem u1cubed_anomaly_append (A B : List WeylFermion) :
    u1cubed_anomaly (A ++ B) = u1cubed_anomaly A + u1cubed_anomaly B := by
  unfold u1cubed_anomaly
  rw [List.map_append, List.sum_append]

/-- grav²–U(1) anomaly is additive over `++`. -/
theorem grav_anomaly_append (A B : List WeylFermion) :
    grav_u1_anomaly (A ++ B) = grav_u1_anomaly A + grav_u1_anomaly B := by
  unfold grav_u1_anomaly
  rw [List.map_append, List.sum_append]

/-- The doublet count is additive over `++` (over ℕ). -/
theorem numDoublets_append (A B : List WeylFermion) :
    numDoublets (A ++ B) = numDoublets A + numDoublets B := by
  unfold numDoublets
  rw [List.map_append, List.sum_append]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: N GENERATIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `N` identical SM generations of left-handed Weyl fermions:
    `smGeneration` concatenated with itself `N` times. -/
def nGenerations (N : ℕ) : List WeylFermion := (List.replicate N smGeneration).flatten

@[simp] theorem nGenerations_zero : nGenerations 0 = [] := by
  unfold nGenerations; rw [List.replicate_zero, List.flatten_nil]

/-- `nGenerations (N+1) = smGeneration ++ nGenerations N`.  This is the
    recursion that powers every induction below. -/
theorem nGenerations_succ (N : ℕ) :
    nGenerations (N + 1) = smGeneration ++ nGenerations N := by
  unfold nGenerations
  rw [List.replicate_succ, List.flatten_cons]

/-! ### Each anomaly scales linearly: `A(N gens) = N · A(1 gen)` -/

theorem su3sq_nGen (N : ℕ) :
    su3sq_u1_anomaly (nGenerations N) = N * su3sq_u1_anomaly smGeneration := by
  induction N with
  | zero => rw [nGenerations_zero]; simp [su3sq_u1_anomaly]
  | succ n ih =>
    rw [nGenerations_succ, su3sq_anomaly_append, ih]
    push_cast; ring

theorem su2sq_nGen (N : ℕ) :
    su2sq_u1_anomaly (nGenerations N) = N * su2sq_u1_anomaly smGeneration := by
  induction N with
  | zero => rw [nGenerations_zero]; simp [su2sq_u1_anomaly]
  | succ n ih =>
    rw [nGenerations_succ, su2sq_anomaly_append, ih]
    push_cast; ring

theorem u1cubed_nGen (N : ℕ) :
    u1cubed_anomaly (nGenerations N) = N * u1cubed_anomaly smGeneration := by
  induction N with
  | zero => rw [nGenerations_zero]; simp [u1cubed_anomaly]
  | succ n ih =>
    rw [nGenerations_succ, u1cubed_anomaly_append, ih]
    push_cast; ring

theorem grav_nGen (N : ℕ) :
    grav_u1_anomaly (nGenerations N) = N * grav_u1_anomaly smGeneration := by
  induction N with
  | zero => rw [nGenerations_zero]; simp [grav_u1_anomaly]
  | succ n ih =>
    rw [nGenerations_succ, grav_anomaly_append, ih]
    push_cast; ring

/-- The doublet count of `N` generations is `4N` (over ℕ): `numDoublets`
    of one generation is `4` (three colors of `Q` + one `L`). -/
theorem numDoublets_nGen (N : ℕ) :
    numDoublets (nGenerations N) = 4 * N := by
  induction N with
  | zero => rw [nGenerations_zero]; simp [numDoublets]
  | succ n ih =>
    rw [nGenerations_succ, numDoublets_append, ih]
    have : numDoublets smGeneration = 4 := by
      unfold numDoublets smGeneration
      simp only [Q, uc, dc, L, ec, WeylFermion.isDoublet, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil]
      decide
    rw [this]; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: N GENERATIONS ARE ANOMALY-FREE FOR EVERY N
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

theorem su3sq_nGen_free (N : ℕ) : su3sq_u1_anomaly (nGenerations N) = 0 := by
  rw [su3sq_nGen, su3sq_u1_cancels]; ring

theorem su2sq_nGen_free (N : ℕ) : su2sq_u1_anomaly (nGenerations N) = 0 := by
  rw [su2sq_nGen, su2sq_u1_cancels]; ring

theorem u1cubed_nGen_free (N : ℕ) : u1cubed_anomaly (nGenerations N) = 0 := by
  rw [u1cubed_nGen, u1cubed_cancels]; ring

theorem grav_nGen_free (N : ℕ) : grav_u1_anomaly (nGenerations N) = 0 := by
  rw [grav_nGen, grav_u1_cancels]; ring

/-- **Witten SU(2) parity for `N` generations.**  The doublet count is
    `4N`, which is even for every `N` — so any whole number of
    generations automatically satisfies the global anomaly. -/
theorem witten_nGen (N : ℕ) : Even (numDoublets (nGenerations N)) := by
  rw [numDoublets_nGen]
  exact ⟨2 * N, by ring⟩

/-- **`N` generations are anomaly-free for every `N`** — all five
    quantum-consistency conditions simultaneously. -/
theorem nGen_anomaly_free (N : ℕ) :
    su3sq_u1_anomaly (nGenerations N) = 0 ∧
    su2sq_u1_anomaly (nGenerations N) = 0 ∧
    u1cubed_anomaly  (nGenerations N) = 0 ∧
    grav_u1_anomaly  (nGenerations N) = 0 ∧
    Even (numDoublets (nGenerations N)) :=
  ⟨su3sq_nGen_free N, su2sq_nGen_free N, u1cubed_nGen_free N,
   grav_nGen_free N, witten_nGen N⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE HONEST NEGATIVE — GENERATION COUNT IS UNCONSTRAINED
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST NEGATIVE: anomaly freedom does NOT fix the generation
    count.**

    For EVERY natural number `N`, the `N`-generation content satisfies
    all five anomaly-cancellation conditions.  Hence anomaly
    cancellation places NO constraint on the number of generations:
    the "why exactly 3 generations?" question is provably *not*
    answered by quantum gauge consistency.  Anomalies fix the
    hypercharges WITHIN a generation (see
    `AnomalyCancellation.hypercharge_uniqueness`) but are blind to how
    many generations exist. -/
theorem generation_count_unconstrained :
    ∀ N : ℕ,
      su3sq_u1_anomaly (nGenerations N) = 0 ∧
      su2sq_u1_anomaly (nGenerations N) = 0 ∧
      u1cubed_anomaly  (nGenerations N) = 0 ∧
      grav_u1_anomaly  (nGenerations N) = 0 ∧
      Even (numDoublets (nGenerations N)) :=
  fun N => nGen_anomaly_free N

/-- **Sharper negative: two DIFFERENT generation counts are both
    anomaly-free.**  In particular the actual SM value (`3`) and any
    other value (e.g. `4`) are equally consistent — there is no
    anomaly-theoretic discriminator between them. -/
theorem distinct_counts_both_free :
    (su3sq_u1_anomaly (nGenerations 3) = 0 ∧
     su2sq_u1_anomaly (nGenerations 3) = 0 ∧
     u1cubed_anomaly  (nGenerations 3) = 0 ∧
     grav_u1_anomaly  (nGenerations 3) = 0 ∧
     Even (numDoublets (nGenerations 3))) ∧
    (su3sq_u1_anomaly (nGenerations 4) = 0 ∧
     su2sq_u1_anomaly (nGenerations 4) = 0 ∧
     u1cubed_anomaly  (nGenerations 4) = 0 ∧
     grav_u1_anomaly  (nGenerations 4) = 0 ∧
     Even (numDoublets (nGenerations 4))) ∧
    (3 : ℕ) ≠ 4 :=
  ⟨nGen_anomaly_free 3, nGen_anomaly_free 4, by decide⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: WITTEN — INTEGRALITY IS THE REAL CONSTRAINT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Witten global anomaly constrains the PARITY of the doublet
    count, not the generation number.  For any whole number `N` of
    generations the count `4N` is even (Part 3).  We make the
    counterpoint explicit: it is *odd* doublet content — a hypothetical
    "half generation" carrying a single extra SU(2) doublet — that the
    Witten anomaly forbids.  So Witten constrains INTEGRALITY of the
    matter content, never the generation count. -/

/-- A single bare SU(2) doublet (a hypothetical fractional/extra piece),
    color singlet, hypercharge irrelevant to the count. -/
def loneDoublet : WeylFermion := { Y := 0, colorMult := 1, weakMult := 2 }

/-- `N` generations PLUS one lone doublet has an ODD doublet count
    (`4N + 1`), so the Witten global anomaly is VIOLATED.  This is the
    real edge of the constraint: it is parity/integrality of the
    doublet content, not the number of generations, that Witten fixes. -/
theorem witten_violated_halfGen (N : ℕ) :
    ¬ Even (numDoublets (nGenerations N ++ [loneDoublet])) := by
  rw [numDoublets_append, numDoublets_nGen]
  have h : numDoublets [loneDoublet] = 1 := by
    unfold numDoublets loneDoublet
    simp only [WeylFermion.isDoublet, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    decide
  rw [h]
  -- 4*N + 1 is odd.
  rw [Nat.not_even_iff_odd]
  exact ⟨2 * N, by ring⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: BOUNDARY MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The full HONEST-BOUNDARY statement as a single `Prop`:

      (A) **charges YES** — within one generation, the gauge + grav
          anomalies and Yukawa constraints FORCE the hypercharges to the
          SM values at the standard normalization
          (`AnomalyCancellation.hypercharge_uniqueness`);
      (B) **generation count NO** — every `N`-generation content is
          anomaly-free, so the number of generations is unconstrained;
      (C) **Witten parity** — the doublet count `4N` is even for every
          whole `N`, while an odd (half-generation) content is
          forbidden, so Witten fixes integrality, not the count. -/
def Anomaly_Boundary_Target : Prop :=
  -- (A) charges forced within a generation
  (∀ a : HyperchargeAssignment,
      SatisfiesGaugeGrav a → SatisfiesYukawa a → a.yH = 1 / 2 →
      a = smHypercharges) ∧
  -- (B) generation count free
  (∀ N : ℕ,
      su3sq_u1_anomaly (nGenerations N) = 0 ∧
      su2sq_u1_anomaly (nGenerations N) = 0 ∧
      u1cubed_anomaly  (nGenerations N) = 0 ∧
      grav_u1_anomaly  (nGenerations N) = 0 ∧
      Even (numDoublets (nGenerations N))) ∧
  -- (C) Witten parity holds for integer N, fails for a half-generation
  (∀ N : ℕ, Even (numDoublets (nGenerations N))) ∧
  (∀ N : ℕ, ¬ Even (numDoublets (nGenerations N ++ [loneDoublet])))

/-- **ANOMALY-BOUNDARY MASTER THEOREM.**

    Sharpens exactly what "quantum consistency forces the SM" means:

    * The hypercharges WITHIN one generation are forced (charges YES).
    * The number of generations is NOT forced — any `N` is anomaly-free
      (the honest negative: anomalies do not answer "why 3 families").
    * The Witten global anomaly is satisfied for every whole-number
      generation count and is violated only by an odd, non-integer
      doublet content — so it constrains integrality of the matter
      content, not the generation count. -/
theorem anomaly_boundary_master : Anomaly_Boundary_Target := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a hg hy hn
    exact hypercharge_uniqueness a hg hy hn
  · exact generation_count_unconstrained
  · exact witten_nGen
  · exact witten_violated_halfGen

end UnifiedTheory.LayerC.AnomalyBoundary
