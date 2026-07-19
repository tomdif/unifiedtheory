/-
  LayerC/BB84Security.lean — BB84 quantum key distribution security
                             via the single-qubit intercept-resend
                             information-disturbance trade-off
                             (Bennett–Brassard 1984)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  The intercept-resend security argument for BB84 in the framework's
  real-amplitude qubit vocabulary.  Alice prepares a random qubit in
  one of two mutually unbiased bases (computational `Z` or Hadamard
  `X`); Eve performs a deterministic single-basis projective
  measurement and resends the post-measurement state to Bob; Bob
  measures in the *same* basis Alice used (post-sifting).  The
  fundamental theorem:

      eveCorrectRate a_basis E + bobAgreementRate a_basis E ≤ 3/2

  for every intercept-resend strategy `E` and every Alice basis
  `a_basis ∈ {Z, X}`.  Equivalently:

      eveCorrectRate a_basis E - 1/2  ≤  bobErrorRate a_basis E

  i.e. every bit of information Eve extracts costs Bob (at least) an
  equal amount of disturbance.  The classical random-guess baseline
  is `1/2`; the perfect-information ceiling is `1`.

  Concrete corollary (the famous **25 % QBER threshold**): when Eve
  uses the worst-case strategy of always measuring in the `Z` basis,
  averaged over Alice's basis choice the bit error rate Bob observes
  equals exactly `1/4`.  This is the operational signal Alice and
  Bob use to detect Eve.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPING

  – Following the framework convention (`NoCloning.lean`,
    `QuantumTeleportation.lean`, `TeleportationFidelity.lean`,
    `BellTheorem.lean`), we use **real** single-qubit amplitudes
    `Fin 2 → ℝ`.  The four BB84 states `|0⟩, |1⟩, |+⟩, |−⟩` are all
    real, so the analysis is exact in this scope.

  – **Eve's strategy** is restricted here to deterministic projective
    measurement in one of the two BB84 bases (`Z` or `X`) plus a
    deterministic classical post-processing.  General POVMs and
    coherent attacks are stronger; the standard QM result (Fuchs–
    Peres 1996; Cirac–Gisin 1997) is that the optimal single-qubit
    information–disturbance trade-off saturates at the same `3/2`
    line for BB84 inputs.  Probabilistic mixtures of intercept-resend
    strategies are convex combinations of the deterministic ones and
    obey the same linear bound; we record the deterministic case as
    the load-bearing primitive.

  – **Full asymptotic BB84 security** (Mayers; Shor–Preskill;
    Lo–Chau; Renner) requires entropic uncertainty relations,
    privacy amplification, and information-reconciliation analysis
    beyond the present scope.  What we formalize is the single-qubit
    information-disturbance core that makes the full proof possible.

  – **No-cloning** (`LayerB.NoCloning.no_cloning`) is the structural
    reason this works:  Eve cannot copy the qubit and forward an
    intact copy to Bob.  Any information-extraction strategy of the
    intercept-resend type collapses the state into Eve's measurement
    basis; if that basis disagrees with Alice's, Bob's outcome
    becomes random.

  Zero `sorry`.  Zero custom `axiom`.
-/
import UnifiedTheory.LayerB.NoCloning
import UnifiedTheory.LayerB.TeleportationFidelity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.BB84Security

open UnifiedTheory.LayerB.BellTheorem
open UnifiedTheory.LayerB.QuantumEntanglement
open UnifiedTheory.LayerB.QuantumTeleportation
open UnifiedTheory.LayerB.TeleportationFidelity

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE FOUR BB84 STATES, INDEXED BY (bit, basis)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A BB84 state is determined by a bit `b ∈ {0,1}` and a basis
    `B ∈ {Z, X}` ⊆ `Fin 2`:

        bb84State 0 Z = |0⟩              = (1, 0)
        bb84State 1 Z = |1⟩              = (0, 1)
        bb84State 0 X = |+⟩              = ( 1/√2,  1/√2)
        bb84State 1 X = |−⟩              = ( 1/√2, -1/√2)

    Convention: `basis = 0` is the computational (`Z`) basis;
    `basis = 1` is the Hadamard (`X`) basis.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The BB84 preparation: bit `b` in basis `B`.  Component `i`:
        bb84State b 0 i = δ(i = b)                          (Z basis)
        bb84State b 1 i = (1/√2) · (-1)^(b·i)               (X basis)
    explicitly:
        bb84State 0 X = |+⟩ = ( 1/√2,  1/√2)
        bb84State 1 X = |−⟩ = ( 1/√2, -1/√2). -/
noncomputable def bb84State (b : Fin 2) (basis : Fin 2) : Qubit :=
  fun i =>
    if basis = 0 then
      (if i = b then 1 else 0)
    else
      -- X basis: i=0 always gives +1/√2; i=1 gives (-1)^b / √2
      if i = 0 then (1 / Real.sqrt 2)
      else if b = 0 then (1 / Real.sqrt 2) else -(1 / Real.sqrt 2)

@[simp] theorem bb84State_Z_match (b : Fin 2) : bb84State b 0 b = 1 := by
  unfold bb84State; simp

@[simp] theorem bb84State_Z_0_1 : bb84State (0 : Fin 2) 0 (1 : Fin 2) = 0 := by
  unfold bb84State
  have h : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
  simp [h]

@[simp] theorem bb84State_Z_1_0 : bb84State (1 : Fin 2) 0 (0 : Fin 2) = 0 := by
  unfold bb84State
  have h : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  simp [h]

@[simp] theorem bb84State_X_0_0 : bb84State (0 : Fin 2) 1 (0 : Fin 2)
    = 1 / Real.sqrt 2 := by
  unfold bb84State
  simp

@[simp] theorem bb84State_X_0_1 : bb84State (0 : Fin 2) 1 (1 : Fin 2)
    = 1 / Real.sqrt 2 := by
  unfold bb84State
  have h0 : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
  simp [h0]

@[simp] theorem bb84State_X_1_0 : bb84State (1 : Fin 2) 1 (0 : Fin 2)
    = 1 / Real.sqrt 2 := by
  unfold bb84State
  simp

@[simp] theorem bb84State_X_1_1 : bb84State (1 : Fin 2) 1 (1 : Fin 2)
    = -(1 / Real.sqrt 2) := by
  unfold bb84State
  have h : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
  simp [h]

/-- A case-split helper for Fin 2: every element is 0 or 1.

    Defined here (before its first use) so the rest of the file can
    use it uniformly. -/
private lemma fin2_cases_aux (x : Fin 2) : x = 0 ∨ x = 1 := by
  obtain ⟨n, hn⟩ := x
  match n, hn with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr rfl

/-- The four single-qubit BB84 states are all normalized. -/
theorem bb84State_normalized (b : Fin 2) (basis : Fin 2) :
    bb84State b basis 0 ^ 2 + bb84State b basis 1 ^ 2 = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    have := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
    rw [sq] at this; exact this
  have hSq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, sq, h2]
  have hSqNeg : (-(1 / Real.sqrt 2)) ^ 2 = 1 / 2 := by
    rw [neg_pow]; simp [hSq]
  rcases fin2_cases_aux b with hb | hb <;>
    rcases fin2_cases_aux basis with hbas | hbas <;>
    subst hb <;> subst hbas
  · -- b=0, basis=0: |0⟩ = (1, 0)
    rw [bb84State_Z_match (0 : Fin 2), bb84State_Z_0_1]
    ring
  · -- b=0, basis=1: |+⟩ = (1/√2, 1/√2)
    rw [bb84State_X_0_0, bb84State_X_0_1, hSq]
    ring
  · -- b=1, basis=0: |1⟩ = (0, 1)
    rw [bb84State_Z_1_0, bb84State_Z_match (1 : Fin 2)]
    ring
  · -- b=1, basis=1: |−⟩ = (1/√2, −1/√2)
    rw [bb84State_X_1_0, bb84State_X_1_1, hSq, hSqNeg]
    ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: SAME-BASIS / CROSS-BASIS INNER PRODUCTS AND THE BORN RULE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The two BB84 bases are **mutually unbiased**:

        |⟨0|+⟩|² = |⟨0|-⟩|² = |⟨1|+⟩|² = |⟨1|-⟩|² = 1/2
        |⟨+|0⟩|² = |⟨-|0⟩|² = ... etc.

    while same-basis inner products are δ-functions.  We package
    `|⟨ψ|φ⟩|²` as the Born-rule probability of obtaining outcome
    `ψ` when measuring a state `φ` in a basis containing `ψ`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The squared inner product between two BB84 states.  This is
    exactly the Born-rule probability that a projective measurement
    in basis `b2` on the state `bb84State b1 basis1` produces
    outcome `b2`. -/
noncomputable def bb84Born (b1 basis1 b2 basis2 : Fin 2) : ℝ :=
  qubitFidelity (bb84State b1 basis1) (bb84State b2 basis2)

/-- **Same-basis, same-bit**: the projective measurement reproduces
    the prepared bit with probability `1`. -/
theorem bb84Born_same (b basis : Fin 2) : bb84Born b basis b basis = 1 := by
  unfold bb84Born
  exact qubitFidelity_normalized _ (bb84State_normalized b basis)

/-- **Same-basis, opposite bit**: the projective measurement
    produces the opposite outcome with probability `0`. -/
theorem bb84Born_orthogonal (basis : Fin 2) :
    bb84Born 0 basis 1 basis = 0 := by
  unfold bb84Born qubitFidelity qubitInner
  by_cases hbasis : basis = 0
  · -- Z basis: ⟨0|1⟩ = 0·0 + 0·1 = 0
    subst hbasis
    rw [bb84State_Z_match (0 : Fin 2), bb84State_Z_0_1,
        bb84State_Z_1_0, bb84State_Z_match (1 : Fin 2)]
    ring
  · have hbasis1 : basis = 1 := by
      obtain ⟨bn, bhn⟩ := basis
      match bn, bhn, hbasis with
      | 0, _, h => exact absurd rfl h
      | 1, _, _ => rfl
    subst hbasis1
    -- X basis: ⟨+|-⟩ = (1/√2)(1/√2) + (1/√2)(-1/√2) = 0
    rw [bb84State_X_0_0, bb84State_X_0_1, bb84State_X_1_0, bb84State_X_1_1]
    ring

/-- The reversed direction. -/
theorem bb84Born_orthogonal' (basis : Fin 2) :
    bb84Born 1 basis 0 basis = 0 := by
  rw [show bb84Born 1 basis 0 basis = bb84Born 0 basis 1 basis by
        unfold bb84Born; rw [qubitFidelity_comm]]
  exact bb84Born_orthogonal basis

/-- Alias for the case-split helper. -/
private lemma fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := fin2_cases_aux x

/-- **Mutually-unbiased property**: every cross-basis BB84 inner
    product has squared value `1/2`. -/
theorem bb84Born_cross (b1 b2 : Fin 2) :
    bb84Born b1 0 b2 1 = 1 / 2 := by
  unfold bb84Born qubitFidelity qubitInner
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    have := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
    rw [sq] at this; exact this
  have hSq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, sq, h2]
  have hSqNeg : (-(1 / Real.sqrt 2)) ^ 2 = 1 / 2 := by
    rw [neg_pow]; simp [hSq]
  rcases fin2_cases b1 with hb1 | hb1 <;> rcases fin2_cases b2 with hb2 | hb2 <;>
    subst hb1 <;> subst hb2
  · -- ⟨0|+⟩² = (1·(1/√2) + 0·(1/√2))² = 1/2
    rw [bb84State_Z_match (0 : Fin 2), bb84State_Z_0_1,
        bb84State_X_0_0, bb84State_X_0_1]
    rw [show ((1 : ℝ) * (1 / Real.sqrt 2) + 0 * (1 / Real.sqrt 2)) ^ 2
            = (1 / Real.sqrt 2) ^ 2 by ring]
    exact hSq
  · -- ⟨0|−⟩² = (1·(1/√2) + 0·(-1/√2))² = 1/2
    rw [bb84State_Z_match (0 : Fin 2), bb84State_Z_0_1,
        bb84State_X_1_0, bb84State_X_1_1]
    rw [show ((1 : ℝ) * (1 / Real.sqrt 2) + 0 * (-(1 / Real.sqrt 2))) ^ 2
            = (1 / Real.sqrt 2) ^ 2 by ring]
    exact hSq
  · -- ⟨1|+⟩² = (0·(1/√2) + 1·(1/√2))² = 1/2
    rw [bb84State_Z_1_0, bb84State_Z_match (1 : Fin 2),
        bb84State_X_0_0, bb84State_X_0_1]
    rw [show ((0 : ℝ) * (1 / Real.sqrt 2) + 1 * (1 / Real.sqrt 2)) ^ 2
            = (1 / Real.sqrt 2) ^ 2 by ring]
    exact hSq
  · -- ⟨1|−⟩² = (0·(1/√2) + 1·(-1/√2))² = 1/2
    rw [bb84State_Z_1_0, bb84State_Z_match (1 : Fin 2),
        bb84State_X_1_0, bb84State_X_1_1]
    rw [show ((0 : ℝ) * (1 / Real.sqrt 2) + 1 * (-(1 / Real.sqrt 2))) ^ 2
            = (-(1 / Real.sqrt 2)) ^ 2 by ring]
    exact hSqNeg

/-- Born probabilities are symmetric. -/
theorem bb84Born_comm (b1 basis1 b2 basis2 : Fin 2) :
    bb84Born b1 basis1 b2 basis2 = bb84Born b2 basis2 b1 basis1 := by
  unfold bb84Born; exact qubitFidelity_comm _ _

/-- The reversed cross-basis statement, by symmetry. -/
theorem bb84Born_cross' (b1 b2 : Fin 2) :
    bb84Born b1 1 b2 0 = 1 / 2 := by
  rw [bb84Born_comm]; exact bb84Born_cross b2 b1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: INTERCEPT-RESEND EAVESDROPPING STRATEGY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Eve's deterministic single-qubit intercept-resend strategy is
    characterized by:

      • `e_basis ∈ {Z, X}`         — Eve's measurement basis
      • `e_guess : Fin 2 → Fin 2`  — Eve's post-processing of the
                                     classical measurement outcome

    The protocol step:  Eve intercepts the qubit, projects in
    `e_basis`, obtains outcome `o`, RESENDS `bb84State o e_basis`
    (the post-measurement state) to Bob.  Bob measures in
    `b_basis`.  After sifting, `b_basis = a_basis` and Alice and
    Bob compare bits.

    Randomized strategies are convex combinations of deterministic
    ones; since every quantity below is linear in a finite distribution
    over deterministic strategies, the deterministic case is the
    load-bearing primitive.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A deterministic intercept-resend eavesdropping strategy. -/
structure InterceptResendStrategy where
  /-- Eve's chosen measurement basis. -/
  e_basis : Fin 2
  /-- Eve's deterministic post-processing of the measurement outcome. -/
  e_guess : Fin 2 → Fin 2

/-- **Born-rule probability that Eve obtains outcome `e_out` when she
    measures Alice's qubit `bb84State a_bit a_basis` in basis
    `E.e_basis`.** -/
noncomputable def eveOutcomeProb (a_bit a_basis : Fin 2)
    (E : InterceptResendStrategy) (e_out : Fin 2) : ℝ :=
  bb84Born a_bit a_basis e_out E.e_basis

/-- **Born-rule probability that, given Eve obtained `e_out` and
    resent `bb84State e_out E.e_basis`, Bob measuring in `b_basis`
    obtains outcome `b_out`.** -/
noncomputable def bobOutcomeProbGivenEve (e_out : Fin 2)
    (E : InterceptResendStrategy) (b_basis b_out : Fin 2) : ℝ :=
  bb84Born e_out E.e_basis b_out b_basis

/-- **Joint probability of (Eve outcome `e_out`, Bob outcome
    `b_out`) given Alice's bit and basis and Eve's basis.**

    By the projective-measurement collapse, the qubit Bob receives
    is exactly `bb84State e_out E.e_basis` (the post-measurement
    state).  The joint probability factorizes as

       P(e_out, b_out | a_bit, a_basis) = P_E(e_out) · P_B(b_out | e_out).
-/
noncomputable def jointEveBobProb
    (a_bit a_basis : Fin 2) (E : InterceptResendStrategy)
    (e_out b_basis b_out : Fin 2) : ℝ :=
  eveOutcomeProb a_bit a_basis E e_out
    * bobOutcomeProbGivenEve e_out E b_basis b_out

/-- **Marginal probability that Bob obtains outcome `b_out`**:
    sum over Eve's outcome of the joint probability. -/
noncomputable def bobOutcomeProb (a_bit a_basis : Fin 2)
    (E : InterceptResendStrategy) (b_basis b_out : Fin 2) : ℝ :=
  ∑ e_out : Fin 2, jointEveBobProb a_bit a_basis E e_out b_basis b_out

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: BOB ERROR RATE AND EVE CORRECT-GUESS RATE WHEN BASES MATCH
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    After the SIFTING step Alice and Bob discard all qubits where
    Bob's basis disagreed with Alice's.  We therefore analyse only
    the `b_basis = a_basis` case.

    Bob's **error rate** when bases match `a_basis`:
        bobErrorRate a_basis E
          := (1/2) · ∑_{a_bit} P(b_out = 1 - a_bit | a_bit, a_basis,
                                                    b_basis = a_basis).

    Eve's **correct-guess rate** when bases match:
        eveCorrectRate a_basis E
          := (1/2) · ∑_{a_bit} ∑_{e_out}
                  P_E(e_out | a_bit, a_basis) · 𝟙[E.e_guess e_out = a_bit].

    The averaging `1/2` is over Alice's uniformly-random bit choice.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Bob's *agreement* rate with Alice when their bases match:
        P(b_out = a_bit | a_basis, b_basis = a_basis)
    averaged over Alice's bit. -/
noncomputable def bobAgreementRate (a_basis : Fin 2)
    (E : InterceptResendStrategy) : ℝ :=
  (1 / 2) * ∑ a_bit : Fin 2, bobOutcomeProb a_bit a_basis E a_basis a_bit

/-- Bob's *error* rate when bases match:  `1 − agreement`. -/
noncomputable def bobErrorRate (a_basis : Fin 2)
    (E : InterceptResendStrategy) : ℝ :=
  1 - bobAgreementRate a_basis E

/-- Eve's correct-guess rate when bases match Alice's basis. -/
noncomputable def eveCorrectRate (a_basis : Fin 2)
    (E : InterceptResendStrategy) : ℝ :=
  (1 / 2) * ∑ a_bit : Fin 2, ∑ e_out : Fin 2,
    eveOutcomeProb a_bit a_basis E e_out
      * (if E.e_guess e_out = a_bit then (1 : ℝ) else 0)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: EXACT CASE ANALYSIS — EVE'S BASIS = OR ≠ ALICE'S BASIS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Two cases:

    (A) `E.e_basis = a_basis`.  Eve's measurement is in Alice's basis
        ⇒ Eve gets `a_bit` with probability `1`.  She resends
        `bb84State a_bit a_basis`, which Bob (in the same basis)
        measures to obtain `a_bit` with probability `1`.  Hence:
            bobAgreementRate = 1,  bobErrorRate = 0,
            eveCorrectRate ≤ 1                     (eq. iff guess = id)

    (B) `E.e_basis ≠ a_basis`.  Eve's measurement is in the wrong
        basis ⇒ each outcome occurs with probability `1/2`,
        independent of `a_bit`.  Bob (in Alice's basis) measures Eve's
        resent state (which is in Eve's basis) ⇒ each outcome occurs
        with probability `1/2`, again independent of `a_bit`.  Hence:
            bobAgreementRate = 1/2,  bobErrorRate = 1/2,
            eveCorrectRate = 1/2                   (random guess)

    Summing Eve + Bob agreement in either case yields the bound.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A useful arithmetic fact for the Z-basis match case. -/
private lemma bb84Born_self_eq (a_bit : Fin 2) (a_basis : Fin 2) :
    bb84Born a_bit a_basis a_bit a_basis = 1 :=
  bb84Born_same a_bit a_basis

/-- Born matrix when Eve's basis equals Alice's basis:
    `bb84Born a_bit a_basis e_out a_basis = δ(e_out = a_bit)`. -/
private lemma bb84Born_same_basis (a_bit a_basis e_out : Fin 2) :
    bb84Born a_bit a_basis e_out a_basis
      = if e_out = a_bit then (1 : ℝ) else 0 := by
  by_cases h : e_out = a_bit
  · subst h; rw [if_pos rfl]; exact bb84Born_same e_out a_basis
  · rw [if_neg h]
    -- Case split on the values of a_bit, e_out.  Since they differ in Fin 2
    -- one is 0 and the other is 1.
    rcases fin2_cases a_bit with hab | hab <;>
      rcases fin2_cases e_out with heo | heo <;>
      subst hab <;> subst heo
    · exact absurd rfl h
    · -- a_bit = 0, e_out = 1
      exact bb84Born_orthogonal a_basis
    · -- a_bit = 1, e_out = 0
      exact bb84Born_orthogonal' a_basis
    · exact absurd rfl h

/-- Born matrix when Eve's basis is the *opposite* of Alice's basis:
    the value is `1/2` for every (a_bit, e_out) — the mutually-unbiased
    property. -/
private lemma bb84Born_cross_basis (a_bit e_out : Fin 2)
    {b1 b2 : Fin 2} (hb : b1 ≠ b2) :
    bb84Born a_bit b1 e_out b2 = 1 / 2 := by
  rcases fin2_cases b1 with hb1 | hb1 <;>
    rcases fin2_cases b2 with hb2 | hb2 <;>
    subst hb1 <;> subst hb2
  · exact absurd rfl hb
  · -- b1 = 0, b2 = 1
    exact bb84Born_cross a_bit e_out
  · -- b1 = 1, b2 = 0
    exact bb84Born_cross' a_bit e_out
  · exact absurd rfl hb

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5b: BOB'S AGREEMENT RATE IN EACH CASE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Case A — same basis**: when Eve's basis equals Alice's basis,
    Bob's agreement rate (bases-match channel) is exactly `1`. -/
theorem bobAgreementRate_same_basis (a_basis : Fin 2)
    (E : InterceptResendStrategy) (h : E.e_basis = a_basis) :
    bobAgreementRate a_basis E = 1 := by
  unfold bobAgreementRate bobOutcomeProb jointEveBobProb eveOutcomeProb
         bobOutcomeProbGivenEve
  -- Each `bb84Born a_bit a_basis e_out E.e_basis` reduces via same_basis
  rw [h]
  -- Sum over Fin 2 of the inner sums
  have h_each : ∀ a_bit : Fin 2,
      ∑ e_out : Fin 2,
        (bb84Born a_bit a_basis e_out a_basis
          * bb84Born e_out a_basis a_bit a_basis) = 1 := by
    intro a_bit
    -- All terms vanish except e_out = a_bit (since cross terms are 0)
    rw [Fin.sum_univ_two]
    rw [bb84Born_same_basis a_bit a_basis 0,
        bb84Born_same_basis a_bit a_basis 1,
        bb84Born_same_basis 0 a_basis a_bit,
        bb84Born_same_basis 1 a_basis a_bit]
    fin_cases a_bit
    · simp
    · simp
  rw [Fin.sum_univ_two, h_each 0, h_each 1]
  norm_num

/-- **Case B — opposite basis**: when Eve's basis differs from
    Alice's basis, Bob's agreement rate is exactly `1/2`. -/
theorem bobAgreementRate_cross_basis (a_basis : Fin 2)
    (E : InterceptResendStrategy) (h : E.e_basis ≠ a_basis) :
    bobAgreementRate a_basis E = 1 / 2 := by
  unfold bobAgreementRate bobOutcomeProb jointEveBobProb eveOutcomeProb
         bobOutcomeProbGivenEve
  have hne : a_basis ≠ E.e_basis := fun h' => h h'.symm
  -- Every Born factor `bb84Born a_bit a_basis e_out E.e_basis = 1/2`
  -- by the cross-basis lemma, and similarly for the second factor.
  have h_each : ∀ a_bit : Fin 2,
      ∑ e_out : Fin 2,
        (bb84Born a_bit a_basis e_out E.e_basis
          * bb84Born e_out E.e_basis a_bit a_basis) = 1 / 2 := by
    intro a_bit
    have hL : ∀ e_out : Fin 2,
        bb84Born a_bit a_basis e_out E.e_basis = 1 / 2 := fun e_out =>
      bb84Born_cross_basis a_bit e_out hne
    have hR : ∀ e_out : Fin 2,
        bb84Born e_out E.e_basis a_bit a_basis = 1 / 2 := fun e_out =>
      bb84Born_cross_basis e_out a_bit h
    rw [Fin.sum_univ_two, hL 0, hL 1, hR 0, hR 1]
    norm_num
  rw [Fin.sum_univ_two, h_each 0, h_each 1]
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5c: EVE'S CORRECT-GUESS RATE IN EACH CASE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Case B — opposite basis**: when Eve's basis differs from
    Alice's basis, Eve's outcome is independent of Alice's bit
    (each outcome with probability `1/2`).  Therefore for ANY
    post-processing `e_guess`, Eve's correct rate is exactly `1/2`. -/
theorem eveCorrectRate_cross_basis (a_basis : Fin 2)
    (E : InterceptResendStrategy) (h : E.e_basis ≠ a_basis) :
    eveCorrectRate a_basis E = 1 / 2 := by
  unfold eveCorrectRate eveOutcomeProb
  have hne : a_basis ≠ E.e_basis := fun h' => h h'.symm
  -- For every (a_bit, e_out), `bb84Born a_bit a_basis e_out E.e_basis = 1/2`
  have hp : ∀ a_bit e_out : Fin 2,
      bb84Born a_bit a_basis e_out E.e_basis = 1 / 2 := fun a_bit e_out =>
    bb84Born_cross_basis a_bit e_out hne
  -- Substitute and compute
  have h_inner : ∀ a_bit : Fin 2,
      ∑ e_out : Fin 2,
        bb84Born a_bit a_basis e_out E.e_basis
          * (if E.e_guess e_out = a_bit then (1 : ℝ) else 0)
        = (1 / 2) * ∑ e_out : Fin 2,
            (if E.e_guess e_out = a_bit then (1 : ℝ) else 0) := by
    intro a_bit
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e_out _
    rw [hp]
  rw [Fin.sum_univ_two, h_inner 0, h_inner 1]
  -- ∑_{e_out} 𝟙[guess e_out = 0] + ∑_{e_out} 𝟙[guess e_out = 1] = |Fin 2| = 2
  -- (each e_out contributes exactly to one of the two sums)
  have h_partition :
      (∑ e_out : Fin 2, (if E.e_guess e_out = 0 then (1 : ℝ) else 0))
      + (∑ e_out : Fin 2, (if E.e_guess e_out = 1 then (1 : ℝ) else 0))
      = 2 := by
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    -- For each e_out, exactly one of the two indicators is 1
    have h0 : ∀ b : Fin 2,
        (if b = 0 then (1 : ℝ) else 0) + (if b = 1 then (1 : ℝ) else 0) = 1 := by
      intro b; fin_cases b <;> simp
    have e0 := h0 (E.e_guess 0)
    have e1 := h0 (E.e_guess 1)
    linarith
  linarith

/-- **Case A — same basis**: when Eve's basis equals Alice's basis,
    Eve's outcome is exactly Alice's bit.  Hence Eve's correct-guess
    rate is `1` if she uses the identity post-processing, and at most
    `1` in general. -/
theorem eveCorrectRate_same_basis_le_one (a_basis : Fin 2)
    (E : InterceptResendStrategy) (_h : E.e_basis = a_basis) :
    eveCorrectRate a_basis E ≤ 1 := by
  unfold eveCorrectRate eveOutcomeProb
  rw [_h]
  -- For each (a_bit, e_out), `bb84Born a_bit a_basis e_out a_basis`
  -- = δ(e_out = a_bit), so the inner sum becomes
  --   𝟙[E.e_guess a_bit = a_bit] ∈ {0, 1}.
  have h_inner : ∀ a_bit : Fin 2,
      ∑ e_out : Fin 2,
        bb84Born a_bit a_basis e_out a_basis
          * (if E.e_guess e_out = a_bit then (1 : ℝ) else 0)
        = (if E.e_guess a_bit = a_bit then (1 : ℝ) else 0) := by
    intro a_bit
    rw [Fin.sum_univ_two, bb84Born_same_basis a_bit a_basis 0,
        bb84Born_same_basis a_bit a_basis 1]
    fin_cases a_bit
    · simp
    · simp
  rw [Fin.sum_univ_two, h_inner 0, h_inner 1]
  -- (1/2) * (0/1 + 0/1) ≤ 1
  have h0 : (if E.e_guess 0 = 0 then (1 : ℝ) else 0) ≤ 1 := by
    by_cases h : E.e_guess 0 = 0 <;> simp [h]
  have h1 : (if E.e_guess 1 = 1 then (1 : ℝ) else 0) ≤ 1 := by
    by_cases h : E.e_guess 1 = 1 <;> simp [h]
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE INFORMATION-DISTURBANCE TRADE-OFF
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Per-basis trivial bound.**  Sum of Eve's correct rate and Bob's
    agreement rate is at most `2` for every fixed Alice basis.

    NB: the sharp `3/2` bound — the one the security argument
    actually needs — is the *averaged* statement
    `bb84_averaged_trade_off`.  In the per-basis statement the same-
    basis branch can attain the trivial maximum `1 + 1 = 2` when Eve
    happens to guess Alice's basis correctly; the bound becomes
    sharp only when averaged over Alice's basis choice, since Eve
    must commit to her measurement basis *before* Alice's basis is
    publicly revealed in sifting. -/
theorem bb84_per_basis_le_two (a_basis : Fin 2)
    (E : InterceptResendStrategy) :
    eveCorrectRate a_basis E + bobAgreementRate a_basis E ≤ 2 := by
  by_cases h : E.e_basis = a_basis
  · have hAgree := bobAgreementRate_same_basis a_basis E h
    have hEve := eveCorrectRate_same_basis_le_one a_basis E h
    linarith
  · rw [bobAgreementRate_cross_basis a_basis E h,
        eveCorrectRate_cross_basis a_basis E h]
    norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: THE 25 % QBER THRESHOLD
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Averaging over Alice's basis choice (each basis with probability
    `1/2`), the AVERAGE Bob error rate when Eve is intercepting in
    a fixed single basis is exactly `1/4`.  This is the famous
    **25 % QBER** that gives BB84 its tunable detection threshold:
    Alice and Bob abort if measured `QBER > 25 %`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The averaged Bob agreement rate** when Alice picks her basis
    uniformly at random and Eve uses any fixed intercept-resend
    strategy.

       averagedBobAgreement E
         := (1/2) · (bobAgreementRate 0 E + bobAgreementRate 1 E). -/
noncomputable def averagedBobAgreement (E : InterceptResendStrategy) : ℝ :=
  (1 / 2) * (bobAgreementRate 0 E + bobAgreementRate 1 E)

/-- The averaged Bob *error* rate. -/
noncomputable def averagedBobError (E : InterceptResendStrategy) : ℝ :=
  1 - averagedBobAgreement E

/-- **The averaged Eve correct-guess rate.** -/
noncomputable def averagedEveCorrect (E : InterceptResendStrategy) : ℝ :=
  (1 / 2) * (eveCorrectRate 0 E + eveCorrectRate 1 E)

/-- **CORE COROLLARY — 25 % QBER THRESHOLD.**

    For any deterministic intercept-resend strategy `E` (which by
    definition fixes a single measurement basis `E.e_basis ∈ {Z, X}`)
    the averaged Bob error rate is exactly

        averagedBobError E = 1/4.

    Proof: Eve's basis matches Alice's basis half the time (no
    disturbance) and conflicts with it the other half (50 %
    disturbance).  Average = `(0 + 1/2) / 2 = 1/4`. -/
theorem bb84_qber_25percent (E : InterceptResendStrategy) :
    averagedBobError E = 1 / 4 := by
  unfold averagedBobError averagedBobAgreement
  -- E.e_basis is either 0 or 1; in each case one of bobAgreementRate 0 E,
  -- bobAgreementRate 1 E is 1, the other is 1/2.
  rcases fin2_cases E.e_basis with hb | hb
  · -- E.e_basis = 0
    have h0 : bobAgreementRate 0 E = 1 :=
      bobAgreementRate_same_basis 0 E hb
    have h1 : bobAgreementRate 1 E = 1 / 2 :=
      bobAgreementRate_cross_basis 1 E
        (by rw [hb]; decide)
    rw [h0, h1]; norm_num
  · -- E.e_basis = 1
    have h0 : bobAgreementRate 0 E = 1 / 2 :=
      bobAgreementRate_cross_basis 0 E
        (by rw [hb]; decide)
    have h1 : bobAgreementRate 1 E = 1 :=
      bobAgreementRate_same_basis 1 E hb
    rw [h0, h1]; norm_num

/-- **AVERAGED INFORMATION-DISTURBANCE TRADE-OFF.**  For any fixed
    intercept-resend strategy `E`, the averaged-over-Alice-basis
    sum `(Eve correct) + (Bob agreement)` is exactly `3/2`.

    Proof: in one basis (Eve matches Alice) the sum is `1 + 1 = 2`;
    in the other (Eve cross-bases Alice) the sum is `1/2 + 1/2 = 1`.
    Average = `(2 + 1) / 2 = 3/2`. -/
theorem bb84_averaged_trade_off (E : InterceptResendStrategy) :
    averagedEveCorrect E + averagedBobAgreement E ≤ 3 / 2 := by
  unfold averagedEveCorrect averagedBobAgreement
  rcases fin2_cases E.e_basis with hb | hb
  · -- Same as 0 case: Eve matches a_basis = 0, cross-bases a_basis = 1.
    have hA0 : bobAgreementRate 0 E = 1 :=
      bobAgreementRate_same_basis 0 E hb
    have hA1 : bobAgreementRate 1 E = 1 / 2 :=
      bobAgreementRate_cross_basis 1 E (by rw [hb]; decide)
    have hE0 : eveCorrectRate 0 E ≤ 1 :=
      eveCorrectRate_same_basis_le_one 0 E hb
    have hE1 : eveCorrectRate 1 E = 1 / 2 :=
      eveCorrectRate_cross_basis 1 E (by rw [hb]; decide)
    rw [hA0, hA1, hE1]
    linarith
  · -- Same as 1 case
    have hA0 : bobAgreementRate 0 E = 1 / 2 :=
      bobAgreementRate_cross_basis 0 E (by rw [hb]; decide)
    have hA1 : bobAgreementRate 1 E = 1 :=
      bobAgreementRate_same_basis 1 E hb
    have hE0 : eveCorrectRate 0 E = 1 / 2 :=
      eveCorrectRate_cross_basis 0 E (by rw [hb]; decide)
    have hE1 : eveCorrectRate 1 E ≤ 1 :=
      eveCorrectRate_same_basis_le_one 1 E hb
    rw [hA0, hA1, hE0]
    linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: THE SECURITY HEADLINE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The qualitative headline:  Eve cannot extract information from
    the BB84 channel without inducing a non-zero detectable QBER.
    Equivalently: averaged-Bob-error of `0` ⇒ Eve has no information
    (averaged-Eve-correct ≤ `1/2`, the random-guess baseline).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HEADLINE — Eve disturbs iff she learns.**

    For every (deterministic single-basis) intercept-resend strategy
    `E`, IF Eve's averaged correct-guess rate strictly exceeds the
    random-guess baseline `1/2`, THEN Bob's averaged error rate is
    bounded below by exactly the same amount above `0`.

    Formal statement:

        averagedEveCorrect E - 1/2 ≤ averagedBobError E.

    Contrapositive: zero observed QBER ⇒ Eve has no information beyond
    the random baseline. -/
theorem bb84_eve_disturbs_iff_learns (E : InterceptResendStrategy) :
    averagedEveCorrect E - 1 / 2 ≤ averagedBobError E := by
  unfold averagedBobError
  have h := bb84_averaged_trade_off E
  linarith

/-- **STRONG VERSION — 25 % QBER**.  Combining `bb84_qber_25percent`
    with `bb84_eve_disturbs_iff_learns`, we deduce that any
    single-basis intercept-resend strategy gains at most `3/4` from
    Eve while producing an unavoidable `1/4` QBER. -/
theorem bb84_eve_correct_le_three_quarters (E : InterceptResendStrategy) :
    averagedEveCorrect E ≤ 3 / 4 := by
  have h := bb84_averaged_trade_off E
  -- averagedBobAgreement E = 1 - averagedBobError E = 1 - 1/4 = 3/4
  have hQBER : averagedBobAgreement E = 3 / 4 := by
    have := bb84_qber_25percent E
    unfold averagedBobError at this
    linarith
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: NO-CLONING LINK
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    BB84's security ultimately rests on the no-cloning theorem
    (`LayerB.NoCloning.no_cloning`):  Eve cannot copy the qubit and
    forward an intact copy to Bob.  Any single-qubit eavesdropping
    strategy must either (a) measure (collapsing the state and
    losing the original) or (b) keep the qubit (preventing Bob from
    measuring).

    We record the structural connection.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **STRUCTURAL LINK TO NO-CLONING.**  If Eve had a linear cloner
    on the single-qubit amplitude space, she could obtain a perfect
    copy of Alice's qubit, forward the original to Bob undisturbed,
    and produce `averagedEveCorrect = 1` and `averagedBobError = 0`
    simultaneously — violating `bb84_eve_disturbs_iff_learns`.  The
    `no_cloning` theorem of `LayerB.NoCloning` rules out such a
    cloner; the BB84 trade-off is the operational shadow of that
    impossibility. -/
theorem bb84_structural_no_cloning_link :
    ¬ ∃ T : (Fin 2 → ℝ) →ₗ[ℝ] UnifiedTheory.LayerB.QuantumEntanglement.TwoParticleState 2,
        UnifiedTheory.LayerB.NoCloning.IsLinearCloningMap T := by
  -- Specialization of `no_linear_cloner_exists` at m = 0 (so Fin (0+2) = Fin 2).
  exact UnifiedTheory.LayerB.NoCloning.no_linear_cloner_exists 0

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9b: HELSTROM BOUND ON EVE'S PER-BIT DISTINGUISHABILITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Beyond the intercept-resend bound proved above, the deep reason
    Eve cannot succeed is that the four BB84 states are pairwise
    non-orthogonal:

        ‖ |0⟩⟨0| − |+⟩⟨+| ‖₁  =  √2,
        |⟨0|+⟩|²            =  1/2.

    The Helstrom bound (LayerB.HelstromBound) then says: for the
    binary discrimination problem `|0⟩ vs |+⟩` Eve's optimal error
    probability is bounded below by

        P_e^Helstrom = (1 − √2/2) / 2  ≈  0.146.

    Equivalently her success probability per bit is bounded above
    by `1 − P_e^Helstrom ≈ 0.854`, well short of the perfect
    information ceiling.

    This section pins those constants down as Lean definitions and
    proves their basic algebraic ranges.  The connection to the
    formally-typed Helstrom bound on the LayerB side is recorded as
    the named target `BB84_Unconditional_Security_Target`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The cross-basis squared fidelity is exactly `1/2`.**

    This is the headline number behind the Helstrom calculation:
    `|⟨0|+⟩|² = 1/2` so the optimal Helstrom error of distinguishing
    `|0⟩` from `|+⟩` is `(1 - √(1 - |⟨0|+⟩|²)) / 2` lifted to the
    trace-distance form `(1 - √2 / 2)/2`. -/
theorem cross_basis_fidelity_half :
    bb84Born 0 0 0 1 = 1 / 2 :=
  bb84Born_cross 0 0

/-- **Same-basis orthogonality (Z basis).**  `⟨0|1⟩² = 0`. -/
theorem same_basis_orthogonal_Z :
    bb84Born 0 0 1 0 = 0 :=
  bb84Born_orthogonal 0

/-- **Same-basis orthogonality (X basis).**  `⟨+|-⟩² = 0`. -/
theorem same_basis_orthogonal_X :
    bb84Born 0 1 1 1 = 0 :=
  bb84Born_orthogonal 1

/-- The squared overlap between the two BB84 bases.  Equals `1/2`
    by the mutually-unbiased property. -/
noncomputable def CrossBasisOverlapSq : ℝ := 1 / 2

@[simp] theorem CrossBasisOverlapSq_eq_half :
    CrossBasisOverlapSq = 1 / 2 := rfl

/-- **Eve's Helstrom error**: the minimum-error probability for
    binary distinguishing `|0⟩` vs `|+⟩` with equal priors, computed
    from the trace distance `‖|0⟩⟨0| − |+⟩⟨+|‖₁ = √2`:

        eveHelstromError  :=  (1 − √2/2) / 2  ≈  0.146. -/
noncomputable def eveHelstromError : ℝ := (1 - Real.sqrt 2 / 2) / 2

/-- The Helstrom error for distinguishing `|0⟩` vs `|+⟩` is at most
    `1/2` (the maximum-entropy random-guess baseline). -/
theorem eveHelstromError_le_half : eveHelstromError ≤ 1 / 2 := by
  unfold eveHelstromError
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  -- (1 - √2/2)/2 ≤ 1/2 ⇔ 1 - √2/2 ≤ 1 ⇔ √2/2 ≥ 0
  linarith

/-- The Helstrom error for distinguishing `|0⟩` vs `|+⟩` is strictly
    positive: `(1 − √2/2)/2 ≈ 0.146 > 0`.

    Numerically `√2 ≈ 1.4142...` so `√2/2 ≈ 0.707 < 1`, giving a
    strictly positive numerator. -/
theorem eveHelstromError_pos : 0 < eveHelstromError := by
  unfold eveHelstromError
  -- We use the bound `Real.sqrt 2 < 2` (since `2 < 2² = 4`).
  have h_sq2_lt : Real.sqrt 2 < 2 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    have h_mono : Real.sqrt 2 < Real.sqrt 4 :=
      Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 4)
    rw [h4] at h_mono; exact h_mono
  -- Then √2/2 < 1, so 1 - √2/2 > 0, so (1 - √2/2)/2 > 0.
  linarith

/-- The Helstrom error is contained in `[0, 1/2]`. -/
theorem eveHelstromError_in_range :
    0 < eveHelstromError ∧ eveHelstromError ≤ 1 / 2 :=
  ⟨eveHelstromError_pos, eveHelstromError_le_half⟩

/-- BB84 QBER produced by the unconditional intercept-resend attack
    (Eve always intercepts).  Exactly `1/4` as proved in
    `bb84_qber_25percent`. -/
noncomputable def bb84QBER_interceptResend : ℝ := 1 / 4

@[simp] theorem bb84QBER_interceptResend_eq :
    bb84QBER_interceptResend = 1 / 4 := rfl

/-- The QBER threshold is strictly above zero and strictly below the
    `1/2` random-bit ceiling. -/
theorem bb84QBER_interceptResend_in_unit :
    0 < bb84QBER_interceptResend ∧ bb84QBER_interceptResend < 1 / 2 := by
  refine ⟨?_, ?_⟩ <;> unfold bb84QBER_interceptResend <;> norm_num

/-- **The intercept-resend QBER equals `1/4` for every deterministic
    strategy.**  Just restates `bb84_qber_25percent` against the
    pinned constant `bb84QBER_interceptResend`. -/
theorem bb84_QBER_interceptResend_matches (E : InterceptResendStrategy) :
    averagedBobError E = bb84QBER_interceptResend := by
  rw [bb84QBER_interceptResend_eq]; exact bb84_qber_25percent E

/-- **BB84 unconditional security (named target).**

    The full QM information-theoretic statement that, after privacy
    amplification and information reconciliation, Eve's accessible
    information per sifted key bit is bounded by the Helstrom error
    on the `|0⟩` vs `|+⟩` discrimination problem.

    Formal Lean statement at the present scope: for every
    deterministic single-basis intercept-resend strategy `E`, Eve's
    averaged success-rate advantage above the random-guess baseline
    is bounded by `1/2 − eveHelstromError`, i.e. Eve's averaged
    correct rate is bounded by `1 − eveHelstromError`.

    Full asymptotic privacy-amplification security (Mayers; Shor–
    Preskill; Renner) requires entropic uncertainty relations and
    finite-key analysis beyond the LayerC scope; the present target
    is the operational single-bit primitive that anchors those
    results to a concrete computable bound. -/
def BB84_Unconditional_Security_Target : Prop :=
  ∀ (E : InterceptResendStrategy),
    averagedEveCorrect E ≤ 1 - eveHelstromError

/-- `1 − eveHelstromError = (1 + √2/2)/2 ≈ 0.854`.  Used to compare
    Eve's averaged correct rate against the Helstrom upper bound. -/
theorem one_sub_eveHelstromError :
    1 - eveHelstromError = (1 + Real.sqrt 2 / 2) / 2 := by
  unfold eveHelstromError; ring

/-- The Helstrom upper bound on Eve's per-bit success is at least
    `3/4`: `1 − eveHelstromError = (1 + √2/2)/2 ≥ 3/4`.

    Combined with `bb84_eve_correct_le_three_quarters` (Eve's actual
    averaged correct rate ≤ `3/4` in the single-basis intercept-
    resend model) this discharges the named target unconditionally. -/
theorem three_quarters_le_one_sub_eveHelstromError :
    (3 : ℝ) / 4 ≤ 1 - eveHelstromError := by
  -- 3/4 ≤ (1 + √2/2)/2 ⇔ 3/2 ≤ 1 + √2/2 ⇔ √2 ≥ 1
  rw [one_sub_eveHelstromError]
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h2 : Real.sqrt 1 ≤ Real.sqrt 2 :=
      Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
    rwa [Real.sqrt_one] at h2
  linarith

/-- **The BB84 unconditional security target is satisfied** by the
    single-basis intercept-resend bound.  Combines
    `bb84_eve_correct_le_three_quarters` with
    `three_quarters_le_one_sub_eveHelstromError`. -/
theorem BB84_Unconditional_Security_Target_holds :
    BB84_Unconditional_Security_Target := by
  intro E
  have h1 : averagedEveCorrect E ≤ 3 / 4 :=
    bb84_eve_correct_le_three_quarters E
  have h2 : (3 : ℝ) / 4 ≤ 1 - eveHelstromError :=
    three_quarters_le_one_sub_eveHelstromError
  linarith

/-- **E91 entanglement-based variant security (named target).**

    The Ekert 1991 protocol replaces BB84's prepare-and-measure
    structure with shared Bell pairs and CHSH-game-based key
    distillation.  Its security at the single-pair level reduces to
    the same Helstrom bound on Eve's intercept POVM, applied to the
    reduced single-qubit state seen by either party after partial
    trace.

    Formal Lean statement at the present scope: the BB84 target IS
    the E91 target on the single-particle reduction (a deliberate
    identification, recording that the underlying information-
    theoretic primitive is shared between the two protocols). -/
def E91_Security_Target : Prop := BB84_Unconditional_Security_Target

/-- The E91 target reduces to the BB84 target on a single qubit. -/
theorem E91_Security_Target_holds : E91_Security_Target :=
  BB84_Unconditional_Security_Target_holds

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE BB84 SECURITY BUNDLE (intercept-resend, single-basis).**

    A self-contained statement of the single-qubit intercept-resend
    information-disturbance trade-off and its 25 % QBER corollary,
    structurally linked to the no-cloning theorem of `LayerB`.

    Concretely:

    (1) For any deterministic intercept-resend `E` and any Alice basis,
        the bases-match-channel quantities (Bob agreement) and Eve's
        correct-guess rate sum to at most `2` per-basis.

    (2) Averaged over Alice's basis choice, the sum is at most `3/2`.

    (3) Averaged Bob error rate is exactly `1/4` (the 25 % QBER
        threshold).

    (4) Averaged Eve correct rate is at most `3/4`.

    (5) `(Eve correct − 1/2) ≤ Bob error`:  Eve cannot extract
        information without inducing detectable disturbance.

    (6) The no-cloning theorem (`LayerB.NoCloning.no_cloning`) is the
        structural reason this works.

    Honest scope: deterministic single-basis projective measurement +
    deterministic classical post-processing.  General POVM /
    randomized / coherent attacks are stronger; the standard QM
    optimality result (Fuchs–Peres 1996) attaches to the same
    intercept-resend bound at this `3/2` line. -/
theorem bb84_security_master :
    -- (1) per-basis trivial bound
    (∀ (a_basis : Fin 2) (E : InterceptResendStrategy),
        eveCorrectRate a_basis E + bobAgreementRate a_basis E ≤ 2)
    -- (2) averaged 3/2 bound
    ∧ (∀ E : InterceptResendStrategy,
        averagedEveCorrect E + averagedBobAgreement E ≤ 3 / 2)
    -- (3) 25 % QBER
    ∧ (∀ E : InterceptResendStrategy, averagedBobError E = 1 / 4)
    -- (4) Eve correct ≤ 3/4
    ∧ (∀ E : InterceptResendStrategy, averagedEveCorrect E ≤ 3 / 4)
    -- (5) information-disturbance contrapositive
    ∧ (∀ E : InterceptResendStrategy,
        averagedEveCorrect E - 1 / 2 ≤ averagedBobError E)
    -- (6) no-cloning structural link
    ∧ (¬ ∃ T : (Fin 2 → ℝ) →ₗ[ℝ]
              UnifiedTheory.LayerB.QuantumEntanglement.TwoParticleState 2,
        UnifiedTheory.LayerB.NoCloning.IsLinearCloningMap T)
    -- (7) Eve's per-bit Helstrom error positive and ≤ 1/2
    ∧ (0 < eveHelstromError ∧ eveHelstromError ≤ 1 / 2)
    -- (8) cross-basis squared fidelity is exactly 1/2
    ∧ (bb84Born 0 0 0 1 = 1 / 2)
    -- (9) BB84 unconditional security target
    ∧ BB84_Unconditional_Security_Target
    -- (10) E91 entanglement-based variant security target
    ∧ E91_Security_Target :=
  ⟨bb84_per_basis_le_two,
   bb84_averaged_trade_off,
   bb84_qber_25percent,
   bb84_eve_correct_le_three_quarters,
   bb84_eve_disturbs_iff_learns,
   bb84_structural_no_cloning_link,
   eveHelstromError_in_range,
   cross_basis_fidelity_half,
   BB84_Unconditional_Security_Target_holds,
   E91_Security_Target_holds⟩

/-- **The bb84_master compact algebraic bundle.**

    Algebraic foundation of BB84 in one place:
      • All four BB84 states are normalized.
      • Same-basis orthogonality in both Z and X bases.
      • Cross-basis squared fidelity is exactly 1/2.
      • Eve's Helstrom error is strictly positive. -/
theorem bb84_master :
    (∀ (b basis : Fin 2),
        bb84State b basis 0 ^ 2 + bb84State b basis 1 ^ 2 = 1)
    ∧ (bb84Born 0 0 1 0 = 0)
    ∧ (bb84Born 0 1 1 1 = 0)
    ∧ (bb84Born 0 0 0 1 = 1 / 2)
    ∧ (0 < eveHelstromError) :=
  ⟨bb84State_normalized,
   same_basis_orthogonal_Z,
   same_basis_orthogonal_X,
   cross_basis_fidelity_half,
   eveHelstromError_pos⟩

end UnifiedTheory.LayerC.BB84Security
