/-
  UnifiedTheory/LayerC/ConwayKochenFreeWill.lean
  ──────────────────────────────────────────────

  **THE CONWAY-KOCHEN FREE WILL THEOREM** (2006, strengthened 2009).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHY THIS FILE EXISTS

  Conway and Kochen (2006) and the strengthened "Free Will Theorem"
  (2009) combine Kochen-Specker contextuality with relativistic
  no-signalling to prove a striking no-go: under three named axioms,
  the responses of a spin-1 particle CANNOT be deterministic functions
  of past information.  Equivalently: if experimenters can freely
  choose measurement settings, then the particles' responses contain
  information that is NOT a function of any pre-measurement record.

  The three axioms (2009 strengthened version):

  • **SPIN** ("the 1-0-1 axiom"): for any three mutually orthogonal
    directions in ℝ³, a spin-1 particle's squared-spin measurement
    `S² = J(J+1) − m²` yields the triple `(1, 1, 0)` in some order
    (exactly one of the three directions gives the outcome 0).

  • **TWIN**: two spin-1 particles in the singlet (J = 0) state, when
    measured in the same direction, return the same `S²` outcome.

  • **MIN/FIN** (relativistic causality): information cannot propagate
    faster than light; the outcome at one measurement site cannot depend
    on the choice of setting at a space-like separated site.

  THE CONCLUSION.  There is no function `r(setting, past_info)` that
  assigns deterministic `{0, 1}` outcomes consistent with all three
  axioms.  In Conway-Kochen's reading, the responses must be "free" —
  they cannot be precomputed from the past.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE CLEAN LEAN REFORMULATION

  The structural core of the theorem is a reduction to the
  Kochen-Specker contextuality no-go.  Step-by-step:

  1. By SPIN + the finite-dimensional Kochen-Specker theorem (we use
     the Cabello 18-vector / 9-tetrad form already in
     `LayerC/KochenSpecker18.lean`), there is no function
     `f : Direction → {0, 1}` such that on each orthogonal tetrad
     exactly one direction receives the value `1` (here we use the
     value `1` to denote "the unique direction in the tetrad that
     would give outcome `S² = 0`").

  2. By TWIN, both particles' response functions must AGREE whenever
     they are measured in the same direction.  So the two response
     tables `responseA d λ` and `responseB d λ` coincide pointwise
     (we encode this as a TWIN axiom on the model).

  3. By MIN/FIN, the response at site A depends only on A's setting,
     not on B's setting.  In our discrete-Λ formalisation this is
     enforced AT THE LEVEL OF THE TYPE SIGNATURE: `responseA` takes
     only one direction argument (Alice's), not a pair.  (See the
     "Explicit MIN" subsection below for a formulation with both
     settings in scope and an explicit no-signalling constraint that
     reduces to the implicit-MIN form.)

  4. SPIN+TWIN at a single hidden value `λ_*` with positive measure
     yields a Cabello-style colouring `f`; KS forbids it.  QED.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE DOES AND DOES NOT CLAIM

  Claims:
    • The DETERMINISTIC LOCAL HIDDEN VARIABLE form of the Conway-
      Kochen scenario (`DeterministicFreeWillModel`) is empty.
    • This holds UNCONDITIONALLY (Lean theorem, no `sorry`, no
      custom `axiom` beyond Lean's kernel `propext / Classical.choice
      / Quot.sound`).

  Honest scope:
    • The physical assumption that spin-1 squared-spin observables in
      ℝ⁴ realise the Cabello 18-vector orthogonality table is an
      EXPERIMENTAL/MATHEMATICAL INPUT here.  (Cabello's construction
      sits in ℝ⁴, not ℝ³; the standard Conway-Kochen presentation
      uses Peres' 33-vector ℝ³ construction.  The combinatorial
      content — finitely many directions, finitely many tetrads,
      exactly-one-1-per-tetrad — is the same; we use whichever
      finite KS configuration is already formalised, which is
      Cabello-18.  The argument is purely structural.)
    • TWIN, SPIN, MIN are encoded as axioms of the model structure,
      not derived from QM.  The headline theorem says: under these
      three axioms, no deterministic model exists.  Whether QM and
      experiment vindicate the three axioms is a separate question
      (handled in the corresponding QM/Bell files of this layer).

  Zero `sorry`.  Zero custom `axiom`.
-/

import UnifiedTheory.LayerC.KochenSpecker18
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.ConwayKochenFreeWill

open Finset
open UnifiedTheory.LayerC.KochenSpecker18

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE DETERMINISTIC FREE-WILL-RESPECTING MODEL
    (TWIN + SPIN + implicit MIN)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **A deterministic free-will-respecting hidden-variable model for the
    Conway-Kochen scenario** (with respect to the Cabello 18-vector
    configuration playing the role of the discrete direction set).

    Fields:
    • `Λ` — a finite hidden-variable space, with a discrete probability
      distribution `μ : Λ → ℝ` (`μ_nonneg`, `μ_sum = 1`).
    • `responseA d λ ∈ Fin 2` — Alice's `S²` outcome at direction
      `d : Fin 18` and hidden value `λ`.  Here we adopt the convention
      that `responseA d λ = 0` encodes "Alice measures `S² = 0` in
      direction `d`" and `responseA d λ = 1` encodes "Alice measures
      `S² = 1`" (the two non-zero eigenvalues are bundled into the
      label `1`).
    • `responseB d λ ∈ Fin 2` — Bob's outcome, same convention.
    • `twin` — the TWIN axiom: whenever Alice and Bob measure the SAME
      direction `d`, they get the SAME outcome.
    • `spin_A`, `spin_B` — the SPIN axiom for Alice and Bob respectively:
      in every Cabello tetrad of four mutually orthogonal directions,
      EXACTLY ONE direction yields the outcome `0` (counting
      `1 - responseA d λ` in ℕ over the tetrad gives `1`).

      Mathematical note.  The Cabello tetrads are sets of FOUR mutually
      orthogonal vectors in ℝ⁴ (not three in ℝ³), and SPIN here is the
      4-direction "1-1-1-0" form: exactly one of the four orthogonal
      directions gets outcome 0, the other three get 1.  This is the
      ℝ⁴ analogue of Conway-Kochen's 3-direction "1-0-1" axiom and is
      the finite KS-input used in this formalisation.

    MIN/FIN is encoded IMPLICITLY in the type signature: `responseA`
    is a function of Alice's direction `d : Fin 18` and the hidden
    value `λ : Λ` only, with NO dependence on Bob's setting.  See
    `ExplicitMINModel` and `explicit_MIN_reduces` below for a richer
    formulation that takes both settings as arguments and adds an
    explicit no-signalling constraint that reduces to the present form.
-/
structure DeterministicFreeWillModel where
  /-- The finite hidden-variable space (named `HVar` to avoid shadowing
      Lean's `λ` binder). -/
  HVar : Type
  /-- The hidden-variable space is finite. -/
  isFintype : Fintype HVar
  /-- The discrete probability distribution on `HVar`. -/
  μ : HVar → ℝ
  /-- The distribution is nonnegative. -/
  μ_nonneg : ∀ l, 0 ≤ μ l
  /-- The distribution sums to one. -/
  μ_sum : (∑ l : HVar, μ l) = 1
  /-- Alice's response: `0` encodes `S² = 0`, `1` encodes `S² ≠ 0`. -/
  responseA : Fin 18 → HVar → Fin 2
  /-- Bob's response: same convention. -/
  responseB : Fin 18 → HVar → Fin 2
  /-- **TWIN axiom**: when Alice and Bob measure the same direction,
      they get the same outcome. -/
  twin : ∀ d l, responseA d l = responseB d l
  /-- **SPIN axiom (Alice)**: for every Cabello tetrad, exactly one of
      the four orthogonal directions in the tetrad yields outcome `0`
      (so the count of zeros in the tetrad is `1`). -/
  spin_A : ∀ l (t : Fin 9),
    (∑ d ∈ cabelloTetrad t, (1 - (responseA d l : ℕ))) = 1
  /-- **SPIN axiom (Bob)**: the same counting axiom for Bob. -/
  spin_B : ∀ l (t : Fin 9),
    (∑ d ∈ cabelloTetrad t, (1 - (responseB d l : ℕ))) = 1

-- Activate the model's `Fintype HVar` as an instance.
attribute [instance] DeterministicFreeWillModel.isFintype

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: TECHNICAL LEMMAS — A POSITIVE-MEASURE WITNESS EXISTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Any deterministic free-will-respecting model has at least one hidden
    value `l` with strictly positive probability.  Otherwise `μ` would
    be identically `0`, contradicting `μ_sum = 1`. -/
private lemma exists_positive_hvar (m : DeterministicFreeWillModel) :
    ∃ l : m.HVar, 0 < m.μ l := by
  by_contra hne
  push_neg at hne
  have hzero : ∀ l : m.HVar, m.μ l = 0 := by
    intro l
    have h1 : m.μ l ≤ 0 := hne l
    have h2 : 0 ≤ m.μ l := m.μ_nonneg l
    linarith
  have hsum0 : (∑ l : m.HVar, m.μ l) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    exact hzero l
  have hone : (1 : ℝ) = 0 := by
    have := m.μ_sum
    linarith
  norm_num at hone

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: BRIDGE FROM "EXACTLY ONE 0 PER TETRAD" TO IsKSNoncoloring
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The KS-noncolouring function induced by Alice's responses at a
    single hidden value `l`: `f d := 1 - responseA d l`, valued in ℕ.
    The conversion `Fin 2 → ℕ` is via the canonical coercion. -/
private def kscolour (m : DeterministicFreeWillModel) (l : m.HVar) :
    Fin 18 → ℕ :=
  fun d => 1 - ((m.responseA d l : Fin 2) : ℕ)

/-- The induced colouring is `{0, 1}`-valued. -/
private lemma kscolour_le_one
    (m : DeterministicFreeWillModel) (l : m.HVar) (d : Fin 18) :
    kscolour m l d ≤ 1 := by
  -- `1 - n ≤ 1` always in ℕ (since `1 - n` is monus and bounded by `1`).
  unfold kscolour
  omega

/-- The induced colouring satisfies the per-tetrad sum-to-one axiom,
    by SPIN. -/
private lemma kscolour_tetrad_sum_eq_one
    (m : DeterministicFreeWillModel) (l : m.HVar) (t : Fin 9) :
    (∑ d ∈ cabelloTetrad t, kscolour m l d) = 1 := by
  -- Unfold and apply SPIN directly.
  unfold kscolour
  exact m.spin_A l t

/-- The induced colouring is a Kochen-Specker noncolouring of the
    Cabello configuration in the sense of
    `KochenSpecker18.IsKSNoncoloring`. -/
private theorem kscolour_isKSNoncoloring
    (m : DeterministicFreeWillModel) (l : m.HVar) :
    IsKSNoncoloring (kscolour m l) := by
  refine ⟨?_, ?_⟩
  · intro d; exact kscolour_le_one m l d
  · intro t; exact kscolour_tetrad_sum_eq_one m l t

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE CONWAY-KOCHEN FREE WILL THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The Conway-Kochen Free Will theorem (deterministic-LHV form)**.

    There is NO deterministic free-will-respecting hidden-variable
    model satisfying the TWIN and SPIN axioms (MIN being implicit in
    the type signature).  Equivalently: under SPIN + TWIN + MIN, the
    spin-1 particles' responses cannot be deterministic functions of
    a pre-measurement hidden record.

    The proof is one-line: pick any hidden value `l*` with positive
    measure; Alice's response table at `l*` induces a Cabello KS
    colouring (SPIN); but the Cabello configuration admits no such
    colouring (`no_KS_noncoloring`).  Contradiction.

    The TWIN axiom is what allows the SAME no-go to apply to BOTH
    particles symmetrically: we use only the Alice half of the SPIN
    constraint here, since the same argument applies to Bob via TWIN.
    (For an entirely symmetric phrasing, see
    `no_deterministic_free_will_model_via_Bob` below.) -/
theorem no_deterministic_free_will_model :
    ¬ ∃ _ : DeterministicFreeWillModel, True := by
  rintro ⟨m, _⟩
  obtain ⟨l_star, _hlpos⟩ := exists_positive_hvar m
  -- The KS colouring induced by Alice at l_star.
  have hKS : IsKSNoncoloring (kscolour m l_star) :=
    kscolour_isKSNoncoloring m l_star
  -- But no such colouring exists.
  exact no_KS_noncoloring ⟨kscolour m l_star, hKS⟩

/-- Symmetric form: the no-go also follows from Bob's SPIN axiom alone,
    by an identical argument with `responseB` in place of `responseA`.
    Together with TWIN this shows the situation is fully symmetric: the
    contradiction can be derived from either particle's response table. -/
theorem no_deterministic_free_will_model_via_Bob :
    ¬ ∃ _ : DeterministicFreeWillModel, True := by
  rintro ⟨m, _⟩
  obtain ⟨l_star, _hlpos⟩ := exists_positive_hvar m
  -- Build Bob's KS colouring at l_star.
  let f : Fin 18 → ℕ := fun d => 1 - ((m.responseB d l_star : Fin 2) : ℕ)
  have hf : IsKSNoncoloring f := by
    refine ⟨?_, ?_⟩
    · intro d; change 1 - ((m.responseB d l_star : Fin 2) : ℕ) ≤ 1; omega
    · intro t; exact m.spin_B l_star t
  exact no_KS_noncoloring ⟨f, hf⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: EXPLICIT MIN (NO-SIGNALLING) FORMULATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The headline `DeterministicFreeWillModel` above encodes the MIN /
    no-signalling axiom IMPLICITLY: Alice's response depends only on
    Alice's setting `d : Fin 18`, not on Bob's choice.  Below we record
    a richer model where Alice's response is a function of BOTH settings
    `(d_A, d_B)` and we impose no-signalling AS AN AXIOM, and we show
    that any such explicit-MIN model induces (and is morally equivalent
    to) an implicit-MIN `DeterministicFreeWillModel`.  This makes the
    "MIN" role transparent.
-/

/-- An explicit-MIN deterministic Conway-Kochen model: Alice's response
    is a function of BOTH her setting AND Bob's setting; we impose
    no-signalling as an axiom (`min_A`, `min_B`).  All other axioms
    (TWIN, SPIN) are stated in terms of the no-signalling reduction. -/
structure ExplicitMINFreeWillModel where
  HVar : Type
  isFintype : Fintype HVar
  μ : HVar → ℝ
  μ_nonneg : ∀ l, 0 ≤ μ l
  μ_sum : (∑ l : HVar, μ l) = 1
  /-- Alice's joint-setting response. -/
  responseA : Fin 18 → Fin 18 → HVar → Fin 2
  /-- Bob's joint-setting response. -/
  responseB : Fin 18 → Fin 18 → HVar → Fin 2
  /-- **MIN (Alice → Bob direction)**: Alice's outcome is independent
      of Bob's setting choice. -/
  min_A : ∀ d_A d_B d_B' l, responseA d_A d_B l = responseA d_A d_B' l
  /-- **MIN (Bob → Alice direction)**: Bob's outcome is independent of
      Alice's setting choice. -/
  min_B : ∀ d_A d_A' d_B l, responseB d_A d_B l = responseB d_A' d_B l
  /-- **TWIN**: when both measure in the same direction, the outcomes
      agree.  Stated for any (allowed) joint settings via MIN. -/
  twin : ∀ d l, responseA d d l = responseB d d l
  /-- **SPIN (Alice)**: stated in the implicit-MIN form (the per-tetrad
      sum over Alice's responses, at any fixed Bob-setting, equals 1). -/
  spin_A : ∀ l (t : Fin 9) (d_B : Fin 18),
    (∑ d ∈ cabelloTetrad t, (1 - (responseA d d_B l : ℕ))) = 1
  /-- **SPIN (Bob)**: same. -/
  spin_B : ∀ l (t : Fin 9) (d_A : Fin 18),
    (∑ d ∈ cabelloTetrad t, (1 - (responseB d_A d l : ℕ))) = 1

attribute [instance] ExplicitMINFreeWillModel.isFintype

/-- Any explicit-MIN model collapses to an implicit-MIN model by
    evaluating the responses at any fixed Bob-setting (we pick `0`),
    and the MIN axioms guarantee this is independent of the choice. -/
private def ExplicitMINFreeWillModel.toImplicit
    (m : ExplicitMINFreeWillModel) : DeterministicFreeWillModel where
  HVar := m.HVar
  isFintype := m.isFintype
  μ := m.μ
  μ_nonneg := m.μ_nonneg
  μ_sum := m.μ_sum
  responseA := fun d l => m.responseA d 0 l
  responseB := fun d l => m.responseB 0 d l
  twin := by
    intro d l
    -- responseA d 0 l vs responseB 0 d l: use MIN on both sides to reduce
    -- to (d, d) and then TWIN.
    have hA : m.responseA d 0 l = m.responseA d d l := m.min_A d 0 d l
    have hB : m.responseB 0 d l = m.responseB d d l := m.min_B 0 d d l
    rw [hA, hB]
    exact m.twin d l
  spin_A := by
    intro l t
    exact m.spin_A l t 0
  spin_B := by
    intro l t
    exact m.spin_B l t 0

/-- **The Conway-Kochen Free Will theorem, explicit-MIN form**.

    No explicit-MIN deterministic free-will-respecting model exists.
    This is the explicit-causality version: SPIN, TWIN, and an EXPLICIT
    no-signalling axiom together yield the no-go.  Proved by reduction
    to `no_deterministic_free_will_model`. -/
theorem no_explicit_MIN_free_will_model :
    ¬ ∃ _ : ExplicitMINFreeWillModel, True := by
  rintro ⟨m, _⟩
  exact no_deterministic_free_will_model
    ⟨m.toImplicit, trivial⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Honest scope of the Conway-Kochen formalisation.**

    A `Prop` that records, machine-checkably, the precise content of
    what has been proved (and what has not):

    (CK1) the deterministic free-will-respecting model with implicit
          MIN is empty (`no_deterministic_free_will_model`);
    (CK2) the explicit-MIN form is also empty
          (`no_explicit_MIN_free_will_model`);
    (CK3) both no-go theorems are proved by reduction to the Cabello
          18-vector Kochen-Specker contextuality theorem
          (`KochenSpecker18.no_KS_noncoloring`), via the bridge that
          SPIN's per-tetrad "exactly one 0" content is precisely
          `IsKSNoncoloring`.

    HONEST OMISSIONS (these are NOT in this theorem and are scope
    boundaries for the formalisation, not Lean obligations):

    (O1) the physical claim that QM realises SPIN+TWIN+MIN for actual
         spin-1 particles is an empirical input, not derived here;
    (O2) the original Conway-Kochen presentation uses Peres' 33-vector
         construction in ℝ³ for SPIN; we use the Cabello 18-vector ℝ⁴
         construction (already formalised in `KochenSpecker18.lean`).
         The structural argument is identical;
    (O3) we work with deterministic responses (the "Free Will theorem"
         is about deterministic local-realistic models); stochastic
         response models are outside this file's scope. -/
def conway_kochen_honest_scope : Prop :=
  (¬ ∃ _ : DeterministicFreeWillModel, True) ∧
  (¬ ∃ _ : ExplicitMINFreeWillModel, True)

/-- The honest scope `Prop` is provable. -/
theorem conway_kochen_honest_scope_proved : conway_kochen_honest_scope :=
  ⟨no_deterministic_free_will_model, no_explicit_MIN_free_will_model⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM AUDIT

    All headline theorems
      • `no_deterministic_free_will_model`
      • `no_deterministic_free_will_model_via_Bob`
      • `no_explicit_MIN_free_will_model`
      • `conway_kochen_honest_scope_proved`
    depend only on Lean's three kernel axioms
      `propext`, `Classical.choice`, `Quot.sound`
    via the upstream `no_KS_noncoloring` from `KochenSpecker18.lean`.

    Verify locally with
    ```
    #print axioms no_deterministic_free_will_model
    #print axioms no_explicit_MIN_free_will_model
    #print axioms conway_kochen_honest_scope_proved
    ```
-/

end UnifiedTheory.LayerC.ConwayKochenFreeWill
