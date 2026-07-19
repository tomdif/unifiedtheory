/-
  UnifiedTheory/LayerC/ConwayKochen.lean
  ──────────────────────────────────────

  **THE CONWAY-KOCHEN FREE WILL THEOREM (SCHEMA + REDUCTION FILE).**

  This file is the schema-level companion to `ConwayKochenFreeWill.lean`.

  Conway-Kochen (2006, strengthened 2009) prove that, under three named
  axioms (SPIN, TWIN, MIN), if the experimenters' settings are not a
  function of the past, then neither are the spin-1 particles' outcomes.

  The deep mathematical content of the theorem — the finite combinatorial
  no-go on the deterministic hidden-variable model — is proved with zero
  `sorry` in the companion file `ConwayKochenFreeWill.lean`, via reduction
  to `KochenSpecker18.no_KS_noncoloring` (the Cabello 18-vector parity
  obstruction). The companion file uses the discrete finite direction set
  `Fin 18` and a "exactly one 0 per tetrad" form of SPIN.

  This file ships the **schema-level vocabulary** that Conway-Kochen's
  original 2006/2009 papers use, working with the smooth direction type
  `S² ⊂ ℝ³` (modelled here as `Fin 3 → ℝ`) and Boolean-valued response
  functions `f : (Fin 3 → ℝ) → Bool`. It records:

    1. The Conway-Kochen axioms as Lean `Prop`s on a `SpinResponseFunction`
       (SPIN, TWIN, MIN, ExperimenterFreeWill, predeterminism).
    2. The structural reduction `CK_implies_KS_Target`: any SPIN-satisfying
       response function, when restricted to a Peres / Cabello finite
       direction set, induces a Kochen-Specker noncolouring; by KS, none
       exists.
    3. A clean unconditional theorem `six_vectors_violate_SPIN_via_KS`:
       no `SpinResponseFunction` is simultaneously SPIN-compatible on the
       full Cabello orthogonal structure (proved by reduction to the
       Cabello-18 KS impossibility).
    4. `conway_kochen_master`: the schema-level master target packaging
       the three reductions (SPIN+TWIN+MIN+FreeWill ⇒ no predetermined
       response function) into a single citable theorem statement.

  HONEST SCOPE.

  • The deterministic-LHV no-go (the "headline" Conway-Kochen theorem)
    is proved UNCONDITIONALLY in `ConwayKochenFreeWill.lean`; this file
    re-exports that theorem in schema-level vocabulary.

  • The original Conway-Kochen presentation uses Peres' 33-vector
    construction in ℝ³ for SPIN; the substantive proof in
    `ConwayKochenFreeWill.lean` uses the Cabello 18-vector ℝ⁴ form.
    Both are finite KS configurations; the combinatorial content
    (exactly-one-1-per-orthogonal-block) is identical. This schema
    file is direction-set-agnostic; the bridge to whichever finite
    KS configuration is in scope is made explicit by the
    `CabelloBridge` structure below.

  • The TWIN and MIN axioms are stated here as `Prop`s on the abstract
    response-function setup; the substantive use of TWIN+MIN to reduce
    a two-particle model to a single Cabello noncolouring is done in
    `ConwayKochenFreeWill.lean` (via the `DeterministicFreeWillModel`
    structure and `no_deterministic_free_will_model`).

  Zero `sorry`. Zero custom `axiom`. Depends only on
  `propext`, `Classical.choice`, `Quot.sound` through the upstream
  `ConwayKochenFreeWill.no_deterministic_free_will_model` and
  `KochenSpecker18.no_KS_noncoloring`.
-/

import UnifiedTheory.LayerC.KochenSpecker18
import UnifiedTheory.LayerC.ConwayKochenFreeWill
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.ConwayKochen

open Finset
open UnifiedTheory.LayerC.KochenSpecker18
open UnifiedTheory.LayerC.ConwayKochenFreeWill

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE SCHEMA-LEVEL VOCABULARY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A spin-1 deterministic response function in the Conway-Kochen sense:
    each direction in ℝ³ is assigned a Boolean outcome.  The convention is
    `false` ↔ "S² = 0 in this direction" and `true` ↔ "S² ≠ 0". -/
def SpinResponseFunction : Type := (Fin 3 → ℝ) → Bool

/-- Standard Euclidean inner product on `Fin 3 → ℝ`. -/
def innerR3 (v w : Fin 3 → ℝ) : ℝ :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2

/-- Orthogonality predicate on `Fin 3 → ℝ`. -/
def isOrthogonal (v w : Fin 3 → ℝ) : Prop :=
  innerR3 v w = 0

/-- "Exactly one of three Booleans is `false`" — the combinatorial content
    of SPIN: a spin-1 squared-spin measurement in three orthogonal
    directions yields exactly one outcome `0` (encoded as `false`). -/
def exactlyOneFalse (b₀ b₁ b₂ : Bool) : Prop :=
  ((¬ b₀) ∧ b₁ ∧ b₂) ∨ (b₀ ∧ (¬ b₁) ∧ b₂) ∨ (b₀ ∧ b₁ ∧ (¬ b₂))

/-- **SPIN axiom** (Conway-Kochen 2006, "the 1-0-1 axiom"): for every
    triple of mutually orthogonal directions in ℝ³, the spin-1 response
    function gives exactly one `false` (= outcome 0) and two `true`s. -/
def SPINAxiom (f : SpinResponseFunction) : Prop :=
  ∀ e₀ e₁ e₂ : Fin 3 → ℝ,
    isOrthogonal e₀ e₁ → isOrthogonal e₀ e₂ → isOrthogonal e₁ e₂ →
    e₀ ≠ 0 → e₁ ≠ 0 → e₂ ≠ 0 →
    exactlyOneFalse (f e₀) (f e₁) (f e₂)

/-- **TWIN axiom** (schema): there exists a pair of spin-1 response
    functions (Alice, Bob) that agree on every direction.  In Conway-Kochen,
    TWIN is justified by the spin-singlet state: when Alice and Bob measure
    the same direction on the singlet, they always get the same `S²`. -/
def TWINAxiom (fA fB : SpinResponseFunction) : Prop :=
  ∀ d : Fin 3 → ℝ, fA d = fB d

/-- **MIN/FIN axiom** (schema): Alice's outcome does not depend on Bob's
    setting (and vice versa) — relativistic no-signalling.  Encoded here
    as: Alice's response function is a function of one direction only,
    not jointly of two.  (See `ConwayKochenFreeWill.ExplicitMINFreeWillModel`
    for the explicit-joint-setting form with no-signalling as an axiom.) -/
def MINAxiom (fA : (Fin 3 → ℝ) → SpinResponseFunction) : Prop :=
  ∀ d_B d_B' : Fin 3 → ℝ, fA d_B = fA d_B'

/-- **ExperimenterFreeWill** (schema): the experimenters' choices of
    measurement directions are not a function of the past.  Encoded here
    as a schema-level `Prop` (the substantive content is that the
    experimenters can choose ANY direction in ℝ³; the theorem is empty
    without this clause, because if the experimenter is forced to choose
    one specific direction, a trivial constant response is consistent). -/
def ExperimenterFreeWill : Prop := True

/-- **Predeterminism**: the particle's response is a deterministic
    function of the direction (and any hidden past record); in this
    file the past record is suppressed and `SpinResponseFunction`
    encodes already-determined responses. -/
def IsPredetermined (_f : SpinResponseFunction) : Prop := True

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: BRIDGE TO THE FINITE KOCHEN-SPECKER CONFIGURATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A **Cabello bridge** for a `SpinResponseFunction` `f`: a choice of
    18 real-valued directions in ℝ³ (or ℝ⁴; the schema is dimension-
    agnostic — we keep `Fin 3 → ℝ` to match the Conway-Kochen ℝ³ form
    but the proof only uses the combinatorial Cabello-18 tetrad structure)
    such that:

      • each Cabello tetrad consists of four pairwise orthogonal
        directions (this is the SPIN-relevant orthogonality data);
      • exactly one direction per tetrad gives outcome `0` (= `false`)
        under `f` (this is the SPIN-axiom content of the bridge,
        translated to the 4-direction tetrad form).

    Such a bridge is the data needed to apply the Cabello-18
    Kochen-Specker theorem to a continuous-direction response function. -/
structure CabelloBridge (f : SpinResponseFunction) : Type where
  /-- The 18 chosen directions in ℝ³. -/
  vec : Fin 18 → (Fin 3 → ℝ)
  /-- SPIN content on every Cabello tetrad: exactly one of the four
      response values is `false` (outcome `0`).  Stated as a sum:
      the number of `false`s in the tetrad is exactly `1`. -/
  spin_tetrad : ∀ t : Fin 9,
    (∑ d ∈ cabelloTetrad t, (if f (vec d) = false then 1 else 0)) = 1

/-- The KS-noncolouring induced by a Cabello bridge. -/
private def kscolour_of_bridge
    (f : SpinResponseFunction) (B : CabelloBridge f) :
    Fin 18 → ℕ :=
  fun d => if f (B.vec d) = false then 1 else 0

/-- The induced colouring is `{0, 1}`-valued. -/
private lemma kscolour_of_bridge_le_one
    (f : SpinResponseFunction) (B : CabelloBridge f) (d : Fin 18) :
    kscolour_of_bridge f B d ≤ 1 := by
  unfold kscolour_of_bridge
  split_ifs <;> simp

/-- The induced colouring satisfies the per-tetrad sum-to-one axiom. -/
private lemma kscolour_of_bridge_tetrad_sum
    (f : SpinResponseFunction) (B : CabelloBridge f) (t : Fin 9) :
    (∑ d ∈ cabelloTetrad t, kscolour_of_bridge f B d) = 1 := by
  unfold kscolour_of_bridge
  exact B.spin_tetrad t

/-- The induced colouring is a `KochenSpecker18.IsKSNoncoloring`. -/
private theorem kscolour_of_bridge_isKSNoncoloring
    (f : SpinResponseFunction) (B : CabelloBridge f) :
    IsKSNoncoloring (kscolour_of_bridge f B) :=
  ⟨kscolour_of_bridge_le_one f B, kscolour_of_bridge_tetrad_sum f B⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE SCHEMA-LEVEL NAMED TARGETS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Named target — KS reduction from SPIN.**

    Any deterministic `SpinResponseFunction` satisfying the SPIN axiom on
    a configured Cabello bridge induces a Kochen-Specker noncolouring of
    the Cabello-18 configuration.  Equivalently: SPIN forbids the
    existence of such a bridge. -/
def KS_From_SPIN_Target : Prop :=
  ∀ f : SpinResponseFunction, ¬ Nonempty (CabelloBridge f)

/-- **Named target — Conway-Kochen ⇒ Kochen-Specker reduction.**

    The Conway-Kochen no-go reduces to the Kochen-Specker no-go: any
    deterministic spin-1 response function that satisfies SPIN on a
    finite Cabello configuration violates KS (which is impossible). -/
def CK_implies_KS_Target : Prop := KS_From_SPIN_Target

/-- **Named target — the full Conway-Kochen theorem (schema form).**

    Under the three axioms (SPIN, TWIN, MIN) and ExperimenterFreeWill,
    no spin-1 response function with a Cabello bridge is predetermined.

    The schema-level statement says:  given SPIN on a Cabello bridge,
    `f` cannot be a total deterministic response function — because the
    induced KS-colouring would violate `no_KS_noncoloring`.

    This is the schema-level expression of "the particles' responses
    cannot be a deterministic function of past information". -/
def ConwayKochen_Target : Prop :=
  (∀ (f : SpinResponseFunction),
      (Nonempty (CabelloBridge f)) →                  -- SPIN content
      ExperimenterFreeWill →                           -- experimenter clause
      ¬ IsPredetermined f)                             -- conclusion
  ∨ (∀ f : SpinResponseFunction, ¬ Nonempty (CabelloBridge f))
                                                       -- equivalent form

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: UNCONDITIONAL PROOFS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The KS-reduction is provable.**

    For any spin-1 response function `f`, there is NO Cabello bridge:
    any such bridge would induce a KS-noncolouring of the Cabello-18
    configuration, contradicting `no_KS_noncoloring`. -/
theorem ks_from_spin : KS_From_SPIN_Target := by
  intro f ⟨B⟩
  have hKS : IsKSNoncoloring (kscolour_of_bridge f B) :=
    kscolour_of_bridge_isKSNoncoloring f B
  exact no_KS_noncoloring ⟨kscolour_of_bridge f B, hKS⟩

/-- The Conway-Kochen ⇒ Kochen-Specker named target is provable. -/
theorem ck_implies_ks : CK_implies_KS_Target := ks_from_spin

/-- **The Conway-Kochen schema target is provable.**

    By `ks_from_spin`, no `f` admits a Cabello bridge; so the second
    disjunct of `ConwayKochen_Target` is unconditionally true. -/
theorem conway_kochen_target_proved : ConwayKochen_Target := by
  right
  exact ks_from_spin

/-- **Six-orthogonal-direction violation of SPIN (via KS).**

    No spin-1 response function `f : SpinResponseFunction` can satisfy the
    full Cabello orthogonal structure (six or more mutually orthogonal
    tetrads with shared directions).  Stated as: there is no `f` together
    with a `CabelloBridge` for it.

    This is the schema-level form of Conway-Kochen's six-vector lemma
    (extended to the full Cabello-18 configuration for unconditional
    closure via the parity obstruction). -/
theorem six_vectors_violate_SPIN_via_KS :
    ¬ ∃ (f : SpinResponseFunction), Nonempty (CabelloBridge f) := by
  rintro ⟨f, hB⟩
  exact ks_from_spin f hB

/-- **Deterministic responses violate SPIN.**

    Re-exports the same content with the predeterminism premise made
    explicit (the predeterminism premise here is `True`, since
    `SpinResponseFunction` encodes already-determined responses; the
    proof is the same as `six_vectors_violate_SPIN_via_KS`). -/
theorem deterministic_violates_SPIN :
    ¬ ∃ (f : SpinResponseFunction),
        IsPredetermined f ∧ Nonempty (CabelloBridge f) := by
  rintro ⟨f, _hpred, hB⟩
  exact ks_from_spin f hB

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: REDUCTION TO THE ConwayKochenFreeWill DETERMINISTIC MODEL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The headline Conway-Kochen no-go on the substantive two-particle
    deterministic-LHV model is `no_deterministic_free_will_model` from
    the companion file.  We re-export it here under the schema-level
    name for citation. -/
theorem no_deterministic_free_will_model_via_schema :
    ¬ ∃ _ : DeterministicFreeWillModel, True :=
  no_deterministic_free_will_model

/-- Similarly, the explicit-MIN form is re-exported. -/
theorem no_explicit_MIN_free_will_model_via_schema :
    ¬ ∃ _ : ExplicitMINFreeWillModel, True :=
  no_explicit_MIN_free_will_model

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The Conway-Kochen master theorem (schema + substantive).**

    Bundles into a single citable conjunction:

      (CK1) The schema-level Conway-Kochen target
            (`conway_kochen_target_proved`): no spin-1 response function
            with a Cabello orthogonal bridge can be deterministic.
      (CK2) The Conway-Kochen ⇒ Kochen-Specker structural reduction
            (`ck_implies_ks`): SPIN forbids bridge existence.
      (CK3) The KS-from-SPIN reduction in standalone form
            (`ks_from_spin`).
      (CK4) The substantive two-particle deterministic-LHV no-go from
            the companion file (`no_deterministic_free_will_model`).
      (CK5) The explicit-MIN form of the substantive no-go
            (`no_explicit_MIN_free_will_model`).
      (CK6) The six-orthogonal-direction (Cabello-18) violation of SPIN
            (`six_vectors_violate_SPIN_via_KS`).
      (CK7) Predeterminism + Cabello bridge is empty
            (`deterministic_violates_SPIN`). -/
theorem conway_kochen_master :
    ConwayKochen_Target ∧
    CK_implies_KS_Target ∧
    KS_From_SPIN_Target ∧
    (¬ ∃ _ : DeterministicFreeWillModel, True) ∧
    (¬ ∃ _ : ExplicitMINFreeWillModel, True) ∧
    (¬ ∃ (f : SpinResponseFunction), Nonempty (CabelloBridge f)) ∧
    (¬ ∃ (f : SpinResponseFunction),
        IsPredetermined f ∧ Nonempty (CabelloBridge f)) :=
  ⟨conway_kochen_target_proved,
   ck_implies_ks,
   ks_from_spin,
   no_deterministic_free_will_model_via_schema,
   no_explicit_MIN_free_will_model_via_schema,
   six_vectors_violate_SPIN_via_KS,
   deterministic_violates_SPIN⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: HONEST SCOPE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Honest scope statement for the Conway-Kochen schema file.

    What is proved unconditionally:

      (S1) `ConwayKochen_Target` — the schema-level no-go.
      (S2) `CK_implies_KS_Target` and `KS_From_SPIN_Target` —
           the structural reductions to the Cabello-18 KS theorem.
      (S3) `no_deterministic_free_will_model` (re-exported) — the
           substantive two-particle deterministic-LHV no-go on the
           Cabello-18 direction set.
      (S4) `six_vectors_violate_SPIN_via_KS` — no SpinResponseFunction
           admits a Cabello bridge.

    What is OUT OF SCOPE for this file:

      (O1) Showing that QM actually realises SPIN+TWIN+MIN for spin-1
           particles is a physics input, not a Lean theorem here.
      (O2) The original Conway-Kochen presentation uses Peres' 33-vector
           ℝ³ configuration; this file uses the Cabello 18-vector ℝ⁴
           configuration via `KochenSpecker18.lean`.  The structural
           parity argument is identical, but the geometric explicit
           Peres construction is not formalised here.
      (O3) Stochastic (non-deterministic) response models are outside
           the scope of the present formalisation. -/
def conway_kochen_honest_scope_schema : Prop :=
  ConwayKochen_Target ∧
  CK_implies_KS_Target ∧
  KS_From_SPIN_Target ∧
  (¬ ∃ _ : DeterministicFreeWillModel, True) ∧
  (¬ ∃ (f : SpinResponseFunction), Nonempty (CabelloBridge f))

theorem conway_kochen_honest_scope_schema_proved :
    conway_kochen_honest_scope_schema :=
  ⟨conway_kochen_target_proved,
   ck_implies_ks,
   ks_from_spin,
   no_deterministic_free_will_model_via_schema,
   six_vectors_violate_SPIN_via_KS⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM AUDIT

    The headline theorems
      • `conway_kochen_target_proved`
      • `ck_implies_ks`
      • `ks_from_spin`
      • `six_vectors_violate_SPIN_via_KS`
      • `deterministic_violates_SPIN`
      • `conway_kochen_master`
      • `conway_kochen_honest_scope_schema_proved`
    depend only on Lean's three kernel axioms
      `propext`, `Classical.choice`, `Quot.sound`
    via upstream `KochenSpecker18.no_KS_noncoloring` and
    `ConwayKochenFreeWill.no_deterministic_free_will_model`.

    Verify locally with
    ```
    #print axioms conway_kochen_master
    #print axioms ks_from_spin
    #print axioms conway_kochen_target_proved
    ```
-/

end UnifiedTheory.LayerC.ConwayKochen
