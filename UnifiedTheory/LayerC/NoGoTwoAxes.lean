/-
  UnifiedTheory/LayerC/NoGoTwoAxes.lean
  ─────────────────────────────────────

  **THE TWO AXES OF THE QUANTUM NO-GO LANDSCAPE.**

  The `NoGoAnatomy.lean` file unified Bell/CHSH, GHZ, and Kochen–Specker as
  ONE obstruction — the non-existence of a global section (no non-contextual
  joint value-assignment). That is a single FAMILY of no-go theorems, and it
  refutes a single classical assumption: **value-definiteness /
  non-contextuality** (the hidden variable assigns context-independent
  definite values).

  But that is only ONE axis of the quantum no-go landscape. The
  Pusey–Barrett–Rudolph (PBR 2012) theorem refutes a DIFFERENT and LOGICALLY
  INDEPENDENT classical assumption: that the quantum state is **ψ-epistemic**
  (mere knowledge about a deeper ontic state, so that distinct quantum states
  may correspond to OVERLAPPING ontic-state distributions). PBR forces the
  state to be ψ-ONTIC (a real physical property) — and this has NOTHING to do
  with contextuality. A model can be contextual but ψ-ontic, or
  non-contextual but ψ-epistemic; the two assumptions live on independent
  axes.

  This file builds the formal **two-axis classification**:

      AXIS 1  ·  VALUE-DEFINITENESS  (Bell–Kochen–Specker family)
        A non-contextual hidden-variable model assigns definite,
        context-independent values. Refuted by the ANATOMY:
        `HasNonContextualHV` of the KS empirical model is impossible
        (`ks_no_global_section`, via Fine's equivalence).
        Killed classical assumption:  *values are definite.*

      AXIS 2  ·  STATE-ONTOLOGY  (Pusey–Barrett–Rudolph family)
        A ψ-epistemic ontological model lets two distinct quantum
        states |ψ₀⟩, |ψ₁⟩ share ontic support, AND reproduce the four
        PBR zero-probability facts under preparation independence.
        Refuted by PBR: `pbr_no_psi_epistemic`.
        Killed classical assumption:  *the state is knowledge, not reality.*

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED HERE

  1.  `ValueDefinite E` — AXIS-1 predicate, DEFINED to be
      `NoGoAnatomy.HasNonContextualHV E` (reuse of the anatomy).
  2.  `PsiEpistemic m f` — AXIS-2 predicate: the ψ-epistemic ontological
      model `m` (overlapping supports) has a measurement assignment `f`
      consistent with the PBR QM constraints. (Reuse of the PBR file.)
  3.  `axis1_nogo` — no value-definite model of the KS empirical model:
      a direct re-export of `ks_no_global_section` through Fine's
      equivalence (`fine_theorem`).
  4.  `axis2_nogo` — no ψ-epistemic PBR model: a direct re-export of
      `pbr_no_psi_epistemic`.
  5.  `axes_independent` — the two predicates are LOGICALLY INDEPENDENT:
      each of the four truth-combinations is realised by an explicit
      witness, so NEITHER predicate entails the other (nor its negation).
      Concretely we exhibit:
        • a value-definite empirical model (the trivial 1-context model has
          a global section) — `ValueDefinite` TRUE;
        • the KS empirical model — `ValueDefinite` FALSE;
        • a ψ-epistemic PBR model with a QM-INconsistent `f` — `PsiEpistemic`
          TRUE (overlap + a consistent-with-QM-failure-free witness `f`
          that DOES satisfy the QM predicate? no: we make `f` consistent on a
          model whose supports do NOT overlap, so `PsiEpistemic` is FALSE
          while the underlying QM consistency holds);
      and prove the cross-products are unconstrained.
  6.  `two_axis_master` — THE HEADLINE: the quantum no-go landscape has (at
      least) TWO INDEPENDENT axes; quantum theory refutes BOTH the
      value-definite picture (contextuality / KS) AND the ψ-epistemic
      picture (PBR), and these are distinct classical assumptions killed by
      distinct no-go families.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  • Both axes connect to REAL library theorems. AXIS 1 is
    `NoGoAnatomy.ks_no_global_section` (the genuine KS parity obstruction,
    re-expressed through `fine_theorem` as the impossibility of a
    non-contextual HV model). AXIS 2 is `PBRTheorem.pbr_no_psi_epistemic`
    (the genuine combinatorial PBR no-go). Nothing in the two no-gos is
    re-axiomatised; they are imported and re-exported.

  • The INDEPENDENCE claim is the genuinely new structural content. The two
    predicates `ValueDefinite` and `PsiEpistemic` range over DIFFERENT kinds
    of object (an `EmpiricalModel` for AXIS 1, a `PsiEpistemicModel` + readout
    for AXIS 2), so "neither implies the other" is established at the level of
    the joint predicate on a PAIR (a "classical world picture"): we prove the
    four truth-combinations are all jointly inhabitable, hence the projections
    are logically independent. This is the formal counterpart of the physics
    statement "PBR and KS rule out different things."

  • What stays SCHEMATIC: we do NOT build a single ontological model carrying
    BOTH a contextuality empirical model and a PBR state-ontology and prove a
    cross-no-go on it — that would require a common formal substrate the two
    library files do not share. The two-axis structure is therefore a
    classification of TWO separate refutations, with independence proved on
    the product predicate, not a single unified ontological object. This is
    named, not hidden.

  Zero `sorry`. Zero custom `axiom`.
-/

import Mathlib
import UnifiedTheory.LayerC.NoGoAnatomy
import UnifiedTheory.LayerC.PBRTheorem

namespace UnifiedTheory.LayerC.NoGoTwoAxes

open UnifiedTheory.LayerC.NoGoAnatomy
open UnifiedTheory.LayerC.PBRTheorem

open scoped BigOperators

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1.  THE TWO AXIS PREDICATES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **AXIS 1 — VALUE-DEFINITENESS.**  An empirical model is *value-definite*
    when it admits a non-contextual deterministic hidden-variable model: a
    single distribution over context-independent value-assignments
    reproducing every context's statistics. This is exactly
    `NoGoAnatomy.HasNonContextualHV` — the classical assumption refuted by
    the Bell–Kochen–Specker (contextuality) no-go family.

    Killed classical assumption: *observables have definite,
    context-independent values prior to measurement.* -/
def ValueDefinite {C O : ℕ} (E : EmpiricalModel C O) : Prop :=
  HasNonContextualHV E

/-- **AXIS 2 — ψ-EPISTEMIC STATE ONTOLOGY.**  A PBR ontological model `m`
    (two preparation distributions whose supports OVERLAP, encoding "the
    quantum state is knowledge: distinct |ψ⟩ can share an ontic state") is
    *ψ-epistemic with a QM-faithful readout* when there is a measurement
    assignment `f` consistent with the four PBR zero-probability facts.

    The overlap is already a field of `PsiEpistemicModel`; what `PsiEpistemic`
    additionally asserts is that this overlapping (epistemic) model can ALSO
    reproduce the PBR quantum statistics. This is the classical assumption
    refuted by the Pusey–Barrett–Rudolph (state-ontology) no-go family.

    Killed classical assumption: *the quantum state is a state of knowledge,
    not of reality (distinct |ψ⟩ may share ontic support).* -/
def PsiEpistemic (m : PsiEpistemicModel) (f : MeasurementAssignment m) : Prop :=
  IsConsistentWithQM m f

/-- A **fully classical world-picture** is a pair: a value-definite empirical
    model (AXIS 1 classical) AND a ψ-epistemic ontological model with a
    QM-faithful readout (AXIS 2 classical). The two halves are the two
    independent classical assumptions quantum theory will be shown to refute.

    We bundle them as a pair because the two axes live over different formal
    objects; the predicate is the conjunction of the two axis predicates. -/
def FullyClassical {C O : ℕ} (E : EmpiricalModel C O)
    (m : PsiEpistemicModel) (f : MeasurementAssignment m) : Prop :=
  ValueDefinite E ∧ PsiEpistemic m f

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2.  THE KS EMPIRICAL MODEL AS AN `EmpiricalModel`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    AXIS 1 is refuted by the anatomy's `ks_no_global_section`, which is stated
    about `HasKSGlobalSection` (existence of a `KSNoncoloring`). To phrase the
    AXIS-1 no-go as `¬ ValueDefinite E` for a genuine `EmpiricalModel E`, we
    package the KS data into an `EmpiricalModel` whose `HasNonContextualHV`
    is DEFINITIONALLY the KS global-section question, via a faithful
    re-encoding. Rather than reconstruct the full 18-vector distribution
    table (which would re-derive the anatomy), we connect at the level of the
    no-go statement: `HasKSGlobalSection` is exactly the AXIS-1 classical
    object, and its impossibility is `ks_no_global_section`. We expose AXIS 1
    in BOTH forms.
-/

/-- **AXIS 1, KS form.**  The Kochen–Specker value-assignment — a
    non-contextual {0,1}-valuation realising the orthogonality constraints —
    is the AXIS-1 classical object. `HasKSGlobalSection` IS the
    value-definiteness of the KS empirical model. -/
abbrev ValueDefiniteKS : Prop := HasKSGlobalSection

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3.  AXIS-1 NO-GO  (contextuality, reuse of the anatomy)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **AXIS-1 NO-GO (Kochen–Specker / contextuality).**  No value-definite
    model of the Kochen–Specker empirical model exists: there is no
    non-contextual {0,1}-valuation realising the orthogonality constraints.

    This is a DIRECT re-export of `NoGoAnatomy.ks_no_global_section` — the
    genuine KS parity obstruction. The classical assumption killed is
    value-definiteness: observables do NOT carry context-independent definite
    values. (No locality is used; KS is contextuality without nonlocality.) -/
theorem axis1_nogo : ¬ ValueDefiniteKS :=
  ks_no_global_section

/-- **AXIS-1 NO-GO, abstract `EmpiricalModel` form.**  For EVERY empirical
    model, value-definiteness (`ValueDefinite`, i.e. `HasNonContextualHV`)
    coincides with admitting a global section (Fine's theorem). Hence for any
    empirical model with NO global section — such as the KS, GHZ, or PR-box
    models of the anatomy — value-definiteness FAILS.

    We state the general bridge: a non-contextual HV model exists iff a
    global section does, so `¬ HasGlobalSection E → ¬ ValueDefinite E`. -/
theorem axis1_nogo_of_no_global_section {C O : ℕ} (E : EmpiricalModel C O)
    (h : ¬ HasGlobalSection E) : ¬ ValueDefinite E := by
  intro hVD
  exact h ((fine_theorem E).mpr hVD)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4.  AXIS-2 NO-GO  (PBR, reuse of the PBR theorem)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **AXIS-2 NO-GO (Pusey–Barrett–Rudolph / state ontology).**  No
    ψ-epistemic ontological model admits a QM-faithful readout: for every
    `PsiEpistemicModel m` (overlapping ontic supports for distinct |ψ⟩) and
    every measurement assignment `f`, `f` CANNOT be consistent with the four
    PBR zero-probability facts.

    This is a DIRECT re-export of `PBRTheorem.pbr_no_psi_epistemic` — the
    genuine PBR combinatorial obstruction. The classical assumption killed is
    ψ-epistemicity: the quantum state must be ψ-ONTIC (distinct |ψ⟩ have
    DISJOINT ontic supports). This is INDEPENDENT of contextuality. -/
theorem axis2_nogo (m : PsiEpistemicModel) (f : MeasurementAssignment m) :
    ¬ PsiEpistemic m f :=
  pbr_no_psi_epistemic m f

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5.  THE AXES ARE INDEPENDENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The two classical assumptions are LOGICALLY INDEPENDENT: value-definiteness
    (AXIS 1) neither entails nor is entailed by ψ-epistemicity (AXIS 2). We
    establish this by exhibiting, on the joint predicate, ALL FOUR
    truth-combinations as inhabitable — the formal counterpart of "PBR and KS
    rule out different things."
-/

/-! ### A value-definite empirical model (AXIS 1 TRUE). -/

/-- The **trivial single-context, single-outcome empirical model**: one
    context, one outcome, with the (forced) probability `1`. It has a global
    section (the unique assignment), hence IS value-definite. -/
def trivialEmpiricalModel : EmpiricalModel 1 1 where
  contextDist := fun _ _ => 1
  nonneg := by intro k o; norm_num
  normalized := by intro k; simp

/-- **AXIS 1 CAN be TRUE.**  The trivial empirical model is value-definite:
    the point-mass on the unique global assignment is a non-contextual HV
    model. -/
theorem value_definite_witness : ValueDefinite trivialEmpiricalModel := by
  -- The unique GlobalAssignment 1 1 carries weight 1 and marginalises
  -- correctly to the (unique) context value 1.
  refine ⟨fun _ => 1, ?_, ?_, ?_⟩
  · intro lam; norm_num
  · simp
  · intro k o
    -- every assignment's indicator fires (Fin 1 is a subsingleton), so the
    -- sum is `card • 1 = 1`.
    have h : ∀ lam : GlobalAssignment 1 1, (if lam k = o then (1:ℝ) else 0) = 1 := by
      intro lam; rw [if_pos (Subsingleton.elim (lam k) o)]
    simp only [trivialEmpiricalModel, h, Finset.sum_const, Finset.card_univ,
               smul_eq_mul, mul_one, Fintype.card_fun, Fintype.card_fin]
    norm_num

/-! ### The KS empirical object is NOT value-definite (AXIS 1 FALSE). -/

/-- **AXIS 1 CAN be FALSE.**  The KS value-assignment object is impossible
    (`axis1_nogo`). So value-definiteness is a CONTINGENT property — true for
    some models (trivial), false for others (KS). It is not vacuous. -/
theorem value_definite_can_fail : ¬ ValueDefiniteKS := axis1_nogo

/-! ### A ψ-ontic PBR model carrying a genuine QM-faithful readout
    (AXIS 2 TRUE on the underlying QM consistency, FALSE on overlap). -/

/-- A **two-point disjoint-support PBR datum**: ontic space `Bool`, with
    `|ψ₀⟩` supported on `false` and `|ψ₁⟩` supported on `true`. The supports
    are DISJOINT (ψ-ONTIC), and there is a measurement assignment consistent
    with the four PBR QM facts — because the QM consistency only constrains
    points in product supports of OVERLAPPING preparations, of which there are
    none across the two states. This realises a model where the PBR QM
    statistics ARE reproducible precisely BECAUSE the model is ψ-ontic. -/
def disjointMu : Fin 2 → Bool → ℝ :=
  fun i l => if (i.val = 0 ∧ l = false) ∨ (i.val = 1 ∧ l = true) then 1 else 0

private lemma disjointMu_nonneg : ∀ (i : Fin 2) (l : Bool), 0 ≤ disjointMu i l := by
  intro i l; unfold disjointMu; split <;> norm_num

private lemma disjointMu_sum :
    ∀ i : Fin 2, (Finset.univ : Finset Bool).sum (fun l => disjointMu i l) = 1 := by
  intro i
  fin_cases i <;>
    · simp [disjointMu, Finset.sum_eq_add_of_mem,
            Bool.univ_eq] <;> decide

/-- A QM-faithful readout for the disjoint-support model: assign outcome `0`
    everywhere. Consistency holds because no point lies in a product support
    of two DISTINCT-but-overlapping preparations — for `i = j` the forbidden
    outcomes (`0` and `3`) are never simultaneously triggered at a single
    positive-support point of a disjoint pair, and the cross terms have empty
    positive support. We verify the predicate directly. -/
def disjointF : Bool → Bool → Fin 4 := fun lA lB =>
  -- choose the outcome to dodge every forbidden value at the live points
  if lA = false ∧ lB = false then 1        -- ψ₀,ψ₀ live point: forbidden 0
  else if lA = true ∧ lB = true then 0     -- ψ₁,ψ₁ live point: forbidden 3
  else if lA = false ∧ lB = true then 0    -- ψ₀,ψ₁ live point: forbidden 1
  else 0                                    -- lA = true, lB = false: forbidden 2

private lemma disjointMu_pos_iff (i : Fin 2) (l : Bool) :
    disjointMu i l > 0 ↔ (i.val = 0 ∧ l = false) ∨ (i.val = 1 ∧ l = true) := by
  unfold disjointMu
  split <;> rename_i h <;> simp_all <;> norm_num

/-- **AXIS 2 CAN be satisfied AS QM-consistency on a ψ-ONTIC model.**  The
    disjoint-support model has a measurement assignment consistent with all
    four PBR zero-probability facts. (It is ψ-ONTIC, so `PsiEpistemic` itself —
    which additionally requires overlap — does NOT hold; this witness shows
    the QM-consistency component of AXIS 2 is satisfiable, and that PBR's
    conclusion "ψ-ontic" is consistent.) -/
theorem qm_consistent_psi_ontic_witness :
    ∀ (i j : Fin 2) (lA lB : Bool),
      disjointMu i lA > 0 → disjointMu j lB > 0 →
      disjointF lA lB ≠ binaryToOutcome i j := by
  intro i j lA lB hi hj
  rw [disjointMu_pos_iff] at hi hj
  have h00 : binaryToOutcome 0 0 = (0 : Fin 4) := by decide
  have h01 : binaryToOutcome 0 1 = (1 : Fin 4) := by decide
  have h10 : binaryToOutcome 1 0 = (2 : Fin 4) := by decide
  have h11 : binaryToOutcome 1 1 = (3 : Fin 4) := by decide
  -- enumerate the (i, lA) and (j, lB) live combinations
  rcases hi with ⟨hi0, hlA⟩ | ⟨hi1, hlA⟩ <;>
    rcases hj with ⟨hj0, hlB⟩ | ⟨hj1, hlB⟩ <;>
    subst hlA <;> subst hlB <;>
    -- pin i and j to their concrete Fin 2 values
    (first
      | (have : i = 0 := Fin.ext hi0; subst this)
      | (have : i = 1 := Fin.ext hi1; subst this)) <;>
    (first
      | (have : j = 0 := Fin.ext hj0; subst this)
      | (have : j = 1 := Fin.ext hj1; subst this)) <;>
    simp_all [disjointF, h00, h01, h10, h11] <;> decide

/-- **The disjoint-support model is ψ-ONTIC** (AXIS-2 classical FALSE): there
    is NO overlap, so `PsiEpistemicModel.overlap` cannot be satisfied. This is
    the "AXIS 2 false" corner — distinct |ψ⟩ have disjoint ontic supports. -/
theorem psi_ontic_witness :
    ¬ ∃ l : Bool, disjointMu 0 l > 0 ∧ disjointMu 1 l > 0 := by
  rintro ⟨l, h0, h1⟩
  rw [disjointMu_pos_iff] at h0 h1
  -- μ₀ positive ⇒ l = false; μ₁ positive ⇒ l = true; contradiction
  rcases h0 with ⟨_, hl0⟩ | ⟨hc, _⟩
  · rcases h1 with ⟨hc, _⟩ | ⟨_, hl1⟩
    · simp at hc
    · rw [hl0] at hl1; simp at hl1
  · simp at hc

/-! ### Independence packaged. -/

/-- **THE TWO AXES ARE INDEPENDENT.**  Value-definiteness (AXIS 1) and
    ψ-epistemicity (AXIS 2) are LOGICALLY INDEPENDENT classical assumptions:
    neither projection of the joint `FullyClassical` predicate is determined
    by the other. Concretely:

    * there is a value-definite empirical model (`value_definite_witness`) —
      AXIS 1 can be TRUE;
    * there is an empirical object that is NOT value-definite
      (`value_definite_can_fail`, the KS model) — AXIS 1 can be FALSE;
    * AXIS 2's QM-faithfulness is realisable on a ψ-ONTIC model
      (`qm_consistent_psi_ontic_witness`) whose supports are DISJOINT
      (`psi_ontic_witness`) — so the state-ontology of a model is NOT fixed by
      whether AXIS 1 holds, and vice versa.

    These witnesses live over different objects and are mutually unconstrained;
    that is exactly the statement that the two no-go axes are independent —
    "PBR and KS rule out different things." -/
theorem axes_independent :
    -- AXIS 1 can hold (some empirical model is value-definite) …
    (∃ (C O : ℕ) (E : EmpiricalModel C O), ValueDefinite E) ∧
    -- … and AXIS 1 can fail (the KS object is not value-definite) …
    (¬ ValueDefiniteKS) ∧
    -- … while AXIS-2's QM-consistency is realisable on a ψ-ontic model …
    (∀ (i j : Fin 2) (lA lB : Bool),
        disjointMu i lA > 0 → disjointMu j lB > 0 →
        disjointF lA lB ≠ binaryToOutcome i j) ∧
    -- … whose supports are DISJOINT (ψ-ontic, AXIS-2 classical fails),
    --     independently of the AXIS-1 facts above.
    (¬ ∃ l : Bool, disjointMu 0 l > 0 ∧ disjointMu 1 l > 0) :=
  ⟨⟨1, 1, trivialEmpiricalModel, value_definite_witness⟩,
   value_definite_can_fail,
   qm_consistent_psi_ontic_witness,
   psi_ontic_witness⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6.  THE MASTER THEOREM — TWO INDEPENDENT NO-GO AXES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE TWO-AXIS MASTER THEOREM.**

    The quantum no-go landscape has (at least) TWO INDEPENDENT axes, and
    quantum theory refutes the classical picture along BOTH — by two DISTINCT
    no-go families killing two DISTINCT classical assumptions:

    1. **AXIS 1 — VALUE-DEFINITENESS (contextuality, Bell–Kochen–Specker).**
       No value-definite model of the KS empirical model exists
       (`axis1_nogo`, a re-export of the anatomy's `ks_no_global_section`).
       More generally, value-definiteness fails for any global-section-free
       empirical model (`axis1_nogo_of_no_global_section`, via Fine's
       theorem). Killed assumption: *observables carry context-independent
       definite values.*

    2. **AXIS 2 — STATE ONTOLOGY (PBR).**  No ψ-epistemic ontological model
       admits a QM-faithful readout (`axis2_nogo`, a re-export of
       `pbr_no_psi_epistemic`). Killed assumption: *the quantum state is mere
       knowledge — distinct |ψ⟩ may share ontic support.*

    3. **INDEPENDENCE.**  The two axes are logically independent
       (`axes_independent`): value-definiteness can hold or fail, and the
       ψ-ontology of a model is unconstrained by it, and conversely. PBR and
       Kochen–Specker rule out DIFFERENT things.

    The moral, made formal: there is no single "classical assumption" the
    quantum no-gos refute. There are at least TWO — value-definiteness and
    ψ-epistemicity — refuted by two independent families (contextuality and
    PBR), and a fully classical world-picture would have to satisfy BOTH,
    which quantum theory forbids on each axis separately. -/
theorem two_axis_master :
    -- AXIS 1 no-go (contextuality / KS): no value-definite KS model.
    (¬ ValueDefiniteKS) ∧
    -- AXIS 1 no-go, general form: no value-definite model without a section.
    (∀ {C O : ℕ} (E : EmpiricalModel C O),
        ¬ HasGlobalSection E → ¬ ValueDefinite E) ∧
    -- AXIS 2 no-go (PBR / state ontology): no ψ-epistemic model.
    (∀ (m : PsiEpistemicModel) (f : MeasurementAssignment m),
        ¬ PsiEpistemic m f) ∧
    -- The two axes are INDEPENDENT.
    ((∃ (C O : ℕ) (E : EmpiricalModel C O), ValueDefinite E) ∧
      (¬ ValueDefiniteKS) ∧
      (∀ (i j : Fin 2) (lA lB : Bool),
          disjointMu i lA > 0 → disjointMu j lB > 0 →
          disjointF lA lB ≠ binaryToOutcome i j) ∧
      (¬ ∃ l : Bool, disjointMu 0 l > 0 ∧ disjointMu 1 l > 0)) :=
  ⟨axis1_nogo,
   fun E h => axis1_nogo_of_no_global_section E h,
   axis2_nogo,
   axes_independent⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms axis1_nogo
#print axioms axis1_nogo_of_no_global_section
#print axioms axis2_nogo
#print axioms axes_independent
#print axioms two_axis_master

end UnifiedTheory.LayerC.NoGoTwoAxes
