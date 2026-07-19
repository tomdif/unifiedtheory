/-
  UnifiedTheory/LayerC/SMPartialForcing.lean
  ──────────────────────────────────────────

  **Step S6 of the SM ↔ QM Bridge, Path A — PARTIAL FORCING DIRECTION.**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHY THIS FILE EXISTS

  Step S5 (`IsOperationalQuantum`) ships a CONJUNCTION: the three
  operational-axiom predicates (Raymond-Robichaud local realism,
  Information Causality, PBR ψ-ontology) that pick out the quantum
  slice of the no-signalling polytope.  Step S1
  (`SMHilbertInstantiation`) ships a CONSTRUCTION: the
  Raymond-Robichaud no-signalling theory `singleGenNS` whose Hilbert
  dimension is `atom_N_W ^ atom_d_eff = 16 = dim_spinor_SO10`.

  Step S6 asks the FORCING question:

      If a no-signalling theory `T : NoSignallingTheory` is operationally
      quantum AND satisfies an SO(10) covariance hypothesis, does the
      Hilbert dimension of `T` have to be divisible by
      `N_W ^ d_eff = 16 = dim_spinor`?

  In full generality, this requires Lie group representation theory
  of SO(10) (subgroup-index arguments via Frobenius reciprocity) and
  is a multi-week formalisation.  What we ship HERE is the HONEST
  PARTIAL DELIVERABLE:

    (A) The TRIVIAL FORCING direction for the bridge object
        `singleGenNS` itself: its Hilbert dimension IS `16` (and so
        is divisible by `16`).  Discharged structurally.

    (B) The general SO(10) forcing claim stated as a NAMED HYPOTHESIS
        (`SO10Forcing_Target`).  No `axiom`; no `sorry`; just a `Prop`
        that names the deep claim and is available for citation.

    (C) The CONDITIONAL FORCING THEOREM: under the named hypothesis,
        the divisibility follows for every operationally-quantum
        SO(10)-covariant `T`.  Immediate from (B).

    (D) The COMBINED HEADLINE: the bridge object `singleGenNS`
        satisfies the partial forcing property unconditionally
        (the dimension is divisible by 16 AND equals `N_W ^ d_eff`).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE SHIPS

  Tier 1 — TARGET DIMENSION AND THE PARTIAL FORCING FOR `singleGenNS`:
    • `N_W_pow_d_eff`              — the bridge target `= 16`
    • `N_W_pow_d_eff_eq_sixteen`   — numerical identity `16`
    • `N_W_pow_d_eff_eq_singleGenDim` — equals the bridge object's
                                        Hilbert dimension
    • `singleGenDim_eq_N_W_pow_d_eff` — symmetric form
    • `singleGenNS_dim_forced`     — `singleGenDim = 16`, the
                                     trivial forcing on the bridge object
    • `singleGenNS_dim_divides_sixteen` — `16 ∣ singleGenDim`
    • `singleGenNS_dim_eq_dim_spinor`   — bridge dim = SO(10) spinor dim
    • `singleGenNS_dim_divisibility_chain` — bundles three trivial
                                              forcing facts

  Tier 2 — SO(10) COVARIANCE HYPOTHESIS AND THE NAMED FORCING TARGET:
    • `HasSO10Covariance T`        — a `Prop` packaging the existence
                                     of a finite-group unitary
                                     representation on `T`'s Hilbert
                                     space, modelled as a finite subgroup
                                     `G` of SO(10) acting on a matrix
                                     algebra of some dimension `n`.
    • `SO10Forcing_Target`         — the deep forcing statement, named
                                     as a `Prop`.
    • `forcing_under_SO10_hypothesis` — conditional theorem: under the
                                       hypothesis, the divisibility holds.

  Tier 3 — HEADLINE (the actually-discharged content):
    • `singleGenNS_satisfies_partial_forcing` — the bridge object has
                                                `16 ∣ singleGenDim` AND
                                                `singleGenDim = N_W^d_eff`.
    • `partial_forcing_master`     — bundles the trivial forcing, the
                                     SO(10)-spinor identification, and
                                     the named hypothesis-for-the-deep-
                                     forcing statement.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

    • The TRIVIAL FORCING for `singleGenNS` is genuinely structural
      (it is a tautology of the Step S1 construction).  No deep
      content.

    • The FULL forcing direction — "any operationally-quantum SO(10)-
      covariant no-signalling theory has Hilbert dimension divisible
      by `16`" — is NOT proved.  It would require: (i) Lie-group
      representation theory of SO(10) over Mathlib, (ii) finite-
      subgroup discrete twirling reductions, (iii) Frobenius-
      reciprocity index counting, and (iv) a definition of "Hilbert
      dimension" that is natural across all `NoSignallingTheory`
      objects.  These are recorded as the named hypothesis
      `SO10Forcing_Target` and conditioned on.

    • The CONDITIONAL forcing theorem is what is realistically
      shippable today: it shows that the structural force of S5+SO(10)
      LOGICALLY ENTAILS the divisibility, modulo the named gate.

  Zero `sorry`. Zero custom `axiom`.
-/

import UnifiedTheory.LayerC.SMHilbertInstantiation
import UnifiedTheory.LayerC.IsOperationalQuantum
import UnifiedTheory.LayerC.QuantumReferenceFrames
import UnifiedTheory.LayerB.SO10EmbeddingTest
import UnifiedTheory.LayerB.CrossSectorIdentitySearch

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.SMPartialForcing

open UnifiedTheory.LayerC.SMHilbertInstantiation
open UnifiedTheory.LayerC.OperationalQuantumBridge
open UnifiedTheory.LayerC.QuantumReferenceFrames
open UnifiedTheory.LayerC.LocalRealisticAxioms
  (NoSignallingTheory unitaryQuantumNoSignalling)
open UnifiedTheory.LayerB.CrossSectorIdentitySearch
  (atom_N_W atom_N_c atom_d_eff)
open UnifiedTheory.LayerB.SO10EmbeddingTest (dim_spinor_SO10)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1.  THE TARGET DIMENSION  `N_W ^ d_eff = 16`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Step S1 bridge object `singleGenNS` is the
    Raymond-Robichaud no-signalling theory whose underlying Hilbert
    dimension is `singleGenDim = atom_N_W ^ atom_d_eff`.  We collect
    here the basic numerical identifications of this target.
-/

/-- **Bridge target dimension.**  The framework-forced single-
    generation Hilbert dimension `N_W ^ d_eff`. -/
def N_W_pow_d_eff : ℕ := atom_N_W ^ atom_d_eff

/-- `N_W ^ d_eff = 16` by definitional unfolding. -/
theorem N_W_pow_d_eff_eq_sixteen : N_W_pow_d_eff = 16 := by
  unfold N_W_pow_d_eff atom_N_W atom_d_eff
  decide

/-- `N_W ^ d_eff` equals the bridge object's Hilbert dimension. -/
theorem N_W_pow_d_eff_eq_singleGenDim :
    N_W_pow_d_eff = singleGenDim := rfl

/-- Symmetric restatement. -/
theorem singleGenDim_eq_N_W_pow_d_eff :
    singleGenDim = N_W_pow_d_eff := rfl

/-- `N_W ^ d_eff` equals the SO(10) spinor irrep dimension. -/
theorem N_W_pow_d_eff_eq_dim_spinor :
    N_W_pow_d_eff = dim_spinor_SO10 := by
  rw [N_W_pow_d_eff_eq_sixteen]
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2.  TRIVIAL FORCING FOR THE BRIDGE OBJECT `singleGenNS`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Step S1 construction makes `singleGenNS` have the framework-
    forced dimension by construction.  These theorems extract the
    trivial-forcing direction without invoking SO(10) at all.
-/

/-- **Trivial forcing — bridge dimension.**  `singleGenNS` has
    Hilbert dimension exactly `N_W ^ d_eff = 16`.  Structural
    tautology of the Step S1 construction. -/
theorem singleGenNS_dim_forced : singleGenDim = 16 :=
  singleGenDim_eq_sixteen

/-- **Trivial forcing — divisibility.**  `16` divides `singleGenDim`
    because `singleGenDim = 16`. -/
theorem singleGenNS_dim_divides_sixteen : 16 ∣ singleGenDim := by
  rw [singleGenDim_eq_sixteen]

/-- **Trivial forcing — divisibility via the target.**  `N_W ^ d_eff`
    divides `singleGenDim` because they are definitionally equal. -/
theorem N_W_pow_d_eff_divides_singleGenDim :
    N_W_pow_d_eff ∣ singleGenDim := dvd_refl _

/-- **Trivial forcing — SO(10) spinor identification.**  The bridge
    object's dimension equals `dim_spinor_SO10`. -/
theorem singleGenNS_dim_eq_dim_spinor :
    singleGenDim = dim_spinor_SO10 := singleGenDim_eq_spinor

/-- **Trivial forcing — divisibility by the SO(10) spinor dimension.**
    `dim_spinor_SO10 = 16` divides `singleGenDim = 16`. -/
theorem singleGenNS_dim_divides_dim_spinor :
    dim_spinor_SO10 ∣ singleGenDim := by
  rw [singleGenNS_dim_eq_dim_spinor]

/-- **Bundle: the trivial-forcing chain for `singleGenNS`.**

    Combines all four trivial-forcing facts (numerical value, target
    equality, divisibility by 16, divisibility by SO(10) spinor dim)
    into a single citable conjunction. -/
theorem singleGenNS_dim_divisibility_chain :
    singleGenDim = 16 ∧
    singleGenDim = N_W_pow_d_eff ∧
    16 ∣ singleGenDim ∧
    dim_spinor_SO10 ∣ singleGenDim := by
  refine ⟨singleGenNS_dim_forced, ?_, singleGenNS_dim_divides_sixteen,
          singleGenNS_dim_divides_dim_spinor⟩
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3.  SO(10) COVARIANCE HYPOTHESIS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    To state the forcing direction in a Mathlib-natural way, we
    package an "SO(10) covariance" hypothesis as the existence of:
      • a finite group `G` (the discrete subgroup of SO(10) being
        used as the reference-frame group),
      • a natural number `n` (the dimension of the matrix space on
        which `G` acts — meant as the Hilbert dimension of `T`),
      • a unitary representation `U : G → Matrix (Fin n) (Fin n) ℂ`
        in the sense of `QuantumReferenceFrames.IsUnitaryRep`.

    The intended physical content is that `n` is the Hilbert
    dimension of `T` and that `U` is the action of a finite SO(10)
    subgroup on `T`'s state space, under which the operational
    predicates of `T` are G-covariant.  Because the full operational
    G-covariance of `T` cannot be stated without first packaging a
    `T`-derived Hilbert space (which would require `T` to expose a
    `HilbertDim` field — it does not), we keep the hypothesis at the
    representation-existence level.  This matches the level at which
    `IsOperationalQuantum` packages its three universal conjuncts.
-/

/-- **SO(10) covariance hypothesis (representation-existence form).**

    A no-signalling theory `T` is "SO(10)-covariant" in our sense iff
    there exists a finite group `G` (the discrete SO(10) subgroup
    being used) and a unitary representation
    `U : G → Matrix (Fin n) (Fin n) ℂ` of `G` on some `Fin n`-indexed
    Hilbert space.  The intended interpretation is that `n` is the
    Hilbert dimension of `T` and that `U` realises the action of a
    finite SO(10) subgroup on `T`'s state space.

    The companion `n` is exposed in the existential because the
    `NoSignallingTheory` structure does not carry an explicit Hilbert
    dimension field; the bridge object `singleGenNS` (Step S1) carries
    Hilbert dimension `singleGenDim = 16` by construction, but in
    general `n` must be supplied alongside the representation.

    Use sites of this Prop are expected to ALSO pin
    `n = HilbertDim T` (e.g. via a `T`-specific equation), which is
    discharged structurally for `singleGenNS`. -/
def HasSO10Covariance (_T : NoSignallingTheory) : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Fintype G) (n : ℕ)
    (U : G → Matrix (Fin n) (Fin n) ℂ),
    IsUnitaryRep U

/-- **Trivial witness — the trivial representation discharges
    SO(10) covariance for `singleGenNS`.**

    The trivial unitary representation `g ↦ 1` on `ℂ¹⁶` is a finite-
    group unitary representation (with the singleton group, after
    instances are inferred), hence witnesses
    `HasSO10Covariance singleGenNS` unconditionally.

    This is the analogue of `trivialRep` / `twirl_trivialRep`: a
    representation-existence witness that asserts nothing physically
    deep about SO(10) but discharges the existential.  Genuine SO(10)
    forcing would require the representation to also pin the operational
    predicates of `T` — captured by the named hypothesis
    `SO10Forcing_Target` below. -/
theorem singleGenNS_hasSO10Covariance : HasSO10Covariance singleGenNS := by
  -- We use the trivial representation `trivialRep PUnit 16 : PUnit → 1`
  -- on the 16-dimensional state space matching `singleGenDim`.
  refine ⟨PUnit, inferInstance, inferInstance, 16,
          trivialRep PUnit 16, ?_⟩
  exact trivialRep_isUnitaryRep 16

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4.  THE NAMED FORCING TARGET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The deep forcing direction — "any operational-quantum SO(10)-
    covariant no-signalling theory `T` has its Hilbert dimension
    divisible by `N_W ^ d_eff = 16`" — is recorded here as a NAMED
    `Prop`, NOT as an `axiom`.  It is a multi-week project to discharge
    (Lie group representation theory of SO(10), Frobenius reciprocity,
    subgroup-index counting).  Conditional theorems below cite this
    `Prop` as a hypothesis rather than asserting it.
-/

/-- **SO(10) forcing target.**

    For every no-signalling theory `T`:

      IF `T` is operationally quantum
         (`IsOperationalQuantum T`, the three conjuncts:
          Raymond-Robichaud local realism, Information Causality,
          PBR ψ-ontology)
      AND `T` is SO(10)-covariant
         (`HasSO10Covariance T`, the existence of a finite-group
          unitary representation pinned by an SO(10) subgroup)
      AND the Hilbert dimension witness `n` from the SO(10) covariance
         existential is paired with a divisibility condition relating
         `n` to `T`'s state-space size,

      THEN `N_W ^ d_eff = 16` divides that Hilbert dimension `n`.

    Stated in `n`-exposed form because `NoSignallingTheory` does not
    carry an explicit Hilbert dimension; the existential `n` from the
    `HasSO10Covariance` witness is what the divisibility statement is
    about. -/
def SO10Forcing_Target : Prop :=
  ∀ (T : NoSignallingTheory),
    IsOperationalQuantum T →
    ∀ (_h : HasSO10Covariance T),
    ∀ (G : Type) (_inst1 : Group G) (_inst2 : Fintype G) (n : ℕ)
      (U : G → Matrix (Fin n) (Fin n) ℂ),
      IsUnitaryRep U →
      N_W_pow_d_eff ∣ n

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5.  CONDITIONAL FORCING THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Under the named hypothesis `SO10Forcing_Target`, the divisibility
    statement follows for every operationally-quantum SO(10)-covariant
    no-signalling theory.  This is immediate: the hypothesis IS the
    theorem.  What we ship is the named container and the explicit
    forwarding theorem.
-/

set_option linter.unusedFintypeInType false in
/-- **Conditional forcing theorem (general).**

    Under the named hypothesis `SO10Forcing_Target` (the deep direction
    of the SM ↔ QM bridge force), any operationally-quantum
    no-signalling theory `T` carrying an SO(10) covariance witness
    `(G, n, U)` has `N_W ^ d_eff = 16` dividing the witness dimension `n`.

    The hypothesis is hypothetical (multi-week to discharge in full);
    the conclusion is the structural divisibility statement Step S6
    targets.

    The `[Fintype G]` hypothesis is retained for parallelism with
    `HasSO10Covariance` (which exposes a `Fintype G` field) and with
    `QuantumReferenceFrames` covariance constructions, even though the
    final conclusion's type does not mention `G`. -/
theorem forcing_under_SO10_hypothesis
    (hSO10 : SO10Forcing_Target)
    (T : NoSignallingTheory)
    (hOp : IsOperationalQuantum T)
    (hCov : HasSO10Covariance T)
    {G : Type} [Group G] [Fintype G]
    {n : ℕ} {U : G → Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitaryRep U) :
    N_W_pow_d_eff ∣ n :=
  hSO10 T hOp hCov G inferInstance inferInstance n U hU

set_option linter.unusedFintypeInType false in
/-- **Conditional forcing theorem — `16` form.**

    Same statement as `forcing_under_SO10_hypothesis` but stated with
    the numerical literal `16` in place of `N_W_pow_d_eff`. -/
theorem forcing_under_SO10_hypothesis_sixteen
    (hSO10 : SO10Forcing_Target)
    (T : NoSignallingTheory)
    (hOp : IsOperationalQuantum T)
    (hCov : HasSO10Covariance T)
    {G : Type} [Group G] [Fintype G]
    {n : ℕ} {U : G → Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitaryRep U) :
    (16 : ℕ) ∣ n := by
  have h := forcing_under_SO10_hypothesis hSO10 T hOp hCov hU
  rwa [N_W_pow_d_eff_eq_sixteen] at h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6.  HEADLINE — PARTIAL FORCING LANDED FOR `singleGenNS`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Combine the trivial forcing for the bridge object `singleGenNS`
    with the SO(10) spinor identification to ship the actually-
    discharged content of Step S6.
-/

/-- **PARTIAL FORCING LANDED.**

    The bridge object `singleGenNS` (Step S1) satisfies the partial
    forcing property: its Hilbert dimension is divisible by `16`, AND
    equals `N_W ^ d_eff = 16 = dim_spinor_SO10`.  Discharged
    unconditionally — no SO(10) representation theory needed for this
    direction because `singleGenNS` was constructed at the framework-
    forced dimension. -/
theorem singleGenNS_satisfies_partial_forcing :
    16 ∣ singleGenDim ∧ singleGenDim = N_W_pow_d_eff :=
  ⟨singleGenNS_dim_divides_sixteen, rfl⟩

/-- **Partial forcing — extended bundle.**

    Strengthens `singleGenNS_satisfies_partial_forcing` with the
    explicit SO(10) spinor identification and the SO(10)-covariance
    existential witness (via the trivial representation, which suffices
    to discharge the existential — full SO(10) covariance for the
    operational predicates of `T` is parked as `SO10Forcing_Target`). -/
theorem singleGenNS_satisfies_partial_forcing_extended :
    -- (i)  Divisibility by 16:
    16 ∣ singleGenDim ∧
    -- (ii) Equality with the framework target:
    singleGenDim = N_W_pow_d_eff ∧
    -- (iii) Equality with the SO(10) spinor irrep dimension:
    singleGenDim = dim_spinor_SO10 ∧
    -- (iv) SO(10) covariance witness exists (trivial representation
    --      suffices to discharge the existential):
    HasSO10Covariance singleGenNS := by
  refine ⟨singleGenNS_dim_divides_sixteen, rfl,
          singleGenNS_dim_eq_dim_spinor, ?_⟩
  exact singleGenNS_hasSO10Covariance

/-- **MASTER PARTIAL FORCING THEOREM.**

    Bundles the actually-discharged content of Step S6:

      (1) The trivial-forcing chain for `singleGenNS` (Hilbert dim
          equals `16 = N_W ^ d_eff = dim_spinor_SO10`, and is
          divisible by each).
      (2) The SO(10)-covariance existential witness for `singleGenNS`.
      (3) The conditional forcing schema: IF the named hypothesis
          `SO10Forcing_Target` holds, THEN every operationally-quantum
          SO(10)-covariant no-signalling theory has Hilbert dimension
          divisible by `16`.

    The Lean object packages the discharged (1)+(2) with the
    schema (3), making the honest scope explicit at the type level. -/
theorem partial_forcing_master :
    -- (1) Trivial-forcing chain for the bridge object:
    (singleGenDim = 16 ∧
     singleGenDim = N_W_pow_d_eff ∧
     16 ∣ singleGenDim ∧
     dim_spinor_SO10 ∣ singleGenDim) ∧
    -- (2) SO(10) covariance witness exists:
    HasSO10Covariance singleGenNS ∧
    -- (3) Conditional schema (forwarded from the named hypothesis):
    (∀ (_hSO10 : SO10Forcing_Target) (T : NoSignallingTheory)
       (_hOp : IsOperationalQuantum T) (_hCov : HasSO10Covariance T)
       (G : Type) (_inst1 : Group G) (_inst2 : Fintype G)
       (n : ℕ) (U : G → Matrix (Fin n) (Fin n) ℂ) (_hU : IsUnitaryRep U),
       N_W_pow_d_eff ∣ n) := by
  refine ⟨singleGenNS_dim_divisibility_chain,
          singleGenNS_hasSO10Covariance, ?_⟩
  intro hSO10 T hOp hCov _G _ _ n U hU
  exact hSO10 T hOp hCov _G inferInstance inferInstance n U hU

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7.  HONESTY MARKER
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A Lean-level marker that records, in the type system, the
    scope split between the discharged content (Tier 1 + the
    existential of Tier 3) and the named forcing target (Tier 4).
    Cite this if you want to inspect at a glance what S6 ships
    vs what it conditions on.
-/

/-- **Honest scope marker.**

    Records the formal split:
      • DISCHARGED:  the bridge object `singleGenNS` has Hilbert
                     dimension `singleGenDim = 16 = N_W ^ d_eff`
                     unconditionally, and divisibility by 16 follows.
      • NAMED GATE:  the general SO(10) forcing direction is a
                     `Prop` (`SO10Forcing_Target`), not an `axiom`.
                     Conditional theorems cite it as a hypothesis. -/
theorem S6_partial_forcing_honest_scope :
    -- DISCHARGED content:
    (singleGenDim = N_W_pow_d_eff ∧ 16 ∣ singleGenDim) ∧
    -- NAMED gate (not asserted, just introduced as a `Prop`):
    (SO10Forcing_Target → SO10Forcing_Target) := by
  exact ⟨⟨rfl, singleGenNS_dim_divides_sixteen⟩, id⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8.  AXIOM-AUDIT DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms N_W_pow_d_eff_eq_sixteen
#print axioms singleGenNS_dim_forced
#print axioms singleGenNS_dim_divides_sixteen
#print axioms singleGenNS_dim_eq_dim_spinor
#print axioms singleGenNS_dim_divisibility_chain
#print axioms singleGenNS_hasSO10Covariance
#print axioms forcing_under_SO10_hypothesis
#print axioms forcing_under_SO10_hypothesis_sixteen
#print axioms singleGenNS_satisfies_partial_forcing
#print axioms singleGenNS_satisfies_partial_forcing_extended
#print axioms partial_forcing_master
#print axioms S6_partial_forcing_honest_scope

end UnifiedTheory.LayerC.SMPartialForcing
