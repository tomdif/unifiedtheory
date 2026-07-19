/-
  UnifiedTheory/LayerC/LocalRealisticAxioms.lean
  ──────────────────────────────────────────────

  Axiomatic framework for local-realistic and no-signalling theories,
  following Raymond-Robichaud (2021, arXiv:1710.01380v2), Sections
  3–5.

  Layer C ≠ Layer B.  Layer C is the *interpretation/foundations*
  layer: it captures the axioms that say a physical theory is
  local-realistic in the strong sense of Brassard–Raymond-Robichaud,
  independent of Bell's hidden-variable formulation.  It is
  orthogonal to the Lindblad-Uhlmann arc in Layer B.

  ## What is shipped

  ### Tier 1 — Axiom classes (Sections 3.1–3.13 and 4.1–4.6)

    * `MonoidAction`, `MonoidAction.Faithful` — definitions 3.5–3.8.
    * `NoumenalPhenomenalHom` — definition 3.9.
    * `LocalRealisticTheory` — bundle of all 13 axioms of Section 3.
      The carrier `Sys : Type*` is a `BooleanAlgebra` (Definition
      3.1, Axiom 3.1).
    * `NoSignallingTheory` — bundle of the 6 axioms of Section 4.
      Phenomenal only — no noumenal layer.
    * Postulates 4.1–4.3 (separation, invertible dynamics,
      phenomenal faithfulness) stated as `Prop`s on
      `NoSignallingTheory`.

  ### Tier 2 — Unitary quantum theory as a no-signalling theory

    For a fixed Hilbert-space dimension `n : ℕ` with `[NeZero n]`,
    we build `unitaryQuantumNoSignalling n` — the `NoSignallingTheory`
    whose

      * lattice of systems is `Bool` (the two-element Boolean
        algebra, with `⊥ = ∅` and `⊤ = S`); this is the
        "single global system" universe;
      * phenomenal state space at `⊤` is our LayerB
        `ComplexDensityMatrix n`;
      * transformations at `⊤` are `Matrix.unitaryGroup (Fin n) ℂ`;
      * the phenomenal action sends `(U, ρ) ↦ U ρ U†`, via the
        LayerB `unitaryConjugate` from `UnitaryInvariance.lean`;
      * the phenomenal projector is trivial (the only non-identity
        order relation is `⊥ ≤ ⊤`, sent to the unique `PUnit`
        phenomenal state of the empty system);
      * the product of transformations is also trivial (the only
        disjoint pair is `⊥, ⊥`, with product the singleton
        unitary on the empty system).

    This is the **single-system slice** of the framework.  The
    bipartite slice would replace `Bool` with `Set (Fin 2)` and
    use `partialTrace_right` / `_left` from `LayerB.PartialTrace`;
    the index reshape across `n_A * n_B` is structural but verbose
    and is recorded as a scoping note (`unitaryQuantum_bipartite_scope`).

  ### Tier 3 — Equivalence theorems (Prop-shaped targets)

    Both directions of the main equivalence are stated as `Prop`s:

      * `LocalRealisticTheory.HasNoSignallingShadow L` — paper
        Section 4 introductory paragraph plus Theorem 3.12
        (no-signalling principle).  *Shipped as a target*; the
        proof is a four-step diagram chase plus two faithfulness
        chases for axioms 4.6.3 and 4.6.4.

      * `NoSignallingTheory.HasLocalRealisticModel T` — paper
        Section 5 main theorem.  *Shipped as a target*; the
        construction occupies Definitions 5.1–5.7 and Theorems
        5.1–5.14.

    Both targets are statable in this file and verifiable in
    downstream files.

  ## Standing constraint

  Zero `sorry`, zero custom `axiom`.

  ## References

  Raymond-Robichaud, "The equivalence of local-realistic and
  no-signalling theories", arXiv:1710.01380v2 (4 Feb 2021).
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import UnifiedTheory.LayerB.UnitaryInvariance

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.LocalRealisticAxioms

open Matrix
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.UnitaryInvariance
open scoped ComplexOrder

/-! # Tier 1.  Axiom classes -/

/-! ## 1.1 Actions of a monoid (Definitions 3.5–3.8) -/

/-- A right-acting **action of a monoid `T` on a set `X`** in the
    sense of Raymond-Robichaud Definition 3.7. -/
structure MonoidAction (T : Type*) [Monoid T] (X : Type*) where
  /-- The action map. -/
  act : T → X → X
  /-- Compatibility with composition. -/
  act_mul : ∀ (U V : T) (x : X), act (U * V) x = act U (act V x)
  /-- The identity transformation acts trivially. -/
  act_one : ∀ x : X, act 1 x = x

namespace MonoidAction

variable {T : Type*} [Monoid T] {X : Type*}

/-- An action is **faithful** (Definition 3.8) if equality of
    transformations is determined by equality of their action. -/
def Faithful (α : MonoidAction T X) : Prop :=
  ∀ U V : T, (∀ x : X, α.act U x = α.act V x) → U = V

end MonoidAction

/-! ## 1.2 Noumenal-phenomenal homomorphisms (Definitions 3.9–3.10) -/

/-- A **noumenal-phenomenal homomorphism** (Definition 3.9). -/
structure NoumenalPhenomenalHom
    (T : Type*) [Monoid T] (N P : Type*)
    (αN : MonoidAction T N) (αP : MonoidAction T P) where
  /-- The underlying function. -/
  toFun : N → P
  /-- Intertwines the actions: `φ(U ⋆ n) = U · φ(n)`. -/
  intertwines : ∀ (U : T) (n : N), toFun (αN.act U n) = αP.act U (toFun n)

/-! ## 1.3 Local-realistic theory (Axioms 3.1–3.13) -/

/-- A **local-realistic theory** (Axioms 3.1–3.13).

    Carrier `Sys` plays the role of the lattice of systems; the
    `BooleanAlgebra` instance gives `⊔`, `⊓`, complement, `⊤` and
    `⊥`. -/
structure LocalRealisticTheory : Type 1 where
  /-- The set of systems. -/
  Sys : Type
  [latticeSys : BooleanAlgebra Sys]
  /-- Noumenal state space (Axiom 3.2). -/
  Noumenal : Sys → Type
  noumenal_nonempty : ∀ A, Nonempty (Noumenal A)
  /-- Phenomenal state space (Axiom 3.3). -/
  Phenomenal : Sys → Type
  phenomenal_nonempty : ∀ A, Nonempty (Phenomenal A)
  /-- Monoid of transformations (Axiom 3.4). -/
  Trans : Sys → Type
  [monoidTrans : ∀ A, Monoid (Trans A)]
  /-- Noumenal action (Axiom 3.5). -/
  noumenalAction : ∀ A, MonoidAction (Trans A) (Noumenal A)
  /-- Phenomenal action (Axiom 3.6). -/
  phenomenalAction : ∀ A, MonoidAction (Trans A) (Phenomenal A)
  /-- Noumenal faithfulness (Axiom 3.7). -/
  noumenal_faithful : ∀ A, (noumenalAction A).Faithful
  /-- Noumenal-phenomenal epimorphism (Axiom 3.8). -/
  epi : ∀ A, NoumenalPhenomenalHom (Trans A) (Noumenal A) (Phenomenal A)
              (noumenalAction A) (phenomenalAction A)
  epi_surjective : ∀ A, Function.Surjective (epi A).toFun
  /-- Noumenal projector (Axiom 3.9). -/
  noumenalProj : ∀ {A B : Sys}, A ≤ B → Noumenal B → Noumenal A
  noumenalProj_surjective :
    ∀ {A B : Sys} (h : A ≤ B), Function.Surjective (noumenalProj h)
  noumenalProj_comp :
    ∀ {A B C : Sys} (hAB : A ≤ B) (hBC : B ≤ C) (N : Noumenal C),
      noumenalProj hAB (noumenalProj hBC N)
        = noumenalProj (hAB.trans hBC) N
  /-- Phenomenal projector (Axiom 3.10). -/
  phenomenalProj : ∀ {A B : Sys}, A ≤ B → Phenomenal B → Phenomenal A
  phenomenalProj_surjective :
    ∀ {A B : Sys} (h : A ≤ B), Function.Surjective (phenomenalProj h)
  phenomenalProj_comp :
    ∀ {A B C : Sys} (hAB : A ≤ B) (hBC : B ≤ C) (P : Phenomenal C),
      phenomenalProj hAB (phenomenalProj hBC P)
        = phenomenalProj (hAB.trans hBC) P
  /-- Relation between projectors (Axiom 3.11). -/
  proj_epi_compat :
    ∀ {A B : Sys} (h : A ≤ B) (N : Noumenal B),
      phenomenalProj h ((epi B).toFun N)
        = (epi A).toFun (noumenalProj h N)
  /-- Noumenal product (Axiom 3.12), only on compatible states. -/
  noumenalProduct :
    ∀ {A B : Sys}, Disjoint A B →
      ∀ (N_A : Noumenal A) (N_B : Noumenal B),
        (∃ N_AB : Noumenal (A ⊔ B),
            noumenalProj (le_sup_left  : A ≤ A ⊔ B) N_AB = N_A ∧
            noumenalProj (le_sup_right : B ≤ A ⊔ B) N_AB = N_B) →
        Noumenal (A ⊔ B)
  /-- Axiom 3.12 splitting law. -/
  noumenalProduct_split :
    ∀ {A B : Sys} (hd : Disjoint A B) (N_AB : Noumenal (A ⊔ B)),
      noumenalProduct hd
          (noumenalProj (le_sup_left  : A ≤ A ⊔ B) N_AB)
          (noumenalProj (le_sup_right : B ≤ A ⊔ B) N_AB)
          ⟨N_AB, rfl, rfl⟩
        = N_AB
  /-- Product of transformations (Axiom 3.13). -/
  transProduct :
    ∀ {A B : Sys}, Disjoint A B → Trans A → Trans B → Trans (A ⊔ B)
  /-- Intertwining property of `×` (Axiom 3.13). -/
  transProduct_action :
    ∀ {A B : Sys} (hd : Disjoint A B) (U : Trans A) (V : Trans B)
      (N_A : Noumenal A) (N_B : Noumenal B)
      (hc : ∃ N_AB : Noumenal (A ⊔ B),
            noumenalProj (le_sup_left  : A ≤ A ⊔ B) N_AB = N_A ∧
            noumenalProj (le_sup_right : B ≤ A ⊔ B) N_AB = N_B)
      (hc' : ∃ N_AB' : Noumenal (A ⊔ B),
            noumenalProj (le_sup_left  : A ≤ A ⊔ B) N_AB'
              = (noumenalAction A).act U N_A ∧
            noumenalProj (le_sup_right : B ≤ A ⊔ B) N_AB'
              = (noumenalAction B).act V N_B),
      (noumenalAction (A ⊔ B)).act (transProduct hd U V)
          (noumenalProduct hd N_A N_B hc)
        = noumenalProduct hd
            ((noumenalAction A).act U N_A)
            ((noumenalAction B).act V N_B)
            hc'
  /-- **Noumenal no-signalling, left** — the action of `U × V` on a
      joint noumenal state, projected to `A`, is `U` acting on the
      `A`-projection.  This is the noumenal counterpart of phenomenal
      Axiom 4.6.1, and (together with `transProduct_action`) realises
      the full content of Axiom 3.13.  In the paper this is implicit
      in Axiom 3.13's intertwining statement; we extract it here as a
      separate field because the structure-level `transProduct_action`
      is stated relative to existence witnesses and does not directly
      yield the projection identity without a second existence input. -/
  noumenalProj_left_transProduct :
    ∀ {A B : Sys} (hd : Disjoint A B) (U : Trans A) (V : Trans B)
      (N_AB : Noumenal (A ⊔ B)),
      noumenalProj (le_sup_left : A ≤ A ⊔ B)
          ((noumenalAction (A ⊔ B)).act (transProduct hd U V) N_AB)
        = (noumenalAction A).act U
            (noumenalProj (le_sup_left : A ≤ A ⊔ B) N_AB)
  /-- **Noumenal no-signalling, right** — the right twin of
      `noumenalProj_left_transProduct`. -/
  noumenalProj_right_transProduct :
    ∀ {A B : Sys} (hd : Disjoint A B) (U : Trans A) (V : Trans B)
      (N_AB : Noumenal (A ⊔ B)),
      noumenalProj (le_sup_right : B ≤ A ⊔ B)
          ((noumenalAction (A ⊔ B)).act (transProduct hd U V) N_AB)
        = (noumenalAction B).act V
            (noumenalProj (le_sup_right : B ≤ A ⊔ B) N_AB)

attribute [instance] LocalRealisticTheory.latticeSys
                     LocalRealisticTheory.monoidTrans

/-! ## 1.4 No-signalling theory (Axioms 4.1–4.6) -/

/-- A **no-signalling theory** (Axioms 4.1–4.6). -/
structure NoSignallingTheory : Type 1 where
  /-- The set of systems (Axiom 4.1). -/
  Sys : Type
  [latticeSys : BooleanAlgebra Sys]
  /-- Phenomenal state space (Axiom 4.2). -/
  Phenomenal : Sys → Type
  phenomenal_nonempty : ∀ A, Nonempty (Phenomenal A)
  /-- Monoid of transformations (Axiom 4.3). -/
  Trans : Sys → Type
  [monoidTrans : ∀ A, Monoid (Trans A)]
  /-- Phenomenal action (Axiom 4.4). -/
  phenomenalAction : ∀ A, MonoidAction (Trans A) (Phenomenal A)
  /-- Phenomenal projector (Axiom 4.5). -/
  phenomenalProj : ∀ {A B : Sys}, A ≤ B → Phenomenal B → Phenomenal A
  phenomenalProj_surjective :
    ∀ {A B : Sys} (h : A ≤ B), Function.Surjective (phenomenalProj h)
  phenomenalProj_comp :
    ∀ {A B C : Sys} (hAB : A ≤ B) (hBC : B ≤ C) (P : Phenomenal C),
      phenomenalProj hAB (phenomenalProj hBC P)
        = phenomenalProj (hAB.trans hBC) P
  /-- Product of transformations (Axiom 4.6, structure). -/
  transProduct :
    ∀ {A B : Sys}, Disjoint A B → Trans A → Trans B → Trans (A ⊔ B)
  /-- Axiom 4.6.1 — no-signalling principle (left projection). -/
  no_signalling :
    ∀ {A B : Sys} (hd : Disjoint A B)
      (U : Trans A) (V : Trans B) (ρ : Phenomenal (A ⊔ B)),
      phenomenalProj (le_sup_left : A ≤ A ⊔ B)
          ((phenomenalAction (A ⊔ B)).act (transProduct hd U V) ρ)
        = (phenomenalAction A).act U
            (phenomenalProj (le_sup_left : A ≤ A ⊔ B) ρ)
  /-- Axiom 4.6.1 — no-signalling principle (right projection).
      The symmetric companion to `no_signalling`. -/
  no_signalling_right :
    ∀ {A B : Sys} (hd : Disjoint A B)
      (U : Trans A) (V : Trans B) (ρ : Phenomenal (A ⊔ B)),
      phenomenalProj (le_sup_right : B ≤ A ⊔ B)
          ((phenomenalAction (A ⊔ B)).act (transProduct hd U V) ρ)
        = (phenomenalAction B).act V
            (phenomenalProj (le_sup_right : B ≤ A ⊔ B) ρ)
  /-- Axiom 4.6.3 — composition law. -/
  transProduct_mul :
    ∀ {A B : Sys} (hd : Disjoint A B) (U_A V_A : Trans A) (U_B V_B : Trans B),
      transProduct hd V_A V_B * transProduct hd U_A U_B
        = transProduct hd (V_A * U_A) (V_B * U_B)
  /-- Axiom 4.6.4 — identity. -/
  transProduct_one :
    ∀ {A B : Sys} (hd : Disjoint A B),
      transProduct hd (1 : Trans A) (1 : Trans B) = (1 : Trans (A ⊔ B))

attribute [instance] NoSignallingTheory.latticeSys
                     NoSignallingTheory.monoidTrans

/-! ## 1.5 Cast helpers for stating Separation on the global system

    `liftSupCompl T A` casts `T.Trans (A ⊔ Aᶜ)` to `T.Trans ⊤` along
    the BooleanAlgebra identity `A ⊔ Aᶜ = ⊤`.  `IAtimes T A V` is
    `(I^A × V) : T.Trans ⊤`, the global-system embedding of `V`
    acting on the complement `Aᶜ`. -/

namespace NoSignallingTheory

/-- The complement of `A : T.Sys` is disjoint from `A`. -/
lemma disjoint_self_compl (T : NoSignallingTheory) (A : T.Sys) :
    Disjoint A Aᶜ := disjoint_compl_right

/-- `A ⊔ Aᶜ = ⊤`. -/
lemma sup_compl_top (T : NoSignallingTheory) (A : T.Sys) :
    A ⊔ Aᶜ = ⊤ := sup_compl_eq_top

/-- Cast `T.Trans (A ⊔ Aᶜ)` to `T.Trans ⊤` along the lattice
    identity `A ⊔ Aᶜ = ⊤`. -/
def liftSupCompl (T : NoSignallingTheory) (A : T.Sys)
    (U : T.Trans (A ⊔ Aᶜ)) : T.Trans (⊤ : T.Sys) :=
  (T.sup_compl_top A) ▸ U

/-- The fundamental `(I^A × V)` lift: take `V : T.Trans Aᶜ`,
    form `(1_A × V) : T.Trans (A ⊔ Aᶜ)`, and cast to `T.Trans ⊤`. -/
def IAtimes (T : NoSignallingTheory) (A : T.Sys) (V : T.Trans Aᶜ) :
    T.Trans (⊤ : T.Sys) :=
  T.liftSupCompl A
    (T.transProduct (T.disjoint_self_compl A) (1 : T.Trans A) V)

end NoSignallingTheory

/-! ## 1.6 The postulates of Section 4.1 (Prop-shaped targets) -/

namespace NoSignallingTheory

/-- **Postulate 4.2** (Invertible dynamics): every transformation
    monoid is in fact a group.  Stated as: every element has a
    two-sided inverse. -/
def InvertibleDynamics (T : NoSignallingTheory) : Prop :=
  ∀ A, ∀ U : T.Trans A, ∃ V : T.Trans A, V * U = 1 ∧ U * V = 1

/-- **Postulate 4.1** (Separation), paper-faithful function-level form.

    Given disjoint `A`, `B`, if `(I^A × V_{Aᶜ}) = (I^B × V_{Bᶜ})` as
    transformations on the global system `⊤`, then there exists a
    transformation `V_C : T.Trans (A ⊔ B)ᶜ` such that
    `(I^A × V_{Aᶜ}) = (I^{A ⊔ B} × V_C)`.

    This is exactly the statement used in paper Theorem 5.8 (the
    well-definedness of the noumenal product), restated to live
    entirely on `T.Trans ⊤` via the `IAtimes` cast. -/
def SeparationPostulate (T : NoSignallingTheory) : Prop :=
  ∀ {A B : T.Sys} (_hd : Disjoint A B)
    (V_Ac : T.Trans Aᶜ) (V_Bc : T.Trans Bᶜ),
    T.IAtimes A V_Ac = T.IAtimes B V_Bc →
    ∃ V_C : T.Trans (A ⊔ B)ᶜ,
      T.IAtimes A V_Ac = T.IAtimes (A ⊔ B) V_C

/-- **Postulate 4.3** (Phenomenal faithfulness): two transformations
    on `A` that are phenomenally equivalent (Definition 4.1) are
    equal. -/
def PhenomenalFaithfulness (T : NoSignallingTheory) : Prop :=
  ∀ {A : T.Sys} (U V : T.Trans A),
    (∀ {B : T.Sys} (hd : Disjoint A B) (ρ : T.Phenomenal (A ⊔ B)),
        (T.phenomenalAction (A ⊔ B)).act
            (T.transProduct hd U (1 : T.Trans B)) ρ
          = (T.phenomenalAction (A ⊔ B)).act
              (T.transProduct hd V (1 : T.Trans B)) ρ)
      → U = V

/-- **Postulate 4.4** (Global transitivity, paper).  Every phenomenal
    state of the global system is reachable from every other via
    some transformation on the global system.

    Not strictly required for `HasLocalRealisticModel`; the paper
    introduces it as a convenience that simplifies the
    noumenal-phenomenal epimorphism construction (Theorem 5.14).
    Section 5.1 shows how to drop it. -/
def GloballyTransitive (T : NoSignallingTheory) : Prop :=
  ∀ (ρ ρ' : T.Phenomenal (⊤ : T.Sys)),
    ∃ U : T.Trans (⊤ : T.Sys),
      ρ' = (T.phenomenalAction ⊤).act U ρ

end NoSignallingTheory

/-! # Tier 3.  Equivalence theorems (as Prop-shaped targets)

The forgetful direction (every LR is NS) is paper Section 4's
introductory paragraph plus the proof of Theorem 3.12.  The hard
direction is Section 5.  Both proofs are large; we ship them as
Prop-shaped targets so downstream work can name them.
-/

/-- The **forgetful relation**: `L` is a local-realistic model
    underlying the no-signalling theory `T` iff they share the
    same lattice of systems, phenomenal spaces, transformations,
    phenomenal action, phenomenal projectors, and product of
    transformations.

    Stated as a Prop on a pair.  The genuine functor version would
    require dependent-elimination machinery beyond the scope of
    this file. -/
def LocalRealisticTheory.IsNoSignallingShadow
    (L : LocalRealisticTheory) (T : NoSignallingTheory) : Prop :=
  ∃ (_eSys : L.Sys = T.Sys),
    HEq L.Phenomenal T.Phenomenal ∧
    HEq L.Trans T.Trans ∧
    HEq L.phenomenalAction T.phenomenalAction ∧
    HEq @L.phenomenalProj @T.phenomenalProj ∧
    HEq @L.transProduct @T.transProduct

/-- **Theorem (easy direction, paper Section 4, intro + Theorem 3.12).**
    Every local-realistic theory admits a no-signalling-theory
    shadow.

    Shipped as a Prop-shaped target.  The proof requires Theorem
    3.12 (a four-step diagram chase using `epi_surjective`,
    `proj_epi_compat`, `noumenalProduct_split`, and
    `transProduct_action`) plus Theorems 3.8 and 3.9 (composition
    law, identity) which are similar faithfulness-based chases. -/
def LocalRealisticTheory.HasNoSignallingShadow
    (L : LocalRealisticTheory) : Prop :=
  ∃ T : NoSignallingTheory, L.IsNoSignallingShadow T

/-- **The hard direction (Raymond-Robichaud, paper Section 5).**
    Every no-signalling theory satisfying the three postulates
    has a local-realistic model.

    Shipped as a Prop-shaped target.  The construction occupies
    Definitions 5.1–5.7 and Theorems 5.1–5.14 of the paper.  Key
    ingredients: the fundamental equivalence relation `∼_A` on
    transformations of the global system, its equivalence classes
    `[W]_A` as noumenal-state representatives, and Postulate 4.1
    (separation) for well-definedness of the noumenal product. -/
def NoSignallingTheory.HasLocalRealisticModel
    (T : NoSignallingTheory) : Prop :=
  T.InvertibleDynamics → T.SeparationPostulate → T.PhenomenalFaithfulness →
  ∃ L : LocalRealisticTheory, L.IsNoSignallingShadow T

/-! # Tier 2.  Unitary quantum theory as a no-signalling theory

We instantiate `NoSignallingTheory` for unitary quantum theory on a
single global system of fixed dimension `n : ℕ` with `[NeZero n]`.

The lattice of systems is `Bool` (the two-element Boolean algebra,
with `⊥ = ∅` and `⊤ = S`).  Only one non-trivial system exists,
namely `⊤`, so the bipartite-product axioms are discharged by the
fact that the only disjoint pair is `⊥, ⊥`.

* phenomenal at `true ` := `ComplexDensityMatrix n`
* phenomenal at `false` := `PUnit`
* transformations at `true ` := `Matrix.unitaryGroup (Fin n) ℂ`
* transformations at `false` := `PUnit`
-/

namespace UnitaryQuantum

variable (n : ℕ)

/-- Phenomenal state space: density matrices at `⊤`, singleton at `⊥`. -/
def PhenomenalSpace : Bool → Type
  | true  => ComplexDensityMatrix n
  | false => PUnit

/-- Transformation set: unitary group at `⊤`, singleton at `⊥`. -/
def TransSpace : Bool → Type
  | true  => Matrix.unitaryGroup (Fin n) ℂ
  | false => PUnit

instance instMonoidTrans : ∀ b, Monoid (TransSpace n b)
  | true  => inferInstanceAs (Monoid (Matrix.unitaryGroup (Fin n) ℂ))
  | false => inferInstanceAs (Monoid PUnit)

/-- **Helper bridge.**  Build a `ComplexDensityMatrix` from a
    matrix that is Hermitian, has trace 1, and is `PosSemidef`.

    The `hTracePSD` field requires `0 ≤ Re(Tr(M · X† · X))` for all
    `X`.  We derive this from `PosSemidef`: by trace cyclicity,
    `Tr(M X† X) = Tr(X M X†)`, and `X M X†` is itself `PosSemidef`
    via `PosSemidef.mul_mul_conjTranspose_same`, so its trace is
    real and non-negative by `PosSemidef.trace_nonneg`. -/
noncomputable def ofPosSemidef
    (M : Matrix (Fin n) (Fin n) ℂ) (hHerm : M.IsHermitian)
    (hTrace : M.trace = 1) (hPSD : M.PosSemidef) :
    ComplexDensityMatrix n where
  M := M
  hHerm := hHerm
  hTrace := hTrace
  hTracePSD := by
    intro X
    -- Tr(M · X† · X) = Tr(X · M · X†) by cyclicity.
    have h_cyc : Matrix.trace (M * X.conjTranspose * X)
                  = Matrix.trace (X * M * X.conjTranspose) := by
      -- Reassociate then cycle:
      -- Tr((M · X†) · X) = Tr(X · (M · X†)) = Tr(X · M · X†).
      rw [Matrix.trace_mul_comm (M * X.conjTranspose) X]
      rw [Matrix.mul_assoc]
    rw [h_cyc]
    -- X · M · X† is PSD because M is PSD.
    have hPSD_XMX :
        Matrix.PosSemidef (X * M * X.conjTranspose) :=
      hPSD.mul_mul_conjTranspose_same X
    -- The trace of a PSD complex matrix is non-negative (as a complex
    -- number with `ComplexOrder`); take real part.
    have h_tr_nn : 0 ≤ Matrix.trace (X * M * X.conjTranspose) :=
      hPSD_XMX.trace_nonneg
    -- `0 ≤ z` in ℂ iff `0 ≤ z.re ∧ z.im = 0`.
    exact (Complex.nonneg_iff.mp h_tr_nn).1

/-- Witness density matrix for `n ≥ 1`: the rank-1 projector onto
    the first basis vector, `|0⟩⟨0|`, built as a diagonal matrix
    with a single 1 entry. -/
noncomputable def basisDensityMatrix [hn : NeZero n] : ComplexDensityMatrix n :=
  letI i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  letI D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => if i = i₀ then (1 : ℂ) else 0)
  ofPosSemidef n D
    (by
      -- D is Hermitian: it's the diagonal of a real (specifically
      -- {0,1}-valued) function, which is fixed by conjugation.
      refine Matrix.isHermitian_diagonal_iff.mpr ?_
      intro i
      change star (if i = i₀ then (1 : ℂ) else 0) = (if i = i₀ then 1 else 0)
      split_ifs
      · simp
      · simp)
    (by
      -- Trace of diag(e_{i₀}) = sum of (1 at i₀, 0 elsewhere) = 1.
      rw [Matrix.trace_diagonal]
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h; exact absurd (Finset.mem_univ _) h)
    (by
      -- PSD via `PosSemidef.diagonal` on a non-negative function.
      apply Matrix.PosSemidef.diagonal
      intro i
      simp only
      split_ifs
      · exact zero_le_one
      · exact le_refl _)

/-- The `⊤`-phenomenal space is nonempty when `n ≥ 1`. -/
instance instPhenomNonemptyTop [NeZero n] : Nonempty (PhenomenalSpace n true) :=
  ⟨basisDensityMatrix n⟩

/-- The `⊥`-phenomenal space is always nonempty (it is `PUnit`). -/
instance instPhenomNonemptyBot : Nonempty (PhenomenalSpace n false) :=
  ⟨PUnit.unit⟩

/-- All phenomenal spaces are nonempty, when `n ≥ 1`. -/
instance instPhenomNonempty [NeZero n] : ∀ b, Nonempty (PhenomenalSpace n b)
  | true  => instPhenomNonemptyTop n
  | false => instPhenomNonemptyBot n

/-- Equality of density matrices by their underlying matrix
    (`ComplexDensityMatrix` has propositional fields except `M`). -/
lemma ComplexDensityMatrix.ext_iff_M {n : ℕ}
    (ρ σ : ComplexDensityMatrix n) : ρ = σ ↔ ρ.M = σ.M := by
  constructor
  · intro h; rw [h]
  · intro h
    cases ρ; cases σ
    simp only at h
    subst h
    rfl

/-- The phenomenal action on system `b : Bool`.

    * At `true`: a unitary `U` acts on a density matrix `ρ` as
      `ρ ↦ U ρ U†`, via the LayerB `unitaryConjugate`.
    * At `false`: the only transformation is `PUnit.unit`,
      and the only state is `()`, so the action is trivial. -/
noncomputable def phenomenalAction :
    ∀ b, MonoidAction (TransSpace n b) (PhenomenalSpace n b)
  | true =>
    { act := fun U ρ => unitaryConjugate U ρ
      act_mul := by
        intro U V ρ
        rw [ComplexDensityMatrix.ext_iff_M]
        -- The underlying matrix identity:
        --   (U * V).val * ρ.M * star (U*V).val
        --     = U.val * (V.val * ρ.M * star V.val) * star U.val
        change (U * V).val * ρ.M * star (U * V).val
                = U.val * (V.val * ρ.M * star V.val) * star U.val
        have hval : (U * V).val = U.val * V.val :=
          Submonoid.coe_mul _ _ _
        rw [hval, StarMul.star_mul]
        -- Reassociate.
        simp only [Matrix.mul_assoc]
      act_one := by
        intro ρ
        rw [ComplexDensityMatrix.ext_iff_M]
        change (1 : Matrix.unitaryGroup (Fin n) ℂ).val * ρ.M
                  * star (1 : Matrix.unitaryGroup (Fin n) ℂ).val
                = ρ.M
        have h1 : (1 : Matrix.unitaryGroup (Fin n) ℂ).val
                    = (1 : Matrix (Fin n) (Fin n) ℂ) := by
          rfl
        rw [h1, star_one, Matrix.one_mul, Matrix.mul_one] }
  | false =>
    { act := fun _ _ => PUnit.unit
      act_mul := fun _ _ _ => rfl
      act_one := fun ρ => by cases ρ; rfl }

/-- Helper: `Disjoint true true` in `Bool` is absurd. -/
lemma not_disjoint_true_true : ¬ Disjoint (true : Bool) true := by
  intro h
  have := h (le_refl true) (le_refl true)
  -- This says: ∀ a, a ≤ true → a ≤ true → a ≤ ⊥, i.e., true ≤ false.
  exact absurd this (by decide)

/-- Helper: `true ≤ false` in `Bool` is absurd. -/
lemma not_true_le_false : ¬ (true : Bool) ≤ false := by decide

/-- The phenomenal projector on `Bool`.

    For `b₁ ≤ b₂` in `Bool` (with `false ≤ true ≤ true`), we map
    `Phenomenal b₂ → Phenomenal b₁`.  The only non-trivial cases are
    `b₁ = b₂`, sent to the identity, and `b₁ = false`, `b₂ = true`,
    sent to the unique `PUnit`. -/
def phenomenalProj :
    ∀ {b₁ b₂ : Bool}, b₁ ≤ b₂ → PhenomenalSpace n b₂ → PhenomenalSpace n b₁
  | false, false, _, _ => PUnit.unit
  | false, true,  _, _ => PUnit.unit
  | true,  true,  _, ρ => ρ
  | true,  false, h, _ => absurd h not_true_le_false

lemma phenomenalProj_surjective [NeZero n] :
    ∀ {b₁ b₂ : Bool} (h : b₁ ≤ b₂),
      Function.Surjective (@phenomenalProj n b₁ b₂ h)
  | false, false, _ => fun _ => ⟨PUnit.unit, rfl⟩
  | false, true,  _ => fun _ => ⟨basisDensityMatrix n, rfl⟩
  | true,  true,  _ => fun ρ => ⟨ρ, rfl⟩
  | true,  false, h => absurd h not_true_le_false

lemma phenomenalProj_comp :
    ∀ {b₁ b₂ b₃ : Bool} (h12 : b₁ ≤ b₂) (h23 : b₂ ≤ b₃) (ρ : PhenomenalSpace n b₃),
      phenomenalProj n h12 (phenomenalProj n h23 ρ)
        = phenomenalProj n (h12.trans h23) ρ
  | false, false, false, _, _, _ => rfl
  | false, false, true,  _, _, _ => rfl
  | false, true,  true,  _, _, _ => rfl
  | true,  true,  true,  _, _, _ => rfl
  | true,  true,  false, _, h23, _ => absurd h23 not_true_le_false
  | true,  false, _, h12, _, _ => absurd h12 not_true_le_false
  | false, true,  false, _, h23, _ => absurd h23 not_true_le_false

/-- Product of transformations on `Bool`.  The only `Disjoint` cases
    are `(false, false)`, `(false, true)`, and `(true, false)`. -/
def transProduct :
    ∀ {b₁ b₂ : Bool}, Disjoint b₁ b₂ → TransSpace n b₁ → TransSpace n b₂
      → TransSpace n (b₁ ⊔ b₂)
  | false, false, _, _, _ => PUnit.unit
  | false, true,  _, _, U => U
  | true,  false, _, U, _ => U
  | true,  true,  hd, _, _ => absurd hd not_disjoint_true_true

/-- Axiom 4.6.1 — no-signalling principle, trivially satisfied in
    the single-system universe (the only disjoint pairs involve
    `false`, on which the action is trivial). -/
lemma no_signalling_bool :
    ∀ {b₁ b₂ : Bool} (hd : Disjoint b₁ b₂)
      (U : TransSpace n b₁) (V : TransSpace n b₂)
      (ρ : PhenomenalSpace n (b₁ ⊔ b₂)),
      phenomenalProj n (le_sup_left : b₁ ≤ b₁ ⊔ b₂)
          ((phenomenalAction n (b₁ ⊔ b₂)).act (transProduct n hd U V) ρ)
        = (phenomenalAction n b₁).act U
            (phenomenalProj n (le_sup_left : b₁ ≤ b₁ ⊔ b₂) ρ)
  | false, false, _, _, _, _ => rfl
  | false, true,  _, _, _, _ => rfl
  | true,  false, _, _, _, _ => rfl
  | true,  true,  hd, _, _, _ => absurd hd not_disjoint_true_true

/-- Axiom 4.6.1' — right-side no-signalling, trivially satisfied. -/
lemma no_signalling_right_bool :
    ∀ {b₁ b₂ : Bool} (hd : Disjoint b₁ b₂)
      (U : TransSpace n b₁) (V : TransSpace n b₂)
      (ρ : PhenomenalSpace n (b₁ ⊔ b₂)),
      phenomenalProj n (le_sup_right : b₂ ≤ b₁ ⊔ b₂)
          ((phenomenalAction n (b₁ ⊔ b₂)).act (transProduct n hd U V) ρ)
        = (phenomenalAction n b₂).act V
            (phenomenalProj n (le_sup_right : b₂ ≤ b₁ ⊔ b₂) ρ)
  | false, false, _, _, _, _ => rfl
  | false, true,  _, _, _, _ => rfl
  | true,  false, _, _, _, _ => rfl
  | true,  true,  hd, _, _, _ => absurd hd not_disjoint_true_true

lemma transProduct_mul_bool :
    ∀ {b₁ b₂ : Bool} (hd : Disjoint b₁ b₂)
      (U₁ V₁ : TransSpace n b₁) (U₂ V₂ : TransSpace n b₂),
      transProduct n hd V₁ V₂ * transProduct n hd U₁ U₂
        = transProduct n hd (V₁ * U₁) (V₂ * U₂)
  | false, false, _, _, _, _, _ => rfl
  | false, true,  _, _, _, _, _ => rfl
  | true,  false, _, _, _, _, _ => rfl
  | true,  true,  hd, _, _, _, _ => absurd hd not_disjoint_true_true

lemma transProduct_one_bool :
    ∀ {b₁ b₂ : Bool} (hd : Disjoint b₁ b₂),
      transProduct n hd (1 : TransSpace n b₁) (1 : TransSpace n b₂)
        = (1 : TransSpace n (b₁ ⊔ b₂))
  | false, false, _ => rfl
  | false, true,  _ => rfl
  | true,  false, _ => rfl
  | true,  true,  hd => absurd hd not_disjoint_true_true

end UnitaryQuantum

/-- **Unitary quantum theory (single global system, dimension `n`)
    as a no-signalling theory.**

    See `UnitaryQuantum` namespace for the constituent data.  This
    is the **Tier 2 deliverable** of the file. -/
noncomputable def unitaryQuantumNoSignalling
    (n : ℕ) [NeZero n] : NoSignallingTheory where
  Sys := Bool
  latticeSys := inferInstance
  Phenomenal := UnitaryQuantum.PhenomenalSpace n
  phenomenal_nonempty := UnitaryQuantum.instPhenomNonempty n
  Trans := UnitaryQuantum.TransSpace n
  monoidTrans := UnitaryQuantum.instMonoidTrans n
  phenomenalAction := UnitaryQuantum.phenomenalAction n
  phenomenalProj := @UnitaryQuantum.phenomenalProj n
  phenomenalProj_surjective := fun {_ _} h =>
    UnitaryQuantum.phenomenalProj_surjective (n := n) h
  phenomenalProj_comp := @UnitaryQuantum.phenomenalProj_comp n
  transProduct := @UnitaryQuantum.transProduct n
  no_signalling := @UnitaryQuantum.no_signalling_bool n
  no_signalling_right := @UnitaryQuantum.no_signalling_right_bool n
  transProduct_mul := @UnitaryQuantum.transProduct_mul_bool n
  transProduct_one := @UnitaryQuantum.transProduct_one_bool n

/-! ## Scoping note: bipartite extension

The full bipartite slice would replace `Bool` with `Set (Fin 2)`
(a 4-element Boolean lattice: `∅`, `{0}`, `{1}`, `{0,1}`) and:

  * `Phenomenal {0,1} := ComplexDensityMatrix (n₀ * n₁)`
  * `Phenomenal {0  } := ComplexDensityMatrix n₀`
  * `Phenomenal {  1} := ComplexDensityMatrix n₁`
  * `Phenomenal ∅     := PUnit`

  * `phenomenalProj : {0} ≤ {0,1}` is `partialTrace_right` (from
    `UnifiedTheory.LayerB.PartialTrace`, after the `reindexFactor`
    bridge through `finProdFinEquiv : Fin n₀ × Fin n₁ ≃ Fin (n₀ * n₁)`).
  * `phenomenalProj : {1} ≤ {0,1}` is `partialTrace_left`.

  * `transProduct {0} {1}` is the Kronecker / tensor product of
    unitaries, which is itself unitary by
    `Matrix.kronecker_mem_unitary`.

The construction is direct but verbose due to the index reshape; it
is recorded here as scope, not formalised.  All required Lemmas
(`densityPartialTrace_right_isHermitian`,
`densityPartialTrace_right_trace`,
`densityPartialTrace_right_posSemidef`, and their left twins) are
already proven in `UnifiedTheory.LayerB.PartialTrace`. -/
example : True := trivial

end UnifiedTheory.LayerC.LocalRealisticAxioms
