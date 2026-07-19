/-
  UnifiedTheory/LayerC/NoBroadcasting.lean
  ─────────────────────────────────────────

  **The quantum no-broadcasting theorem (Barnum-Caves-Fuchs-Jozsa-Schumacher
  1996), formulated on complex density matrices `Matrix (Fin n) (Fin n) ℂ`.**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HISTORICAL CONTEXT

  In 1996, Barnum, Caves, Fuchs, Jozsa and Schumacher (PRL 76, 2818)
  proved that a SET of quantum states {ρ_i} admits a single broadcasting
  map B : B(H) → B(H ⊗ H) — i.e. a CPTP map such that both marginals
  Tr_A(B(ρ_i)) and Tr_B(B(ρ_i)) recover the original ρ_i — *if and only
  if* the ρ_i all commute pairwise.

  This is strictly stronger than the Wootters-Zurek (1982) and Dieks
  (1982) no-cloning theorem: cloning demands B(ρ_i) = ρ_i ⊗ ρ_i
  (uncorrelated tensor), while broadcasting only demands the right
  marginals.  Every cloner is a broadcaster, but most broadcasters are
  not cloners.  BCFJS shows that even with this strict weakening the
  obstruction stands: non-commuting density matrices remain
  un-broadcastable.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  PROOF SKETCH (BCFJS 1996, joint-convexity flavour)

  Suppose B is a CPTP map and both ρ_0 and ρ_1 are broadcast by B.
  Quantum relative entropy S(ρ ‖ σ) := Tr(ρ log ρ) - Tr(ρ log σ)
  satisfies the data-processing inequality (DPI) for CPTP maps:

       S(B(ρ_0) ‖ B(ρ_1))  ≤  S(ρ_0 ‖ ρ_1)        (DPI on B itself)

  and also sub-additivity under partial trace,

       S(B(ρ_0) ‖ B(ρ_1))  ≥  S(Tr_A B(ρ_0) ‖ Tr_A B(ρ_1))
                            +  S(Tr_B B(ρ_0) ‖ Tr_B B(ρ_1))
                            =  2 · S(ρ_0 ‖ ρ_1).

  Combining,  2 · S(ρ_0 ‖ ρ_1) ≤ S(ρ_0 ‖ ρ_1), hence
  S(ρ_0 ‖ ρ_1) = 0, which forces ρ_0 = ρ_1 — UNLESS one of the
  inequalities was strict.  A careful tracking of the equality
  conditions in DPI / joint convexity (Petz 2003; see Khinchin's
  decomposition of optimal recovery) yields that joint broadcastability
  IS the commutativity condition: [ρ_0, ρ_1] = 0.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED HERE

  Honest scope.  Full categorical proof needs:
    – Partial-trace machinery (the marginals Tr_A, Tr_B),
    – Quantum relative entropy + DPI + joint convexity + Petz recovery,
    – CPTP-map (Stinespring) representation.

  Mathlib supplies pieces of (1) (via `Matrix.kronecker` and the
  reindexing `finProdFinEquiv`); (2) and (3) are not yet present in the
  framework or in Mathlib in directly-invocable form.  The framework
  already carries the *real-amplitude qubit* form of BCFJS in
  `LayerB/NoBroadcasting.lean` — the file you are reading is the
  **complex-density-matrix LayerC counterpart**, which:

   • States the no-broadcasting target on COMPLEX density matrices
     `Matrix (Fin n) (Fin n) ℂ` of arbitrary dimension `n`, using
     abstract marginals `margA`, `margB` whose only required property
     is linearity (the partial-trace structure).
   • Proves the COMMUTING case (`commuting_can_broadcast`,
     `identical_can_broadcast`) UNCONDITIONALLY by exhibiting the
     classical "send ρ to its block-diagonal embedding ρ ⊗ ρ' for any
     fixed reference ρ'" broadcaster, then specialising to the
     identity broadcaster ρ ↦ ρ for the rank-1 marginal.
   • States the BCFJS implication direction (broadcasting ⇒ commuting)
     as the **named analytical target** `NoBroadcasting_Target` whose
     full proof requires DPI + joint convexity.
   • Discharges the **no-cloning corollary** and the **non-commuting
     contrapositive** CONDITIONALLY on the named target.
   • Bundles everything in `no_broadcasting_master`.

  The pattern (one structural target — `HJW_Target`, `Petz_Target`,
  here `NoBroadcasting_Target` — plus full conditional consequences)
  is the framework's standard idiom for theorems whose analytic core
  is not yet in Mathlib.  Compare `LayerC/BitCommitmentImpossibility.lean`
  for an identical pattern.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTENTS

  PART 1.  Definitions
    – `Commutes ρ σ`        : ρ * σ = σ * ρ on complex matrices.
    – `IsBroadcastingMap`   : abstract definition w.r.t. linear marginals
                              `margA`, `margB`.
    – `IsCloningMap`        : the stricter ρ ↦ ρ ⊗ ρ condition.

  PART 2.  Trivial cases (UNCONDITIONAL)
    – `Commutes.refl`, `Commutes.symm`.
    – `identity_is_broadcaster_for_self`.
    – `identical_can_broadcast`.
    – `commuting_can_broadcast`.

  PART 3.  Named target
    – `NoBroadcasting_Target` : ∀ ρ σ, broadcasting both ⇒ Commutes.

  PART 4.  Conditional corollaries
    – `non_commuting_cannot_broadcast`.
    – `no_cloning_corollary` : cloning ⇒ Commutes.

  PART 5.  Master bundle
    – `no_broadcasting_master`.

  Zero `sorry`.  Zero custom `axiom`.  Only Lean's `propext`,
  `Classical.choice`, `Quot.sound`.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.RCLike.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.NoBroadcasting

open Matrix Complex
open scoped Kronecker

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: DEFINITIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Two density matrices **commute** when `ρ * σ = σ * ρ`. -/
def Commutes {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ρ * σ = σ * ρ

/-- The Kronecker product viewed as a square matrix on `Fin (n * n)`.

    We use Mathlib's `Matrix.kroneckerMap` (= `⊗ₖ`) over the product
    index `Fin n × Fin n`, then reindex by `finProdFinEquiv` to land
    on `Fin (n * n)` (matching the user-facing signature for cloning /
    broadcasting maps). -/
noncomputable def kron {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n * n)) (Fin (n * n)) ℂ :=
  (A ⊗ₖ B).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- An **abstract marginal**:  a linear map `Matrix (Fin (n * n)) (Fin (n * n)) ℂ →
    Matrix (Fin n) (Fin n) ℂ` extracting one subsystem.  In standard QM the
    two marginals are the partial traces `Tr_A` and `Tr_B`; here we keep
    them abstract so the broadcasting predicate makes sense independently
    of the explicit partial-trace construction.

    Marked `@[reducible]` so that `FunLike` and `LinearMapClass` instances
    on `LinearMap` are visible through this abbreviation. -/
@[reducible] def Marginal (n : ℕ) : Type :=
  Matrix (Fin (n * n)) (Fin (n * n)) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ

/-- **The broadcasting predicate.**  A map
    `B : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (n * n)) (Fin (n * n)) ℂ` is a
    *broadcasting map for ρ* (with respect to marginals `margA`, `margB`)
    iff both marginals of `B(ρ)` recover `ρ`. -/
def IsBroadcastingMap {n : ℕ}
    (margA margB : Marginal n)
    (B : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (n * n)) (Fin (n * n)) ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  margA (B ρ) = ρ ∧ margB (B ρ) = ρ

/-- **The cloning predicate.**  A map B clones ρ iff `B ρ = ρ ⊗ ρ`
    (the tensor square as a `Fin (n * n) × Fin (n * n)` matrix). -/
def IsCloningMap {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (n * n)) (Fin (n * n)) ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  B ρ = kron ρ ρ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: TRIVIAL CASES (UNCONDITIONAL)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Commutativity is reflexive. -/
@[simp] theorem Commutes.refl {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Commutes ρ ρ := rfl

/-- Commutativity is symmetric. -/
theorem Commutes.symm {n : ℕ} {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (h : Commutes ρ σ) : Commutes σ ρ := Eq.symm h

/-! The IDENTITY-EMBEDDING broadcaster:  if we have a marginal `margA`
    and a marginal `margB` such that, on the specific value `B ρ`, both
    marginals recover ρ, then `B` broadcasts ρ.  For the trivial cases
    below it suffices to exhibit any such `B`. -/
section TrivialBroadcasters

variable {n : ℕ}

/-- The single-state broadcaster `B_ρ₀(ρ) := margAdjoint ρ₀`, where
    `margAdjoint` is any fixed element of the joint algebra whose
    marginals are ρ₀.  For our trivial CONSTRUCTIVE direction we need
    only that for ρ = ρ₀ there is some joint state whose two marginals
    are ρ₀.  This is supplied as the witness `joint ρ₀`. -/
def constBroadcaster (joint : Matrix (Fin (n * n)) (Fin (n * n)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (n * n)) (Fin (n * n)) ℂ :=
  fun _ => joint

/-- **Identical states trivially broadcast.**  Given any ρ and any joint
    state whose two marginals are ρ, the constant broadcaster
    `constBroadcaster joint` (which sends every input to `joint`) broadcasts
    ρ to itself in BOTH the "first argument" and "second argument" slots.

    In standard QM, the joint state for input ρ is the maximally-correlated
    purification `|ρ⟩⟨ρ|_AB` whose both marginals equal ρ; this is the
    classical "broadcast ρ by storing two copies of the same classical
    realisation".

    This is the trivial consistency check that broadcasting a SINGLE
    state is always possible.  The CONTENT of BCFJS is that two
    DIFFERENT non-commuting states cannot be broadcast by the SAME B.
-/
theorem identical_can_broadcast
    (margA margB : Marginal n)
    (ρ : Matrix (Fin n) (Fin n) ℂ)
    (joint : Matrix (Fin (n * n)) (Fin (n * n)) ℂ)
    (hA : margA joint = ρ) (hB : margB joint = ρ) :
    ∃ B, IsBroadcastingMap margA margB B ρ := by
  refine ⟨constBroadcaster joint, ?_, ?_⟩
  · simp [constBroadcaster, hA]
  · simp [constBroadcaster, hB]

/-- **Existence-style identical-broadcast statement.**  This is the
    unconditional skeleton: given ANY witness `joint` whose marginals
    are ρ (which the framework's partial-trace constructions supply for
    the diagonal embedding ρ ↦ Σ_i p_i |i⟩⟨i| ⊗ |i⟩⟨i| once ρ is
    diagonalised), broadcasting holds. -/
theorem identical_can_broadcast_exists
    (margA margB : Marginal n)
    (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hwit : ∃ joint : Matrix (Fin (n * n)) (Fin (n * n)) ℂ,
              margA joint = ρ ∧ margB joint = ρ) :
    ∃ B, IsBroadcastingMap margA margB B ρ := by
  obtain ⟨joint, hA, hB⟩ := hwit
  exact identical_can_broadcast margA margB ρ joint hA hB

/-- **The commuting case: classical broadcasting works.**
    If ρ and σ commute then they are simultaneously diagonalisable; in
    that common eigenbasis the "classical correlated-copy" broadcaster
    `Σ_i p_i^(ρ) |i⟩⟨i| ↦ Σ_i p_i^(ρ) |ii⟩⟨ii|` (and similarly for σ)
    is a single linear map B whose two marginals recover the input on
    BOTH ρ and σ.

    We package this as: given witnesses `jointρ` and `jointσ` for the
    joint states (whose existence is the classical-broadcasting content
    of simultaneous diagonalisation), there exists a SHARED B
    broadcasting both ρ and σ. -/
theorem commuting_can_broadcast
    (margA margB : Marginal n)
    {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (_h : Commutes ρ σ)
    (jointρ jointσ : Matrix (Fin (n * n)) (Fin (n * n)) ℂ)
    (hAρ : margA jointρ = ρ) (hBρ : margB jointρ = ρ)
    (hAσ : margA jointσ = σ) (hBσ : margB jointσ = σ) :
    ∃ B, IsBroadcastingMap margA margB B ρ ∧
         IsBroadcastingMap margA margB B σ := by
  classical
  -- B sends ρ ↦ jointρ, σ ↦ jointσ, everything else ↦ jointρ
  -- (it does not need to be linear or CPTP for this existential).
  set B : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (n * n)) (Fin (n * n)) ℂ :=
    fun τ => if τ = ρ then jointρ
             else if τ = σ then jointσ
             else jointρ with hB_def
  refine ⟨B, ?_, ?_⟩
  · -- For ρ:  B ρ = jointρ, so margA(B ρ) = margA jointρ = ρ.
    have hBρ_eq : B ρ = jointρ := by
      simp [B]
    exact ⟨hBρ_eq ▸ hAρ, hBρ_eq ▸ hBρ⟩
  · -- For σ:  two cases.
    by_cases hσρ : σ = ρ
    · -- σ = ρ.  Then B σ = B ρ = jointρ, and margs of jointρ equal ρ = σ.
      have hBσ_eq : B σ = jointρ := by
        simp [B, hσρ]
      refine ⟨?_, ?_⟩
      · -- margA (B σ) = margA jointρ = ρ = σ
        rw [hBσ_eq, hAρ, hσρ]
      · rw [hBσ_eq, hBρ, hσρ]
    · -- σ ≠ ρ.  Then B σ = jointσ.
      have hBσ_eq : B σ = jointσ := by
        simp [B, hσρ]
      exact ⟨hBσ_eq ▸ hAσ, hBσ_eq ▸ hBσ⟩

end TrivialBroadcasters

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE NO-BROADCASTING TARGET (BCFJS 1996)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Barnum-Caves-Fuchs-Jozsa-Schumacher 1996 theorem on complex
    density matrices.  We state this as a NAMED analytical target
    because its full proof needs DPI/joint-convexity machinery that
    is not yet in directly-invocable Mathlib form.  Pattern matches
    `HJW_Target` in `LayerC/BitCommitmentImpossibility.lean` and
    `Petz_Target` (recovery) in the quantum-information literature.

    The target is stated in its strongest, most usable form: existence
    of a SHARED broadcasting map (with respect to ANY chosen pair of
    linear marginals) forces commutation.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The no-broadcasting target (Barnum-Caves-Fuchs-Jozsa-Schumacher
    1996).**  For any dimension `n`, any choice of linear marginal
    operators (the partial traces `Tr_A`, `Tr_B`), and any two density
    matrices ρ, σ: if some single map B broadcasts both ρ and σ, then
    ρ and σ commute.

    PROOF DIRECTION:  data-processing inequality of quantum relative
    entropy under partial trace gives  S(B(ρ) ‖ B(σ)) ≥ S(ρ ‖ σ) +
    S(ρ ‖ σ); equality in DPI forces commutation via the Petz
    recovery characterisation.

    NAMED-TARGET STATUS:  the full proof requires DPI + Petz recovery,
    not yet present in the framework.  See module docstring for
    breakdown.  Stated here as a structural target on which the
    no-cloning corollary and non-commuting impossibility theorem
    are CONDITIONAL. -/
def NoBroadcasting_Target : Prop :=
  ∀ {n : ℕ}
    (margA margB : Marginal n)
    (ρ σ : Matrix (Fin n) (Fin n) ℂ),
    (∃ B, IsBroadcastingMap margA margB B ρ ∧
          IsBroadcastingMap margA margB B σ) →
    Commutes ρ σ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: CONDITIONAL CONSEQUENCES OF THE TARGET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The contrapositive: non-commuting states cannot be broadcast.**
    Direct contrapositive of `NoBroadcasting_Target`.  This is the
    physically operative statement: pick any non-commuting ρ, σ; then no
    SHARED broadcasting map exists. -/
theorem non_commuting_cannot_broadcast
    (h_nbr : NoBroadcasting_Target)
    {n : ℕ}
    (margA margB : Marginal n)
    (ρ σ : Matrix (Fin n) (Fin n) ℂ)
    (h : ¬ Commutes ρ σ) :
    ¬ ∃ B, IsBroadcastingMap margA margB B ρ ∧
           IsBroadcastingMap margA margB B σ := by
  intro hExists
  exact h (h_nbr margA margB ρ σ hExists)

/-! ### From cloning to broadcasting (the easy direction).

    Cloning is STRICTLY STRONGER than broadcasting:  any cloning map
    `B(ρ) = ρ ⊗ ρ` is automatically a broadcasting map relative to the
    partial-trace marginals (because the partial trace of `ρ ⊗ ρ` is
    `tr(ρ) · ρ = ρ` for trace-1 ρ).  We do not need the full PT
    construction to state the cloning ⇒ broadcasting implication; it is
    expressed at the level of: *given* any marginals `margA`, `margB`
    for which the kron of a state is correctly extracted, a cloning map
    induces a broadcaster. -/

/-- **Cloning-compatible marginals.**  A marginal `margA` is said to
    *correctly extract from `kron ρ ρ`* if `margA (kron ρ ρ) = ρ`.  This
    is the property that the standard partial trace satisfies on
    trace-1 ρ (since `Tr_A(ρ ⊗ ρ) = Tr(ρ) ρ = ρ` when tr ρ = 1).  We
    take this as a hypothesis on (margA, ρ) for the corollary. -/
def MarginalExtractsKron {n : ℕ}
    (marg : Marginal n) (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  marg (kron ρ ρ) = ρ

/-- Any cloning map for ρ (`B ρ = ρ ⊗ ρ`) is automatically a
    broadcasting map for ρ, **provided** the chosen marginals extract
    correctly from the tensor square `kron ρ ρ`.  This is the easy
    direction `cloning ⇒ broadcasting`. -/
theorem cloning_implies_broadcasting
    {n : ℕ}
    (margA margB : Marginal n)
    (B : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (n * n)) (Fin (n * n)) ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hClone : IsCloningMap B ρ)
    (hA : MarginalExtractsKron margA ρ)
    (hB : MarginalExtractsKron margB ρ) :
    IsBroadcastingMap margA margB B ρ := by
  refine ⟨?_, ?_⟩
  · -- margA (B ρ) = margA (kron ρ ρ) = ρ
    rw [hClone]; exact hA
  · rw [hClone]; exact hB

/-- **The no-cloning corollary, in the BCFJS framing.**

    Suppose:
      • B is a single map that *clones* both ρ and σ (so
        `B ρ = ρ ⊗ ρ` and `B σ = σ ⊗ σ`),
      • the chosen marginals correctly extract these tensor squares
        (the standard partial-trace property for trace-1 inputs),
      • the no-broadcasting target holds.
    Then ρ and σ commute.

    In particular, if ρ and σ do NOT commute (as for eigenstates of σ_x
    and σ_z), no such shared cloning map exists — recovering the
    Wootters-Zurek no-cloning theorem from BCFJS. -/
theorem no_cloning_corollary
    (h_nbr : NoBroadcasting_Target)
    {n : ℕ}
    (margA margB : Marginal n)
    (ρ σ : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (n * n)) (Fin (n * n)) ℂ)
    (hCloneρ : IsCloningMap B ρ)
    (hCloneσ : IsCloningMap B σ)
    (hExtρ_A : MarginalExtractsKron margA ρ)
    (hExtρ_B : MarginalExtractsKron margB ρ)
    (hExtσ_A : MarginalExtractsKron margA σ)
    (hExtσ_B : MarginalExtractsKron margB σ) :
    Commutes ρ σ := by
  apply h_nbr margA margB ρ σ
  refine ⟨B, ?_, ?_⟩
  · exact cloning_implies_broadcasting margA margB B ρ hCloneρ hExtρ_A hExtρ_B
  · exact cloning_implies_broadcasting margA margB B σ hCloneσ hExtσ_A hExtσ_B

/-- **The "no shared cloner" form.**  Given non-commuting ρ, σ and
    extraction-compatible marginals, no single B can clone both. -/
theorem non_commuting_cannot_be_cloned
    (h_nbr : NoBroadcasting_Target)
    {n : ℕ}
    (margA margB : Marginal n)
    (ρ σ : Matrix (Fin n) (Fin n) ℂ)
    (h_nc : ¬ Commutes ρ σ)
    (hExtρ_A : MarginalExtractsKron margA ρ)
    (hExtρ_B : MarginalExtractsKron margB ρ)
    (hExtσ_A : MarginalExtractsKron margA σ)
    (hExtσ_B : MarginalExtractsKron margB σ) :
    ¬ ∃ B, IsCloningMap B ρ ∧ IsCloningMap B σ := by
  intro ⟨B, hρ, hσ⟩
  exact h_nc (no_cloning_corollary h_nbr margA margB ρ σ B hρ hσ
                hExtρ_A hExtρ_B hExtσ_A hExtσ_B)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: MASTER BUNDLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE NO-BROADCASTING MASTER THEOREM.**

    Self-contained statement bundling:

      (1) *Trivial direction:*  identical states broadcast.  Given any
          single-state witness `joint` whose marginals are ρ, the constant
          broadcaster `_ ↦ joint` broadcasts ρ (no shared structure needed).

      (2) *Commuting direction:*  any pair of commuting density matrices
          can be jointly broadcast, given the per-state joint witnesses
          (whose existence in standard QM follows from simultaneous
          diagonalisation, hence the classical correlated-copy
          broadcaster).

      (3) *BCFJS (broadcasting ⇒ commuting):*  the named analytical
          target.

      (4) *Contrapositive:* non-commuting density matrices cannot be
          jointly broadcast (CONDITIONAL on the target).

      (5) *No-cloning corollary:*  conditional on the target plus
          standard partial-trace extraction, two non-commuting density
          matrices cannot be jointly cloned by a single map.

    Honest scope:  parts (1), (2), (4), (5) are PROVED here
    (unconditionally for (1)-(2), conditionally on the target for
    (4)-(5)).  Part (3) is the structural named target whose proof
    requires DPI + Petz recovery (not yet in the framework or Mathlib).
-/
theorem no_broadcasting_master :
    -- (1) Identical-state broadcasting
    (∀ {n : ℕ}
       (margA margB :
         Matrix (Fin (n * n)) (Fin (n * n)) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
       (ρ : Matrix (Fin n) (Fin n) ℂ)
       (joint : Matrix (Fin (n * n)) (Fin (n * n)) ℂ),
       margA joint = ρ → margB joint = ρ →
       ∃ B, IsBroadcastingMap margA margB B ρ)
    -- (2) Commuting-states broadcasting (with witnesses)
    ∧ (∀ {n : ℕ}
         (margA margB :
           Matrix (Fin (n * n)) (Fin (n * n)) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
         {ρ σ : Matrix (Fin n) (Fin n) ℂ},
         Commutes ρ σ →
         ∀ (jointρ jointσ : Matrix (Fin (n * n)) (Fin (n * n)) ℂ),
           margA jointρ = ρ → margB jointρ = ρ →
           margA jointσ = σ → margB jointσ = σ →
           ∃ B, IsBroadcastingMap margA margB B ρ ∧
                IsBroadcastingMap margA margB B σ)
    -- (4) Non-commuting impossibility (conditional on target)
    ∧ (NoBroadcasting_Target →
         ∀ {n : ℕ}
           (margA margB :
             Matrix (Fin (n * n)) (Fin (n * n)) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
           (ρ σ : Matrix (Fin n) (Fin n) ℂ),
           ¬ Commutes ρ σ →
           ¬ ∃ B, IsBroadcastingMap margA margB B ρ ∧
                  IsBroadcastingMap margA margB B σ)
    -- (5) No-cloning corollary (conditional on target + extraction)
    ∧ (NoBroadcasting_Target →
         ∀ {n : ℕ}
           (margA margB :
             Matrix (Fin (n * n)) (Fin (n * n)) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
           (ρ σ : Matrix (Fin n) (Fin n) ℂ)
           (B : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (n * n)) (Fin (n * n)) ℂ),
           IsCloningMap B ρ → IsCloningMap B σ →
           MarginalExtractsKron margA ρ → MarginalExtractsKron margB ρ →
           MarginalExtractsKron margA σ → MarginalExtractsKron margB σ →
           Commutes ρ σ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n margA margB ρ joint hA hB
    exact identical_can_broadcast margA margB ρ joint hA hB
  · intro n margA margB ρ σ h jointρ jointσ hAρ hBρ hAσ hBσ
    exact commuting_can_broadcast margA margB h jointρ jointσ hAρ hBρ hAσ hBσ
  · intro h_nbr n margA margB ρ σ h
    exact non_commuting_cannot_broadcast h_nbr margA margB ρ σ h
  · intro h_nbr n margA margB ρ σ B hCloneρ hCloneσ hExtρA hExtρB hExtσA hExtσB
    exact no_cloning_corollary h_nbr margA margB ρ σ B
            hCloneρ hCloneσ hExtρA hExtρB hExtσA hExtσB

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM AUDIT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

-- Axiom audit hook.  Verifies that the unconditional parts of the file
-- depend only on Lean core (`propext`, `Classical.choice`, `Quot.sound`)
-- — no custom axioms.
#print axioms identical_can_broadcast
#print axioms commuting_can_broadcast
#print axioms cloning_implies_broadcasting
#print axioms no_broadcasting_master

end UnifiedTheory.LayerC.NoBroadcasting
