/-
  LayerB/NaimarkDilation.lean
  ────────────────────────────

  **Naimark's dilation theorem** — every POVM extends to a projective
  measurement via an isometric embedding into a larger Hilbert space.

  This file closes the structural gap in `HolevoBoundQuantum.lean`,
  where the `QuantumMeasurement` type carries only an input/output map
  with no operator-level realisation.  Naimark says: every POVM
  `{E_α}_{α ∈ A}` on `ℂ^n` is the pull-back of a projective
  measurement (PVM) `{P_α}` on `ℂ^n ⊗ ℂ^A` along an isometry
  `V : ℂ^n → ℂ^n ⊗ ℂ^A`:

    ∀ ρ.  Tr(ρ · E_α)  =  Tr( (V ρ V†) · P_α ).

  Built on top of:
    • `KrausRepresentation` (LayerB/KrausRepresentation.lean) — the
      sum-to-identity completeness condition `Σ K_α† K_α = I`.
    • `krausToStinespring` (LayerB/StinespringDilation.lean) — the
      isometry `V_{(i,α), j} := (K_α)_{i,j}`.
    • `partialTrace_right_krausToStinespring` — the channel-recovery
      identity (used here only indirectly, as a sanity check).

  ──────────────────────────────────────────────────────────────────
  SCOPING (honest):

  The full Naimark construction `POVM → PVM` requires an operator
  square root `K_α := √E_α` so that `E_α = K_α† K_α` (since √E_α is
  Hermitian, `K_α† K_α = √E_α · √E_α = E_α`).  Mathlib v4.28 does
  NOT provide `Matrix.PosSemidef.sqrt` as a packaged operator.  The
  spectral-functional-calculus stack in this project (LayerB/
  SpectralFunctionalCalculus.lean) provides `cfc` for matrices, but
  bridging cfc-of-x↦√x with the "K† K = E" identity is itself a
  substantial verification project.

  Following the project's standard pattern (Margolus–Levitin), we
  package the "POVM → Kraus family" step as a hypothesis and prove
  the *structural* Naimark theorem unconditionally for Kraus-derived
  POVMs.  The headline theorem
    `kraus_gives_naimark_born_rule`
  closes with NO `sorry` and NO custom axiom.

  We also expose a stronger conditional form
    `POVM.naimark_dilation_exists`
  which says: every POVM admitting a "Kraus square root" extends to
  a PVM on the dilation space.  The hypothesis is a clean trade
  off — the Kraus family is what one would actually compute in any
  concrete instance, and existence of the operator square root for
  PSD matrices is a classical fact (just not yet in our Lean stack).

  ──────────────────────────────────────────────────────────────────
  WHAT IS DEFINED / PROVEN (no sorry, no custom axiom):

    1. `POVM n k` : structure (PSD operators summing to identity).
    2. `POVM.bornProb` : the Born-rule probability `Re Tr(ρ · E_α)`.
    3. `PVM N k` : structure (Hermitian projectors summing to
       identity, with `P² = P`).
    4. `PVM.bornProb` : the Born-rule probability for a PVM.
    5. `KrausRepresentation.toPOVM` : the POVM `E_α := K_α† K_α`
       derived from any Kraus family.
    6. `KrausRepresentation.naimarkPVM` : the PVM
       `P_α := I_n ⊗ |α⟩⟨α|` on `Fin n × Fin k`.
    7. `naimarkPVM_isProj`, `naimarkPVM_isHerm`,
       `naimarkPVM_complete` — the PVM axioms verified.
    8. `kraus_naimark_born_rule` : **Born-rule preservation** —
       `Tr(ρ · K_α† K_α) = Tr( (V ρ V†) · P_α )` as complex traces,
       and the `.re` form gives the probability identity.
    9. `kraus_gives_naimark` : the existence statement packaged for
       reuse downstream.
   10. `POVM.naimark_dilation_exists` : the same statement for any
       POVM that has a Kraus square root.

  All proofs use `Matrix (Fin n × Fin k) ...` rather than reindexing
  through `Fin (n*k)` for cleaner book-keeping.  A reindex layer to
  `Fin (n*k)` is provided as a thin wrapper at the bottom.
-/

import UnifiedTheory.LayerB.KrausRepresentation
import UnifiedTheory.LayerB.StinespringDilation
import UnifiedTheory.LayerB.RobertsonSchrodinger

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.NaimarkDilation

open Matrix Complex
open scoped BigOperators ComplexOrder
open UnifiedTheory.LayerB.Kraus
open UnifiedTheory.LayerB.StinespringDilation
open UnifiedTheory.LayerB.RobertsonSchrodinger

/-! ## 1. POVM and PVM structures -/

/-- A **POVM** (Positive Operator-Valued Measure) with `k` outcomes on
    an `n`-dimensional complex Hilbert space.  A finite indexed family
    `E_α : Matrix (Fin n) (Fin n) ℂ` of positive semidefinite operators
    that sum to the identity.

    Born rule (axiomatic input from QM): the probability of outcome `α`
    on the state `ρ` is `Tr(ρ · E_α)`.  See `POVM.bornProb`. -/
structure POVM (n k : ℕ) where
  /-- The `k` POVM effect operators. -/
  E : Fin k → Matrix (Fin n) (Fin n) ℂ
  /-- Each effect is positive semidefinite (Hermitian + PSD). -/
  isPSD : ∀ α, (E α).PosSemidef
  /-- Completeness: `∑ α, E α = 1`. -/
  complete : (∑ α, E α) = (1 : Matrix (Fin n) (Fin n) ℂ)

namespace POVM

variable {n k : ℕ}

/-- Each POVM effect is Hermitian (derived from PSD). -/
theorem isHerm (P : POVM n k) (α : Fin k) : (P.E α).IsHermitian :=
  (P.isPSD α).isHermitian

/-- The **Born-rule probability** of outcome `α` on a complex density
    matrix `ρ`.  Defined as `Re(Tr(ρ.M · E_α))`. -/
noncomputable def bornProb (P : POVM n k) (ρ : ComplexDensityMatrix n)
    (α : Fin k) : ℝ :=
  (Matrix.trace (ρ.M * P.E α)).re

end POVM

/-- A **PVM** (Projection-Valued Measure) with `k` outcomes on an
    `N`-dimensional complex Hilbert space.  Each `P_α` is a Hermitian
    projector and the projectors sum to the identity.  Equivalently:
    a set of mutually orthogonal projectors whose ranges decompose
    the Hilbert space.

    Mutual orthogonality `P_α · P_β = 0` for `α ≠ β` follows from
    the sum-to-identity + self-projector axioms (a standard exercise),
    but we leave that as a derived theorem to keep the structure
    minimal. -/
structure PVM (N k : ℕ) where
  /-- The `k` projector operators. -/
  P : Fin k → Matrix (Fin N) (Fin N) ℂ
  /-- Each `P α` is Hermitian. -/
  isHerm : ∀ α, (P α).IsHermitian
  /-- Each `P α` is idempotent: `P α * P α = P α`. -/
  isProj : ∀ α, P α * P α = P α
  /-- Completeness: `∑ α, P α = 1`. -/
  complete : (∑ α, P α) = (1 : Matrix (Fin N) (Fin N) ℂ)

namespace PVM

variable {N k : ℕ}

/-- The **Born-rule probability** of outcome `α` on a complex density
    matrix `ρ` on the (possibly enlarged) `N`-dimensional space. -/
noncomputable def bornProb (Q : PVM N k) (ρ : ComplexDensityMatrix N)
    (α : Fin k) : ℝ :=
  (Matrix.trace (ρ.M * Q.P α)).re

end PVM

/-! ## 2. POVM from a Kraus family

The completeness condition `Σ_α K_α† · K_α = I` is exactly the
condition that the operators `E_α := K_α† · K_α` form a POVM.  Each
`K_α† K_α` is PSD (`posSemidef_conjTranspose_mul_self`), the sum is
`I` by hypothesis. -/

/-- The POVM `E_α := K_α† · K_α` derived from a Kraus family on a
    square system (`m = n`).  We restrict to `m = n` because POVMs
    live on a fixed Hilbert space, while the structure
    `KrausRepresentation m n k` is allowed to be rectangular. -/
noncomputable def krausToPOVM {n k : ℕ}
    (K : UnifiedTheory.LayerB.Kraus.KrausRepresentation n n k) : POVM n k where
  E α := (K.K α).conjTranspose * K.K α
  isPSD := fun _ => Matrix.posSemidef_conjTranspose_mul_self _
  complete := K.complete

@[simp]
theorem krausToPOVM_E {n k : ℕ}
    (K : UnifiedTheory.LayerB.Kraus.KrausRepresentation n n k) (α : Fin k) :
    (krausToPOVM K).E α = (K.K α).conjTranspose * K.K α := rfl

/-! ## 3. The Naimark PVM on the dilation space

For a Kraus family `K : Fin k → Matrix (Fin n) (Fin n) ℂ`, the
Naimark dilation lives on the index type `Fin n × Fin k`.  The
projectors are `P_α := I_n ⊗ |α⟩⟨α|`, with matrix entries

    (P_α)_{(i, a), (i', a')}  =  δ_{i, i'} · δ_{a, α} · δ_{a', α}.

We define these directly as functions `Fin n × Fin k → Fin n × Fin k → ℂ`. -/

section NaimarkPVM

variable {n k : ℕ}

/-- The α-th **Naimark projector** on the dilation space `Fin n × Fin k`.

    `(naimarkProj α)_{(i, a), (i', a')} = 1` iff `i = i'`, `a = α`,
    and `a' = α`; else `0`. -/
noncomputable def naimarkProj (α : Fin k) :
    Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ :=
  fun p p' => if p.1 = p'.1 ∧ p.2 = α ∧ p'.2 = α then 1 else 0

/-- Entries of `naimarkProj α`. -/
@[simp]
lemma naimarkProj_apply (α : Fin k) (i i' : Fin n) (a a' : Fin k) :
    (naimarkProj (n := n) α) (i, a) (i', a')
      = if i = i' ∧ a = α ∧ a' = α then 1 else 0 := rfl

/-- The Naimark projector is Hermitian. -/
theorem naimarkProj_isHerm (α : Fin k) :
    (naimarkProj (n := n) α).IsHermitian := by
  ext p p'
  change star ((naimarkProj α) p' p) = (naimarkProj α) p p'
  obtain ⟨i, a⟩ := p
  obtain ⟨i', a'⟩ := p'
  rw [naimarkProj_apply, naimarkProj_apply]
  -- LHS: star (if i' = i ∧ a' = α ∧ a = α then 1 else 0)
  -- RHS: if i = i' ∧ a = α ∧ a' = α then 1 else 0
  -- The two conditions are equivalent up to symmetry of equality and commutativity of ∧.
  by_cases hcondR : i = i' ∧ a = α ∧ a' = α
  · obtain ⟨hii, haα, ha'α⟩ := hcondR
    have hcondL : i' = i ∧ a' = α ∧ a = α := ⟨hii.symm, ha'α, haα⟩
    rw [if_pos hcondL, if_pos ⟨hii, haα, ha'α⟩]
    simp
  · have hcondL : ¬ (i' = i ∧ a' = α ∧ a = α) := by
      intro ⟨hii, ha'α, haα⟩
      exact hcondR ⟨hii.symm, haα, ha'α⟩
    rw [if_neg hcondL, if_neg hcondR]
    simp

/-- The Naimark projector is idempotent: `P_α · P_α = P_α`. -/
theorem naimarkProj_isProj (α : Fin k) :
    (naimarkProj (n := n) α) * (naimarkProj α) = (naimarkProj α) := by
  ext p p'
  obtain ⟨i, a⟩ := p
  obtain ⟨i', a'⟩ := p'
  rw [Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  -- Inner sum: ∑_{j} ∑_{b} (P α) (i, a) (j, b) * (P α) (j, b) (i', a')
  -- = ∑_{j} ∑_{b} (if i=j ∧ a=α ∧ b=α then 1 else 0)
  --             * (if j=i' ∧ b=α ∧ a'=α then 1 else 0)
  -- The product is nonzero (= 1) iff: i=j ∧ a=α ∧ b=α ∧ j=i' ∧ b=α ∧ a'=α
  -- iff: a=α ∧ a'=α ∧ i=i' ∧ j=i ∧ b=α.
  have h_each : ∀ j b,
      ((naimarkProj (n := n) α) (i, a) (j, b))
        * ((naimarkProj α) (j, b) (i', a'))
        = if i = j ∧ a = α ∧ b = α ∧ j = i' ∧ a' = α then (1 : ℂ) else 0 := by
    intro j b
    rw [naimarkProj_apply, naimarkProj_apply]
    by_cases h1 : i = j ∧ a = α ∧ b = α
    · by_cases h2 : j = i' ∧ b = α ∧ a' = α
      · rw [if_pos h1, if_pos h2, mul_one]
        rw [if_pos ⟨h1.1, h1.2.1, h1.2.2, h2.1, h2.2.2⟩]
      · rw [if_pos h1, if_neg h2, mul_zero]
        symm
        apply if_neg
        intro hcomb
        exact h2 ⟨hcomb.2.2.2.1, hcomb.2.2.1, hcomb.2.2.2.2⟩
    · rw [if_neg h1, zero_mul]
      symm
      apply if_neg
      intro hcomb
      exact h1 ⟨hcomb.1, hcomb.2.1, hcomb.2.2.1⟩
  simp_rw [h_each]
  -- Inner sum over b: only b = α can fire (when other conditions are met).
  have h_b_sum : ∀ j,
      (∑ b, if i = j ∧ a = α ∧ b = α ∧ j = i' ∧ a' = α then (1 : ℂ) else 0)
        = if i = j ∧ a = α ∧ j = i' ∧ a' = α then 1 else 0 := by
    intro j
    by_cases hother : i = j ∧ a = α ∧ j = i' ∧ a' = α
    · rw [Finset.sum_eq_single α]
      · rw [if_pos ⟨hother.1, hother.2.1, rfl, hother.2.2.1, hother.2.2.2⟩]
        rw [if_pos hother]
      · intro b _ hb
        apply if_neg
        intro hcomb
        exact hb hcomb.2.2.1
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hother]
      apply Finset.sum_eq_zero
      intro b _
      apply if_neg
      intro hcomb
      exact hother ⟨hcomb.1, hcomb.2.1, hcomb.2.2.2.1, hcomb.2.2.2.2⟩
  simp_rw [h_b_sum]
  -- Outer sum over j: only j = i can fire (need i = j); but also j = i' to land on RHS i = i'.
  rw [naimarkProj_apply]
  by_cases hRHS : i = i' ∧ a = α ∧ a' = α
  · rw [if_pos hRHS]
    rw [Finset.sum_eq_single i]
    · rw [if_pos ⟨rfl, hRHS.2.1, hRHS.1, hRHS.2.2⟩]
    · intro j _ hj
      apply if_neg
      intro hcomb
      exact hj hcomb.1.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hRHS]
    apply Finset.sum_eq_zero
    intro j _
    apply if_neg
    intro hcomb
    exact hRHS ⟨hcomb.1.trans hcomb.2.2.1, hcomb.2.1, hcomb.2.2.2⟩

/-- **Completeness of the Naimark PVM:** `Σ_α P_α = I` on `Fin n × Fin k`. -/
theorem naimarkProj_complete :
    (∑ α, (naimarkProj (n := n) (k := k) α))
      = (1 : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ) := by
  ext p p'
  obtain ⟨i, a⟩ := p
  obtain ⟨i', a'⟩ := p'
  rw [Finset.sum_apply]
  rw [Finset.sum_apply]
  simp only [naimarkProj_apply]
  -- ∑_{α} if i = i' ∧ a = α ∧ a' = α then 1 else 0
  -- = if i = i' ∧ a = a' then 1 else 0 (only α = a = a' contributes)
  by_cases hii' : i = i'
  · by_cases haa' : a = a'
    · -- Diagonal in both: pick α = a (= a')
      subst haa'
      rw [Finset.sum_eq_single a]
      · simp [hii']
        -- Goal: 1 = (1 : Matrix _ _ ℂ) (i, a) (i', a)
        subst hii'
        rw [Matrix.one_apply]
        simp
      · intro α _ hα
        simp [hα.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    · -- Off-diagonal in a, a': sum is 0
      have h_each : ∀ α ∈ (Finset.univ : Finset (Fin k)),
          (if i = i' ∧ a = α ∧ a' = α then (1 : ℂ) else 0) = 0 := by
        intro α _
        by_cases hcond : i = i' ∧ a = α ∧ a' = α
        · exact absurd (hcond.2.1.trans hcond.2.2.symm) haa'
        · simp [hcond]
      rw [Finset.sum_congr rfl h_each, Finset.sum_const_zero]
      -- RHS = 0 since (i, a) ≠ (i', a')
      have hne : ((i, a) : Fin n × Fin k) ≠ (i', a') := by
        intro heq
        exact haa' (Prod.mk.inj heq).2
      rw [Matrix.one_apply_ne hne]
  · -- Off-diagonal in i: sum is 0
    have h_each : ∀ α ∈ (Finset.univ : Finset (Fin k)),
        (if i = i' ∧ a = α ∧ a' = α then (1 : ℂ) else 0) = 0 := by
      intro α _
      by_cases hcond : i = i' ∧ a = α ∧ a' = α
      · exact absurd hcond.1 hii'
      · simp [hcond]
    rw [Finset.sum_congr rfl h_each, Finset.sum_const_zero]
    have hne : ((i, a) : Fin n × Fin k) ≠ (i', a') := by
      intro heq
      exact hii' (Prod.mk.inj heq).1
    rw [Matrix.one_apply_ne hne]

/-- The bundled **Naimark PVM** on the dilation space `Fin n × Fin k`. -/
noncomputable def naimarkPVM_prod (n k : ℕ) :
    { Q : Fin k → Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ //
        (∀ α, (Q α).IsHermitian)
      ∧ (∀ α, Q α * Q α = Q α)
      ∧ (∑ α, Q α) = (1 : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ) } :=
  ⟨fun α => naimarkProj α,
   fun α => naimarkProj_isHerm α,
   fun α => naimarkProj_isProj α,
   naimarkProj_complete⟩

end NaimarkPVM

/-! ## 4. The Born-rule identity (Stinespring–Naimark)

For a Kraus family `K : Fin k → Matrix (Fin n) (Fin n) ℂ` with
isometry `V := krausToStinespring K`, the conjugated state has
explicit entries

  (V ρ V†)_{(i,α),(i',α')} = (K_α · ρ · K_α'†)_{i, i'}

from `krausToStinespring_conj_apply`.  Multiplying by the Naimark
projector `P_β` (with support `(_, β), (_, β)`) and tracing gives

  Tr( (V ρ V†) · P_β )
    = ∑_{(i, a)} ((V ρ V†) · P_β)_{(i, a), (i, a)}
    = ∑_{i, a} ∑_{(i', a')} (V ρ V†)_{(i, a), (i', a')} · (P_β)_{(i', a'), (i, a)}.

The only nonzero contribution requires `a' = β` and `a = β` and
`i' = i`, leaving `∑_i (K_β · ρ · K_β†)_{i, i} = Tr(K_β · ρ · K_β†)
= Tr(K_β† · K_β · ρ) = Tr(ρ · E_β)`. -/

section BornRule

variable {n k : ℕ}

/-- **The Born-rule identity for the Kraus-Naimark dilation.**

    For any Kraus family `K_α` on `Fin n`, conjugating `ρ` by the
    Stinespring isometry `V` and measuring with the Naimark
    projector `P_β` recovers the POVM probability:

      `Tr( (V · ρ · V†) · P_β )  =  Tr( ρ · K_β† · K_β )`. -/
theorem kraus_naimark_trace_identity
    (K : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (β : Fin k) :
    Matrix.trace
        ((krausToStinespring K * ρ * (krausToStinespring K).conjTranspose
          : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)
         * (naimarkProj (n := n) β))
      = Matrix.trace (ρ * ((K β).conjTranspose * K β)) := by
  -- Step 1: identify the diagonal entries of (V ρ V†) * P_β.
  have h_diag : ∀ (p : Fin n × Fin k),
      ((krausToStinespring K * ρ * (krausToStinespring K).conjTranspose
            : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)
          * (naimarkProj (n := n) β)) p p
        = (if p.2 = β then (K β * ρ * (K β).conjTranspose) p.1 p.1 else 0) := by
    rintro ⟨i, a⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    -- Inner: ∑_{j, b} (V ρ V†)_{(i,a),(j,b)} * (P β)_{(j,b),(i,a)}.
    have h_per : ∀ j b,
        ((krausToStinespring K * ρ * (krausToStinespring K).conjTranspose
            : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)) (i, a) (j, b)
          * (naimarkProj (n := n) β) (j, b) (i, a)
          = (K a * ρ * (K b).conjTranspose) i j
              * (if j = i ∧ b = β ∧ a = β then (1 : ℂ) else 0) := by
      intro j b
      rw [krausToStinespring_conj_apply, naimarkProj_apply]
    simp_rw [h_per]
    by_cases ha : a = β
    · simp only [ha, and_true, if_true]
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single β]
        · simp
        · intro b _ hb
          have hneg : ¬ (i = i ∧ b = β) := fun h => hb h.2
          rw [if_neg hneg, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro j _ hj
        have h_zero : ∀ b ∈ (Finset.univ : Finset (Fin k)),
            (K β * ρ * (K b).conjTranspose) i j
              * (if j = i ∧ b = β then (1 : ℂ) else 0) = 0 := by
          intro b _
          have hneg : ¬ (j = i ∧ b = β) := fun h => hj h.1
          rw [if_neg hneg, mul_zero]
        rw [Finset.sum_congr rfl h_zero, Finset.sum_const_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · -- a ≠ β: every inner condition is False
      have h_zero : ∀ j b,
          (K a * ρ * (K b).conjTranspose) i j
            * (if j = i ∧ b = β ∧ a = β then (1 : ℂ) else 0) = 0 := by
        intro j b
        have hneg : ¬ (j = i ∧ b = β ∧ a = β) := by
          intro hcomb
          exact ha hcomb.2.2
        rw [if_neg hneg, mul_zero]
      simp_rw [h_zero, Finset.sum_const_zero]
      rw [if_neg ha]
  -- Step 2: expand the trace.
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  simp_rw [h_diag]
  rw [Fintype.sum_prod_type]
  have h_inner : ∀ i,
      (∑ a, if a = β then (K β * ρ * (K β).conjTranspose) i i else (0 : ℂ))
        = (K β * ρ * (K β).conjTranspose) i i := by
    intro i
    rw [Finset.sum_eq_single β]
    · simp
    · intro a _ ha; simp [ha]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [h_inner]
  -- LHS now: ∑ i, (K β * ρ * (K β)†) i i
  -- This equals Matrix.trace (K β * ρ * (K β)†).
  -- We then rewrite RHS via cyclicity.
  -- Goal becomes: ∑ i, (K β * ρ * (K β)†) i i = ∑ i, (ρ * ((K β)† * K β)) i i
  -- via Tr (K β ρ K β†) = Tr ((K β)† K β ρ) = Tr (ρ (K β)† K β).
  have h_cyc :
      (∑ i, (K β * ρ * (K β).conjTranspose) i i)
        = (∑ i, (ρ * ((K β).conjTranspose * K β)) i i) := by
    have step1 :
        (∑ i, (K β * ρ * (K β).conjTranspose) i i)
          = Matrix.trace (K β * ρ * (K β).conjTranspose) := by
      unfold Matrix.trace
      simp only [Matrix.diag_apply]
    have step2 :
        (∑ i, (ρ * ((K β).conjTranspose * K β)) i i)
          = Matrix.trace (ρ * ((K β).conjTranspose * K β)) := by
      unfold Matrix.trace
      simp only [Matrix.diag_apply]
    rw [step1, step2]
    -- Tr (K β * ρ * (K β)†) = Tr ((K β)† * K β * ρ) = Tr (ρ * ((K β)† * K β))
    calc Matrix.trace (K β * ρ * (K β).conjTranspose)
        = Matrix.trace ((K β * ρ) * (K β).conjTranspose) := by rfl
      _ = Matrix.trace ((K β).conjTranspose * (K β * ρ)) :=
          Matrix.trace_mul_comm (K β * ρ) (K β).conjTranspose
      _ = Matrix.trace ((K β).conjTranspose * K β * ρ) := by rw [← Matrix.mul_assoc]
      _ = Matrix.trace (ρ * ((K β).conjTranspose * K β)) :=
          Matrix.trace_mul_comm ((K β).conjTranspose * K β) ρ
  exact h_cyc

end BornRule

/-! ## 5. Naimark from Kraus: existence statement -/

/-- **Naimark's theorem (Kraus-derived form).**

    Every Kraus representation on a square system `Fin n → Fin n`
    gives rise to:
      • a POVM `E_α := K_α† K_α` (`(krausToPOVM K)`);
      • a PVM `P_α := I ⊗ |α⟩⟨α|` on the dilation space `Fin n × Fin k`
        (the bundled `naimarkPVM_prod`);
      • the Stinespring isometry `V := krausToStinespring K` from
        `Fin n` into `Fin n × Fin k`;

    such that the Born-rule probability of the POVM on any state `ρ`
    equals the Born-rule probability of the PVM on the conjugated
    state `V ρ V†`.  No `sorry`, no custom axiom. -/
theorem kraus_gives_naimark_born_rule
    {n k : ℕ} (K : KrausRepresentation n n k)
    (ρ : ComplexDensityMatrix n) (β : Fin k) :
    (Matrix.trace (ρ.M * (krausToPOVM K).E β)).re
      = (Matrix.trace
          ((krausToStinespring K.K * ρ.M * (krausToStinespring K.K).conjTranspose
            : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)
           * (naimarkProj (n := n) β))).re := by
  congr 1
  rw [kraus_naimark_trace_identity K.K ρ.M β]
  rw [krausToPOVM_E]

/-- **Born-rule identity packaged in POVM/PVM form.**

    On a Kraus-derived POVM `(krausToPOVM K)`, the Born-rule probability
    coincides with the trace of `(V ρ V†) · P_β`. -/
theorem kraus_naimark_bornProb_eq
    {n k : ℕ} (K : KrausRepresentation n n k)
    (ρ : ComplexDensityMatrix n) (β : Fin k) :
    (krausToPOVM K).bornProb ρ β
      = (Matrix.trace
          ((krausToStinespring K.K * ρ.M * (krausToStinespring K.K).conjTranspose
            : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)
           * (naimarkProj (n := n) β))).re := by
  unfold POVM.bornProb
  exact kraus_gives_naimark_born_rule K ρ β

/-- **Existence form (Kraus-derived).**

    For every Kraus representation `K : KrausRepresentation n n k`,
    there exists a Naimark dilation (isometry `V` + PVM data on
    `Fin n × Fin k`) reproducing the POVM `(krausToPOVM K)`'s Born-rule
    probabilities.  All components are explicit. -/
theorem kraus_gives_naimark
    {n k : ℕ} (K : KrausRepresentation n n k) :
    ∃ (V : Matrix (Fin n × Fin k) (Fin n) ℂ)
      (_ : IsIsometry V)
      (P : Fin k → Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)
      (_ : ∀ α, (P α).IsHermitian)
      (_ : ∀ α, P α * P α = P α)
      (_ : (∑ α, P α) = 1),
      ∀ (ρ : ComplexDensityMatrix n) (α : Fin k),
        (krausToPOVM K).bornProb ρ α
          = (Matrix.trace ((V * ρ.M * V.conjTranspose) * P α)).re := by
  refine ⟨krausToStinespring K.K, ?_, naimarkProj, naimarkProj_isHerm,
          naimarkProj_isProj, naimarkProj_complete, ?_⟩
  · exact krausToStinespring_isIsometry K.complete
  · intro ρ α
    exact kraus_naimark_bornProb_eq K ρ α

/-! ## 6. POVM-side existence: assumes a Kraus square root

We expose a clean conditional existence statement for arbitrary
POVMs: any POVM that admits a Kraus square root extends to a PVM
on the dilation space.  The hypothesis is exactly the missing piece
(`E_α = K_α† K_α`); when an in-stack `PosSemidef.sqrt` lemma lands,
this becomes unconditional. -/

namespace POVM

variable {n k : ℕ}

/-- **Naimark's theorem (conditional on Kraus square root).**

    If a POVM `P` admits a Kraus square root — a family `K_α` with
    `K_α† · K_α = P.E α` — then there exists a Naimark dilation:
    an isometry `V` and a PVM `{Q_α}` on `Fin n × Fin k` such that
    the Born-rule probabilities agree on every state `ρ`. -/
theorem naimark_dilation_exists (P : POVM n k)
    (K : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hSqrt : ∀ α, (K α).conjTranspose * K α = P.E α) :
    ∃ (V : Matrix (Fin n × Fin k) (Fin n) ℂ)
      (_ : IsIsometry V)
      (Q : Fin k → Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)
      (_ : ∀ α, (Q α).IsHermitian)
      (_ : ∀ α, Q α * Q α = Q α)
      (_ : (∑ α, Q α) = 1),
      ∀ (ρ : ComplexDensityMatrix n) (α : Fin k),
        P.bornProb ρ α
          = (Matrix.trace ((V * ρ.M * V.conjTranspose) * Q α)).re := by
  -- Build the Kraus representation from `K` using `hSqrt` + `P.complete`.
  have hCompleteK : (∑ α, (K α).conjTranspose * K α)
                     = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have : (∑ α, (K α).conjTranspose * K α) = (∑ α, P.E α) := by
      apply Finset.sum_congr rfl
      intro α _
      exact hSqrt α
    rw [this, P.complete]
  let Krep : KrausRepresentation n n k :=
    { K := K, complete := hCompleteK }
  -- The Kraus-derived POVM coincides with `P` on every effect.
  have hSameEffects : ∀ α, (krausToPOVM Krep).E α = P.E α := by
    intro α
    rw [krausToPOVM_E]
    exact hSqrt α
  -- Apply `kraus_gives_naimark` to `Krep`, then rewrite the bornProb.
  obtain ⟨V, hV, Q, hQH, hQP, hQC, hBR⟩ := kraus_gives_naimark Krep
  refine ⟨V, hV, Q, hQH, hQP, hQC, ?_⟩
  intro ρ α
  -- P.bornProb ρ α = (Tr(ρ.M * P.E α)).re = (Tr(ρ.M * (krausToPOVM Krep).E α)).re
  -- = (krausToPOVM Krep).bornProb ρ α = ...
  unfold POVM.bornProb
  rw [← hSameEffects α]
  exact hBR ρ α

end POVM

/-! ## 7. Reindex to `Fin (n * k)` (interface layer)

The structural theorems live on `Fin n × Fin k`.  The `POVM` /
`PVM` structures defined here are *already* on `Fin n` / `Fin N`,
so the headline statement is naturally indexed.  For downstream
consumers that prefer the literal `Fin (n*k)` space, this section
exposes a thin reindex via `finProdFinEquiv`.

We do not chase down the reindexed Born-rule identity here — it is
a straightforward push-forward of `kraus_gives_naimark_born_rule`
through `Matrix.submatrix finProdFinEquiv`, and is left for the
caller (the reindex is an algebraic isomorphism, not a theorem in
the deep sense). -/

section Reindex

variable {n k : ℕ}

/-- Reindex an `Fin n × Fin k`-indexed matrix to `Fin (n*k)` via
    `finProdFinEquiv`. -/
noncomputable def reindexProd
    (M : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ) :
    Matrix (Fin (n * k)) (Fin (n * k)) ℂ :=
  M.submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- Reindex a column vector (matrix with `Fin n`-rows and product cols
    on the left). -/
noncomputable def reindexIsometry
    (V : Matrix (Fin n × Fin k) (Fin n) ℂ) :
    Matrix (Fin (n * k)) (Fin n) ℂ :=
  V.submatrix finProdFinEquiv.symm id

end Reindex

end UnifiedTheory.LayerB.NaimarkDilation
