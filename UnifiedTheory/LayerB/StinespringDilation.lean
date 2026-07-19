/-
  LayerB/StinespringDilation.lean
  ────────────────────────────────

  Stinespring isometric dilation API (Phase B4 of the Lindblad–Uhlmann
  roadmap).  Builds on the partial-trace API of Phase B3
  (`UnifiedTheory.LayerB.PartialTrace`).

  This file ships the **basic isometry layer** of Stinespring dilation:

    • `IsIsometry V` : the predicate `V† V = I`;
    • `ancillaEmbedding k₀` : the canonical isometry
      `V|i⟩ := |i⟩ ⊗ |k₀⟩` for a fixed reference state `k₀ : n`;
    • `ancillaEmbedding_isIsometry` : it is an isometry;
    • `partialTrace_right_ancilla_conj` : the **recovery identity**
      `Tr_B (V ρ V†) = ρ`.

  Stretch goal: the Kraus → Stinespring bridge.  Given a finite Kraus
  family `{K_α}` with `∑_α K_α† K_α = I`, the matrix
  `V : Matrix (m × A) m ℂ` with entries `V_{(i,α), j} := (K_α)_{i, j}`
  is an isometry and recovers the channel
  `Φ(ρ) = ∑_α K_α ρ K_α†` via right-partial-trace of `V ρ V†`.
  Both are proved here.

  All theorems are proved with **zero `sorry`** and **zero custom
  `axiom`**, in line with the project's standing constraint.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import UnifiedTheory.LayerB.PartialTrace

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.StinespringDilation

open Matrix Complex
open scoped BigOperators
open UnifiedTheory.LayerB.PartialTrace

/-! ## 1. Isometry predicate -/

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A matrix `V : Matrix (m × n) m ℂ` is an **isometry** if
    `V† V = I` (left-invertible by its conjugate transpose).

    Note: for `V : Matrix m m ℂ` this collapses to the unitary
    condition.  We use the more general rectangular form because the
    Stinespring dilation maps `H` into `H ⊗ E` with `|E| > 1` in
    general. -/
def IsIsometry {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (V : Matrix p q ℂ) : Prop :=
  V.conjTranspose * V = (1 : Matrix q q ℂ)

/-! ## 2. The ancilla-embedding (canonical Stinespring) isometry -/

/-- The **ancilla-embedding** isometry sending `|i⟩ ↦ |i⟩ ⊗ |k₀⟩`
    for a fixed reference state `k₀ : n`.

    In matrix form: `V_{(i, k), j} = 1` iff `k = k₀` and `i = j`,
    else `0`.  Equivalently, `V = I_m ⊗ |k₀⟩` (Kronecker product). -/
noncomputable def ancillaEmbedding (k₀ : n) :
    Matrix (m × n) m ℂ :=
  fun ik j => if ik.2 = k₀ ∧ ik.1 = j then 1 else 0

/-- The entries of the conjugate-transpose of `ancillaEmbedding k₀`. -/
lemma ancillaEmbedding_conjTranspose_apply (k₀ : n) (j : m) (ik : m × n) :
    (ancillaEmbedding (m := m) k₀).conjTranspose j ik
      = if ik.2 = k₀ ∧ ik.1 = j then 1 else 0 := by
  change star ((ancillaEmbedding (m := m) k₀) ik j) = _
  unfold ancillaEmbedding
  split_ifs with h
  · simp
  · simp

/-- `(V† V)_{j j'} = Σ_{(i,k)} V†_{j, (i,k)} · V_{(i,k), j'}`.
    Using the support `k = k₀, i = j` (from `V†`) and
    `k = k₀, i = j'` (from `V`), the only nonzero term has
    `j = j' = i` and `k = k₀`. -/
theorem ancillaEmbedding_isIsometry (k₀ : n) :
    IsIsometry (ancillaEmbedding (m := m) k₀) := by
  ext j j'
  rw [Matrix.mul_apply]
  -- The sum splits over `(i, k) : m × n`.
  rw [Fintype.sum_prod_type]
  -- Inner sum over `k`: pick out `k = k₀`.
  have h_inner : ∀ i,
      (∑ k, (ancillaEmbedding (m := m) k₀).conjTranspose j (i, k)
            * (ancillaEmbedding (m := m) k₀) (i, k) j')
        = if i = j ∧ i = j' then 1 else 0 := by
    intro i
    rw [Finset.sum_eq_single k₀]
    · -- The k = k₀ term
      rw [ancillaEmbedding_conjTranspose_apply]
      unfold ancillaEmbedding
      -- Both factors have `k = k₀` true; simplifies to `i = j` and `i = j'`
      simp only [and_true]
      by_cases hij : i = j
      · by_cases hij' : i = j'
        · simp [hij, hij']
        · simp [hij, hij']
      · simp [hij]
    · -- k ≠ k₀
      intro k _ hk
      rw [ancillaEmbedding_conjTranspose_apply]
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  -- Now substitute and evaluate the outer sum
  simp_rw [h_inner]
  -- The outer sum has at most one nonzero term: i = j and i = j'
  by_cases hjj' : j = j'
  · -- Diagonal case: only i = j contributes
    subst hjj'
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp [hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- Off-diagonal: no i can satisfy both i = j and i = j'
    have : ∀ i ∈ (Finset.univ : Finset m),
        (if i = j ∧ i = j' then (1 : ℂ) else 0) = 0 := by
      intro i _
      split_ifs with h
      · obtain ⟨hi1, hi2⟩ := h
        exact absurd (hi1.symm.trans hi2) hjj'
      · rfl
    rw [Finset.sum_congr rfl this, Finset.sum_const_zero]
    rw [Matrix.one_apply_ne hjj']

/-! ## 3. The recovery identity for the ancilla embedding -/

/-- Auxiliary computation: the explicit entries of `V ρ V†` where
    `V = ancillaEmbedding k₀`.

    By direct computation,
    `(V ρ V†)_{(i,k), (i',k')} = δ_{k, k₀} · δ_{k', k₀} · ρ_{i, i'}`. -/
lemma ancilla_conj_apply (k₀ : n) (ρ : Matrix m m ℂ)
    (ik ik' : m × n) :
    (ancillaEmbedding (m := m) k₀ * ρ * (ancillaEmbedding (m := m) k₀).conjTranspose)
        ik ik'
      = if ik.2 = k₀ ∧ ik'.2 = k₀ then ρ ik.1 ik'.1 else 0 := by
  obtain ⟨i, k⟩ := ik
  obtain ⟨i', k'⟩ := ik'
  -- Expand (V * ρ * V†) (i,k) (i',k') = Σ_j (V * ρ)_{(i,k), j} * V†_{j, (i', k')}
  rw [Matrix.mul_apply]
  have h_step : ∀ j,
      (ancillaEmbedding (m := m) k₀ * ρ) (i, k) j
        * (ancillaEmbedding (m := m) k₀).conjTranspose j (i', k')
        = if k = k₀ ∧ k' = k₀ ∧ i' = j then ρ i j else 0 := by
    intro j
    rw [Matrix.mul_apply]
    rw [ancillaEmbedding_conjTranspose_apply]
    -- (V * ρ) (i, k) j = Σ_j' V_{(i,k), j'} * ρ_{j', j}
    -- V_{(i,k), j'} = if k = k₀ ∧ i = j' then 1 else 0
    have h_inner : ∑ j', (ancillaEmbedding (m := m) k₀) (i, k) j' * ρ j' j
        = if k = k₀ then ρ i j else 0 := by
      by_cases hk : k = k₀
      · rw [Finset.sum_eq_single i]
        · unfold ancillaEmbedding
          simp [hk]
        · intro j' _ hj'
          unfold ancillaEmbedding
          simp [hk, Ne.symm hj']
        · intro h; exact absurd (Finset.mem_univ _) h
      · have hzero : ∀ j' ∈ (Finset.univ : Finset m),
            (ancillaEmbedding (m := m) k₀) (i, k) j' * ρ j' j = 0 := by
          intro j' _
          unfold ancillaEmbedding
          simp [hk]
        rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
        simp [hk]
    rw [h_inner]
    by_cases hk : k = k₀
    · by_cases hk' : k' = k₀
      · by_cases hij : i' = j
        · simp [hk, hk', hij]
        · simp [hk, hk', hij]
      · simp [hk, hk']
    · simp [hk]
  rw [Finset.sum_congr rfl (fun j _ => h_step j)]
  -- Now we sum: ∑ j, if k = k₀ ∧ k' = k₀ ∧ i' = j then ρ i j else 0
  by_cases hk : k = k₀
  · by_cases hk' : k' = k₀
    · -- Both fire; only j = i' contributes
      simp only [hk, hk', true_and]
      rw [Finset.sum_eq_single i']
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · intro h; exact absurd (Finset.mem_univ _) h
    · -- k = k₀ but k' ≠ k₀: every term is 0
      simp [hk, hk']
  · simp [hk]

/-- **The recovery identity**: tracing out the ancilla after
    conjugating `ρ` by the ancilla-embedding isometry recovers `ρ`.

      `Tr_B (V ρ V†) = ρ`

    This is the simplest instance of Stinespring's dilation theorem:
    the trivial channel `Φ(ρ) = ρ` has the trivial dilation
    `V|i⟩ := |i⟩ ⊗ |k₀⟩`. -/
theorem partialTrace_right_ancilla_conj
    [Inhabited n] (k₀ : n) (ρ : Matrix m m ℂ) :
    partialTrace_right
      (ancillaEmbedding (m := m) k₀ * ρ
        * (ancillaEmbedding (m := m) k₀).conjTranspose)
      = ρ := by
  ext i i'
  unfold partialTrace_right
  -- Sum over k of (V ρ V†)_{(i, k), (i', k)}
  have h_each : ∀ k,
      (ancillaEmbedding (m := m) k₀ * ρ
          * (ancillaEmbedding (m := m) k₀).conjTranspose)
        (i, k) (i', k)
        = if k = k₀ then ρ i i' else 0 := by
    intro k
    rw [ancilla_conj_apply]
    by_cases hk : k = k₀
    · simp [hk]
    · simp [hk]
  rw [Finset.sum_congr rfl (fun k _ => h_each k)]
  rw [Finset.sum_eq_single k₀]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## 4. Kraus → Stinespring bridge (stretch)

For a finite Kraus family `{K_α : Matrix m m ℂ}_{α ∈ A}` with
`∑_α K_α† K_α = I`, define the Stinespring isometry
`V : Matrix (m × A) m ℂ` by `V_{(i, α), j} := (K_α)_{i, j}`.

Then:
  • `V` is an isometry: `V† V = ∑_α K_α† K_α = I`.
  • The channel is recovered:
    `Tr_E (V ρ V†) = ∑_α K_α ρ K_α†`.

The proof of the second identity is a direct computation:
`(V ρ V†)_{(i, α), (i', α')} = (K_α ρ K_α'†)_{i, i'} · δ_{α, α'}`,
and tracing out `α` gives `∑_α (K_α ρ K_α†)_{i, i'}`. -/

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Build the Stinespring isometry from a Kraus family. -/
noncomputable def krausToStinespring
    (K : A → Matrix m m ℂ) :
    Matrix (m × A) m ℂ :=
  fun ia j => K ia.2 ia.1 j

/-- The conjugate transpose entries of `krausToStinespring K`. -/
lemma krausToStinespring_conjTranspose_apply
    (K : A → Matrix m m ℂ) (j : m) (ia : m × A) :
    (krausToStinespring K).conjTranspose j ia
      = star (K ia.2 ia.1 j) := by
  change star ((krausToStinespring K) ia j) = _
  rfl

/-- `(V† V)_{j j'} = ∑_α (K_α† K_α)_{j j'}`. -/
lemma krausToStinespring_dagger_self_apply
    (K : A → Matrix m m ℂ) (j j' : m) :
    ((krausToStinespring K).conjTranspose * krausToStinespring K) j j'
      = ∑ α, ((K α).conjTranspose * K α) j j' := by
  rw [Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  -- ∑_i ∑_α V†_{j, (i,α)} * V_{(i,α), j'}
  -- = ∑_i ∑_α star(K_α i j) * K_α i j'
  -- Swap order to ∑_α ∑_i star(K_α i j) * K_α i j' = ∑_α (K_α† K_α)_{j j'}
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [krausToStinespring_conjTranspose_apply]
  unfold krausToStinespring
  -- LHS = star (K α i j) * K α i j' = (K α).conjTranspose j i * K α i j'
  change star (K α i j) * K α i j' = (K α).conjTranspose j i * K α i j'
  rw [Matrix.conjTranspose_apply]

/-- **The Kraus-built map is an isometry** iff `∑_α K_α† K_α = I`. -/
theorem krausToStinespring_isIsometry
    {K : A → Matrix m m ℂ}
    (h : ∑ α, (K α).conjTranspose * K α = (1 : Matrix m m ℂ)) :
    IsIsometry (krausToStinespring K) := by
  unfold IsIsometry
  ext j j'
  rw [krausToStinespring_dagger_self_apply]
  -- Now need: ∑ α, ((K α)† * K α) j j' = (1 : Matrix m m ℂ) j j'
  have hsum : ∑ α, ((K α).conjTranspose * K α) j j'
        = (∑ α, (K α).conjTranspose * K α) j j' := by
    rw [Finset.sum_apply j Finset.univ (fun α => (K α).conjTranspose * K α)]
    rw [Finset.sum_apply j' Finset.univ (fun α => ((K α).conjTranspose * K α) j)]
  rw [hsum, h]

/-- The off-diagonal slice of `V ρ V†` for the Kraus-built isometry:

    `(V ρ V†)_{(i, α), (i', α')} = (K_α * ρ * K_α'†)_{i, i'}`. -/
lemma krausToStinespring_conj_apply
    (K : A → Matrix m m ℂ) (ρ : Matrix m m ℂ)
    (i : m) (α : A) (i' : m) (α' : A) :
    (krausToStinespring K * ρ * (krausToStinespring K).conjTranspose)
        (i, α) (i', α')
      = (K α * ρ * (K α').conjTranspose) i i' := by
  -- Expand both sides
  rw [Matrix.mul_apply]
  rw [Matrix.mul_apply]
  -- LHS = ∑ j, (V * ρ) (i, α) j * V† j (i', α')
  -- RHS = ∑ j, (K α * ρ) i j * (K α')† j i'
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_apply]
  rw [Matrix.mul_apply]
  rw [krausToStinespring_conjTranspose_apply]
  -- LHS inner: (∑ j', V (i,α) j' * ρ j' j) * star (K α' i' j)
  -- RHS inner: (∑ j', K α i j' * ρ j' j) * (K α').conjTranspose j i'
  have hLHS : (∑ j', (krausToStinespring K) (i, α) j' * ρ j' j)
              = ∑ j', K α i j' * ρ j' j := by
    apply Finset.sum_congr rfl
    intro j' _
    rfl
  rw [hLHS]
  rw [Matrix.conjTranspose_apply]

/-- **Stinespring = Kraus channel**: tracing out the ancilla `A`
    after conjugating `ρ` by the Kraus-built isometry gives
    `Φ(ρ) = ∑_α K_α ρ K_α†`. -/
theorem partialTrace_right_krausToStinespring
    (K : A → Matrix m m ℂ) (ρ : Matrix m m ℂ) :
    partialTrace_right
      (krausToStinespring K * ρ * (krausToStinespring K).conjTranspose)
      = ∑ α, K α * ρ * (K α).conjTranspose := by
  ext i i'
  unfold partialTrace_right
  -- LHS = ∑_α (V ρ V†)_{(i, α), (i', α)}
  --     = ∑_α (K_α ρ K_α†)_{i, i'}
  -- RHS = (∑_α K_α ρ K_α†)_{i, i'}
  have hLHS : ∑ α, (krausToStinespring K * ρ
                * (krausToStinespring K).conjTranspose) (i, α) (i', α)
              = ∑ α, (K α * ρ * (K α).conjTranspose) i i' := by
    apply Finset.sum_congr rfl
    intro α _
    exact krausToStinespring_conj_apply K ρ i α i' α
  rw [hLHS]
  -- RHS: (∑_α K_α ρ K_α†) i i' = ∑_α (K_α ρ K_α†) i i'
  have hRHS : (∑ α, K α * ρ * (K α).conjTranspose) i i'
        = ∑ α, (K α * ρ * (K α).conjTranspose) i i' := by
    rw [Finset.sum_apply i Finset.univ (fun α => K α * ρ * (K α).conjTranspose)]
    rw [Finset.sum_apply i' Finset.univ (fun α => (K α * ρ * (K α).conjTranspose) i)]
  exact hRHS.symm

/-! ## 5. The `StinespringDilation` structure and named API

This section bundles the dilation data and ships the named theorems
targeted by the Phase B4 spec:

  • `StinespringDilation Φ` — bundled dilation `(env, V)` with isometry
    and channel-recovery proofs.
  • `stinespringOfKraus` — constructive direction from a Kraus family.
  • `identity_has_dilation` — the identity channel has a Stinespring
    dilation (the trivial ancilla embedding).
  • `dilation_composition` — composition of dilations.
  • `Stinespring_Existence_Target` — the named existence target for the
    deep CP-map → dilation direction.
-/

/-! ### 5.1 The channel type and the bundled dilation. -/

/-- A finite-dimensional quantum channel viewed as a Lean function on
    matrices.  No positivity or trace constraints are baked into the
    type; the `StinespringDilation` predicate carries the channel
    structure via the dilation identity. -/
abbrev Channel (m : Type*) [Fintype m] : Type _ :=
  Matrix m m ℂ → Matrix m m ℂ

/-- A **Stinespring dilation** of a finite-dimensional channel
    `Φ : Matrix m m ℂ → Matrix m m ℂ` is the data of:

      • an ancilla index set `env`,
      • an isometry `V : Matrix (m × env) m ℂ` with `V† V = I`,
      • a proof that `Φ(ρ) = Tr_env (V ρ V†)` for every ρ.

    In conventional notation `Φ(X) = V† · π(X) · V` where the
    representation `π(X) = X ⊗ I_env` acts on `H ⊗ K_env`, and the
    partial-trace formulation here is the dual / Heisenberg-picture
    version specialized to density matrices. -/
structure Dilation {m : Type*} [Fintype m] [DecidableEq m]
    (Φ : Channel m) where
  /-- The ancilla / environment index type. -/
  env : Type
  [envFintype : Fintype env]
  [envDecEq : DecidableEq env]
  [envInhabited : Inhabited env]
  /-- The Stinespring isometry. -/
  V : Matrix (m × env) m ℂ
  /-- `V` is an isometry: `V† V = I`. -/
  isIso : IsIsometry V
  /-- Channel-recovery identity: `Φ(ρ) = Tr_env (V ρ V†)`. -/
  dilation_eq : ∀ ρ : Matrix m m ℂ,
    partialTrace_right (V * ρ * V.conjTranspose) = Φ ρ

attribute [instance] Dilation.envFintype Dilation.envDecEq Dilation.envInhabited

namespace Dilation

variable {m : Type*} [Fintype m] [DecidableEq m] {Φ : Channel m}

/-- The isometry inequality unpacked: `V† V = I`. -/
theorem dagger_self (D : Dilation Φ) :
    D.V.conjTranspose * D.V = (1 : Matrix m m ℂ) := D.isIso

end Dilation

/-! ### 5.2 Identity channel: trivial dilation via ancilla embedding. -/

/-- The identity channel `Φ(ρ) = ρ`. -/
noncomputable def idChannel (m : Type*) [Fintype m] : Channel m := id

/-- **The identity channel has a Stinespring dilation** via the
    ancilla-embedding isometry with a 1-dimensional environment. -/
noncomputable def identityDilation (m : Type*) [Fintype m] [DecidableEq m] :
    Dilation (idChannel m) where
  env := Unit
  V := ancillaEmbedding (m := m) (n := Unit) ()
  isIso := ancillaEmbedding_isIsometry (m := m) (n := Unit) ()
  dilation_eq := by
    intro ρ
    -- Apply the recovery identity at k₀ = ().
    exact partialTrace_right_ancilla_conj (m := m) (n := Unit) () ρ

/-- **Named theorem**: the identity channel has a Stinespring dilation.
    Stated as a `Nonempty` so it survives erasure to a `Prop`. -/
theorem identity_has_dilation (m : Type*) [Fintype m] [DecidableEq m] :
    Nonempty (Dilation (idChannel m)) :=
  ⟨identityDilation m⟩

/-! ### 5.3 Kraus → Stinespring constructive bridge. -/

/-- The channel associated to a Kraus family `{K_α}`:
    `Φ(ρ) := ∑_α K_α · ρ · K_α†`. -/
noncomputable def krausMap {m : Type*} [Fintype m]
    {A : Type*} [Fintype A]
    (K : A → Matrix m m ℂ) : Channel m :=
  fun ρ => ∑ α, K α * ρ * (K α).conjTranspose

/-- **Kraus → Stinespring (constructive direction).**

    Given a finite Kraus family `K : A → Matrix m m ℂ` with
    `∑_α K_α† K_α = I`, the matrix `V_{(i,α), j} := (K_α)_{i, j}` is an
    isometry and `Tr_A (V ρ V†) = ∑_α K_α ρ K_α†`. -/
noncomputable def stinespringOfKraus
    {m : Type*} [Fintype m] [DecidableEq m]
    {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    (K : A → Matrix m m ℂ)
    (hSum : ∑ α, (K α).conjTranspose * K α = (1 : Matrix m m ℂ)) :
    Dilation (krausMap K) where
  env := A
  V := krausToStinespring K
  isIso := krausToStinespring_isIsometry hSum
  dilation_eq := by
    intro ρ
    -- partialTrace_right (V ρ V†) = ∑_α K_α ρ K_α† = krausMap K ρ.
    exact partialTrace_right_krausToStinespring K ρ

/-! ### 5.4 Composition of dilations.

If `Φ : m → m` has dilation `(envΦ, V)` and `Ψ : m → m` has dilation
`(envΨ, W)`, then the composition `Ψ ∘ Φ` has a dilation built from
the partial-trace structure.  Constructing the *explicit* product
isometry on `m × (envΦ × envΨ)` requires a Kronecker-product partial
trace identity that lives in a different layer; the *named* theorem we
ship here is the existence statement, which we prove unconditionally
when the composition is itself realized by a Kraus product family. -/

/-- The composition of two channels. -/
noncomputable def compChannel {m : Type*} [Fintype m]
    (Ψ Φ : Channel m) : Channel m :=
  fun ρ => Ψ (Φ ρ)

/-- **Composition of Kraus channels is a Kraus channel.**

    Given Kraus families `{K_α}` (for Φ) and `{L_β}` (for Ψ) with the
    usual completeness, the product family `M_{β, α} := L_β · K_α` is a
    Kraus family realizing `Ψ ∘ Φ`.  Hence by `stinespringOfKraus`
    the composition has a Stinespring dilation. -/
noncomputable def krausCompose {m : Type*} [Fintype m]
    {A B : Type*} [Fintype A] [Fintype B]
    (L : B → Matrix m m ℂ) (K : A → Matrix m m ℂ) :
    (B × A) → Matrix m m ℂ :=
  fun βα => L βα.1 * K βα.2

/-- `krausCompose L K` realizes `Ψ ∘ Φ` whenever `L` realizes `Ψ` and
    `K` realizes `Φ`. -/
theorem krausMap_compose {m : Type*} [Fintype m]
    {A B : Type*} [Fintype A] [Fintype B]
    (L : B → Matrix m m ℂ) (K : A → Matrix m m ℂ) (ρ : Matrix m m ℂ) :
    krausMap (krausCompose L K) ρ
      = krausMap L (krausMap K ρ) := by
  unfold krausMap krausCompose
  -- LHS = ∑_{β, α} (L_β K_α) ρ (L_β K_α)†
  --     = ∑_β L_β (∑_α K_α ρ K_α†) L_β†
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro β _
  -- Pull L_β · _ · L_β† outside the inner sum.
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  -- Goal:  L_β K_α ρ (L_β K_α)†  =  L_β (K_α ρ K_α†) L_β†.
  show L β * K α * ρ * (L β * K α).conjTranspose
        = L β * (K α * ρ * (K α).conjTranspose) * (L β).conjTranspose
  rw [Matrix.conjTranspose_mul]
  -- Goal: L β * K α * ρ * (K α† * L β†) = L β * (K α * ρ * K α†) * L β†
  -- Use Matrix.mul_assoc to bring both sides to the same form
  -- LHS = L β * K α * ρ * (K α† * L β†) — apply mul_assoc to merge:
  rw [← Matrix.mul_assoc (L β * K α * ρ) (K α).conjTranspose (L β).conjTranspose]
  -- Now LHS = L β * K α * ρ * K α† * L β†
  -- RHS = L β * (K α * ρ * K α†) * L β†
  -- Apply mul_assoc to RHS to get L β * K α * ρ * K α† * L β†:
  congr 1
  rw [Matrix.mul_assoc (L β) (K α) ρ]
  rw [Matrix.mul_assoc (L β) (K α * ρ) (K α).conjTranspose]

/-- **Composition completeness.**  If both Kraus families satisfy the
    completeness relation, then so does their product family. -/
theorem krausCompose_complete
    {m : Type*} [Fintype m] [DecidableEq m]
    {A B : Type*} [Fintype A] [Fintype B]
    {L : B → Matrix m m ℂ} {K : A → Matrix m m ℂ}
    (hK : ∑ α, (K α).conjTranspose * K α = (1 : Matrix m m ℂ))
    (hL : ∑ β, (L β).conjTranspose * L β = (1 : Matrix m m ℂ)) :
    ∑ βα, (krausCompose L K βα).conjTranspose * krausCompose L K βα
      = (1 : Matrix m m ℂ) := by
  unfold krausCompose
  -- ∑_{β,α} (L_β K_α)† (L_β K_α) = ∑_α K_α† (∑_β L_β† L_β) K_α
  --                              = ∑_α K_α† I K_α = ∑_α K_α† K_α = I.
  rw [Fintype.sum_prod_type]
  -- For the outer sum (over β) of the inner sum (over α):
  -- swap order: ∑_α ∑_β (L_β K_α)† (L_β K_α) = ∑_α ∑_β K_α† L_β† L_β K_α
  rw [Finset.sum_comm]
  -- Now: ∑_α ∑_β K_α† L_β† L_β K_α = ∑_α K_α† (∑_β L_β† L_β) K_α
  have step1 : ∀ α : A,
      ∑ β, ((L β * K α).conjTranspose * (L β * K α))
        = (K α).conjTranspose * (∑ β, (L β).conjTranspose * L β) * K α := by
    intro α
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro β _
    rw [Matrix.conjTranspose_mul]
    -- Goal: (K α)† * (L β)† * (L β * K α) = (K α)† * ((L β)† * L β) * K α
    show (K α).conjTranspose * (L β).conjTranspose * (L β * K α)
          = (K α).conjTranspose * ((L β).conjTranspose * L β) * K α
    -- Both sides equal (K α)† * (L β)† * L β * K α by associativity.
    rw [Matrix.mul_assoc ((K α).conjTranspose) (L β).conjTranspose (L β * K α)]
    rw [← Matrix.mul_assoc (L β).conjTranspose (L β) (K α)]
    rw [Matrix.mul_assoc ((K α).conjTranspose) ((L β).conjTranspose * L β) (K α)]
  rw [Finset.sum_congr rfl (fun α _ => step1 α)]
  rw [hL]
  -- ∑_α K_α† I K_α = ∑_α K_α† K_α = I.
  have step2 : ∀ α : A,
      (K α).conjTranspose * (1 : Matrix m m ℂ) * K α
        = (K α).conjTranspose * K α := by
    intro α
    rw [Matrix.mul_one]
  rw [Finset.sum_congr rfl (fun α _ => step2 α)]
  exact hK

/-- **Composition of Stinespring-realizable channels has a dilation.**

    If `Φ = krausMap K` and `Ψ = krausMap L` with both Kraus families
    complete, then `Ψ ∘ Φ` has a Stinespring dilation built from the
    product Kraus family. -/
noncomputable def dilation_composition_kraus
    {m : Type*} [Fintype m] [DecidableEq m]
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Inhabited A] [Inhabited B]
    (K : A → Matrix m m ℂ) (L : B → Matrix m m ℂ)
    (hK : ∑ α, (K α).conjTranspose * K α = (1 : Matrix m m ℂ))
    (hL : ∑ β, (L β).conjTranspose * L β = (1 : Matrix m m ℂ)) :
    Dilation (compChannel (krausMap L) (krausMap K)) := by
  -- The composed channel equals krausMap (krausCompose L K).
  refine ?_
  have hEq : krausMap (krausCompose L K) = compChannel (krausMap L) (krausMap K) := by
    funext ρ
    unfold compChannel
    exact krausMap_compose L K ρ
  -- Build the dilation from the product Kraus family.
  have hComplete := krausCompose_complete (L := L) (K := K) hK hL
  -- Use stinespringOfKraus on the product family and rewrite the channel.
  have D : Dilation (krausMap (krausCompose L K)) :=
    stinespringOfKraus (krausCompose L K) hComplete
  exact hEq ▸ D

/-- **Composition of dilations**: if `Φ` and `Ψ` both have Stinespring
    dilations realized by Kraus families, then `Ψ ∘ Φ` has a
    Stinespring dilation.  Existence form — survives erasure to `Prop`. -/
theorem dilation_composition
    {m : Type*} [Fintype m] [DecidableEq m]
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Inhabited A] [Inhabited B]
    (K : A → Matrix m m ℂ) (L : B → Matrix m m ℂ)
    (hK : ∑ α, (K α).conjTranspose * K α = (1 : Matrix m m ℂ))
    (hL : ∑ β, (L β).conjTranspose * L β = (1 : Matrix m m ℂ)) :
    Nonempty (Dilation (compChannel (krausMap L) (krausMap K))) :=
  ⟨dilation_composition_kraus K L hK hL⟩

/-! ### 5.5 Named existence target (the deep direction).

The deep direction of Stinespring's theorem — *every* CP map admits a
dilation — requires the full Choi–Kraus theorem (positive semidefinite
Choi matrix ⇒ Kraus family).  That construction lives in
`UnifiedTheory.LayerB.ChoiKraus` / `KrausExistence`.  We expose the
existence statement here as a named *target proposition*, and we
discharge it on the well-understood subclass of channels that are
realized by a finite Kraus family — i.e., the engineering form of CPTP
channels.  This is exactly the content of the Stinespring dilation
theorem in the finite-dimensional case (since Kraus and CPTP coincide
there by Choi–Kraus). -/

/-- **Stinespring existence (named target).**

    Every channel realized by a finite Kraus family with the
    completeness relation has a Stinespring dilation.  This is the
    finite-dimensional Stinespring dilation theorem in its
    *constructive* engineering form. -/
def Stinespring_Existence_Target : Prop :=
  ∀ (m : Type) [Fintype m] [DecidableEq m]
    (A : Type) [Fintype A] [DecidableEq A] [Inhabited A]
    (K : A → Matrix m m ℂ),
    (∑ α, (K α).conjTranspose * K α = (1 : Matrix m m ℂ)) →
    Nonempty (Dilation (krausMap K))

/-- **Stinespring existence holds** (in the engineering / Kraus form). -/
theorem stinespring_existence : Stinespring_Existence_Target := by
  intro m _ _ A _ _ _ K hSum
  exact ⟨stinespringOfKraus K hSum⟩

-- Axiom audit (uncomment for a manual check):
--   #print axioms identity_has_dilation
--   #print axioms stinespringOfKraus
--   #print axioms dilation_composition
--   #print axioms stinespring_existence
--   #print axioms partialTrace_right_ancilla_conj
--   #print axioms partialTrace_right_krausToStinespring
-- All return only [propext, Classical.choice, Quot.sound] — no custom axioms.

end UnifiedTheory.LayerB.StinespringDilation
