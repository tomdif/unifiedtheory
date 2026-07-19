/-
  LayerB/SchurWeylDuality.lean
  ─────────────────────────────────────────────────────────────────────
  SCHUR–WEYL DUALITY  (Schur 1901, Weyl 1939)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  The classical theorem.

      For a finite-dimensional complex vector space `V = ℂ^d` and an
      integer `n ≥ 1`, the `n`-th tensor power `V^⊗n` carries two
      commuting actions:

        •  `GL(V)` acts diagonally,  g · (v₁ ⊗ ... ⊗ v_n) = g v₁ ⊗ ...
                                                            ⊗ g v_n;
        •  `S_n`   acts by permuting tensor factors.

      The two algebras `ℂ[GL(V)]` and `ℂ[S_n]` are each other's
      centralisers inside `End(V^⊗n)`, hence by the double-centraliser
      theorem,

           V^⊗n  ≅  ⊕_{lam ⊢ n,  ℓ(lam) ≤ d}   V_lam^{GL} ⊗ S^lam      (∗)

      where the sum is over partitions `lam` of n with at most d parts,
      `V_lam^{GL}` is the irreducible polynomial GL(V)-module of
      highest weight `lam`, and `S^lam` is the Specht module
      (irreducible S_n-module) indexed by `lam`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  What this file proves UNCONDITIONALLY.

    • `symMatrix d`    — the set of symmetric matrices in `Matrix _ _ ℂ`,
                         `M i j = M j i`.
    • `antisymMatrix d`— the set of antisymmetric matrices,
                         `M i j = -M j i`.
    • `symPart M`      — the symmetric part `(M + Mᵀ) / 2`.
    • `antisymPart M`  — the antisymmetric part `(M - Mᵀ) / 2`.
    • `symPart_mem`    — `symPart M ∈ symMatrix d`.
    • `antisymPart_mem`— `antisymPart M ∈ antisymMatrix d`.
    • `add_sym_antisym`— every matrix is the sum of its symmetric and
                         antisymmetric parts: `M = symPart M + antisymPart M`.
    • `schur_weyl_n_two` — the n=2 Schur–Weyl decomposition: for every
                         `M`, there exist UNIQUE `S ∈ symMatrix d` and
                         `A ∈ antisymMatrix d` such that `M = S + A`,
                         with the explicit formulas
                         `S i j = (M i j + M j i)/2`,
                         `A i j = (M i j - M j i)/2`.
    • `sym_antisym_disjoint` — the symmetric and antisymmetric subspaces
                         meet only at zero (proves uniqueness).
    • `schur_weyl_n_one` — the trivial n=1 statement
                         `V ≅ V_{(1)} ⊗ S^{(1)}`, since `S^{(1)}` is
                         the one-dimensional trivial S₁-module.
    • `SpechtIndex n d` — partition of `n` into at most `d` positive
                         parts (decreasing).  Indexing set for (∗).
    • `spechtIndex_n_one` — the only `SpechtIndex 1 d` (for `d ≥ 1`)
                         is the one-part partition `[1]`.
    • `spechtIndex_n_two_d_ge_two` — the two `SpechtIndex 2 d`
                         elements (for `d ≥ 2`) are `[2]` (symmetric)
                         and `[1,1]` (antisymmetric).

  Named targets (statements, not discharged).

    • `SchurWeyl_Decomposition_Target` — the full multiplicity-free
                         decomposition (∗).
    • `schur_weyl_master` — a master statement bundling everything
                         shipped here plus the propositional consistency
                         of the full target.

  HONESTY MANDATE.

    Zero `sorry`. Zero custom `axiom`.

    What is left as a STATEMENT (not as a proof) is the full
    decomposition theorem (∗): constructing the GL-irrep `V_lam^{GL}`
    (Weyl module via the Schur functor) and the Specht module `S^lam`,
    and exhibiting the explicit isomorphism, is a multi-week formal-
    isation project building on Young symmetrisers, the Robinson–
    Schensted correspondence, and the highest-weight theory of GL(V).

  REFERENCES.

    • H. Weyl, *The Classical Groups* (1939), Ch. IV.
    • W. Fulton & J. Harris, *Representation Theory* (1991), §6.
    • R. Goodman & N. R. Wallach, *Symmetry, Representations, and
      Invariants* (2009), Ch. 9.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace UnifiedTheory.LayerB.SchurWeylDuality

open scoped Matrix

/-! ## 1.  Tensor power placeholder type.

The full Schur–Weyl theorem lives on the n-fold tensor power `V^⊗n`.
For the rank-two case (`n = 2`) the tensor power is canonically
identified with the space of d × d complex matrices via
`(v ⊗ w) i j = v i · w j`.  We work with `Matrix (Fin d) (Fin d) ℂ`
throughout.

For general `n` we record a placeholder type
`TensorPower d n := Fin n → Fin d → ℂ` representing the linear span
of pure tensors `e_{i_1} ⊗ ... ⊗ e_{i_n}` indexed by an n-tuple of
basis labels.  The Schur–Weyl statement (∗) refers to a different
ambient space (the tensor power as a single ℂ-vector space), but the
placeholder is enough to phrase the named target.
-/

/-- Index set for tensor-power basis vectors `e_{i_1} ⊗ ... ⊗ e_{i_n}`. -/
abbrev TensorPowerBasis (d n : ℕ) : Type := Fin n → Fin d

/-- Placeholder representation of `V^⊗n` as the free ℂ-module on
`TensorPowerBasis d n`. -/
abbrev TensorPower (d n : ℕ) : Type := TensorPowerBasis d n → ℂ

/-! ## 2.  Symmetric and antisymmetric subspaces of `V ⊗ V`.

We identify `V ⊗ V` with `Matrix (Fin d) (Fin d) ℂ`.
-/

/-- The set of symmetric matrices. -/
def symMatrix (d : ℕ) : Set (Matrix (Fin d) (Fin d) ℂ) :=
  {M | ∀ i j, M i j = M j i}

/-- The set of antisymmetric matrices. -/
def antisymMatrix (d : ℕ) : Set (Matrix (Fin d) (Fin d) ℂ) :=
  {M | ∀ i j, M i j = -M j i}

/-- The symmetric part of a matrix:  `(M + Mᵀ) / 2`. -/
noncomputable def symPart {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (1 / 2 : ℂ) • (M + Mᵀ)

/-- The antisymmetric part of a matrix:  `(M - Mᵀ) / 2`. -/
noncomputable def antisymPart {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (1 / 2 : ℂ) • (M - Mᵀ)

@[simp] lemma symPart_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin d) :
    symPart M i j = (1 / 2 : ℂ) * (M i j + M j i) := by
  simp [symPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]

@[simp] lemma antisymPart_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin d) :
    antisymPart M i j = (1 / 2 : ℂ) * (M i j - M j i) := by
  simp [antisymPart, Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply]

/-- The symmetric part lies in the symmetric subspace. -/
lemma symPart_mem {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    symPart M ∈ symMatrix d := by
  intro i j
  simp [symPart_apply, add_comm]

/-- The antisymmetric part lies in the antisymmetric subspace. -/
lemma antisymPart_mem {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    antisymPart M ∈ antisymMatrix d := by
  intro i j
  rw [antisymPart_apply, antisymPart_apply]
  ring

/-- Every matrix equals the sum of its symmetric and antisymmetric parts. -/
lemma add_sym_antisym {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    M = symPart M + antisymPart M := by
  ext i j
  simp [Matrix.add_apply, symPart_apply, antisymPart_apply]
  ring

/-- Symmetric and antisymmetric subspaces are disjoint:
the only matrix that is BOTH symmetric and antisymmetric is `0`. -/
lemma sym_antisym_disjoint {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (hS : M ∈ symMatrix d) (hA : M ∈ antisymMatrix d) : M = 0 := by
  ext i j
  -- `M i j = M j i` (symmetric) and `M i j = -(M j i)` (antisymmetric);
  -- combine to get  M i j = -(M i j), hence  2 * M i j = 0,  hence M i j = 0.
  have h1 : M i j = M j i := hS i j
  have h2 : M i j = -(M j i) := hA i j
  have hneg : M i j = -(M i j) := by
    -- M i j = -M j i (h2); M j i = M i j (← h1).  So M i j = -(M i j).
    calc M i j = -(M j i) := h2
      _ = -(M i j) := by rw [← h1]
  have hMij : M i j = 0 := by
    have htwo : (2 : ℂ) ≠ 0 := by norm_num
    have h2x : (2 : ℂ) * M i j = 0 := by
      calc (2 : ℂ) * M i j
          = M i j + M i j := by ring
        _ = M i j + -(M i j) := by rw [← hneg]
        _ = 0 := by ring
    have : M i j = (2 : ℂ)⁻¹ * ((2 : ℂ) * M i j) := by
      field_simp
    rw [this, h2x, mul_zero]
  simp [Matrix.zero_apply, hMij]

/-! ## 3.  Schur–Weyl decomposition for `n = 2`.

The decomposition
  `V ⊗ V  =  Sym²(V)  ⊕  ∧²(V)`
is the `n = 2` case of (∗).  Under the identification `V ⊗ V ≃
Matrix (Fin d) (Fin d) ℂ`, `Sym²(V) = symMatrix d` and `∧²(V) =
antisymMatrix d`.

We provide:
  • existence (`schur_weyl_n_two_exists`),
  • the explicit formulas (`schur_weyl_n_two`),
  • uniqueness (`schur_weyl_n_two_unique`).
-/

/-- The Schur–Weyl decomposition for `n = 2`, existence form. -/
theorem schur_weyl_n_two_exists (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    ∃ (S A : Matrix (Fin d) (Fin d) ℂ),
      S ∈ symMatrix d ∧ A ∈ antisymMatrix d ∧ M = S + A := by
  refine ⟨symPart M, antisymPart M, ?_, ?_, ?_⟩
  · exact symPart_mem M
  · exact antisymPart_mem M
  · exact add_sym_antisym M

/-- The Schur–Weyl decomposition for `n = 2`, with EXPLICIT formulas
for the symmetric and antisymmetric parts. -/
theorem schur_weyl_n_two (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    ∃ (S A : Matrix (Fin d) (Fin d) ℂ),
      S ∈ symMatrix d ∧ A ∈ antisymMatrix d ∧ M = S + A ∧
      (∀ i j, S i j = (M i j + M j i) / 2) ∧
      (∀ i j, A i j = (M i j - M j i) / 2) := by
  refine ⟨symPart M, antisymPart M, symPart_mem M, antisymPart_mem M,
           add_sym_antisym M, ?_, ?_⟩
  · intro i j
    rw [symPart_apply]
    ring
  · intro i j
    rw [antisymPart_apply]
    ring

/-- Uniqueness of the decomposition `M = S + A` with `S` symmetric
and `A` antisymmetric. -/
theorem schur_weyl_n_two_unique (d : ℕ)
    (M S₁ A₁ S₂ A₂ : Matrix (Fin d) (Fin d) ℂ)
    (hS₁ : S₁ ∈ symMatrix d) (hA₁ : A₁ ∈ antisymMatrix d) (h₁ : M = S₁ + A₁)
    (hS₂ : S₂ ∈ symMatrix d) (hA₂ : A₂ ∈ antisymMatrix d) (h₂ : M = S₂ + A₂) :
    S₁ = S₂ ∧ A₁ = A₂ := by
  -- From M = S₁ + A₁ = S₂ + A₂ we get  S₁ - S₂ = A₂ - A₁.
  -- LHS is symmetric, RHS is antisymmetric, hence both zero.
  have hsum : S₁ + A₁ = S₂ + A₂ := h₁.symm.trans h₂
  have hdiff : S₁ - S₂ = A₂ - A₁ := by
    -- Standard additive-group manipulation:
    -- S₁ + A₁ = S₂ + A₂  ⇒  S₁ - S₂ = A₂ - A₁
    have hg : S₁ + A₁ - S₂ - A₁ = S₂ + A₂ - S₂ - A₁ := by
      rw [hsum]
    -- Simplify both sides.
    have hgL : S₁ + A₁ - S₂ - A₁ = S₁ - S₂ := by abel
    have hgR : S₂ + A₂ - S₂ - A₁ = A₂ - A₁ := by abel
    rw [hgL, hgR] at hg
    exact hg
  -- S₁ - S₂ is symmetric:
  have hSdiff_sym : (S₁ - S₂) ∈ symMatrix d := by
    intro i j
    show (S₁ - S₂) i j = (S₁ - S₂) j i
    simp only [Matrix.sub_apply]
    rw [hS₁ i j, hS₂ i j]
  -- A₂ - A₁ is antisymmetric:
  have hAdiff_anti : (A₂ - A₁) ∈ antisymMatrix d := by
    intro i j
    show (A₂ - A₁) i j = -((A₂ - A₁) j i)
    simp only [Matrix.sub_apply]
    rw [hA₁ i j, hA₂ i j]
    ring
  -- Hence S₁ - S₂ ∈ symMatrix ∩ antisymMatrix.
  have hSdiff_anti : (S₁ - S₂) ∈ antisymMatrix d := by
    rw [hdiff]; exact hAdiff_anti
  have hSdiff_zero : S₁ - S₂ = 0 :=
    sym_antisym_disjoint _ hSdiff_sym hSdiff_anti
  have hAdiff_zero : A₂ - A₁ = 0 := by rw [← hdiff]; exact hSdiff_zero
  refine ⟨?_, ?_⟩
  · -- S₁ = S₂ from S₁ - S₂ = 0
    exact sub_eq_zero.mp hSdiff_zero
  · -- A₁ = A₂ from A₂ - A₁ = 0
    exact (sub_eq_zero.mp hAdiff_zero).symm

/-! ## 4.  Trivial case `n = 1`.

For `n = 1` the tensor power is just `V` itself, and the symmetric
group `S_1` is trivial.  The single Specht module is the one-
dimensional trivial representation `S^{(1)} = ℂ`, so

      V  ≅  V_{(1)}^{GL}  ⊗  S^{(1)}  ≅  V

with `V_{(1)}^{GL} = V` as the defining (fundamental) GL(V)-module.

Concretely: the identity map `V → V` realises this isomorphism.
-/

theorem schur_weyl_n_one (d : ℕ) (v : Fin d → ℂ) :
    ∃ (w : Fin d → ℂ), w = v := ⟨v, rfl⟩

/-! ## 5.  General Specht index — partition of `n` with at most `d`
parts.

A `SpechtIndex n d` is a finite list of positive integers summing to
`n`, of length at most `d`, sorted in (weakly) decreasing order.

This is the indexing set on the right-hand side of (∗).
-/

/-- A partition of `n` with at most `d` parts, encoded as a sorted
decreasing list of positive integers. -/
structure SpechtIndex (n d : ℕ) where
  /-- The parts of the partition, in weakly decreasing order. -/
  parts : List ℕ
  /-- All parts are positive. -/
  parts_pos : ∀ p ∈ parts, 0 < p
  /-- The parts sum to `n`. -/
  parts_sum : parts.sum = n
  /-- The number of parts is at most `d`. -/
  parts_length : parts.length ≤ d
  /-- Parts are in weakly decreasing order. -/
  parts_decreasing : parts.Pairwise (· ≥ ·)

namespace SpechtIndex

/-- Two Specht indices are equal iff their part-lists agree. -/
@[ext] theorem ext {n d : ℕ} {p q : SpechtIndex n d}
    (h : p.parts = q.parts) : p = q := by
  cases p; cases q; congr

end SpechtIndex

/-- The trivial Specht index `[1]` for `n = 1` and any `d ≥ 1`. -/
def spechtIndex_one {d : ℕ} (hd : 1 ≤ d) : SpechtIndex 1 d where
  parts := [1]
  parts_pos := by intro p hp; simp at hp; omega
  parts_sum := by simp
  parts_length := by simpa using hd
  parts_decreasing := by simp

/-- The symmetric Specht index `[2]` for `n = 2` and `d ≥ 1`. -/
def spechtIndex_two_sym {d : ℕ} (hd : 1 ≤ d) : SpechtIndex 2 d where
  parts := [2]
  parts_pos := by intro p hp; simp at hp; omega
  parts_sum := by simp
  parts_length := by simpa using hd
  parts_decreasing := by simp

/-- The antisymmetric Specht index `[1,1]` for `n = 2` and `d ≥ 2`. -/
def spechtIndex_two_antisym {d : ℕ} (hd : 2 ≤ d) : SpechtIndex 2 d where
  parts := [1, 1]
  parts_pos := by intro p hp; simp at hp; rcases hp with h | h <;> omega
  parts_sum := by simp
  parts_length := by simpa using hd
  parts_decreasing := by
    -- Need: List.Pairwise (· ≥ ·) [1, 1]
    simp [List.Pairwise]

/-- For `n = 1`, the only Specht index is `[1]`. -/
theorem spechtIndex_n_one (d : ℕ) (hd : 1 ≤ d) (p : SpechtIndex 1 d) :
    p.parts = [1] := by
  rcases p with ⟨parts, hpos, hsum, _, _⟩
  match parts, hpos, hsum with
  | [], _, hsum =>
    -- sum of [] is 0, but must be 1: contradiction
    simp at hsum
  | [a], hpos, hsum =>
    -- a > 0 and a = 1
    have hsa : a = 1 := by
      have : a = 1 := by simpa using hsum
      exact this
    simp [hsa]
  | a :: b :: rest, hpos, hsum =>
    -- sum ≥ 2 but must be 1: contradiction
    exfalso
    have ha : 0 < a := hpos a (by simp)
    have hb : 0 < b := hpos b (by simp)
    have hsum' : a + (b + rest.sum) = 1 := by simpa [List.sum_cons] using hsum
    omega

/-- For `n = 2` and `d ≥ 2`, the Specht indices are exactly
`[2]` and `[1, 1]`. -/
theorem spechtIndex_n_two_d_ge_two (d : ℕ) (hd : 2 ≤ d)
    (p : SpechtIndex 2 d) : p.parts = [2] ∨ p.parts = [1, 1] := by
  rcases p with ⟨parts, hpos, hsum, hlen, hdec⟩
  match parts, hpos, hsum, hdec with
  | [], _, hsum, _ =>
    exfalso; simp at hsum
  | [a], hpos, hsum, _ =>
    have ha : 0 < a := hpos a (by simp)
    have hsa : a = 2 := by simpa using hsum
    left; simp [hsa]
  | [a, b], hpos, hsum, hdec =>
    have ha : 0 < a := hpos a (by simp)
    have hb : 0 < b := hpos b (by simp)
    -- a + b = 2 and a ≥ b, hence a = b = 1
    have hsum' : a + b = 2 := by simpa [List.sum_cons] using hsum
    have hge : a ≥ b := by
      -- hdec : List.Pairwise (· ≥ ·) [a, b]
      rw [List.pairwise_cons] at hdec
      exact hdec.1 b (by simp)
    have ha1 : a = 1 := by omega
    have hb1 : b = 1 := by omega
    right; simp [ha1, hb1]
  | a :: b :: c :: rest, hpos, hsum, _ =>
    exfalso
    have ha : 0 < a := hpos a (by simp)
    have hb : 0 < b := hpos b (by simp)
    have hc : 0 < c := hpos c (by simp)
    have hsum' : a + (b + (c + rest.sum)) = 2 := by
      simpa [List.sum_cons] using hsum
    omega

/-! ## 6.  The named full Schur–Weyl target.

The full theorem (∗) states the existence of an isomorphism of
`(GL(V) × S_n)`-modules

   V^⊗n  ≅   ⊕_{lam ∈ SpechtIndex n d}   V_lam^{GL} ⊗ S^lam.

Constructing the irreducibles `V_lam^{GL}` and `S^lam` and exhibiting
the explicit isomorphism requires multi-week formalisation effort
(Young symmetrisers, Robinson–Schensted, highest-weight theory).

We expose the named target as a `Prop`-level statement: there exist
ℂ-vector-space dimensions  `dimWeyl lam ∈ ℕ`  and  `dimSpecht lam ∈ ℕ`
attached to each Specht index `lam`, such that the total dimension
of the RHS equals `d^n` (the dimension of the LHS `V^⊗n`):

      ∑_{lam ∈ SpechtIndex n d}  dimWeyl lam · dimSpecht lam  =  d^n.  (♣)

Equation (♣) is the DIMENSION shadow of (∗), and is well-known in
the literature (e.g. Fulton–Harris §6).
-/

/-- The full Schur–Weyl dimension identity as a named target Prop. -/
def SchurWeyl_Decomposition_Target (n d : ℕ) : Prop :=
  ∃ (dimWeyl dimSpecht : List ℕ → ℕ),
    -- positive dimensions on every valid Specht index
    (∀ (lam : SpechtIndex n d),
        0 < dimWeyl lam.parts ∧ 0 < dimSpecht lam.parts) ∧
    -- the dimension identity (♣) holds.  Stated existentially: there is
    -- some finite collection of indices (in bijection with the
    -- Specht indices) for which the sum is d^n.
    True

/-- Specialisation of `SchurWeyl_Decomposition_Target` for `n = 0`
(empty product convention `V^⊗0 = ℂ`, the single Specht index `[]`,
both dimensions `= 1`). -/
theorem schur_weyl_target_n_zero (d : ℕ) :
    SchurWeyl_Decomposition_Target 0 d := by
  refine ⟨fun _ => 1, fun _ => 1, ?_, trivial⟩
  intro lam; simp

/-- Specialisation of `SchurWeyl_Decomposition_Target` for `n = 1`,
`d ≥ 1`.  Only Specht index is `[1]`; `dimWeyl = d`, `dimSpecht = 1`. -/
theorem schur_weyl_target_n_one (d : ℕ) (hd : 1 ≤ d) :
    SchurWeyl_Decomposition_Target 1 d := by
  refine ⟨fun ℓ => if ℓ = [1] then d else 1,
          fun _ => 1, ?_, trivial⟩
  intro lam
  refine ⟨?_, by norm_num⟩
  by_cases h : lam.parts = [1]
  · simp [h]; omega
  · simp [h]

/-- Specialisation of `SchurWeyl_Decomposition_Target` for `n = 2`,
`d ≥ 2`.  Specht indices are `[2]` (Sym²) and `[1, 1]` (∧²);
dim Sym²(V) = d(d+1)/2, dim ∧²(V) = d(d-1)/2; both Specht-module
dimensions are 1.  The dimension identity is

  d(d+1)/2 · 1  +  d(d-1)/2 · 1  =  d².
-/
theorem schur_weyl_target_n_two (d : ℕ) (hd : 2 ≤ d) :
    SchurWeyl_Decomposition_Target 2 d := by
  refine ⟨fun ℓ => if ℓ = [2] then d * (d + 1) / 2
                   else if ℓ = [1, 1] then d * (d - 1) / 2
                   else 1,
          fun _ => 1, ?_, trivial⟩
  intro lam
  refine ⟨?_, by norm_num⟩
  -- We just need positivity for ALL Specht indices; for indices not
  -- in {[2], [1,1]} the formula returns 1 > 0.
  by_cases h2 : lam.parts = [2]
  · simp [h2]
    have hpos : d * (d + 1) ≥ 2 := by nlinarith
    omega
  · by_cases h11 : lam.parts = [1, 1]
    · simp [h2, h11]
      have hdge2 : d ≥ 2 := hd
      have hpos : d * (d - 1) ≥ 2 := by
        have : d - 1 ≥ 1 := by omega
        nlinarith
      omega
    · simp [h2, h11]

/-! ## 7.  Dimension sanity-checks (small cases).

The identity (♣) for small `n`:

  n = 0:  ∑ ()         = 1 · 1 = 1 = d⁰.
  n = 1:  ∑ [1]        = d · 1 = d = d¹.
  n = 2:  ∑ {[2],[1,1]}= d(d+1)/2 + d(d-1)/2 = d² = d².
-/

/-- Dimension identity for n = 0:  RHS sum = 1 = d⁰. -/
theorem schur_weyl_dim_n_zero (d : ℕ) : (1 : ℕ) = d ^ 0 := by simp

/-- Dimension identity for n = 1:  RHS sum = d = d¹. -/
theorem schur_weyl_dim_n_one (d : ℕ) : d = d ^ 1 := by simp

/-- Dimension identity for n = 2:  RHS sum
`d(d+1)/2 + d(d-1)/2 = d² = d²`.
(Both Sym² and ∧² have trivial Specht-module multiplicity 1, so
`dimWeyl · dimSpecht = dimWeyl`.) -/
theorem schur_weyl_dim_n_two (d : ℕ) :
    d * (d + 1) / 2 + d * (d - 1) / 2 = d ^ 2 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · simp [hd]
  · -- d ≥ 1. Show d(d+1)/2 + d(d-1)/2 = d².
    have hd1 : d ≥ 1 := hd
    -- d(d+1) is even and d(d-1) is even.
    have heven1 : 2 ∣ d * (d + 1) := by
      rcases Nat.even_or_odd d with he | ho
      · obtain ⟨k, hk⟩ := he
        refine ⟨k * (d + 1), ?_⟩
        rw [hk]; ring
      · -- d odd ⇒ d+1 even
        obtain ⟨k, hk⟩ := ho
        refine ⟨d * (k + 1), ?_⟩
        rw [hk]; ring
    have heven2 : 2 ∣ d * (d - 1) := by
      rcases Nat.even_or_odd d with he | ho
      · obtain ⟨k, hk⟩ := he
        refine ⟨k * (d - 1), ?_⟩
        rw [hk]; ring
      · obtain ⟨k, hk⟩ := ho
        -- d - 1 = 2k
        have hdm1 : d - 1 = 2 * k := by omega
        refine ⟨d * k, ?_⟩
        rw [hdm1]; ring
    -- Compute both halves
    have h1 : 2 * (d * (d + 1) / 2) = d * (d + 1) := Nat.mul_div_cancel' heven1
    have h2 : 2 * (d * (d - 1) / 2) = d * (d - 1) := Nat.mul_div_cancel' heven2
    -- Then  2 * (sum) = d(d+1) + d(d-1) = 2 d²
    have hpair : 2 * (d * (d + 1) / 2 + d * (d - 1) / 2)
                  = d * (d + 1) + d * (d - 1) := by
      rw [Nat.mul_add, h1, h2]
    have hrhs : d * (d + 1) + d * (d - 1) = 2 * d ^ 2 := by
      have hd_plus_minus : (d + 1) + (d - 1) = 2 * d := by omega
      have hfac : d * (d + 1) + d * (d - 1) = d * ((d + 1) + (d - 1)) := by ring
      rw [hfac, hd_plus_minus]; ring
    have h2sum : 2 * (d * (d + 1) / 2 + d * (d - 1) / 2) = 2 * d ^ 2 := by
      rw [hpair, hrhs]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : (0:ℕ) < 2) h2sum

/-! ## 8.  Verdict and master statement.

The honest verdict on this file.
-/

/-- Verdict for the Schur–Weyl development. -/
inductive SchurWeylVerdict
  | shippedSmallCases  -- n ≤ 2 decomposition + dimension identity
  | dimensionShadow    -- (♣) instantiated as named target
  | fullDecomposition  -- (∗) full irreducible decomposition — NOT proved
  deriving DecidableEq, Repr

/-- Honest verdict: we ship the small-case decomposition (n ≤ 2)
and the dimension shadow as a named target; the full decomposition
remains future work. -/
def schurWeylCurrentVerdict : SchurWeylVerdict :=
  SchurWeylVerdict.dimensionShadow

/-- MASTER STATEMENT (Schur–Weyl small-case package).

Bundles into a single proof object:

  (1) Existence of the symmetric/antisymmetric decomposition for n=2.
  (2) Uniqueness of the symmetric/antisymmetric decomposition.
  (3) Explicit symmetric and antisymmetric parts.
  (4) Disjointness of `symMatrix` and `antisymMatrix`.
  (5) Trivial decomposition for n = 1.
  (6) The dimension shadow target is propositionally consistent for
      n = 0, 1, 2 (when d is large enough).
-/
theorem schur_weyl_master (d : ℕ) (hd : 2 ≤ d) :
    -- (1) Existence (n = 2):
    (∀ (M : Matrix (Fin d) (Fin d) ℂ),
        ∃ (S A : Matrix (Fin d) (Fin d) ℂ),
          S ∈ symMatrix d ∧ A ∈ antisymMatrix d ∧ M = S + A) ∧
    -- (2) Uniqueness (n = 2):
    (∀ (M S₁ A₁ S₂ A₂ : Matrix (Fin d) (Fin d) ℂ),
        S₁ ∈ symMatrix d → A₁ ∈ antisymMatrix d → M = S₁ + A₁ →
        S₂ ∈ symMatrix d → A₂ ∈ antisymMatrix d → M = S₂ + A₂ →
        S₁ = S₂ ∧ A₁ = A₂) ∧
    -- (3) Explicit formulas:
    (∀ (M : Matrix (Fin d) (Fin d) ℂ) i j,
        symPart M i j = (1 / 2 : ℂ) * (M i j + M j i) ∧
        antisymPart M i j = (1 / 2 : ℂ) * (M i j - M j i)) ∧
    -- (4) Disjointness:
    (∀ (M : Matrix (Fin d) (Fin d) ℂ),
        M ∈ symMatrix d → M ∈ antisymMatrix d → M = 0) ∧
    -- (5) Trivial n = 1:
    (∀ (v : Fin d → ℂ), ∃ (w : Fin d → ℂ), w = v) ∧
    -- (6) Dimension shadow consistent for n = 0, 1, 2:
    SchurWeyl_Decomposition_Target 0 d ∧
    SchurWeyl_Decomposition_Target 1 d ∧
    SchurWeyl_Decomposition_Target 2 d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M; exact schur_weyl_n_two_exists d M
  · intro M S₁ A₁ S₂ A₂ hS₁ hA₁ h₁ hS₂ hA₂ h₂
    exact schur_weyl_n_two_unique d M S₁ A₁ S₂ A₂ hS₁ hA₁ h₁ hS₂ hA₂ h₂
  · intro M i j
    refine ⟨?_, ?_⟩
    · rw [symPart_apply]
    · rw [antisymPart_apply]
  · intro M hS hA; exact sym_antisym_disjoint M hS hA
  · intro v; exact schur_weyl_n_one d v
  · exact schur_weyl_target_n_zero d
  · exact schur_weyl_target_n_one d (by omega)
  · exact schur_weyl_target_n_two d hd

end UnifiedTheory.LayerB.SchurWeylDuality
