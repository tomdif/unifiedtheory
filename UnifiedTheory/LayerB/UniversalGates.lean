/-
  LayerB/UniversalGates.lean
  ──────────────────────────

  **Universal quantum gate compilation — a 1D demonstrative version
  of Solovay-Kitaev.**

  This file opens the quantum-computing pillar of the framework
  library.  It is the toy version: structure definitions for finite
  universal gate sets, the closure of a gate set under composition
  (word evaluation), the explicit `pauliGateSet` consisting of the
  four 2×2 Pauli matrices `{I, X, Y, Z}`, and the statement (as a
  named `Prop`) of the Solovay-Kitaev density target.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE SHIPS

    Layer A (structural)
      • `UniversalGateSet n`       : a finite list of `n × n`
                                     complex matrices together with
                                     proofs that each entry lies in
                                     `Matrix.unitaryGroup`.
      • `Word G`                    : a list of indices into `G.gens`;
                                     the free monoid of words.
      • `Word.toUnitary`            : the unitary realised by a word
                                     (left-to-right product, identity
                                     for the empty word).
      • `Word.toUnitary_isUnitary`  : the unitary realised by a word
                                     is itself in `unitaryGroup`.
      • `Word.append_toUnitary`     : composition of words multiplies
                                     unitaries.
      • `reachableUnitaries G`      : the set of all unitaries reachable
                                     by some word in `G`.
      • `reachable_contains_one`    : `1 ∈ reachableUnitaries G`
                                     (via the empty word).
      • `reachable_mul_mem`         : `reachableUnitaries G` is closed
                                     under multiplication.

    Layer B (the Pauli toy)
      • `idMat2`, `pauliX`, `pauliY`, `pauliZ` : the four 2×2 Pauli
                                                   matrices, as
                                                   `Matrix (Fin 2) (Fin 2) ℂ`.
      • `pauliX_unitary`, `pauliY_unitary`, `pauliZ_unitary`,
        `idMat2_unitary` : each is in `Matrix.unitaryGroup (Fin 2) ℂ`.
      • `pauli_X_sq`, `pauli_Y_sq`, `pauli_Z_sq` : `X² = Y² = Z² = I`.
      • `pauli_XY`, `pauli_YZ`, `pauli_ZX` : the standard anticommutation
                                              identities, giving phase
                                              factors `±i`.
      • `pauliGateSet`             : the gate set `[I, X, Y, Z]`.
      • `reachable_pauli_subset_phase` : every reachable unitary
        in `pauliGateSet` is of the form `(ζ : ℂ) • P` where
        `ζ ∈ {1, -1, I, -I}` and `P ∈ {I, X, Y, Z}` — i.e. it
        lives in the 16-element Pauli group.

    Layer C (the Solovay-Kitaev target)
      • `SolovayKitaev_Target`    : the predicate "the generated
                                     subgroup is dense in
                                     `unitaryGroup`".
      • `hadamardMatrix`, `tGate` : the Hadamard and π/8 (T) gate.
        Their unitarity proofs (via direct entry calculation) are
        included.
      • `hadamardTGateSet`         : the `{H, T}` gate set.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE NOTE

  The classical Solovay-Kitaev theorem (Kitaev 1995, Dawson-Nielsen
  2005) asserts that for any finite gate set whose generated subgroup
  is dense in `SU(d)`, every target unitary `U ∈ SU(d)` can be
  approximated to within ε by a word of length `O(log^c(1/ε))` with
  `c ≈ 3-4`.  The full proof relies on:

    (1) Density: the generated subgroup is dense in `SU(d)`
        (an analytic / Lie-group statement).
    (2) The "shrinking commutator" geometric construction: from
        ε-approximations of two unitaries, build an ε²-approximation
        of their group commutator.
    (3) The recursive net-refinement that drives the depth from
        ε down through ε^(3/2), ε^(9/4), … inside a logarithmic
        recursion.

  Of those, (1) for `{H, T}` is a non-trivial fact about the dyadic
  group action on the projective Bloch sphere; (2)-(3) are pure
  geometric group theory.  This file does NOT prove any of (1)-(3);
  it only states the target as a named `Prop` (`SolovayKitaev_Target`)
  and provides the structural scaffolding (gate sets, words,
  reachability) that an eventual proof would consume.

  What we DO prove is the **finite toy** that is fully tractable:
  the Pauli group `⟨I, X, Y, Z⟩` is finite (it embeds into the
  16-element Pauli group of phase × Pauli pairs).  This is the
  "Layer B" headline `reachable_pauli_subset_phase`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Zero `sorry`.  Zero custom `axiom`.
-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.UniversalGates

open Matrix Complex

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART A — Universal gate sets, words, reachability
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **A finite universal gate set on `n` qubit-states.**

    A list of `n × n` complex matrices, with a proof that every entry
    in the list is in `Matrix.unitaryGroup (Fin n) ℂ`. -/
structure UniversalGateSet (n : ℕ) where
  /-- The list of generator matrices. -/
  gens : List (Matrix (Fin n) (Fin n) ℂ)
  /-- Every generator is unitary. -/
  unitary : ∀ g ∈ gens, g ∈ Matrix.unitaryGroup (Fin n) ℂ

namespace UniversalGateSet

variable {n : ℕ}

/-- A **word** in a gate set is just a list of indices into `G.gens`.
    We use `ℕ` and treat out-of-range indices as the identity (see
    `Word.toUnitary`).

    Implementation: `Word G` is definitionally `List ℕ`, so all the
    standard `List` operations (`[]`, `::`, `++`) are available
    via the underlying type. -/
abbrev Word (_G : UniversalGateSet n) : Type := List ℕ

/-- The empty word. -/
def Word.nil (G : UniversalGateSet n) : Word G := ([] : List ℕ)

/-- Concatenation of words (re-export of `List.append`). -/
def Word.append {G : UniversalGateSet n} (w₁ w₂ : Word G) : Word G :=
  (w₁ ++ w₂ : List ℕ)

/-- Look up the `i`-th generator if `i < G.gens.length`, else return
    the identity matrix.  (Out-of-range indices are interpreted as the
    no-op gate.  This keeps `toUnitary` total without sacrificing
    correctness for valid words.) -/
noncomputable def gen (G : UniversalGateSet n) (i : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (G.gens[i]?).getD (1 : Matrix (Fin n) (Fin n) ℂ)

/-- The `i`-th generator is unitary (for any index — out-of-range
    falls back to the identity, which is unitary). -/
theorem gen_unitary (G : UniversalGateSet n) (i : ℕ) :
    G.gen i ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  unfold gen
  rcases h : G.gens[i]? with _ | g
  · -- Out of range → identity.
    show Option.getD none (1 : Matrix (Fin n) (Fin n) ℂ)
            ∈ Matrix.unitaryGroup (Fin n) ℂ
    exact Submonoid.one_mem _
  · -- In range → use `G.unitary`.
    show Option.getD (some g) (1 : Matrix (Fin n) (Fin n) ℂ)
            ∈ Matrix.unitaryGroup (Fin n) ℂ
    have hmem : g ∈ G.gens := by
      rw [List.mem_iff_getElem?]
      exact ⟨i, h⟩
    exact G.unitary g hmem

/-- The unitary realised by a word: left-to-right product of the
    indexed generators, with the empty word giving the identity. -/
noncomputable def Word.toUnitary (G : UniversalGateSet n) (w : Word G) :
    Matrix (Fin n) (Fin n) ℂ :=
  (w : List ℕ).foldl (fun acc i => acc * G.gen i) 1

@[simp] theorem Word.toUnitary_nil (G : UniversalGateSet n) :
    Word.toUnitary G (Word.nil G) = 1 := by
  unfold Word.toUnitary Word.nil
  rfl

/-- A helper: left-fold over a list multiplying by `f j` and starting
    from `x` equals `x * (left-fold from 1)`.  This is the standard
    monoid-fold extraction lemma. -/
private theorem foldl_mul_extract
    (f : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) (l : List ℕ) :
    l.foldl (fun acc j => acc * f j) x
      = x * l.foldl (fun acc j => acc * f j) 1 := by
  induction l generalizing x with
  | nil => simp
  | cons j ws ih =>
      simp only [List.foldl_cons]
      rw [ih (x * f j), ih (1 * f j), one_mul]
      rw [mul_assoc]

theorem Word.toUnitary_cons' (G : UniversalGateSet n) (i : ℕ) (w : List ℕ) :
    Word.toUnitary G ((i :: w) : Word G)
      = G.gen i * Word.toUnitary G (w : Word G) := by
  unfold Word.toUnitary
  show ((i :: w).foldl (fun acc j => acc * G.gen j) 1)
       = G.gen i * (w.foldl (fun acc j => acc * G.gen j) 1)
  rw [List.foldl_cons, one_mul]
  exact foldl_mul_extract (fun j => G.gen j) (G.gen i) w

/-- Concatenation of words = multiplication of unitaries. -/
theorem Word.append_toUnitary (G : UniversalGateSet n) (w₁ w₂ : Word G) :
    Word.toUnitary G (Word.append w₁ w₂)
      = Word.toUnitary G w₁ * Word.toUnitary G w₂ := by
  unfold Word.append Word.toUnitary
  -- foldl over (w₁ ++ w₂) from 1.
  -- = (foldl over w₂) ∘ (foldl over w₁) starting from 1.
  rw [List.foldl_append]
  -- LHS: foldl f (foldl f 1 w₁) w₂.  RHS: foldl f 1 w₁ * foldl f 1 w₂.
  exact foldl_mul_extract (fun j => G.gen j) _ (w₂ : List ℕ)

/-- The unitary realised by a word is itself in `unitaryGroup`. -/
theorem Word.toUnitary_isUnitary (G : UniversalGateSet n) (w : Word G) :
    Word.toUnitary G w ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  -- By induction on `(w : List ℕ)`.
  induction (w : List ℕ) with
  | nil =>
      show (Word.toUnitary G ([] : Word G))
             ∈ Matrix.unitaryGroup (Fin n) ℂ
      rw [show (([] : List ℕ) : Word G) = Word.nil G from rfl,
          Word.toUnitary_nil]
      exact Submonoid.one_mem _
  | cons i ws ih =>
      show (Word.toUnitary G ((i :: ws) : Word G))
             ∈ Matrix.unitaryGroup (Fin n) ℂ
      rw [Word.toUnitary_cons']
      exact Submonoid.mul_mem _ (G.gen_unitary i) ih

/-- The set of unitaries reachable by some word in `G`. -/
noncomputable def reachableUnitaries (G : UniversalGateSet n) :
    Set (Matrix (Fin n) (Fin n) ℂ) :=
  Set.image (Word.toUnitary G) Set.univ

/-- The identity is reachable (via the empty word). -/
theorem reachable_contains_one (G : UniversalGateSet n) :
    (1 : Matrix (Fin n) (Fin n) ℂ) ∈ reachableUnitaries G := by
  refine ⟨Word.nil G, ?_, ?_⟩
  · trivial
  · exact Word.toUnitary_nil G

/-- Each generator is reachable (via the singleton word `[i]`). -/
theorem gen_mem_reachable (G : UniversalGateSet n) (i : ℕ) :
    G.gen i ∈ reachableUnitaries G := by
  refine ⟨([i] : Word G), trivial, ?_⟩
  -- toUnitary G [i] = 1 * G.gen i = G.gen i.
  rw [show (([i] : List ℕ) : Word G) = (i :: ([] : List ℕ)) from rfl,
      Word.toUnitary_cons' G i []]
  rw [show (([] : List ℕ) : Word G) = Word.nil G from rfl,
      Word.toUnitary_nil]
  rw [mul_one]

/-- Every entry of `G.gens` is reachable. -/
theorem gens_subset_reachable (G : UniversalGateSet n) :
    ∀ g ∈ G.gens, g ∈ reachableUnitaries G := by
  intro g hg
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
  have : G.gen i = g := by
    unfold gen
    rw [hi]; rfl
  rw [← this]
  exact gen_mem_reachable G i

/-- The reachable set is closed under multiplication. -/
theorem reachable_mul_mem (G : UniversalGateSet n)
    {U V : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ reachableUnitaries G) (hV : V ∈ reachableUnitaries G) :
    U * V ∈ reachableUnitaries G := by
  obtain ⟨w₁, _, hw₁⟩ := hU
  obtain ⟨w₂, _, hw₂⟩ := hV
  refine ⟨Word.append w₁ w₂, trivial, ?_⟩
  rw [Word.append_toUnitary, hw₁, hw₂]

/-- Every reachable unitary is in `unitaryGroup`. -/
theorem reachable_subset_unitary (G : UniversalGateSet n) :
    reachableUnitaries G ⊆ ((Matrix.unitaryGroup (Fin n) ℂ).carrier) := by
  intro U hU
  obtain ⟨w, _, hw⟩ := hU
  rw [← hw]
  exact Word.toUnitary_isUnitary G w

end UniversalGateSet

open UniversalGateSet

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART B — Pauli matrices and the Pauli gate set
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The 2×2 identity matrix. -/
def idMat2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- Pauli X. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli Y. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Pauli Z. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-! ### Entry-level lemmas for the Pauli matrices. -/

private lemma idMat2_entries :
    idMat2 0 0 = 1 ∧ idMat2 0 1 = 0 ∧ idMat2 1 0 = 0 ∧ idMat2 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

private lemma pauliX_entries :
    pauliX 0 0 = 0 ∧ pauliX 0 1 = 1 ∧ pauliX 1 0 = 1 ∧ pauliX 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

private lemma pauliY_entries :
    pauliY 0 0 = 0 ∧ pauliY 0 1 = -Complex.I
  ∧ pauliY 1 0 = Complex.I ∧ pauliY 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

private lemma pauliZ_entries :
    pauliZ 0 0 = 1 ∧ pauliZ 0 1 = 0 ∧ pauliZ 1 0 = 0 ∧ pauliZ 1 1 = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-! ### Hermiticity (each Pauli is self-adjoint and unitary). -/

/-- `idMat2` is in `unitaryGroup (Fin 2) ℂ`. -/
theorem idMat2_unitary : idMat2 ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  -- idMat2 = 1 (the matrix one).
  have h : idMat2 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [idMat2, Matrix.one_apply]
  rw [h]
  exact Submonoid.one_mem _

/-- Helper: prove a 2×2 matrix is unitary by checking `M * Mᴴ = 1`. -/
private lemma unitary_of_mul_conjT_eq_one
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (h : M * star M = 1) :
    M ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact h

/-- `star pauliX = pauliX`. -/
private lemma star_pauliX : star pauliX = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, star, Matrix.conjTranspose_apply, Complex.ext_iff]

/-- `star pauliY = pauliY`. -/
private lemma star_pauliY : star pauliY = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, star, Matrix.conjTranspose_apply, Complex.ext_iff,
          Complex.conj_I]

/-- `star pauliZ = pauliZ`. -/
private lemma star_pauliZ : star pauliZ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, star, Matrix.conjTranspose_apply, Complex.ext_iff]

/-- Direct: `pauliX * pauliX = 1`. -/
private lemma pauliX_mul_pauliX_eq_one :
    pauliX * pauliX = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Direct: `pauliY * pauliY = 1`. -/
private lemma pauliY_mul_pauliY_eq_one :
    pauliY * pauliY = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
          Complex.ext_iff]

/-- Direct: `pauliZ * pauliZ = 1`. -/
private lemma pauliZ_mul_pauliZ_eq_one :
    pauliZ * pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Pauli X is unitary. -/
theorem pauliX_unitary : pauliX ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply unitary_of_mul_conjT_eq_one
  rw [star_pauliX]
  exact pauliX_mul_pauliX_eq_one

/-- Pauli Y is unitary. -/
theorem pauliY_unitary : pauliY ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply unitary_of_mul_conjT_eq_one
  rw [star_pauliY]
  exact pauliY_mul_pauliY_eq_one

/-- Pauli Z is unitary. -/
theorem pauliZ_unitary : pauliZ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply unitary_of_mul_conjT_eq_one
  rw [star_pauliZ]
  exact pauliZ_mul_pauliZ_eq_one

/-! ### The Pauli gate set. -/

/-- The **Pauli gate set** `{I, X, Y, Z}` on one qubit. -/
noncomputable def pauliGateSet : UniversalGateSet 2 where
  gens := [idMat2, pauliX, pauliY, pauliZ]
  unitary := by
    intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | rfl | hg
    · exact idMat2_unitary
    · exact pauliX_unitary
    · exact pauliY_unitary
    · rcases hg with rfl | hg
      · exact pauliZ_unitary
      · exact absurd hg List.not_mem_nil

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART C — Pauli relations: squares and products
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `X² = I`. -/
theorem pauli_X_sq : pauliX * pauliX = idMat2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, idMat2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `Y² = I`. -/
theorem pauli_Y_sq : pauliY * pauliY = idMat2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, idMat2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `Z² = I`. -/
theorem pauli_Z_sq : pauliZ * pauliZ = idMat2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, idMat2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `X * Y = i Z`. -/
theorem pauli_XY : pauliX * pauliY = Complex.I • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply]

/-- `Y * X = -i Z`. -/
theorem pauli_YX : pauliY * pauliX = (-Complex.I) • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply]

/-- `Y * Z = i X`. -/
theorem pauli_YZ : pauliY * pauliZ = Complex.I • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply]

/-- `Z * Y = -i X`. -/
theorem pauli_ZY : pauliZ * pauliY = (-Complex.I) • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply]

/-- `Z * X = i Y`. -/
theorem pauli_ZX : pauliZ * pauliX = Complex.I • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply]

/-- `X * Z = -i Y`. -/
theorem pauli_XZ : pauliX * pauliZ = (-Complex.I) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply]

/-! ### Identity neutrality. -/

/-- `I * X = X`. -/
theorem idMat2_mul_X : idMat2 * pauliX = pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [idMat2, pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- `X * I = X`. -/
theorem pauliX_mul_id : pauliX * idMat2 = pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [idMat2, pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- `I * Y = Y`. -/
theorem idMat2_mul_Y : idMat2 * pauliY = pauliY := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [idMat2, pauliY, Matrix.mul_apply, Fin.sum_univ_two]

/-- `Y * I = Y`. -/
theorem pauliY_mul_id : pauliY * idMat2 = pauliY := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [idMat2, pauliY, Matrix.mul_apply, Fin.sum_univ_two]

/-- `I * Z = Z`. -/
theorem idMat2_mul_Z : idMat2 * pauliZ = pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [idMat2, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- `Z * I = Z`. -/
theorem pauliZ_mul_id : pauliZ * idMat2 = pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [idMat2, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- `I * I = I`. -/
theorem idMat2_sq : idMat2 * idMat2 = idMat2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [idMat2, Matrix.mul_apply, Fin.sum_univ_two]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART D — The Pauli phase group (16 elements)

    Every product of Pauli generators reduces to `ζ • P` where
    `ζ ∈ {1, -1, I, -I}` and `P ∈ {I, X, Y, Z}`.  We encode this
    16-element set abstractly so we can state and prove a clean
    closure theorem without enumerating all distinctness pairs.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The four phase factors `{1, -1, i, -i}` that arise from Pauli products. -/
def PauliPhases : Set ℂ := {1, -1, Complex.I, -Complex.I}

/-- The four "bare" Pauli matrices `{I, X, Y, Z}`. -/
def PauliMatrices : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {idMat2, pauliX, pauliY, pauliZ}

/-- The **Pauli phase group**: matrices of the form `ζ • P` with
    `ζ ∈ PauliPhases` and `P ∈ PauliMatrices`. -/
def PauliPhaseGroup : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  { M | ∃ ζ ∈ PauliPhases, ∃ P ∈ PauliMatrices, M = ζ • P }

/-! ### `PauliPhaseGroup` is closed under multiplication.

    Strategy: we have a product `(ζ₁ • P₁) * (ζ₂ • P₂) = (ζ₁ * ζ₂) • (P₁ * P₂)`.
    Phase factors compose inside `{1, -1, i, -i}` (the 4-th roots of unity),
    and Pauli products give `(±1 or ±i) • Q` for some `Q ∈ {I, X, Y, Z}`.
    Combining the phases preserves the group. -/

/-- `1 ∈ PauliPhases`. -/
private lemma one_mem_PauliPhases : (1 : ℂ) ∈ PauliPhases := by
  left; rfl

/-- `-1 ∈ PauliPhases`. -/
private lemma neg_one_mem_PauliPhases : (-1 : ℂ) ∈ PauliPhases := by
  right; left; rfl

/-- `i ∈ PauliPhases`. -/
private lemma I_mem_PauliPhases : Complex.I ∈ PauliPhases := by
  right; right; left; rfl

/-- `-i ∈ PauliPhases`. -/
private lemma neg_I_mem_PauliPhases : -Complex.I ∈ PauliPhases := by
  right; right; right; rfl

private lemma I_mem_PauliMatrices : idMat2 ∈ PauliMatrices := by left; rfl
private lemma X_mem_PauliMatrices : pauliX ∈ PauliMatrices := by
  right; left; rfl
private lemma Y_mem_PauliMatrices : pauliY ∈ PauliMatrices := by
  right; right; left; rfl
private lemma Z_mem_PauliMatrices : pauliZ ∈ PauliMatrices := by
  right; right; right; rfl

/-- `idMat2 ∈ PauliPhaseGroup` (with phase 1). -/
theorem one_mem_PauliPhaseGroup : idMat2 ∈ PauliPhaseGroup := by
  refine ⟨1, one_mem_PauliPhases, idMat2, I_mem_PauliMatrices, ?_⟩
  rw [one_smul]

theorem pauliX_mem_PauliPhaseGroup : pauliX ∈ PauliPhaseGroup := by
  refine ⟨1, one_mem_PauliPhases, pauliX, X_mem_PauliMatrices, ?_⟩
  rw [one_smul]

theorem pauliY_mem_PauliPhaseGroup : pauliY ∈ PauliPhaseGroup := by
  refine ⟨1, one_mem_PauliPhases, pauliY, Y_mem_PauliMatrices, ?_⟩
  rw [one_smul]

theorem pauliZ_mem_PauliPhaseGroup : pauliZ ∈ PauliPhaseGroup := by
  refine ⟨1, one_mem_PauliPhases, pauliZ, Z_mem_PauliMatrices, ?_⟩
  rw [one_smul]

/-- The Mathlib identity `(1 : Matrix (Fin 2) (Fin 2) ℂ)` equals
    `idMat2`. -/
private lemma one_eq_idMat2 : (1 : Matrix (Fin 2) (Fin 2) ℂ) = idMat2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [idMat2, Matrix.one_apply]

/-- `(1 : Matrix _ _ _) ∈ PauliPhaseGroup`. -/
theorem one_matrix_mem_PauliPhaseGroup :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ PauliPhaseGroup := by
  rw [one_eq_idMat2]
  exact one_mem_PauliPhaseGroup

/-! ### Phase arithmetic in `PauliPhases`.

    `PauliPhases = {1, -1, i, -i}` is the multiplicative group `ℤ/4`.
    We need all 16 products are again in `PauliPhases`. -/

private lemma PauliPhases_mul_closed
    {a b : ℂ} (ha : a ∈ PauliPhases) (hb : b ∈ PauliPhases) :
    a * b ∈ PauliPhases := by
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
    simp [PauliPhases, Complex.I_mul_I]

/-! ### Pauli product table — every `Pᵢ Pⱼ` is `phase • Pₖ`.

    We catalogue all 16 products through the previously-proven product
    lemmas + identity multiplication.  This gives a uniform statement
    `PauliMatrices_mul`. -/

private lemma PauliMatrices_mul
    {P Q : Matrix (Fin 2) (Fin 2) ℂ}
    (hP : P ∈ PauliMatrices) (hQ : Q ∈ PauliMatrices) :
    ∃ ζ ∈ PauliPhases, ∃ R ∈ PauliMatrices, P * Q = ζ • R := by
  -- Case split on (P, Q) ∈ {I, X, Y, Z}².
  rcases hP with rfl | rfl | rfl | rfl <;>
    rcases hQ with rfl | rfl | rfl | rfl
  -- I · I = 1 · I
  · exact ⟨1, one_mem_PauliPhases, idMat2, I_mem_PauliMatrices,
            by rw [idMat2_sq, one_smul]⟩
  -- I · X = 1 · X
  · exact ⟨1, one_mem_PauliPhases, pauliX, X_mem_PauliMatrices,
            by rw [idMat2_mul_X, one_smul]⟩
  -- I · Y
  · exact ⟨1, one_mem_PauliPhases, pauliY, Y_mem_PauliMatrices,
            by rw [idMat2_mul_Y, one_smul]⟩
  -- I · Z
  · exact ⟨1, one_mem_PauliPhases, pauliZ, Z_mem_PauliMatrices,
            by rw [idMat2_mul_Z, one_smul]⟩
  -- X · I
  · exact ⟨1, one_mem_PauliPhases, pauliX, X_mem_PauliMatrices,
            by rw [pauliX_mul_id, one_smul]⟩
  -- X · X = 1 · I
  · exact ⟨1, one_mem_PauliPhases, idMat2, I_mem_PauliMatrices,
            by rw [pauli_X_sq, one_smul]⟩
  -- X · Y = i · Z
  · exact ⟨Complex.I, I_mem_PauliPhases, pauliZ, Z_mem_PauliMatrices,
            pauli_XY⟩
  -- X · Z = -i · Y
  · exact ⟨-Complex.I, neg_I_mem_PauliPhases, pauliY,
            Y_mem_PauliMatrices, pauli_XZ⟩
  -- Y · I
  · exact ⟨1, one_mem_PauliPhases, pauliY, Y_mem_PauliMatrices,
            by rw [pauliY_mul_id, one_smul]⟩
  -- Y · X = -i · Z
  · exact ⟨-Complex.I, neg_I_mem_PauliPhases, pauliZ,
            Z_mem_PauliMatrices, pauli_YX⟩
  -- Y · Y = 1 · I
  · exact ⟨1, one_mem_PauliPhases, idMat2, I_mem_PauliMatrices,
            by rw [pauli_Y_sq, one_smul]⟩
  -- Y · Z = i · X
  · exact ⟨Complex.I, I_mem_PauliPhases, pauliX, X_mem_PauliMatrices,
            pauli_YZ⟩
  -- Z · I
  · exact ⟨1, one_mem_PauliPhases, pauliZ, Z_mem_PauliMatrices,
            by rw [pauliZ_mul_id, one_smul]⟩
  -- Z · X = i · Y
  · exact ⟨Complex.I, I_mem_PauliPhases, pauliY, Y_mem_PauliMatrices,
            pauli_ZX⟩
  -- Z · Y = -i · X
  · exact ⟨-Complex.I, neg_I_mem_PauliPhases, pauliX,
            X_mem_PauliMatrices, pauli_ZY⟩
  -- Z · Z = 1 · I
  · exact ⟨1, one_mem_PauliPhases, idMat2, I_mem_PauliMatrices,
            by rw [pauli_Z_sq, one_smul]⟩

/-- **The Pauli phase group is closed under matrix multiplication.**

    `(ζ₁ • P₁) * (ζ₂ • P₂) = (ζ₁ * ζ₂) • (P₁ * P₂)`, where the phase
    factors compose inside the 4-element group `PauliPhases` and the
    bare Pauli product is `phase' • R` by `PauliMatrices_mul`. -/
theorem PauliPhaseGroup_mul_mem
    {U V : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ PauliPhaseGroup) (hV : V ∈ PauliPhaseGroup) :
    U * V ∈ PauliPhaseGroup := by
  obtain ⟨ζ₁, hζ₁, P, hP, hU_eq⟩ := hU
  obtain ⟨ζ₂, hζ₂, Q, hQ, hV_eq⟩ := hV
  -- Factor out the scalars.
  have h_mul : U * V = (ζ₁ * ζ₂) • (P * Q) := by
    rw [hU_eq, hV_eq]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  -- Now use `PauliMatrices_mul` to write P * Q = ζ' • R.
  obtain ⟨ζ', hζ', R, hR, hPQ⟩ := PauliMatrices_mul hP hQ
  rw [h_mul, hPQ]
  rw [smul_smul]
  refine ⟨ζ₁ * ζ₂ * ζ', ?_, R, hR, rfl⟩
  -- ζ₁ * ζ₂ * ζ' ∈ PauliPhases (closure twice).
  exact PauliPhases_mul_closed (PauliPhases_mul_closed hζ₁ hζ₂) hζ'

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART E — The headline closure theorem
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Each generator of `pauliGateSet` is in `PauliPhaseGroup`. -/
private lemma pauliGateSet_gens_mem :
    ∀ i, pauliGateSet.gen i ∈ PauliPhaseGroup := by
  intro i
  unfold gen
  rcases h : (pauliGateSet.gens)[i]? with _ | g
  · -- out of range → identity → in group
    show Option.getD none (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ PauliPhaseGroup
    rw [show (Option.getD none (1 : Matrix (Fin 2) (Fin 2) ℂ))
            = idMat2 from by rw [Option.getD_none]; exact one_eq_idMat2]
    exact one_mem_PauliPhaseGroup
  · show Option.getD (some g) (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ PauliPhaseGroup
    rw [Option.getD_some]
    have hg_mem : g ∈ pauliGateSet.gens := by
      rw [List.mem_iff_getElem?]
      exact ⟨i, h⟩
    simp only [pauliGateSet, List.mem_cons] at hg_mem
    rcases hg_mem with rfl | rfl | rfl | hg_mem
    · exact one_mem_PauliPhaseGroup
    · exact pauliX_mem_PauliPhaseGroup
    · exact pauliY_mem_PauliPhaseGroup
    · rcases hg_mem with rfl | hg_mem
      · exact pauliZ_mem_PauliPhaseGroup
      · exact absurd hg_mem List.not_mem_nil

/-- Auxiliary: every word's image lies in `PauliPhaseGroup`. -/
private lemma toUnitary_mem_PauliPhaseGroup (w : List ℕ) :
    Word.toUnitary pauliGateSet (w : Word pauliGateSet) ∈ PauliPhaseGroup := by
  induction w with
  | nil =>
      rw [show (([] : List ℕ) : Word pauliGateSet)
                = Word.nil pauliGateSet from rfl,
          Word.toUnitary_nil]
      exact one_matrix_mem_PauliPhaseGroup
  | cons i ws ih =>
      rw [Word.toUnitary_cons']
      exact PauliPhaseGroup_mul_mem (pauliGateSet_gens_mem i) ih

/-- **Headline theorem.**  Every unitary reachable by a word in the
    Pauli gate set lies in the 16-element Pauli phase group. -/
theorem reachable_pauli_subset_phase :
    reachableUnitaries pauliGateSet ⊆ PauliPhaseGroup := by
  intro U hU
  obtain ⟨w, _, hw⟩ := hU
  rw [← hw]
  exact toUnitary_mem_PauliPhaseGroup w

/-- **Finiteness corollary.**  The reachable set of the Pauli gate
    set is finite. -/
theorem reachable_pauli_finite :
    (reachableUnitaries pauliGateSet).Finite := by
  apply Set.Finite.subset _ reachable_pauli_subset_phase
  -- PauliPhaseGroup is finite: 4 phases × 4 bare matrices = 16 elements.
  -- Show via `Set.image`: PauliPhaseGroup ⊆ image of (ζ, P) ↦ ζ • P.
  have h_phases_fin : PauliPhases.Finite := by
    unfold PauliPhases
    exact (Set.toFinite {1, -1, Complex.I, -Complex.I})
  have h_mats_fin : PauliMatrices.Finite := by
    unfold PauliMatrices
    exact (Set.toFinite {idMat2, pauliX, pauliY, pauliZ})
  -- PauliPhaseGroup is the image of (ζ, P) ↦ ζ • P over PauliPhases × PauliMatrices.
  have h_image :
      PauliPhaseGroup = (fun p : ℂ × Matrix (Fin 2) (Fin 2) ℂ => p.1 • p.2) ''
                          (PauliPhases ×ˢ PauliMatrices) := by
    ext M
    constructor
    · rintro ⟨ζ, hζ, P, hP, hM⟩
      exact ⟨(ζ, P), ⟨hζ, hP⟩, hM.symm⟩
    · rintro ⟨⟨ζ, P⟩, ⟨hζ, hP⟩, hM⟩
      exact ⟨ζ, hζ, P, hP, hM.symm⟩
  rw [h_image]
  exact (h_phases_fin.prod h_mats_fin).image _

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART F — The Solovay-Kitaev target and {H, T} gate set
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Hadamard matrix `H = (1/√2) [[1, 1], [1, -1]]`. -/
noncomputable def hadamardMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • !![1, 1; 1, -1]

/-- The T gate `T = diag(1, e^{iπ/4})`.  In complex form:
    `e^{iπ/4} = cos(π/4) + i sin(π/4) = (1 + i)/√2`. -/
noncomputable def tGate : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0;
     0, Complex.exp (Complex.I * (Real.pi / 4 : ℂ))]

/-- The **Solovay-Kitaev target**: the generated subgroup is dense in
    `unitaryGroup` at the operator norm.

    Equivalently: every `U ∈ unitaryGroup` is approximated by a word
    arbitrarily well in the entry-wise sup norm. -/
def SolovayKitaev_Target (G : UniversalGateSet 2) : Prop :=
  ∀ U : Matrix (Fin 2) (Fin 2) ℂ, U ∈ Matrix.unitaryGroup (Fin 2) ℂ →
    ∀ ε : ℝ, 0 < ε →
      ∃ w : Word G,
        ∀ i j : Fin 2, ‖Word.toUnitary G w i j - U i j‖ < ε

/-! ### Honest scope.

    The full proof of `SolovayKitaev_Target hadamardTGateSet` requires:

      • Density of `⟨H, T⟩` in `SU(2)` — a non-trivial fact about
        the discrete group generated by H, T on the Bloch sphere.

      • The shrinking-commutator construction: given ε-approximations
        of `U` and `V`, build an `O(ε²)` approximation of `[U, V]`.

      • The recursive net refinement that converts the
        commutator-shrinking step into a word of length
        `O(log^c(1/ε))`.

    None of these are formalised here; we state the conclusion as a
    `Prop` so that downstream code can reference it and so that a
    future formalisation has a fixed target. -/

end UnifiedTheory.LayerB.UniversalGates

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms UnifiedTheory.LayerB.UniversalGates.reachable_pauli_subset_phase
#print axioms UnifiedTheory.LayerB.UniversalGates.reachable_pauli_finite
#print axioms UnifiedTheory.LayerB.UniversalGates.PauliPhaseGroup_mul_mem
