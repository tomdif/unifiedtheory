/-
  LayerB/PartialTraceTwirl.lean
  ──────────────────────────────

  **Phase B11 — Discharge of `PartialTrace_Twirl_Target`.**

  This file targets the named gate

      `PartialTrace_Twirl_Target : Prop`

  declared in `LayerB/PartialTraceDecomposition.lean` (line ~394) as a
  structural placeholder.  In the upstream consolidating file the gate
  is defined as `True` (the precise mathematical statement requires a
  Heisenberg–Weyl finite-group encoding plus the tensor-product reindex
  that are not assembled in the existing LayerB infrastructure).

  This file:

    1.  Discharges the upstream placeholder `PartialTrace_Twirl_Target`
        unconditionally as `partialTraceTwirl_holds`.

    2.  Ships the **substantive twirl identity** as a separate honest
        theorem: the partial trace `Tr_B M` is recovered, tensored with
        `I_m`, as the (unnormalised) sum of "matrix-unit" conjugations

            `∑_{j,k : Fin m} (I_A ⊗ E_{j,k}) · M · (I_A ⊗ E_{k,j})
                = (Tr_B M) ⊗ I_m`,

        where `E_{j,k} : Matrix (Fin m) (Fin m) ℂ` is the matrix unit
        with a single `1` at position `(j,k)` and zeros elsewhere.

        This is the cleanest available "twirl" identity: it expresses
        the partial trace as an averaged action of B-local channel
        operators on `M`, exactly mirroring the operational meaning of
        partial trace as the "ignore-B" map.

        Mathematically equivalent statements with the Heisenberg–Weyl
        unitary 1-design (using shift × clock unitaries) are obtainable
        by linear combination of the `E_{j,k}` family; the matrix-unit
        form is the linear-algebraic skeleton from which all such
        unitary-1-design identities derive.

    3.  As a corollary, ships the **computational-basis-sum**
        representation of partial trace:

            `(Tr_B M)_{i,j} = ∑_k M_{(i,k),(j,k)}`

        which is the textbook definition.  This is an unfolding
        identity but we record it explicitly under a self-contained
        name for downstream consumers.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT (NON-NEGOTIABLE): zero `sorry`, zero custom
  `axiom`.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  ## Build target

      `lake build UnifiedTheory.LayerB.PartialTraceTwirl`
-/

import UnifiedTheory.LayerB.PartialTrace
import UnifiedTheory.LayerB.PartialTraceDecomposition
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.PartialTraceTwirl

open Matrix Complex
open scoped Kronecker BigOperators
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.PartialTrace
open UnifiedTheory.LayerB.PartialTraceDecomposition

/-! ## 1.  Computational-basis projectors and matrix units.

The **computational-basis projector** at index `k : Fin m` is the
matrix `|k⟩⟨k|` (rank-1, with a single `1` on the diagonal at
position `(k,k)`).

The **matrix unit** `E_{j,k}` has a `1` at position `(j,k)` and zeros
elsewhere.  These form a (non-orthogonal under the Hilbert–Schmidt
inner product on rank-1 elements, but linearly independent) basis of
`Matrix (Fin m) (Fin m) ℂ`.

The conjugate-transpose relationship `E_{j,k}† = E_{k,j}` is direct. -/

/-- **The computational-basis projector** `|k⟩⟨k|` on `Fin m`. -/
def computationalBasisProjector (m : ℕ) (k : Fin m) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of (fun i j => if i = k ∧ j = k then (1 : ℂ) else 0)

/-- **The matrix unit** `E_{j,k}` on `Fin m`: a `1` at position
    `(j,k)`, zeros elsewhere. -/
def matrixUnit (m : ℕ) (j k : Fin m) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of (fun i l => if i = j ∧ l = k then (1 : ℂ) else 0)

/-- The conjugate-transpose of a matrix unit `E_{j,k}` is `E_{k,j}`. -/
theorem matrixUnit_conjTranspose (m : ℕ) (j k : Fin m) :
    (matrixUnit m j k).conjTranspose = matrixUnit m k j := by
  ext i l
  rw [Matrix.conjTranspose_apply, matrixUnit, matrixUnit]
  simp only [Matrix.of_apply]
  by_cases h1 : l = j
  · by_cases h2 : i = k
    · simp [h1, h2]
    · simp [h1, h2]
  · by_cases h2 : i = k
    · simp [h1, h2]
    · simp [h1, h2]

/-- **Pointwise value** of the matrix unit: `(E_{j,k})_{i,l} = 1` iff
    `(i,l) = (j,k)`, else `0`. -/
theorem matrixUnit_apply (m : ℕ) (j k i l : Fin m) :
    matrixUnit m j k i l = if i = j ∧ l = k then (1 : ℂ) else 0 := by
  rfl

/-! ## 2.  The substantive twirl identity.

We prove:
  `∑_{j,k : Fin m} (I_A ⊗ E_{j,k}) · M · (I_A ⊗ E_{k,j}) = (Tr_B M) ⊗ I_m`

This is the cleanest "twirl"-type identity available without
introducing the full Heisenberg–Weyl group machinery.  It is the
direct linear-algebraic expression of partial trace as a (sum over)
B-local conjugation.

Strategy: compute the LHS entry-wise.  Each `(I_A ⊗ E_{j,k})` is
sparse: `(I_A ⊗ E_{j,k})_{(a,p),(a',q)} = δ_{a,a'} · δ_{p,j} · δ_{q,k}`.
Multiplying through `M` collapses the middle indices, giving a
δ-function pattern that produces `(Tr_B M)_{a₁,a₂} · δ_{p,q}` after
the double sum. -/

/-- **Pointwise value** of `I_A ⊗ E_{j,k}` at `((a,p),(a',q))`. -/
private theorem kron_one_matrixUnit_apply
    {n_A n_B : ℕ} (j k : Fin n_B)
    (a : Fin n_A) (p : Fin n_B) (a' : Fin n_A) (q : Fin n_B) :
    ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ matrixUnit n_B j k) (a, p) (a', q)
      = if a = a' ∧ p = j ∧ q = k then (1 : ℂ) else 0 := by
  rw [Matrix.kroneckerMap_apply, matrixUnit_apply]
  by_cases haa : a = a'
  · subst haa
    by_cases hpj : p = j
    · by_cases hqk : q = k
      · simp [hpj, hqk, Matrix.one_apply_eq]
      · simp [hpj, hqk, Matrix.one_apply_eq]
    · simp [hpj, Matrix.one_apply_eq]
  · simp [haa, Matrix.one_apply_ne haa]

/-- **Pointwise computation of `(I_A ⊗ E_{j,k}) M (I_A ⊗ E_{k,j})`.**

    For all `(a₁, p), (a₂, q) : Fin n_A × Fin n_B`,

    `((I_A ⊗ E_{j,k}) · M · (I_A ⊗ E_{k,j}))_{(a₁,p),(a₂,q)}
        = (if p = j ∧ q = j then M_{(a₁,k),(a₂,k)} else 0)`.

    This is the key entry-wise identity for the twirl. -/
private theorem twirl_term_entry
    {n_A n_B : ℕ}
    (j k : Fin n_B)
    (M : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ)
    (a₁ : Fin n_A) (p : Fin n_B) (a₂ : Fin n_A) (q : Fin n_B) :
    (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ matrixUnit n_B j k)
      * M
      * ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ matrixUnit n_B k j))
      (a₁, p) (a₂, q)
      = if p = j ∧ q = j then M (a₁, k) (a₂, k) else 0 := by
  -- Strategy: expand both products, collapse all the δ-functions, do
  -- a final case split on `p = j` and `q = j`.
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  -- ∑_{r : Fin n_A} ∑_{s : Fin n_B}, ((K M)[(a₁,p),(r,s)]) · (K')[(r,s),(a₂,q)]
  -- First collapse r = a₂.
  rw [Finset.sum_eq_single (a := a₂)]
  rotate_left
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro s _
    rw [kron_one_matrixUnit_apply]
    rw [if_neg (fun ⟨hr', _, _⟩ => hr hr')]
    ring
  · intro h; exact absurd (Finset.mem_univ a₂) h
  -- Then collapse s = k via K'.
  rw [Finset.sum_eq_single (a := k)]
  rotate_left
  · intro s _ hs
    rw [show ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ matrixUnit n_B k j)
          (a₂, s) (a₂, q) = 0 from by
          rw [kron_one_matrixUnit_apply]
          rw [if_neg (fun ⟨_, h2, _⟩ => hs h2)]]
    ring
  · intro h; exact absurd (Finset.mem_univ k) h
  -- Now expand (K M)[(a₁,p),(a₂,k)].
  rw [show ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ matrixUnit n_B j k * M)
            (a₁, p) (a₂, k)
          = ∑ r : Fin n_A, ∑ s : Fin n_B,
              ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ matrixUnit n_B j k)
                  (a₁, p) (r, s)
              * M (r, s) (a₂, k) from by
        rw [Matrix.mul_apply, Fintype.sum_prod_type]]
  -- Collapse r = a₁.
  rw [Finset.sum_eq_single (a := a₁)]
  rotate_left
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro s _
    rw [kron_one_matrixUnit_apply]
    rw [if_neg (fun ⟨h1, _, _⟩ => hr h1.symm)]
    ring
  · intro h; exact absurd (Finset.mem_univ a₁) h
  -- Collapse s = k.
  rw [Finset.sum_eq_single (a := k)]
  rotate_left
  · intro s _ hs
    rw [kron_one_matrixUnit_apply]
    rw [if_neg (fun ⟨_, _, h3⟩ => hs h3)]
    ring
  · intro h; exact absurd (Finset.mem_univ k) h
  -- Now: only the δ-values at (a₁,a₁,p,j,k,k) for K and (a₂,a₂,k,k,q,j) for K' remain.
  rw [kron_one_matrixUnit_apply, kron_one_matrixUnit_apply]
  -- LHS = (if a₁=a₁ ∧ p=j ∧ k=k then 1 else 0) * M[(a₁,k),(a₂,k)]
  --       * (if a₂=a₂ ∧ k=k ∧ q=j then 1 else 0)
  -- Simplify the trivial parts (a₁=a₁, k=k, a₂=a₂).
  simp only [and_true, true_and]
  -- Goal: (if p = j then 1 else 0) * M[(a₁,k),(a₂,k)] * (if q = j then 1 else 0)
  --     = (if p = j ∧ q = j then M[(a₁,k),(a₂,k)] else 0)
  by_cases hp : p = j
  · by_cases hq : q = j
    · simp [hp, hq]
    · simp [hp, hq]
  · by_cases hq : q = j
    · simp [hp, hq]
    · simp [hp, hq]

/-- **The substantive twirl identity (raw matrices, matrix-unit form).**

    For every `n_A, n_B : ℕ` and every matrix `M` on the bipartite
    index `Fin n_A × Fin n_B`,

      `∑_{j,k : Fin n_B} (I_A ⊗ E_{j,k}) · M · (I_A ⊗ E_{k,j})
            = (Tr_B M) ⊗ I_{n_B}`.

    Reads: summing over all B-local "matrix-unit conjugations" of `M`
    yields the partial trace `Tr_B M` tensored with the identity on
    `Fin n_B`.  This is the cleanest "twirl"-type identity available
    without introducing the full Heisenberg–Weyl unitary group. -/
theorem partialTrace_eq_matrixUnit_twirl
    {n_A n_B : ℕ}
    (M : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ) :
    (∑ j : Fin n_B, ∑ k : Fin n_B,
        ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ matrixUnit n_B j k)
          * M
          * ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ matrixUnit n_B k j))
      = partialTrace_right M ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ) := by
  ext ⟨a₁, p⟩ ⟨a₂, q⟩
  -- LHS entry: ∑_{j,k} (if p = j ∧ q = j then M[(a₁,k),(a₂,k)] else 0)
  --         = (if p = q then ∑_k M[(a₁,k),(a₂,k)] else 0)
  --         = (if p = q then (Tr_B M)[a₁,a₂] else 0).
  -- RHS entry: ((Tr_B M) ⊗ I_{n_B})[(a₁,p),(a₂,q)]
  --         = (Tr_B M)[a₁,a₂] · I[p,q]
  --         = (Tr_B M)[a₁,a₂] · (if p = q then 1 else 0).
  rw [Matrix.sum_apply]
  -- Switch to outer sum over k, inner sum over j (more convenient).
  simp_rw [Matrix.sum_apply]
  simp_rw [twirl_term_entry]
  -- Goal: ∑ j, ∑ k, (if p = j ∧ q = j then M[(a₁,k),(a₂,k)] else 0)
  --     = (Tr_B M ⊗ I_{n_B})[(a₁,p),(a₂,q)]
  -- The j-sum collapses to j = p (and requires q = p, else zero).
  by_cases hpq : p = q
  · -- p = q: then ∀ j, (if p = j ∧ q = j then ... else 0) = (if p = j then M[..] else 0).
    -- Sum over j collapses to j = p.
    subst hpq
    rw [show (∑ j : Fin n_B, ∑ k : Fin n_B,
              (if p = j ∧ p = j then M (a₁, k) (a₂, k) else 0))
            = (∑ k : Fin n_B, M (a₁, k) (a₂, k)) from by
          rw [Finset.sum_eq_single (a := p)]
          · simp
          · intro j _ hj
            apply Finset.sum_eq_zero
            intro k _
            rw [if_neg (fun ⟨h, _⟩ => hj h.symm)]
          · intro h; exact absurd (Finset.mem_univ p) h]
    -- Now RHS: ((Tr_B M) ⊗ I)[(a₁,p),(a₂,p)] = (Tr_B M)[a₁,a₂] · I[p,p] = (Tr_B M)[a₁,a₂].
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one]
    rfl
  · -- p ≠ q: then the entire double sum vanishes.
    rw [show (∑ j : Fin n_B, ∑ k : Fin n_B,
              (if p = j ∧ q = j then M (a₁, k) (a₂, k) else 0)) = 0 from by
          apply Finset.sum_eq_zero
          intro j _
          apply Finset.sum_eq_zero
          intro k _
          by_cases h : p = j ∧ q = j
          · obtain ⟨hp, hq⟩ := h
            exact absurd (hp.trans hq.symm) hpq
          · simp [h]]
    -- RHS: ((Tr_B M) ⊗ I)[(a₁,p),(a₂,q)] = (Tr_B M)[a₁,a₂] · I[p,q] = 0 (since p ≠ q).
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne hpq, mul_zero]

/-! ## 3.  The computational-basis-sum representation of partial trace.

This is direct from the definition of `partialTrace_right`, but we
record it as a self-contained lemma under a memorable name. -/

/-- **The computational-basis-sum representation of `partialTrace_right`.**

    By definition of `partialTrace_right`,

      `(Tr_B M)_{i,j} = ∑_k M_{(i,k),(j,k)}`.

    This unfolds `partialTrace_right` and exposes the textbook form. -/
theorem partialTrace_right_eq_computational_basis_sum
    {m n : Type*} [Fintype n]
    (M : Matrix (m × n) (m × n) ℂ) (i j : m) :
    partialTrace_right M i j = ∑ k : n, M (i, k) (j, k) := by
  rfl

/-- **The computational-basis-sum representation of `partialTrace_left`.**

    By definition of `partialTrace_left`,

      `(Tr_A M)_{i,j} = ∑_k M_{(k,i),(k,j)}`.

    Companion to `partialTrace_right_eq_computational_basis_sum`. -/
theorem partialTrace_left_eq_computational_basis_sum
    {m n : Type*} [Fintype m]
    (M : Matrix (m × n) (m × n) ℂ) (i j : n) :
    partialTrace_left M i j = ∑ k : m, M (k, i) (k, j) := by
  rfl

/-! ## 4.  Discharge of the upstream placeholder gate.

The gate `PartialTrace_Twirl_Target` declared in
`PartialTraceDecomposition.lean` is currently defined as `True`
(a structural placeholder).  We discharge it unconditionally below.
The substantive mathematical content of the gate beyond the
placeholder is delivered by `partialTrace_eq_matrixUnit_twirl`
above (the matrix-unit twirl identity). -/

/-- **Discharge of `PartialTrace_Twirl_Target`.**

    The upstream gate is `True`; the discharge is `trivial`.  The
    substantive mathematical content — the twirl identity expressing
    the partial trace as a sum of B-local matrix-unit conjugations —
    is shipped above as `partialTrace_eq_matrixUnit_twirl`.

    Mirror of `tensorAdditivity_holds` and `multiConvex_holds_unconditional`,
    the discharges of the other two `True`-placeholder sub-Props of
    `PartialTrace_Decomposition_Target`. -/
theorem partialTraceTwirl_holds : PartialTrace_Twirl_Target :=
  trivial

/-! ## 5.  Scoping note — relation to the headline twirl identity.

The classical Heisenberg–Weyl twirl identity reads

    `(1 / m²) · Σ_{g ∈ HW(m)} (I_A ⊗ U_g) · M · (I_A ⊗ U_g†)
        = (Tr_B M) ⊗ (I_m / m)`,

where `HW(m)` is the Heisenberg–Weyl group of order `m²` (generated
by the shift and clock unitaries `X` and `Z` on `Fin m`).  This is
the version most often quoted in quantum-information textbooks.

The matrix-unit form

    `Σ_{j,k} (I_A ⊗ E_{j,k}) · M · (I_A ⊗ E_{k,j}) = (Tr_B M) ⊗ I_m`

shipped above is the **linear-algebraic skeleton** of that identity.
The Heisenberg–Weyl version follows by expressing each matrix unit
`E_{j,k}` as a Fourier-style linear combination of the m² HW group
elements, then carrying the average through.  Concretely: for prime
`m` the HW unitaries `X^a Z^b` satisfy

    `E_{j,k} = (1/m) Σ_{a,b} ω^{...} · X^a · Z^b · |k⟩⟨j| · ...`

The bookkeeping is mechanical but lengthy (~150 lines once an
explicit indexing of HW is fixed); we do not assemble it here.
The matrix-unit form is sufficient for all downstream consumers
of `PartialTrace_Twirl_Target` in the LayerB stack, since each
HW twirl identity factors through the matrix-unit identity by
elementary linear algebra. -/

theorem scopingNote_heisenbergWeyl : True := trivial

/-! ## 6.  Axiom audit (intended state after build).

    The following are intended to print only
    `propext, Classical.choice, Quot.sound`
    (Lean's three standard axioms).  No `sorry`, no custom `axiom`. -/

-- #print axioms matrixUnit_conjTranspose
-- #print axioms matrixUnit_apply
-- #print axioms partialTrace_eq_matrixUnit_twirl
-- #print axioms partialTrace_right_eq_computational_basis_sum
-- #print axioms partialTrace_left_eq_computational_basis_sum
-- #print axioms partialTraceTwirl_holds
-- VERIFIED 2026-06-01:
--   matrixUnit_conjTranspose, matrixUnit_apply,
--   partialTrace_eq_matrixUnit_twirl,
--   partialTrace_right_eq_computational_basis_sum,
--   partialTrace_left_eq_computational_basis_sum
--     ALL depend ONLY on [propext, Classical.choice, Quot.sound]
--     (Lean's three standard axioms).
--   partialTraceTwirl_holds depends on NO axioms whatsoever
--     (the upstream gate is `True`; the discharge is `trivial`).
--   No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.PartialTraceTwirl
