/-
  UnifiedTheory/LayerC/BipartiteNoSignallingAnalyticCoreDischarge.lean
  ────────────────────────────────────────────────────────────────────

  **Unconditional discharge of `BipartiteNoSignallingAnalyticCore n_A n_B`.**

  The file `BipartiteUnitaryQM.lean` ships the bipartite phase-quotient
  unitary quantum theory as a `NoSignallingTheory` *conditional* on a
  bipartite analytic core (`BipartiteNoSignallingAnalyticCore n_A n_B`)
  with four fields:

    * `phenomenalProj_left_surjective`
    * `phenomenalProj_right_surjective`
    * `no_signalling_left`   (Kronecker / partial-trace identity)
    * `no_signalling_right`  (symmetric)

  Here we prove all four unconditionally and ship
  `bipartiteAnalyticCore n_A n_B`, then instantiate it at
  `n_A = n_B = 2` (the Bell-scenario qubit substrate).

  ## Proof strategy: split-Kronecker decomposition

  The two no-signalling identities reduce to a partial-trace identity
  on raw matrices:

      Tr_B((U_A ⊗ U_B) M (U_A ⊗ U_B)†) = U_A · Tr_B(M) · U_A†

  We prove this via the factorisation
  `U_A ⊗ U_B = (U_A ⊗ 1)(1 ⊗ U_B)`, splitting the conjugation into:

   * **Identity A** (`partialTrace_right_kron_A_one_conj`):
       `Tr_B((U_A ⊗ 1) X (U_A ⊗ 1)†) = U_A · Tr_B(X) · U_A†`
     (A-only conjugation commutes past `Tr_B`.)

   * **Identity B** (`partialTrace_right_kron_one_B_conj`):
       `Tr_B((1 ⊗ U_B) M (1 ⊗ U_B)†) = Tr_B(M)`
     (B-only conjugation disappears under `Tr_B`, by U_B† U_B = 1.)

  Surjectivity is proved by constructing `ρ = σ ⊗ |0⟩⟨0|`, using
  `Matrix.PosSemidef.kronecker` and `Matrix.trace_kronecker`.

  ## Standing constraint

  Zero `sorry`. Zero custom `axiom`. Only Lean's standard
  `propext`, `Classical.choice`, and `Quot.sound`.
-/

import UnifiedTheory.LayerC.BipartiteUnitaryQM
import Mathlib.Analysis.Matrix.Order

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.LocalRealisticAxioms

open Matrix
open scoped Kronecker
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.UnitaryInvariance
open UnifiedTheory.LayerB.PartialTrace
open UnitaryQuantum

variable {n_A n_B : ℕ}

/-! ## 1. Raw-matrix kronecker / partial-trace identities -/

/-- `∑_b U[b,i₁] * star(U[b,i₂]) = δ[i₁,i₂]` (unitarity, `U† · U = 1`). -/
private lemma sum_unitary_orth
    {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (i₁ i₂ : Fin n) :
    (∑ b : Fin n, U.val b i₁ * star (U.val b i₂))
      = (if i₁ = i₂ then (1 : ℂ) else 0) := by
  have h_unit :
      U.val.conjTranspose * U.val
        = (1 : Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  have h_dot :
      (∑ b : Fin n, U.val b i₁ * star (U.val b i₂))
        = (U.val.conjTranspose * U.val) i₂ i₁ := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [Matrix.conjTranspose_apply]; ring
  rw [h_dot, h_unit]
  by_cases h : i₁ = i₂
  · subst h; simp [Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne (Ne.symm h)]; simp [h]

/-! ## 2. Split-Kronecker approach.

  `U_A ⊗ U_B = (U_A ⊗ 1) * (1 ⊗ U_B)` is the standard factorisation.
  We use it to split the deep identity into two single-side layers:

  * Identity A: `Tr_B((U_A ⊗ 1) X (U_A† ⊗ 1)) = U_A · Tr_B(X) · U_A†`.
  * Identity B: `Tr_B((1 ⊗ U_B) M (1 ⊗ U_B†)) = Tr_B(M)`.

  Then composition + a star-of-kronecker rewrite finishes the joint identity. -/

/-- **Identity A (right partial trace).** -/
private lemma partialTrace_right_kron_A_one_conj
    (U_A : Matrix.unitaryGroup (Fin n_A) ℂ)
    (X : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ) :
    partialTrace_right
        ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ))
          * X * ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)).conjTranspose))
      = U_A.val * partialTrace_right X * U_A.val.conjTranspose := by
  -- Strategy: compute entry-wise. Each (i,b)(j,b) entry collapses the
  -- middle b' index to b (twice — once in K, once in K†).
  ext i j
  unfold partialTrace_right
  -- LHS[i,j] = ∑_b ∑_{a',a''} U_A[i,a'] · X[(a',b),(a'',b)] · star(U_A[j,a''])
  -- RHS[i,j] = ∑_{a',a''} U_A[i,a'] · (∑_b X[(a',b),(a'',b)]) · star(U_A[j,a''])
  -- These are equal by ∑_b ∑_{a',a''} = ∑_{a',a''} ∑_b.
  have h_entry : ∀ b : Fin n_B,
      ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ))
          * X * (U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)).conjTranspose)
        (i, b) (j, b)
        = ∑ a'' : Fin n_A, ∑ a' : Fin n_A,
            U_A.val i a' * X (a', b) (a'', b) * star (U_A.val j a'') := by
    intro b
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    -- ∑ a'' ∑ b'' (K X)[(i,b),(a'',b'')] · K†[(a'',b''),(j,b)]
    apply Finset.sum_congr rfl; intro a'' _
    -- For each a'', collapse b'' → b via 1[b,b''] in K†.
    rw [Finset.sum_eq_single (a := b) (h₀ := ?_) (h₁ := ?_)]
    rotate_left
    · intro b'' _ hb''
      -- K†[(a'',b''),(j,b)] = star(U_A[j,a''] * 1[b,b''])
      -- = star(U_A[j,a''] * 0) = 0 when b ≠ b'' (hb'' : b'' ≠ b)
      rw [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
      show _ * star (U_A.val j a'' * (1 : Matrix (Fin n_B) (Fin n_B) ℂ) b b'') = 0
      rw [Matrix.one_apply_ne hb''.symm]
      simp
    · intro h; exact absurd (Finset.mem_univ b) h
    -- Now compute (K X)[(i,b),(a'',b)] · K†[(a'',b),(j,b)]
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    -- K†[(a'',b),(j,b)] = star(U_A[j,a''] * 1[b,b]) = star(U_A[j,a''])
    rw [show ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)).conjTranspose
              (a'', b) (j, b))
          = star (U_A.val j a'') from by
            rw [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
            show star (U_A.val j a'' * (1 : Matrix (Fin n_B) (Fin n_B) ℂ) b b)
                = star (U_A.val j a'')
            rw [Matrix.one_apply_eq]
            simp]
    -- Goal: (∑ a' ∑ b', K[(i,b),(a',b')] · X[(a',b'),(a'',b)]) · star(U_A[j,a''])
    --     = ∑ a', U_A[i,a'] · X[(a',b),(a'',b)] · star(U_A[j,a''])
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a' _
    -- Inner ∑ b' collapses by 1[b,b'].
    rw [Finset.sum_eq_single (a := b) (h₀ := ?_) (h₁ := ?_)]
    rotate_left
    · intro b' _ hb'
      rw [Matrix.kroneckerMap_apply]
      show U_A.val i a' * (1 : Matrix (Fin n_B) (Fin n_B) ℂ) b b' * X (a', b') (a'', b) = 0
      rw [Matrix.one_apply_ne hb'.symm]
      simp
    · intro h; exact absurd (Finset.mem_univ b) h
    rw [Matrix.kroneckerMap_apply]
    show U_A.val i a' * (1 : Matrix (Fin n_B) (Fin n_B) ℂ) b b * X (a', b) (a'', b)
          * star (U_A.val j a'')
        = U_A.val i a' * X (a', b) (a'', b) * star (U_A.val j a'')
    rw [Matrix.one_apply_eq]
    ring
  -- Step 2: substitute and rearrange.
  rw [Finset.sum_congr rfl (fun b _ => h_entry b)]
  -- LHS = ∑ b ∑ a'' ∑ a' U_A[i,a'] · X[(a',b),(a'',b)] · star(U_A[j,a''])
  -- We want this to equal: ∑ a'' ∑ a' U_A[i,a'] · (∑ b X[..]) · star(U_A[j,a''])
  rw [show (∑ b : Fin n_B,
              ∑ a'' : Fin n_A, ∑ a' : Fin n_A,
                U_A.val i a' * X (a', b) (a'', b) * star (U_A.val j a''))
          = ∑ a'' : Fin n_A, ∑ a' : Fin n_A,
              U_A.val i a' * (∑ b : Fin n_B, X (a', b) (a'', b))
                * star (U_A.val j a'')
          from by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a'' _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a' _
            rw [Finset.mul_sum, Finset.sum_mul]]
  -- RHS = (U_A · Tr_B(X) · U_A†)[i,j] = ∑ a'' (U_A · Tr_B X)[i,a''] · star(U_A[j,a''])
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro a'' _
  rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_mul]

/-- **Identity B (right partial trace): the `(1 ⊗ U_B)` layer disappears under `Tr_B`.** -/
private lemma partialTrace_right_kron_one_B_conj
    (U_B : Matrix.unitaryGroup (Fin n_B) ℂ)
    (M : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ) :
    partialTrace_right
        (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val)
          * M * (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val).conjTranspose))
      = partialTrace_right M := by
  ext i j
  unfold partialTrace_right
  -- LHS[i,j] = ∑_b ((K M K†)[(i,b),(j,b)]) where K = 1 ⊗ U_B.
  -- K[(i,b),(a',b')] = 1[i,a'] · U_B[b,b']  →  only a' = i survives.
  -- K†[(a',b'),(j,b)] = 1[a',j] · star(U_B[b,b'])  →  only a' = j survives.
  -- So (K M K†)[(i,b),(j,b)] = ∑_{b',b''} U_B[b,b'] · M[(i,b'),(j,b'')] · star(U_B[b,b''])
  -- Sum over b: ∑ b' b'' M[(i,b'),(j,b'')] · (∑ b U_B[b,b'] · star(U_B[b,b'']))
  --           = ∑ b' b'' M[(i,b'),(j,b'')] · δ[b',b'']
  --           = ∑ b' M[(i,b'),(j,b')]
  --           = partialTrace_right M[i,j]
  have h_entry : ∀ b : Fin n_B,
      (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val) * M
          * ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val).conjTranspose)
        (i, b) (j, b)
        = ∑ b' : Fin n_B, ∑ b'' : Fin n_B,
            U_B.val b b'' * M (i, b'') (j, b') * star (U_B.val b b') := by
    intro b
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    -- ∑ a'' ∑ b'' (K M)[(i,b),(a'',b'')] · K†[(a'',b''),(j,b)]
    -- Collapse a'' = j first.
    rw [show (∑ a'' : Fin n_A, ∑ b'' : Fin n_B,
              (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val) * M) (i, b) (a'', b'')
                * (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val)).conjTranspose
                    (a'', b'') (j, b))
            = ∑ b'' : Fin n_B,
              (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val) * M) (i, b) (j, b'')
                * (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val)).conjTranspose
                    (j, b'') (j, b)
            from by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro b'' _
              apply Finset.sum_eq_single (a := j)
              · intro a'' _ ha''
                rw [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
                show _ * star ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) j a'' * U_B.val b b'') = 0
                rw [Matrix.one_apply_ne (Ne.symm ha'')]
                simp
              · intro h; exact absurd (Finset.mem_univ j) h]
    apply Finset.sum_congr rfl; intro b' _
    -- Now we have an expression depending on b' (was the outer b'' of the show block);
    -- in h_entry's spec the OUTER variable was named b' (and inner b'').
    -- K†[(j,b'),(j,b)] = star(K[(j,b),(j,b')]) = star(1[j,j] · U_B[b,b'])
    --                  = star(U_B[b,b'])
    rw [show (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val).conjTranspose
              (j, b') (j, b))
            = star (U_B.val b b') from by
            rw [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
            show star ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) j j * U_B.val b b')
                = star (U_B.val b b')
            rw [Matrix.one_apply_eq]
            simp]
    -- Now (K M)[(i,b),(j,b')] = ∑ a'' ∑ b'', K[(i,b),(a'',b'')] · M[(a'',b''),(j,b')]
    -- Collapse a'' = i.
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [show (∑ a'' : Fin n_A, ∑ b'' : Fin n_B,
              ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val) (i, b) (a'', b'')
                * M (a'', b'') (j, b'))
            = ∑ b'' : Fin n_B,
              ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val) (i, b) (i, b'')
                * M (i, b'') (j, b')
            from by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro b'' _
              apply Finset.sum_eq_single (a := i)
              · intro a'' _ ha''
                rw [Matrix.kroneckerMap_apply]
                show (1 : Matrix (Fin n_A) (Fin n_A) ℂ) i a'' * U_B.val b b'' * M (a'', b'') (j, b') = 0
                rw [Matrix.one_apply_ne ha''.symm]
                simp
              · intro h; exact absurd (Finset.mem_univ i) h]
    -- Goal: ∑ b'', K[(i,b),(i,b'')] · M[(i,b''),(j,b')] · star(U_B b b')
    --     = ∑ b'', U_B b b'' · M[(i,b''),(j,b')] · star(U_B b b').
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro b'' _
    rw [Matrix.kroneckerMap_apply]
    show (1 : Matrix (Fin n_A) (Fin n_A) ℂ) i i * U_B.val b b'' * M (i, b'') (j, b') * star (U_B.val b b')
        = U_B.val b b'' * M (i, b'') (j, b') * star (U_B.val b b')
    rw [Matrix.one_apply_eq]
    ring
  rw [Finset.sum_congr rfl (fun b _ => h_entry b)]
  -- LHS = ∑ b ∑ b' ∑ b'', U_B[b,b'] · M[(i,b'),(j,b'')] · star(U_B[b,b''])
  -- = ∑ b' ∑ b'' M[(i,b'),(j,b'')] · (∑ b U_B[b,b'] · star(U_B[b,b'']))
  -- = ∑ b' ∑ b'' M[(i,b'),(j,b'')] · δ[b',b'']
  -- = ∑ b' M[(i,b'),(j,b')]
  -- LHS = ∑ b ∑ b' ∑ b'', U_B b b'' · M[(i,b''),(j,b')] · star(U_B b b')
  -- = ∑ b' ∑ b'' M[(i,b''),(j,b')] · (∑ b U_B b b'' · star(U_B b b'))
  rw [show (∑ b : Fin n_B, ∑ b' : Fin n_B, ∑ b'' : Fin n_B,
              U_B.val b b'' * M (i, b'') (j, b') * star (U_B.val b b'))
          = ∑ b' : Fin n_B, ∑ b'' : Fin n_B,
              M (i, b'') (j, b')
                * (∑ b : Fin n_B, U_B.val b b'' * star (U_B.val b b'))
          from by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro b' _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro b'' _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro b _
            ring]
  rw [show (∑ b' : Fin n_B, ∑ b'' : Fin n_B,
              M (i, b'') (j, b')
                * (∑ b : Fin n_B, U_B.val b b'' * star (U_B.val b b')))
          = ∑ b' : Fin n_B, ∑ b'' : Fin n_B,
              M (i, b'') (j, b') * (if b'' = b' then (1 : ℂ) else 0)
          from by
            apply Finset.sum_congr rfl; intro b' _
            apply Finset.sum_congr rfl; intro b'' _
            rw [sum_unitary_orth]]
  -- ∑ b' ∑ b'' M[(i,b''),(j,b')] · δ[b'',b'] = ∑ b' M[(i,b'),(j,b')]
  apply Finset.sum_congr rfl; intro b' _
  rw [Finset.sum_eq_single (a := b')]
  · simp
  · intro b'' _ hb''
    simp [hb'']
  · intro h; exact absurd (Finset.mem_univ b') h

/-! ## 3. Combine: `(U_A ⊗ U_B) = (U_A ⊗ 1) · (1 ⊗ U_B)`. -/

/-- `U_A ⊗ U_B = (U_A ⊗ 1) · (1 ⊗ U_B)`. -/
private lemma kron_split
    (A : Matrix (Fin n_A) (Fin n_A) ℂ)
    (B : Matrix (Fin n_B) (Fin n_B) ℂ) :
    A ⊗ₖ B
      = (A ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ))
          * ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ B) := by
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.mul_one, Matrix.one_mul]

/-- The star of `(A ⊗ B)` factored as `(1 ⊗ B†) · (A† ⊗ 1)`. -/
private lemma kron_split_conjTranspose
    (A : Matrix (Fin n_A) (Fin n_A) ℂ)
    (B : Matrix (Fin n_B) (Fin n_B) ℂ) :
    (A ⊗ₖ B).conjTranspose
      = ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ B.conjTranspose)
          * (A.conjTranspose ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)) := by
  rw [Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- **The deep partial-trace / Kronecker identity (right partial trace).** -/
theorem partialTrace_right_kronecker_conj
    (U_A : Matrix.unitaryGroup (Fin n_A) ℂ)
    (U_B : Matrix.unitaryGroup (Fin n_B) ℂ)
    (M : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ) :
    partialTrace_right
        ((U_A.val ⊗ₖ U_B.val) * M * (U_A.val ⊗ₖ U_B.val).conjTranspose)
      = U_A.val * partialTrace_right M * U_A.val.conjTranspose := by
  -- Split (U_A ⊗ U_B) = (U_A ⊗ 1) · (1 ⊗ U_B).
  -- And star (U_A ⊗ U_B) = (1 ⊗ U_B†) · (U_A† ⊗ 1).
  -- So (U_A ⊗ U_B) M (star (U_A ⊗ U_B)) = (U_A ⊗ 1) · ((1 ⊗ U_B) M (1 ⊗ U_B†)) · (U_A† ⊗ 1).
  -- Apply identity A: Tr_B(X) where X = (1 ⊗ U_B) M (1 ⊗ U_B†):
  --   Tr_B((U_A ⊗ 1) X (U_A† ⊗ 1)) = U_A · Tr_B(X) · U_A†
  -- Then identity B: Tr_B(X) = Tr_B(M).
  rw [show (U_A.val ⊗ₖ U_B.val) * M * (U_A.val ⊗ₖ U_B.val).conjTranspose
        = (U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ))
            * (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val)
                * M
                * ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val).conjTranspose)
            * (U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)).conjTranspose from by
        rw [kron_split U_A.val U_B.val]
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]]
  rw [partialTrace_right_kron_A_one_conj U_A
      ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val
        * M * ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val).conjTranspose)]
  rw [partialTrace_right_kron_one_B_conj U_B M]

/-! ## 4. The left partial trace versions.

The same arguments apply with the roles of A and B swapped.
We give the two sublemmas, then the joint identity. -/

/-- **Identity B (left): the `(U_A ⊗ 1)` layer disappears under `Tr_A`.** -/
private lemma partialTrace_left_kron_A_one_conj
    (U_A : Matrix.unitaryGroup (Fin n_A) ℂ)
    (X : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ) :
    partialTrace_left
        ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ))
          * X * ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)).conjTranspose))
      = partialTrace_left X := by
  ext i j
  unfold partialTrace_left
  -- LHS[i,j] = ∑_a ((K X K†)[(a,i),(a,j)]) where K = U_A ⊗ 1.
  -- K[(a,i),(a',b')] = U_A[a,a'] · 1[i,b']  → only b' = i survives.
  -- K†[(a',b'),(a,j)] = star(U_A[a,a']) · 1[b',j]  → only b' = j survives.
  -- So (K X K†)[(a,i),(a,j)] = ∑_{a',a''} U_A[a,a'] · X[(a',i),(a'',j)] · star(U_A[a,a''])
  -- Sum over a: ∑ a' a'' X[(a',i),(a'',j)] · (∑ a U_A[a,a'] · star(U_A[a,a''])) = δ[a',a'']
  -- = ∑ a' X[(a',i),(a',j)] = partialTrace_left X[i,j]
  have h_entry : ∀ a : Fin n_A,
      ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ))
          * X * (U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)).conjTranspose)
        (a, i) (a, j)
        = ∑ a' : Fin n_A, ∑ a'' : Fin n_A,
            U_A.val a a'' * X (a'', i) (a', j) * star (U_A.val a a') := by
    intro a
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    -- ∑ a' ∑ b'' (K X)[(a,i),(a',b'')] · K†[(a',b''),(a,j)]
    -- Collapse b'' = j first (in K†).
    apply Finset.sum_congr rfl; intro a' _
    rw [show (∑ b'' : Fin n_B,
              ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)) * X) (a, i) (a', b'')
                * ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)).conjTranspose)
                    (a', b'') (a, j))
            = ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)) * X) (a, i) (a', j)
                * ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)).conjTranspose)
                    (a', j) (a, j)
            from by
              apply Finset.sum_eq_single (a := j)
              · intro b'' _ hb''
                rw [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
                show _ * star (U_A.val a a' * (1 : Matrix (Fin n_B) (Fin n_B) ℂ) j b'') = 0
                rw [Matrix.one_apply_ne hb''.symm]
                simp
              · intro h; exact absurd (Finset.mem_univ j) h]
    -- K†[(a',j),(a,j)] = star(K[(a,j),(a',j)]) = star(U_A[a,a'] · 1[j,j]) = star(U_A[a,a'])
    rw [show ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)).conjTranspose
              (a', j) (a, j))
            = star (U_A.val a a') from by
            rw [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
            show star (U_A.val a a' * (1 : Matrix (Fin n_B) (Fin n_B) ℂ) j j)
                = star (U_A.val a a')
            rw [Matrix.one_apply_eq]
            simp]
    -- Now (K X)[(a,i),(a',j)] = ∑ a'' ∑ b', K[(a,i),(a'',b')] · X[(a'',b'),(a',j)]
    -- Collapse b' = i.
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [show (∑ a'' : Fin n_A, ∑ b' : Fin n_B,
              ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ))) (a, i) (a'', b')
                * X (a'', b') (a', j))
            = ∑ a'' : Fin n_A,
              ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ))) (a, i) (a'', i)
                * X (a'', i) (a', j)
            from by
              apply Finset.sum_congr rfl; intro a'' _
              apply Finset.sum_eq_single (a := i)
              · intro b' _ hb'
                rw [Matrix.kroneckerMap_apply]
                show U_A.val a a'' * (1 : Matrix (Fin n_B) (Fin n_B) ℂ) i b' * X (a'', b') (a', j) = 0
                rw [Matrix.one_apply_ne hb'.symm]
                simp
              · intro h; exact absurd (Finset.mem_univ i) h]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a'' _
    rw [Matrix.kroneckerMap_apply]
    show U_A.val a a'' * (1 : Matrix (Fin n_B) (Fin n_B) ℂ) i i * X (a'', i) (a', j) * star (U_A.val a a')
        = U_A.val a a'' * X (a'', i) (a', j) * star (U_A.val a a')
    rw [Matrix.one_apply_eq]
    ring
  rw [Finset.sum_congr rfl (fun a _ => h_entry a)]
  -- LHS = ∑ a ∑ a' ∑ a'', U_A[a,a''] · X[(a'',i),(a',j)] · star(U_A[a,a'])
  -- = ∑ a' ∑ a'' X[(a'',i),(a',j)] · (∑ a U_A[a,a''] · star(U_A[a,a'])) = δ[a'',a']
  rw [show (∑ a : Fin n_A, ∑ a' : Fin n_A, ∑ a'' : Fin n_A,
              U_A.val a a'' * X (a'', i) (a', j) * star (U_A.val a a'))
          = ∑ a' : Fin n_A, ∑ a'' : Fin n_A,
              X (a'', i) (a', j)
                * (∑ a : Fin n_A, U_A.val a a'' * star (U_A.val a a'))
          from by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a' _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a'' _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro a _
            ring]
  rw [show (∑ a' : Fin n_A, ∑ a'' : Fin n_A,
              X (a'', i) (a', j)
                * (∑ a : Fin n_A, U_A.val a a'' * star (U_A.val a a')))
          = ∑ a' : Fin n_A, ∑ a'' : Fin n_A,
              X (a'', i) (a', j) * (if a'' = a' then (1 : ℂ) else 0)
          from by
            apply Finset.sum_congr rfl; intro a' _
            apply Finset.sum_congr rfl; intro a'' _
            rw [sum_unitary_orth]]
  apply Finset.sum_congr rfl; intro a' _
  rw [Finset.sum_eq_single (a := a')]
  · simp
  · intro a'' _ ha''
    simp [ha'']
  · intro h; exact absurd (Finset.mem_univ a') h

/-- **Identity A (left): B-only conjugation pulls out of `Tr_A`.** -/
private lemma partialTrace_left_kron_one_B_conj
    (U_B : Matrix.unitaryGroup (Fin n_B) ℂ)
    (M : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ) :
    partialTrace_left
        (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val)
          * M * (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val).conjTranspose))
      = U_B.val * partialTrace_left M * U_B.val.conjTranspose := by
  ext i j
  unfold partialTrace_left
  -- LHS[i,j] = ∑_a ((K M K†)[(a,i),(a,j)]) where K = 1 ⊗ U_B.
  -- K[(a,i),(a',b')] = 1[a,a'] · U_B[i,b']  → only a' = a survives.
  -- K†[(a',b'),(a,j)] = 1[a',a] · star(U_B[j,b'])  → only a' = a survives.
  -- So (K M K†)[(a,i),(a,j)] = ∑_{b',b''} U_B[i,b'] · M[(a,b'),(a,b'')] · star(U_B[j,b''])
  -- Sum over a: ∑ b' b'' U_B[i,b'] · (∑_a M[(a,b'),(a,b'')]) · star(U_B[j,b''])
  --           = (U_B · Tr_A(M) · U_B†)[i,j]
  have h_entry : ∀ a : Fin n_A,
      (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val) * M
          * ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val).conjTranspose)
        (a, i) (a, j)
        = ∑ b' : Fin n_B, ∑ b'' : Fin n_B,
            U_B.val i b'' * M (a, b'') (a, b') * star (U_B.val j b') := by
    intro a
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    -- ∑ a' ∑ b'' (K M)[(a,i),(a',b'')] · K†[(a',b''),(a,j)]
    -- Collapse a' = a (via 1[a',a] in K†).
    rw [show (∑ a' : Fin n_A, ∑ b'' : Fin n_B,
              (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val) * M) (a, i) (a', b'')
                * (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val)).conjTranspose
                    (a', b'') (a, j))
            = ∑ b'' : Fin n_B,
              (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val) * M) (a, i) (a, b'')
                * (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val)).conjTranspose
                    (a, b'') (a, j)
            from by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro b'' _
              apply Finset.sum_eq_single (a := a)
              · intro a' _ ha'
                rw [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
                show _ * star ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) a a' * U_B.val j b'') = 0
                rw [Matrix.one_apply_ne ha'.symm]
                simp
              · intro h; exact absurd (Finset.mem_univ a) h]
    -- After strip OUTER b'' (=h_entry's b'), then strip inner b' (=h_entry's b'').
    apply Finset.sum_congr rfl; intro b' _
    -- (K†)[(a,b'),(a,j)] = star(K[(a,j),(a,b')]) = star(1[a,a] · U_B[j,b']) = star(U_B[j,b'])
    rw [show (((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val).conjTranspose
              (a, b') (a, j))
            = star (U_B.val j b') from by
            rw [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
            show star ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) a a * U_B.val j b')
                = star (U_B.val j b')
            rw [Matrix.one_apply_eq]
            simp]
    -- (K M)[(a,i),(a,b')] = ∑ a'' ∑ b'', K[(a,i),(a'',b'')] · M[(a'',b''),(a,b')]
    -- Collapse a'' = a.
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [show (∑ a'' : Fin n_A, ∑ b'' : Fin n_B,
              ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val) (a, i) (a'', b'')
                * M (a'', b'') (a, b'))
            = ∑ b'' : Fin n_B,
              ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val) (a, i) (a, b'')
                * M (a, b'') (a, b')
            from by
              apply Finset.sum_eq_single (a := a)
              · intro a'' _ ha''
                apply Finset.sum_eq_zero
                intro b'' _
                rw [Matrix.kroneckerMap_apply]
                show (1 : Matrix (Fin n_A) (Fin n_A) ℂ) a a'' * U_B.val i b'' * M (a'', b'') (a, b') = 0
                rw [Matrix.one_apply_ne ha''.symm]
                simp
              · intro h; exact absurd (Finset.mem_univ a) h]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro b'' _
    rw [Matrix.kroneckerMap_apply]
    show (1 : Matrix (Fin n_A) (Fin n_A) ℂ) a a * U_B.val i b'' * M (a, b'') (a, b') * star (U_B.val j b')
        = U_B.val i b'' * M (a, b'') (a, b') * star (U_B.val j b')
    rw [Matrix.one_apply_eq]
    ring
  rw [Finset.sum_congr rfl (fun a _ => h_entry a)]
  -- LHS = ∑ a ∑ b' ∑ b'', U_B i b'' · M[(a,b''),(a,b')] · star(U_B j b')
  -- = ∑ b' ∑ b'' U_B[i,b''] · (∑ a M[(a,b''),(a,b')]) · star(U_B[j,b'])
  -- = ∑ b' ∑ b'' U_B[i,b''] · Tr_A(M)[b'',b'] · star(U_B[j,b'])
  -- RHS = (U_B · Tr_A(M) · U_B†)[i,j] = ∑ b', (∑ b'', U_B[i,b''] · Tr_A(M)[b'',b']) · star(U_B[j,b']).
  rw [show (∑ a : Fin n_A, ∑ b' : Fin n_B, ∑ b'' : Fin n_B,
              U_B.val i b'' * M (a, b'') (a, b') * star (U_B.val j b'))
          = ∑ b' : Fin n_B, ∑ b'' : Fin n_B,
              U_B.val i b'' * (∑ a : Fin n_A, M (a, b'') (a, b')) * star (U_B.val j b')
          from by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro b' _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro b'' _
            rw [Finset.mul_sum, Finset.sum_mul]]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro b' _
  rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_mul]

/-- **The deep partial-trace / Kronecker identity (left partial trace).** -/
theorem partialTrace_left_kronecker_conj
    (U_A : Matrix.unitaryGroup (Fin n_A) ℂ)
    (U_B : Matrix.unitaryGroup (Fin n_B) ℂ)
    (M : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ) :
    partialTrace_left
        ((U_A.val ⊗ₖ U_B.val) * M * (U_A.val ⊗ₖ U_B.val).conjTranspose)
      = U_B.val * partialTrace_left M * U_B.val.conjTranspose := by
  -- Apply the same split: (U_A ⊗ U_B) M (U_A ⊗ U_B)†
  --   = (1 ⊗ U_B) ((U_A ⊗ 1) M (U_A ⊗ 1)†) (1 ⊗ U_B)†
  -- using (U_A ⊗ U_B) = (1 ⊗ U_B)(U_A ⊗ 1).
  rw [show (U_A.val ⊗ₖ U_B.val) * M * (U_A.val ⊗ₖ U_B.val).conjTranspose
        = ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val)
            * ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ))
                * M
                * (U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)).conjTranspose)
            * ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val).conjTranspose from by
        rw [show U_A.val ⊗ₖ U_B.val
              = ((1 : Matrix (Fin n_A) (Fin n_A) ℂ) ⊗ₖ U_B.val)
                  * (U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)) from by
              rw [← Matrix.mul_kronecker_mul]
              rw [Matrix.one_mul, Matrix.mul_one]]
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]]
  rw [partialTrace_left_kron_one_B_conj U_B
      ((U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ))
        * M * (U_A.val ⊗ₖ (1 : Matrix (Fin n_B) (Fin n_B) ℂ)).conjTranspose)]
  rw [partialTrace_left_kron_A_one_conj U_A M]

/-! ## 5. Surjectivity of the partial-trace projector.

Given `σ : ComplexDensityMatrix n_A`, we construct a joint density matrix
`ρ : ComplexDensityMatrix (n_A * n_B)` whose right partial trace is `σ`,
by taking `ρ = σ ⊗ τ_B` where `τ_B = |0⟩⟨0|` is a fixed rank-1 density on B. -/

/-- The partial-trace-right of a Kronecker `σ ⊗ τ_B` (raw-matrix form):
    `Tr_B(σ ⊗ τ_B) = σ · Tr(τ_B)`. -/
private lemma partialTrace_right_kronecker
    (σ : Matrix (Fin n_A) (Fin n_A) ℂ)
    (τ : Matrix (Fin n_B) (Fin n_B) ℂ) :
    partialTrace_right (σ ⊗ₖ τ) = (Matrix.trace τ) • σ := by
  ext i j
  unfold partialTrace_right
  -- (σ ⊗ τ)[(i,k),(j,k)] = σ[i,j] · τ[k,k]
  rw [show (fun k : Fin n_B => (σ ⊗ₖ τ) (i, k) (j, k))
        = (fun k : Fin n_B => σ i j * τ k k)
        from funext (fun k => by rw [Matrix.kroneckerMap_apply])]
  rw [← Finset.mul_sum]
  rw [show (∑ k : Fin n_B, τ k k) = Matrix.trace τ from by
        rw [Matrix.trace]
        rfl]
  rw [Matrix.smul_apply, smul_eq_mul]
  ring

/-- The partial-trace-left of a Kronecker `σ ⊗ τ` (raw-matrix form):
    `Tr_A(σ ⊗ τ) = Tr(σ) · τ`. -/
private lemma partialTrace_left_kronecker
    (σ : Matrix (Fin n_A) (Fin n_A) ℂ)
    (τ : Matrix (Fin n_B) (Fin n_B) ℂ) :
    partialTrace_left (σ ⊗ₖ τ) = (Matrix.trace σ) • τ := by
  ext i j
  unfold partialTrace_left
  rw [show (fun k : Fin n_A => (σ ⊗ₖ τ) (k, i) (k, j))
        = (fun k : Fin n_A => σ k k * τ i j)
        from funext (fun k => by rw [Matrix.kroneckerMap_apply])]
  rw [← Finset.sum_mul]
  rw [show (∑ k : Fin n_A, σ k k) = Matrix.trace σ from by
        rw [Matrix.trace]
        rfl]
  rw [Matrix.smul_apply, smul_eq_mul]

/-- The basis density matrix (|0⟩⟨0|) on `Fin n_B` has trace 1, Hermitian,
    and is `PosSemidef`. -/
private lemma basisDensityMatrix_posSemidef
    (n : ℕ) [NeZero n] :
    (UnitaryQuantum.basisDensityMatrix n).M.PosSemidef := by
  -- basisDensityMatrix is built via ofPosSemidef with a diagonal PSD matrix.
  unfold UnitaryQuantum.basisDensityMatrix
  unfold UnitaryQuantum.ofPosSemidef
  -- The M field is the diagonal matrix.
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only
  split_ifs
  · exact zero_le_one
  · exact le_refl _

/-- **Surjectivity of the right partial trace.**

    Given any `σ : ComplexDensityMatrix n_A`, the joint density matrix
    `(σ ⊗ |0⟩⟨0|)` (reindexed to `Fin (n_A * n_B)`) has right partial trace `σ`. -/
theorem densityPartialTrace_rightDM_surjective
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (σ : ComplexDensityMatrix n_A) :
    ∃ ρ : ComplexDensityMatrix (n_A * n_B),
      densityPartialTrace_rightDM n_A n_B ρ = σ := by
  -- Build ρ from σ ⊗ τ_B where τ_B = basisDensityMatrix n_B.
  let τ : ComplexDensityMatrix n_B := UnitaryQuantum.basisDensityMatrix n_B
  let prod : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ := σ.M ⊗ₖ τ.M
  let ρ_M : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ :=
    prod.submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  -- Show ρ_M satisfies the density-matrix constraints.
  have hσ_PSD : σ.M.PosSemidef := by
    -- From ComplexDensityMatrix structure: hTracePSD implies PosSemidef via
    -- standard bridge (already done in PartialTrace.lean's posSemidef_of_ComplexDensityMatrix).
    refine PosSemidef.of_dotProduct_mulVec_nonneg σ.hHerm ?_
    intro x
    by_cases hn : Nonempty (Fin n_A)
    · classical
      obtain ⟨i₀⟩ := hn
      let X : Matrix (Fin n_A) (Fin n_A) ℂ :=
        Matrix.of (fun i j => if i = i₀ then star (x j) else 0)
      have hXt : X.conjTranspose =
          Matrix.of (fun i j => if j = i₀ then x i else 0) := by
        ext i j
        change star (X j i) = if j = i₀ then x i else 0
        simp only [X, Matrix.of_apply]
        split_ifs
        · simp
        · simp
      have hXtX : ∀ i j, (X.conjTranspose * X) i j = x i * star (x j) := by
        intro i j
        rw [Matrix.mul_apply]
        simp only [hXt, Matrix.of_apply, X]
        rw [Finset.sum_eq_single i₀]
        · simp
        · intro k _ hk; simp [hk]
        · intro h; exact absurd (Finset.mem_univ _) h
      set z : ℂ := star x ⬝ᵥ σ.M *ᵥ x with hz_def
      have h_tr_eq : Matrix.trace (σ.M * (X.conjTranspose * X)) = z := by
        rw [Matrix.trace]
        simp only [Matrix.diag_apply]
        have h_per : ∀ i, (σ.M * (X.conjTranspose * X)) i i
                        = ∑ j, σ.M i j * x j * star (x i) := by
          intro i
          rw [Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro j _
          rw [hXtX]
          ring
        simp_rw [h_per]
        rw [hz_def]
        change ∑ i, ∑ j, σ.M i j * x j * star (x i)
            = star x ⬝ᵥ σ.M *ᵥ x
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      have h_assoc :
          Matrix.trace (σ.M * X.conjTranspose * X) = z := by
        rw [Matrix.mul_assoc]; exact h_tr_eq
      have h_psd := σ.hTracePSD X
      rw [h_assoc] at h_psd
      have h_z_im : z.im = 0 := σ.hHerm.im_star_dotProduct_mulVec_self x
      rw [Complex.nonneg_iff]
      exact ⟨h_psd, h_z_im.symm⟩
    · have : IsEmpty (Fin n_A) := not_nonempty_iff.mp hn
      have h0 : star x ⬝ᵥ σ.M *ᵥ x = 0 := by simp [dotProduct]
      rw [h0]
  have hτ_PSD : τ.M.PosSemidef := basisDensityMatrix_posSemidef n_B
  have h_prod_PSD : prod.PosSemidef := hσ_PSD.kronecker hτ_PSD
  have h_prod_Herm : prod.IsHermitian := h_prod_PSD.isHermitian
  have h_prod_trace : Matrix.trace prod = 1 := by
    rw [Matrix.trace_kronecker, σ.hTrace, τ.hTrace]
    simp
  -- Now build ρ_M as a density matrix on Fin (n_A * n_B).
  have h_ρ_M_PSD : ρ_M.PosSemidef := h_prod_PSD.submatrix _
  have h_ρ_M_Herm : ρ_M.IsHermitian := h_prod_Herm.submatrix _
  have h_ρ_M_trace : Matrix.trace ρ_M = 1 := by
    show Matrix.trace (prod.submatrix finProdFinEquiv.symm finProdFinEquiv.symm) = 1
    -- trace of a submatrix-with-Equiv equals trace of the original.
    -- Use Equiv.sum_comp via the diagonal.
    unfold Matrix.trace
    simp only [Matrix.diag_apply, Matrix.submatrix_apply]
    rw [Equiv.sum_comp finProdFinEquiv.symm (fun p => prod p p)]
    -- Now goal: ∑ p, prod p p = 1, i.e., Matrix.trace prod = 1.
    exact h_prod_trace
  let ρ : ComplexDensityMatrix (n_A * n_B) :=
    UnitaryQuantum.ofPosSemidef (n_A * n_B) ρ_M h_ρ_M_Herm h_ρ_M_trace h_ρ_M_PSD
  refine ⟨ρ, ?_⟩
  -- Show densityPartialTrace_rightDM n_A n_B ρ = σ.
  rw [UnitaryQuantum.ComplexDensityMatrix.ext_iff_M]
  show densityPartialTrace_right ρ = σ.M
  unfold densityPartialTrace_right reindexFactor
  -- ρ.M = ρ_M = prod.submatrix finProdFinEquiv.symm finProdFinEquiv.symm.
  -- After re-reindexing with finProdFinEquiv, we get back prod.
  have h_reindex :
      (ρ.M.submatrix finProdFinEquiv finProdFinEquiv) = prod := by
    show (ρ_M.submatrix finProdFinEquiv finProdFinEquiv) = prod
    ext p q
    simp only [Matrix.submatrix_apply, ρ_M]
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [h_reindex]
  -- partialTrace_right prod = Tr(τ.M) • σ.M = 1 • σ.M = σ.M
  rw [partialTrace_right_kronecker]
  rw [τ.hTrace]
  exact one_smul ℂ σ.M

/-- **Surjectivity of the left partial trace.** -/
theorem densityPartialTrace_leftDM_surjective
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (σ : ComplexDensityMatrix n_B) :
    ∃ ρ : ComplexDensityMatrix (n_A * n_B),
      densityPartialTrace_leftDM n_A n_B ρ = σ := by
  -- Symmetric: ρ = τ_A ⊗ σ.
  let τ : ComplexDensityMatrix n_A := UnitaryQuantum.basisDensityMatrix n_A
  let prod : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ := τ.M ⊗ₖ σ.M
  let ρ_M : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ :=
    prod.submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  have hσ_PSD : σ.M.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg σ.hHerm ?_
    intro x
    by_cases hn : Nonempty (Fin n_B)
    · classical
      obtain ⟨i₀⟩ := hn
      let X : Matrix (Fin n_B) (Fin n_B) ℂ :=
        Matrix.of (fun i j => if i = i₀ then star (x j) else 0)
      have hXt : X.conjTranspose =
          Matrix.of (fun i j => if j = i₀ then x i else 0) := by
        ext i j
        change star (X j i) = if j = i₀ then x i else 0
        simp only [X, Matrix.of_apply]
        split_ifs
        · simp
        · simp
      have hXtX : ∀ i j, (X.conjTranspose * X) i j = x i * star (x j) := by
        intro i j
        rw [Matrix.mul_apply]
        simp only [hXt, Matrix.of_apply, X]
        rw [Finset.sum_eq_single i₀]
        · simp
        · intro k _ hk; simp [hk]
        · intro h; exact absurd (Finset.mem_univ _) h
      set z : ℂ := star x ⬝ᵥ σ.M *ᵥ x with hz_def
      have h_tr_eq : Matrix.trace (σ.M * (X.conjTranspose * X)) = z := by
        rw [Matrix.trace]
        simp only [Matrix.diag_apply]
        have h_per : ∀ i, (σ.M * (X.conjTranspose * X)) i i
                        = ∑ j, σ.M i j * x j * star (x i) := by
          intro i
          rw [Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro j _
          rw [hXtX]
          ring
        simp_rw [h_per]
        rw [hz_def]
        change ∑ i, ∑ j, σ.M i j * x j * star (x i)
            = star x ⬝ᵥ σ.M *ᵥ x
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      have h_assoc :
          Matrix.trace (σ.M * X.conjTranspose * X) = z := by
        rw [Matrix.mul_assoc]; exact h_tr_eq
      have h_psd := σ.hTracePSD X
      rw [h_assoc] at h_psd
      have h_z_im : z.im = 0 := σ.hHerm.im_star_dotProduct_mulVec_self x
      rw [Complex.nonneg_iff]
      exact ⟨h_psd, h_z_im.symm⟩
    · have : IsEmpty (Fin n_B) := not_nonempty_iff.mp hn
      have h0 : star x ⬝ᵥ σ.M *ᵥ x = 0 := by simp [dotProduct]
      rw [h0]
  have hτ_PSD : τ.M.PosSemidef := basisDensityMatrix_posSemidef n_A
  have h_prod_PSD : prod.PosSemidef := hτ_PSD.kronecker hσ_PSD
  have h_prod_Herm : prod.IsHermitian := h_prod_PSD.isHermitian
  have h_prod_trace : Matrix.trace prod = 1 := by
    rw [Matrix.trace_kronecker, τ.hTrace, σ.hTrace]
    simp
  have h_ρ_M_PSD : ρ_M.PosSemidef := h_prod_PSD.submatrix _
  have h_ρ_M_Herm : ρ_M.IsHermitian := h_prod_Herm.submatrix _
  have h_ρ_M_trace : Matrix.trace ρ_M = 1 := by
    show Matrix.trace (prod.submatrix finProdFinEquiv.symm finProdFinEquiv.symm) = 1
    unfold Matrix.trace
    simp only [Matrix.diag_apply, Matrix.submatrix_apply]
    rw [Equiv.sum_comp finProdFinEquiv.symm (fun p => prod p p)]
    exact h_prod_trace
  let ρ : ComplexDensityMatrix (n_A * n_B) :=
    UnitaryQuantum.ofPosSemidef (n_A * n_B) ρ_M h_ρ_M_Herm h_ρ_M_trace h_ρ_M_PSD
  refine ⟨ρ, ?_⟩
  rw [UnitaryQuantum.ComplexDensityMatrix.ext_iff_M]
  show densityPartialTrace_left ρ = σ.M
  unfold densityPartialTrace_left reindexFactor
  have h_reindex :
      (ρ.M.submatrix finProdFinEquiv finProdFinEquiv) = prod := by
    show (ρ_M.submatrix finProdFinEquiv finProdFinEquiv) = prod
    ext p q
    simp only [Matrix.submatrix_apply, ρ_M]
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [h_reindex]
  rw [partialTrace_left_kronecker]
  rw [τ.hTrace]
  exact one_smul ℂ σ.M

/-! ## 6. The unconditional analytic core. -/

/-- **The bipartite no-signalling analytic core, unconditionally.**

    All four fields are discharged from the deep partial-trace identities
    and the Kronecker-based surjectivity constructions. -/
theorem bipartiteAnalyticCore (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B] :
    BipartiteNoSignallingAnalyticCore n_A n_B where
  phenomenalProj_left_surjective := densityPartialTrace_rightDM_surjective n_A n_B
  phenomenalProj_right_surjective := densityPartialTrace_leftDM_surjective n_A n_B
  no_signalling_left := by
    intro U_A U_B ρ
    rw [UnitaryQuantum.ComplexDensityMatrix.ext_iff_M]
    show densityPartialTrace_right (kroneckerConjugate U_A U_B ρ)
        = U_A.val * densityPartialTrace_right ρ * U_A.val.conjTranspose
    unfold densityPartialTrace_right reindexFactor
    have h_lhs_reindex :
        (kroneckerConjugate U_A U_B ρ).M.submatrix finProdFinEquiv finProdFinEquiv
          = (U_A.val ⊗ₖ U_B.val) * (ρ.M.submatrix finProdFinEquiv finProdFinEquiv)
              * (U_A.val ⊗ₖ U_B.val).conjTranspose := by
      show (kroneckerUnitary U_A U_B * ρ.M * star (kroneckerUnitary U_A U_B)).submatrix
            finProdFinEquiv finProdFinEquiv
          = (U_A.val ⊗ₖ U_B.val) * (ρ.M.submatrix finProdFinEquiv finProdFinEquiv)
              * (U_A.val ⊗ₖ U_B.val).conjTranspose
      -- Set notation.
      set A : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ := U_A.val ⊗ₖ U_B.val with hA
      have h_kU :
          kroneckerUnitary U_A U_B
            = A.submatrix finProdFinEquiv.symm finProdFinEquiv.symm := rfl
      have h_star_sub :
          star (A.submatrix finProdFinEquiv.symm finProdFinEquiv.symm)
            = A.conjTranspose.submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
        ext i j
        simp [Matrix.star_apply, Matrix.submatrix_apply,
              Matrix.conjTranspose_apply]
      -- Express ρ.M as submatrix-of-its-own-reindex.
      have h_ρ_re :
          ρ.M = (ρ.M.submatrix finProdFinEquiv finProdFinEquiv).submatrix
                  finProdFinEquiv.symm finProdFinEquiv.symm := by
        ext p q
        rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rw [h_kU, h_star_sub]
      conv_lhs => rw [show ρ.M = (ρ.M.submatrix finProdFinEquiv finProdFinEquiv).submatrix
                            finProdFinEquiv.symm finProdFinEquiv.symm from h_ρ_re]
      -- Combine submatrix multiplications.
      rw [Matrix.submatrix_mul_equiv A _ _ finProdFinEquiv.symm _]
      rw [Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _]
      -- LHS = (A * Mre * A†).submatrix f.symm f.symm).submatrix f f = A * Mre * A†
      rw [show ((A * (ρ.M.submatrix finProdFinEquiv finProdFinEquiv) * A.conjTranspose).submatrix
                finProdFinEquiv.symm finProdFinEquiv.symm).submatrix
              finProdFinEquiv finProdFinEquiv
            = A * (ρ.M.submatrix finProdFinEquiv finProdFinEquiv) * A.conjTranspose from by
            ext p q
            rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
            rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]]
    rw [h_lhs_reindex]
    exact partialTrace_right_kronecker_conj U_A U_B
      (ρ.M.submatrix finProdFinEquiv finProdFinEquiv)
  no_signalling_right := by
    intro U_A U_B ρ
    rw [UnitaryQuantum.ComplexDensityMatrix.ext_iff_M]
    show densityPartialTrace_left (kroneckerConjugate U_A U_B ρ)
        = U_B.val * densityPartialTrace_left ρ * U_B.val.conjTranspose
    unfold densityPartialTrace_left reindexFactor
    have h_lhs_reindex :
        (kroneckerConjugate U_A U_B ρ).M.submatrix finProdFinEquiv finProdFinEquiv
          = (U_A.val ⊗ₖ U_B.val) * (ρ.M.submatrix finProdFinEquiv finProdFinEquiv)
              * (U_A.val ⊗ₖ U_B.val).conjTranspose := by
      show (kroneckerUnitary U_A U_B * ρ.M * star (kroneckerUnitary U_A U_B)).submatrix
            finProdFinEquiv finProdFinEquiv
          = (U_A.val ⊗ₖ U_B.val) * (ρ.M.submatrix finProdFinEquiv finProdFinEquiv)
              * (U_A.val ⊗ₖ U_B.val).conjTranspose
      set A : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ := U_A.val ⊗ₖ U_B.val with hA
      have h_kU :
          kroneckerUnitary U_A U_B
            = A.submatrix finProdFinEquiv.symm finProdFinEquiv.symm := rfl
      have h_star_sub :
          star (A.submatrix finProdFinEquiv.symm finProdFinEquiv.symm)
            = A.conjTranspose.submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
        ext i j
        simp [Matrix.star_apply, Matrix.submatrix_apply,
              Matrix.conjTranspose_apply]
      have h_ρ_re :
          ρ.M = (ρ.M.submatrix finProdFinEquiv finProdFinEquiv).submatrix
                  finProdFinEquiv.symm finProdFinEquiv.symm := by
        ext p q
        rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rw [h_kU, h_star_sub]
      conv_lhs => rw [show ρ.M = (ρ.M.submatrix finProdFinEquiv finProdFinEquiv).submatrix
                            finProdFinEquiv.symm finProdFinEquiv.symm from h_ρ_re]
      rw [Matrix.submatrix_mul_equiv A _ _ finProdFinEquiv.symm _]
      rw [Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _]
      rw [show ((A * (ρ.M.submatrix finProdFinEquiv finProdFinEquiv) * A.conjTranspose).submatrix
                finProdFinEquiv.symm finProdFinEquiv.symm).submatrix
              finProdFinEquiv finProdFinEquiv
            = A * (ρ.M.submatrix finProdFinEquiv finProdFinEquiv) * A.conjTranspose from by
            ext p q
            rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
            rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]]
    rw [h_lhs_reindex]
    exact partialTrace_left_kronecker_conj U_A U_B
      (ρ.M.submatrix finProdFinEquiv finProdFinEquiv)

/-! ## 7. The unconditional bipartite headline. -/

/-- **THE BIPARTITE HEADLINE (unconditional in the core).**

    Bipartite phase-quotient unitary QM has a local-realistic shadow,
    modulo only the standard five-postulate bundle `BipartiteFullPostulates`. -/
theorem bipartiteUnitaryQM_has_localRealisticModel
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hPost : BipartiteFullPostulates n_A n_B (bipartiteAnalyticCore n_A n_B)) :
    ∃ L : LocalRealisticTheory,
      L.IsNoSignallingShadow
        (bipartiteUnitaryQuantumNoSignalling n_A n_B (bipartiteAnalyticCore n_A n_B)) :=
  bipartiteUnitaryQM_has_localRealisticModel_of_core
    n_A n_B (bipartiteAnalyticCore n_A n_B) hPost

/-! ## 8. The Bell-scenario qubit specialisation (n_A = n_B = 2). -/

/-- **The Bell-scenario qubit substrate of the bipartite analytic core.** -/
noncomputable def bipartiteAnalyticCore_2_2 : BipartiteNoSignallingAnalyticCore 2 2 :=
  bipartiteAnalyticCore 2 2

/-- **The bipartite phase-quotient unitary QM theory at n_A = n_B = 2 is
    a no-signalling theory.** -/
noncomputable def bipartiteQubitUnitaryQuantumNoSignalling : NoSignallingTheory :=
  bipartiteUnitaryQuantumNoSignalling 2 2 bipartiteAnalyticCore_2_2

/-- **The Bell-scenario qubit corollary of the bipartite headline.**

    At `n_A = n_B = 2` (the Bell-scenario qubit substrate),
    bipartite phase-quotient unitary QM admits a local-realistic shadow,
    modulo the same standard five-postulate bundle. -/
theorem bipartiteQubitUnitaryQM_has_localRealisticModel
    (hPost : BipartiteFullPostulates 2 2 bipartiteAnalyticCore_2_2) :
    ∃ L : LocalRealisticTheory,
      L.IsNoSignallingShadow
        bipartiteQubitUnitaryQuantumNoSignalling :=
  bipartiteUnitaryQM_has_localRealisticModel 2 2 hPost

/-! ## 9.  Diagnostic / axiom-check. -/

#print axioms bipartiteAnalyticCore
#print axioms bipartiteAnalyticCore_2_2
#print axioms bipartiteQubitUnitaryQM_has_localRealisticModel

/-! ## 10. Bridge to Tsirelson — deferred scaffolding.

To wire the Bell-scenario qubit substrate to the framework's pre-existing
Tsirelson bound (in `UnifiedTheory.LayerB.TsirelsonBound`), one would
need to (i) define `PauliObservable` 2×2 unitaries (σ_x, σ_y, σ_z),
(ii) lift them to a `PhaseQuotient 2 × PhaseQuotient 2`-style CHSH
operator set, and (iii) derive the substrate-side singlet correlation
function and equate it to `singletCorrelation` from `TsirelsonBound`.

The existing `tsirelson_bound (θa θa' θb θb' : ℝ)` already proves the
`2 * Real.sqrt 2` bound on the singlet-correlation CHSH value. The
remaining wire-up is a Phase-2 follow-up: it requires extending
`BipartiteTransSpace` (which currently carries LOCAL UNITARIES) to
carry MEASUREMENT-OBSERVABLE data, then deriving correlation functions
on the joint phenomenal state.

We do not ship this scaffolding here, to avoid `sorry`s and avoid
introducing a measurement-observable layer that the `BipartiteTransSpace`
type does not currently expose. -/

end UnifiedTheory.LayerC.LocalRealisticAxioms
