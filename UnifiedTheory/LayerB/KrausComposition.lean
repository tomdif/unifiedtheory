/-
  LayerB/KrausComposition.lean
  ─────────────────────────────

  Channel composition for Kraus representations.

  Given two Kraus representations
      E : KrausRepresentation m k k_E      (maps Matrix m m ℂ → Matrix k k ℂ)
      F : KrausRepresentation k n k_F      (maps Matrix k k ℂ → Matrix n n ℂ)

  their composition has Kraus operators

      (compose F E).K (j, i)  :=  F.K j * E.K i

  indexed by `Fin (k_F * k_E)` via the bijection `finProdFinEquiv`.

  Completeness follows from the chain

      Σ_(j,i) (Fⱼ · Eᵢ)† · (Fⱼ · Eᵢ)
        = Σᵢ Eᵢ† · (Σⱼ Fⱼ† · Fⱼ) · Eᵢ      [factor out Eᵢ, sum over j first]
        = Σᵢ Eᵢ† · I · Eᵢ                      [F.complete]
        = Σᵢ Eᵢ† · Eᵢ                          [I·M = M]
        = I                                       [E.complete]

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `compose F E : KrausRepresentation m n (k_F * k_E)`.
    2. `compose_apply` : the induced map is the composition
       `(compose F E).apply ρ = F.apply (E.apply ρ)`.
    3. `compose_isCPTP` : composition of CPTP maps is CPTP
       (immediate from `kraus_isCPTP`).

  Combined with `KrausLindbladBridge.lean`, this means we can compose
  the dephasing channel with itself to get the discrete semigroup
  property automatically.
-/

import UnifiedTheory.LayerB.KrausExistence

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Kraus

open Matrix Complex
open scoped ComplexOrder

/-! ## 1. Definition of channel composition -/

/-- The K-function of the composed Kraus representation. -/
private noncomputable def composeK {m k n k_E k_F : ℕ}
    (F : KrausRepresentation k n k_F)
    (E : KrausRepresentation m k k_E)
    (idx : Fin (k_F * k_E)) : Matrix (Fin n) (Fin m) ℂ :=
  F.K (finProdFinEquiv.symm idx).1 * E.K (finProdFinEquiv.symm idx).2

/-- The composition of two Kraus representations as a single Kraus
    representation, with operators `(F.K j) * (E.K i)` indexed by
    `Fin (k_F * k_E)` via the standard `finProdFinEquiv` bijection. -/
noncomputable def compose {m k n k_E k_F : ℕ}
    (F : KrausRepresentation k n k_F)
    (E : KrausRepresentation m k k_E) :
    KrausRepresentation m n (k_F * k_E) where
  K := composeK F E
  complete := by
    -- Step 1: transport sum from Fin (k_F * k_E) to Fin k_F × Fin k_E
    have h_transport :
        (∑ idx : Fin (k_F * k_E),
            (composeK F E idx).conjTranspose * composeK F E idx)
          = (∑ p : Fin k_F × Fin k_E,
              (F.K p.1 * E.K p.2).conjTranspose * (F.K p.1 * E.K p.2)) := by
      symm
      apply Fintype.sum_bijective finProdFinEquiv finProdFinEquiv.bijective
        (fun p => (F.K p.1 * E.K p.2).conjTranspose * (F.K p.1 * E.K p.2))
        (fun idx => (composeK F E idx).conjTranspose * composeK F E idx)
      intro p
      simp [composeK, Equiv.symm_apply_apply]
    rw [h_transport]
    -- Step 2: rewrite each summand using (FE)† = E† F†
    have h_term : ∀ p : Fin k_F × Fin k_E,
        (F.K p.1 * E.K p.2).conjTranspose * (F.K p.1 * E.K p.2)
          = (E.K p.2).conjTranspose
              * ((F.K p.1).conjTranspose * F.K p.1) * E.K p.2 := by
      intro p
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (F.K p.1).conjTranspose,
          ← Matrix.mul_assoc (E.K p.2).conjTranspose]
    simp_rw [h_term]
    -- Step 3: swap sums and factor (Σ_j F_j† F_j) = I
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have h_factor : ∀ i : Fin k_E,
        (∑ j : Fin k_F, (E.K i).conjTranspose
                  * ((F.K j).conjTranspose * F.K j) * E.K i)
          = (E.K i).conjTranspose
              * (∑ j : Fin k_F, (F.K j).conjTranspose * F.K j) * E.K i := by
      intro i
      rw [Matrix.mul_sum, Matrix.sum_mul]
    simp_rw [h_factor]
    rw [F.complete]
    simp_rw [Matrix.mul_one]
    exact E.complete

/-! ## 2. The induced map is the composition of the induced maps -/

/-- The map induced by `compose F E` is the composition of the maps
    induced by F and E:  `(compose F E).apply ρ = F.apply (E.apply ρ)`. -/
theorem compose_apply {m k n k_E k_F : ℕ}
    (F : KrausRepresentation k n k_F)
    (E : KrausRepresentation m k k_E)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    (compose F E).apply ρ = F.apply (E.apply ρ) := by
  unfold KrausRepresentation.apply
  change (∑ idx, composeK F E idx * ρ * (composeK F E idx).conjTranspose)
      = ∑ j, F.K j * (∑ i, E.K i * ρ * (E.K i).conjTranspose)
              * (F.K j).conjTranspose
  -- Transport LHS sum to product sum
  have h_transport :
      (∑ idx : Fin (k_F * k_E),
          composeK F E idx * ρ * (composeK F E idx).conjTranspose)
        = (∑ p : Fin k_F × Fin k_E,
            (F.K p.1 * E.K p.2) * ρ * (F.K p.1 * E.K p.2).conjTranspose) := by
    symm
    apply Fintype.sum_bijective finProdFinEquiv finProdFinEquiv.bijective
      (fun p => (F.K p.1 * E.K p.2) * ρ * (F.K p.1 * E.K p.2).conjTranspose)
      (fun idx => composeK F E idx * ρ * (composeK F E idx).conjTranspose)
    intro p
    simp [composeK, Equiv.symm_apply_apply]
  rw [h_transport]
  -- Σ_p (F_p.1 * E_p.2) * ρ * (F_p.1 * E_p.2)†
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  -- Force the goal into clean (j, y)-reduced form
  change ∑ y : Fin k_E, F.K j * E.K y * ρ * (F.K j * E.K y)ᴴ
     = (F.K j * ∑ i, E.K i * ρ * (E.K i)ᴴ) * (F.K j)ᴴ
  -- RHS: distribute F.K j into the sum, then factor (F.K j)ᴴ out
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  -- Goal: F.K j * E.K i * ρ * (F.K j * E.K i)ᴴ = F.K j * (E.K i * ρ * (E.K i)ᴴ) * (F.K j)ᴴ
  rw [Matrix.conjTranspose_mul]
  -- Both sides are F.K j * E.K i * ρ * (E.K i)ᴴ * (F.K j)ᴴ up to associativity
  simp_rw [← Matrix.mul_assoc]

/-! ## 3. CPTP is closed under composition -/

/-- **Channel composition is CPTP.**  If E and F are CPTP, so is F∘E. -/
theorem compose_isCPTP {m k n k_E k_F : ℕ}
    (F : KrausRepresentation k n k_F)
    (E : KrausRepresentation m k k_E) :
    IsCPTP (compose F E).toLinearMap :=
  kraus_isCPTP _

/-! ## 4. Composition with identity -/

/-- Composing with the identity Kraus rep on the right is the identity. -/
theorem compose_identity_right {m n k : ℕ}
    (F : KrausRepresentation m n k)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    (compose F (KrausRepresentation.identity m)).apply ρ = F.apply ρ := by
  rw [compose_apply, KrausRepresentation.identity_apply]

/-- Composing with the identity Kraus rep on the left is the identity. -/
theorem compose_identity_left {m n k : ℕ}
    (F : KrausRepresentation m n k)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    (compose (KrausRepresentation.identity n) F).apply ρ
      = F.apply ρ := by
  rw [compose_apply, KrausRepresentation.identity_apply]

end UnifiedTheory.LayerB.Kraus
