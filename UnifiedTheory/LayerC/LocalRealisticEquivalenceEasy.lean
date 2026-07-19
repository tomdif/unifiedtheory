/-
  UnifiedTheory/LayerC/LocalRealisticEquivalenceEasy.lean
  ───────────────────────────────────────────────────────

  **Easy direction** of the Raymond-Robichaud equivalence:
  every `LocalRealisticTheory` admits a `NoSignallingTheory`
  shadow.

  Discharges `LocalRealisticTheory.HasNoSignallingShadow L` for
  every `L : LocalRealisticTheory`, by forgetting the noumenal
  layer and verifying the six phenomenal axioms 4.1–4.6.

  ## Proof structure (paper Section 4 intro + Theorem 3.12)

  The forward map sends a `LocalRealisticTheory L` to the
  `NoSignallingTheory` whose phenomenal data IS L's phenomenal
  data.  Five of the six axioms (4.1–4.5) are inherited
  verbatim; only Axiom 4.6 (no-signalling plus the composition
  laws for `transProduct`) needs work.

  ### Axiom 4.6.1 (no-signalling, the key step)

  For `ρ : Phenomenal (A ⊔ B)`, lift to `N_AB : Noumenal (A ⊔ B)`
  via `epi_surjective`.  Then a three-step diagram chase using

    * `epi.intertwines`                   — `ϕ((U×V) ⋆ N) = (U×V) · ϕ(N)`,
    * `proj_epi_compat`                   — `π_A · ϕ = ϕ · π_A^noum`,
    * `noumenalProj_left_transProduct`    — noumenal no-signalling,

  reduces `π_A · ((U×V) · ρ)` to `U · (π_A ρ)`.

  ### Axioms 4.6.3 and 4.6.4 (composition and identity)

  Both follow from `noumenal_faithful` (paper Theorems 3.8, 3.9).
  Two transformations of `A ⊔ B` are equal iff they act
  identically on every noumenal state.  We compare the actions
  on each `N_AB`, splitting via `noumenalProduct_split` and
  applying `transProduct_action` componentwise.

  ## Constraints

  Zero `sorry`, zero custom `axiom`.
-/

import UnifiedTheory.LayerC.LocalRealisticAxioms

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.LocalRealisticAxioms

open Function

namespace LocalRealisticTheory

variable (L : LocalRealisticTheory)

/-! ## 1.  Derived noumenal-product projection lemmas

    From `noumenalProduct_split`, the natural projection laws
    follow by `subst` on the existence witness's components. -/

/-- Projecting a noumenal product to the left factor returns the
    left component. -/
lemma noumenalProduct_proj_left {A B : L.Sys}
    (hd : Disjoint A B) (N_A : L.Noumenal A) (N_B : L.Noumenal B)
    (hc : ∃ N_AB : L.Noumenal (A ⊔ B),
            L.noumenalProj (le_sup_left : A ≤ A ⊔ B) N_AB = N_A ∧
            L.noumenalProj (le_sup_right : B ≤ A ⊔ B) N_AB = N_B) :
    L.noumenalProj (le_sup_left : A ≤ A ⊔ B)
        (L.noumenalProduct hd N_A N_B hc) = N_A := by
  obtain ⟨N_AB, h1, h2⟩ := hc
  subst h1
  subst h2
  rw [L.noumenalProduct_split hd N_AB]

/-- Projecting a noumenal product to the right factor returns the
    right component. -/
lemma noumenalProduct_proj_right {A B : L.Sys}
    (hd : Disjoint A B) (N_A : L.Noumenal A) (N_B : L.Noumenal B)
    (hc : ∃ N_AB : L.Noumenal (A ⊔ B),
            L.noumenalProj (le_sup_left : A ≤ A ⊔ B) N_AB = N_A ∧
            L.noumenalProj (le_sup_right : B ≤ A ⊔ B) N_AB = N_B) :
    L.noumenalProj (le_sup_right : B ≤ A ⊔ B)
        (L.noumenalProduct hd N_A N_B hc) = N_B := by
  obtain ⟨N_AB, h1, h2⟩ := hc
  subst h1
  subst h2
  rw [L.noumenalProduct_split hd N_AB]

/-! ## 1b.  Congruence of `noumenalProduct` under equal projections

    `noumenalProduct` depends dependently on an existence proof
    `hc`.  If we have two states `M, N` with the SAME projections,
    they have the same lifts to `Noumenal (A ⊔ B)`. -/

/-- **General splitting lemma.**  If `W : Noumenal (A ⊔ B)` has
    projections `a` and `b`, then `noumenalProduct hd a b ⟨W, hA, hB⟩ = W`.

    Generalised form of `noumenalProduct_split`: the first two
    arguments to `noumenalProduct` are allowed to be arbitrary
    states equal to the projections of `W`, rather than literally
    the projections.  The witness term is then constructed from
    `W` plus the projection equalities. -/
lemma noumenalProduct_split_witness {A B : L.Sys}
    (hd : Disjoint A B) (a : L.Noumenal A) (b : L.Noumenal B)
    (W : L.Noumenal (A ⊔ B))
    (hA : L.noumenalProj (le_sup_left : A ≤ A ⊔ B) W = a)
    (hB : L.noumenalProj (le_sup_right : B ≤ A ⊔ B) W = b) :
    L.noumenalProduct hd a b ⟨W, hA, hB⟩ = W := by
  subst hA
  subst hB
  exact L.noumenalProduct_split hd W

/-- If two states `M` and `N` of `Noumenal (A ⊔ B)` have equal
    projections, then they are equal.

    Proof: by `noumenalProduct_split_witness` applied to N with
    the witness M and the projection equalities. -/
lemma eq_of_proj_eq {A B : L.Sys}
    (hd : Disjoint A B) (M N : L.Noumenal (A ⊔ B))
    (hA : L.noumenalProj (le_sup_left : A ≤ A ⊔ B) M
            = L.noumenalProj (le_sup_left : A ≤ A ⊔ B) N)
    (hB : L.noumenalProj (le_sup_right : B ≤ A ⊔ B) M
            = L.noumenalProj (le_sup_right : B ≤ A ⊔ B) N) :
    M = N := by
  -- M = noumenalProduct hd (π_A N) (π_B N) ⟨M, hA, hB⟩ by witness-split.
  -- N = noumenalProduct hd (π_A N) (π_B N) ⟨N, rfl, rfl⟩ by the split axiom.
  -- The two values differ only in the existence proof, which is a Prop.
  have hM_to_N :
      L.noumenalProduct hd
          (L.noumenalProj (le_sup_left : A ≤ A ⊔ B) N)
          (L.noumenalProj (le_sup_right : B ≤ A ⊔ B) N)
          ⟨M, hA, hB⟩
        = M := L.noumenalProduct_split_witness hd
                  (L.noumenalProj (le_sup_left : A ≤ A ⊔ B) N)
                  (L.noumenalProj (le_sup_right : B ≤ A ⊔ B) N)
                  M hA hB
  have hN_split :
      L.noumenalProduct hd
          (L.noumenalProj (le_sup_left : A ≤ A ⊔ B) N)
          (L.noumenalProj (le_sup_right : B ≤ A ⊔ B) N)
          ⟨N, rfl, rfl⟩
        = N := L.noumenalProduct_split hd N
  -- Both `noumenalProduct …` LHS terms share the first three arguments
  -- (modulo proof irrelevance on the existence witness).  Equate
  -- them by `congr`.
  have heq : L.noumenalProduct hd
              (L.noumenalProj (le_sup_left : A ≤ A ⊔ B) N)
              (L.noumenalProj (le_sup_right : B ≤ A ⊔ B) N)
              ⟨M, hA, hB⟩
            = L.noumenalProduct hd
              (L.noumenalProj (le_sup_left : A ≤ A ⊔ B) N)
              (L.noumenalProj (le_sup_right : B ≤ A ⊔ B) N)
              ⟨N, rfl, rfl⟩ := by
    congr 1
  exact hM_to_N.symm.trans (heq.trans hN_split)

/-! ## 2.  Composition and identity laws for `transProduct`
    (paper Theorems 3.8, 3.9 — axioms 4.6.3 and 4.6.4). -/

/-- **Paper Theorem 3.8** (composition law for `×` of
    transformations):
    `(V_A × V_B) (U_A × U_B) = (V_A U_A) × (V_B U_B)`.

    Proved by `noumenal_faithful`: it suffices to verify both
    sides act identically on every `N_AB ∈ Noumenal (A ⊔ B)`,
    using `transProduct_action` and the noumenal action's
    `act_mul`. -/
theorem transProduct_mul_of_LR
    {A B : L.Sys} (hd : Disjoint A B)
    (U_A V_A : L.Trans A) (U_B V_B : L.Trans B) :
    L.transProduct hd V_A V_B * L.transProduct hd U_A U_B
      = L.transProduct hd (V_A * U_A) (V_B * U_B) := by
  -- Use faithfulness of the noumenal action on `A ⊔ B`.
  apply L.noumenal_faithful (A ⊔ B)
  intro N_AB
  -- Set N_A := π_A N_AB, N_B := π_B N_AB.
  -- Build the "intermediate" noumenal state after one round of
  -- `transProduct hd U_A U_B`:
  --   M_AB := (U_A × U_B) · N_AB
  -- Its projections, by `noumenalProj_*_transProduct`, are
  --   π_A M_AB = U_A · N_A, π_B M_AB = U_B · N_B.
  -- Then the LHS acts as
  --   (V_A × V_B) · M_AB
  -- whose A-projection is V_A · (U_A · N_A) = (V_A * U_A) · N_A
  -- by noumenal_action.act_mul.
  -- The RHS acts as
  --   (V_A * U_A × V_B * U_B) · N_AB
  -- whose A-projection is (V_A * U_A) · N_A.
  -- Both sides therefore have the same A-projection (and
  -- analogously the same B-projection).  Since both sides are
  -- determined by their joint projections (by
  -- `noumenalProduct_split`), they are equal.
  --
  -- Cleanest path: show direct equality on N_AB by
  -- 1. expanding LHS via act_mul + noumenalProj_*_transProduct,
  -- 2. expanding RHS via noumenalProj_*_transProduct,
  -- and 3. invoking `noumenalProduct_split` for both sides.
  --
  -- LHS = noumenalProduct (proj_A LHS') (proj_B LHS') ⟨LHS', rfl, rfl⟩
  -- RHS = noumenalProduct (proj_A RHS') (proj_B RHS') ⟨RHS', rfl, rfl⟩
  -- where projections agree, so by congr LHS = RHS.
  set N_A : L.Noumenal A :=
    L.noumenalProj (le_sup_left : A ≤ A ⊔ B) N_AB with hNA
  set N_B : L.Noumenal B :=
    L.noumenalProj (le_sup_right : B ≤ A ⊔ B) N_AB with hNB
  -- Reduce LHS using act_mul.
  have hLHS_step1 :
      (L.noumenalAction (A ⊔ B)).act
          (L.transProduct hd V_A V_B * L.transProduct hd U_A U_B) N_AB
        = (L.noumenalAction (A ⊔ B)).act (L.transProduct hd V_A V_B)
            ((L.noumenalAction (A ⊔ B)).act (L.transProduct hd U_A U_B) N_AB) :=
    (L.noumenalAction (A ⊔ B)).act_mul _ _ _
  -- Use noumenal_faithful at level A on the lifted (full) statement.
  -- Actually, we already used noumenal_faithful at A ⊔ B; the goal
  -- now is to show the two sides act equally on N_AB.
  -- We close via `noumenalProduct_split`.
  --
  -- LHS_N := (V × V) · ((U × U) · N_AB)
  -- RHS_N := (V·U × V·U) · N_AB
  --
  -- Show LHS_N = RHS_N by showing both equal
  -- `noumenalProduct hd ((V·U)·N_A) ((V·U)·N_B) ⟨LHS_N, ?, ?⟩`.
  --
  -- Concretely we proceed by:
  rw [hLHS_step1]
  -- New goal:
  --   (V × V) · ((U × U) · N_AB) = (V·U × V·U) · N_AB
  -- Apply `noumenalProduct_split` on both sides to express each as a
  -- product of its projections, then show the projections are equal.
  --
  -- For BOTH sides, the projections are computed via
  -- `noumenalProj_left_transProduct` and `…_right_…`:
  --   π_A LHS_N = V_A · (U_A · N_A)
  --   π_B LHS_N = V_B · (U_B · N_B)
  --   π_A RHS_N = (V_A * U_A) · N_A
  --   π_B RHS_N = (V_B * U_B) · N_B
  -- The two pairs of projections agree by `noumenalAction.act_mul`.
  --
  -- So:
  --   LHS_N = noumenalProduct (π_A LHS_N) (π_B LHS_N) ⟨LHS_N, rfl, rfl⟩
  --         = noumenalProduct (π_A RHS_N) (π_B RHS_N) ⟨LHS_N, hp1, hp2⟩
  --         where hp1 : π_A LHS_N = π_A RHS_N, hp2 : π_B LHS_N = π_B RHS_N.
  -- By proof irrelevance, this equals
  --         noumenalProduct (π_A RHS_N) (π_B RHS_N) ⟨RHS_N, rfl, rfl⟩
  --         = RHS_N.
  --
  -- Let's compute the projection identities.
  set LHS_N : L.Noumenal (A ⊔ B) :=
    (L.noumenalAction (A ⊔ B)).act (L.transProduct hd V_A V_B)
      ((L.noumenalAction (A ⊔ B)).act (L.transProduct hd U_A U_B) N_AB)
    with hLN_def
  set RHS_N : L.Noumenal (A ⊔ B) :=
    (L.noumenalAction (A ⊔ B)).act (L.transProduct hd (V_A * U_A) (V_B * U_B)) N_AB
    with hRN_def
  -- π_A LHS_N = V_A · (U_A · N_A) = (V_A * U_A) · N_A
  have h_pi_A_L :
      L.noumenalProj (le_sup_left : A ≤ A ⊔ B) LHS_N
        = (L.noumenalAction A).act (V_A * U_A) N_A := by
    simp only [hLN_def]
    rw [L.noumenalProj_left_transProduct hd V_A V_B,
        L.noumenalProj_left_transProduct hd U_A U_B,
        ← (L.noumenalAction A).act_mul]
  -- π_B LHS_N = (V_B * U_B) · N_B
  have h_pi_B_L :
      L.noumenalProj (le_sup_right : B ≤ A ⊔ B) LHS_N
        = (L.noumenalAction B).act (V_B * U_B) N_B := by
    simp only [hLN_def]
    rw [L.noumenalProj_right_transProduct hd V_A V_B,
        L.noumenalProj_right_transProduct hd U_A U_B,
        ← (L.noumenalAction B).act_mul]
  -- π_A RHS_N = (V_A * U_A) · N_A
  have h_pi_A_R :
      L.noumenalProj (le_sup_left : A ≤ A ⊔ B) RHS_N
        = (L.noumenalAction A).act (V_A * U_A) N_A := by
    simp only [hRN_def]
    rw [L.noumenalProj_left_transProduct hd]
  -- π_B RHS_N = (V_B * U_B) · N_B
  have h_pi_B_R :
      L.noumenalProj (le_sup_right : B ≤ A ⊔ B) RHS_N
        = (L.noumenalAction B).act (V_B * U_B) N_B := by
    simp only [hRN_def]
    rw [L.noumenalProj_right_transProduct hd]
  -- Apply `eq_of_proj_eq` since the projections of LHS_N and RHS_N agree.
  exact L.eq_of_proj_eq hd LHS_N RHS_N (by rw [h_pi_A_L, h_pi_A_R])
        (by rw [h_pi_B_L, h_pi_B_R])

/-- **Paper Theorem 3.9** (identity law for `×`):
    `1 × 1 = 1`. -/
theorem transProduct_one_of_LR
    {A B : L.Sys} (hd : Disjoint A B) :
    L.transProduct hd (1 : L.Trans A) (1 : L.Trans B)
      = (1 : L.Trans (A ⊔ B)) := by
  apply L.noumenal_faithful (A ⊔ B)
  intro N_AB
  -- Both sides act as the identity on N_AB:
  --   LHS · N_AB = (1 × 1) · N_AB; by noumenalProj_*_transProduct,
  --     π_A LHS_N = 1 · (π_A N_AB) = π_A N_AB, similarly π_B.
  --     So LHS_N has the same projections as N_AB, hence equals N_AB
  --     by noumenalProduct_split + congr on the existence proof.
  --   RHS · N_AB = 1 · N_AB = N_AB.
  rw [(L.noumenalAction (A ⊔ B)).act_one N_AB]
  -- Now show (1 × 1) · N_AB = N_AB.
  set LHS_N : L.Noumenal (A ⊔ B) :=
    (L.noumenalAction (A ⊔ B)).act
      (L.transProduct hd (1 : L.Trans A) (1 : L.Trans B)) N_AB
    with hLN_def
  -- π_A LHS_N = 1 · π_A N_AB = π_A N_AB
  have h_pi_A :
      L.noumenalProj (le_sup_left : A ≤ A ⊔ B) LHS_N
        = L.noumenalProj (le_sup_left : A ≤ A ⊔ B) N_AB := by
    simp only [hLN_def]
    rw [L.noumenalProj_left_transProduct hd]
    rw [(L.noumenalAction A).act_one]
  have h_pi_B :
      L.noumenalProj (le_sup_right : B ≤ A ⊔ B) LHS_N
        = L.noumenalProj (le_sup_right : B ≤ A ⊔ B) N_AB := by
    simp only [hLN_def]
    rw [L.noumenalProj_right_transProduct hd]
    rw [(L.noumenalAction B).act_one]
  exact L.eq_of_proj_eq hd LHS_N N_AB h_pi_A h_pi_B

/-! ## 3.  No-signalling principle (paper Theorem 3.12, axiom 4.6.1) -/

/-- **Paper Theorem 3.12 (no-signalling principle).**

    The phenomenal projection commutes with the product
    transformation:

      π_A^phen ((U × V) · ρ_AB) = U · π_A^phen ρ_AB.

    The proof is a three-step chase:
      1. Lift `ρ_AB = ϕ(N_AB)` via `epi_surjective`.
      2. `(U × V) · ρ_AB = ϕ((U × V) ⋆ N_AB)` by `epi.intertwines`.
      3. `π_A^phen (ϕ(N')) = ϕ(π_A^noum N')` by `proj_epi_compat`.
      4. `π_A^noum ((U × V) ⋆ N_AB) = U ⋆ π_A^noum N_AB`
         by `noumenalProj_left_transProduct`.
      5. Pull `ϕ` back across `π_A^noum` via `proj_epi_compat` again
         (in reverse) and apply `epi.intertwines` (in reverse) to
         recover `U · π_A^phen ρ_AB`. -/
theorem no_signalling_of_LR
    {A B : L.Sys} (hd : Disjoint A B)
    (U : L.Trans A) (V : L.Trans B) (ρ : L.Phenomenal (A ⊔ B)) :
    L.phenomenalProj (le_sup_left : A ≤ A ⊔ B)
        ((L.phenomenalAction (A ⊔ B)).act (L.transProduct hd U V) ρ)
      = (L.phenomenalAction A).act U
          (L.phenomenalProj (le_sup_left : A ≤ A ⊔ B) ρ) := by
  -- Step 1: lift ρ to a noumenal state.
  obtain ⟨N_AB, hN_AB⟩ := L.epi_surjective (A ⊔ B) ρ
  subst hN_AB
  -- Goal: π_A_phen ((U×V) · ϕ(N_AB)) = U · π_A_phen ϕ(N_AB)
  -- Step 2: (U×V) · ϕ(N_AB) = ϕ((U×V) ⋆ N_AB) by epi.intertwines.
  rw [← (L.epi (A ⊔ B)).intertwines (L.transProduct hd U V) N_AB]
  -- Goal: π_A_phen (ϕ((U×V) ⋆ N_AB)) = U · π_A_phen (ϕ N_AB)
  -- Step 3: π_A_phen ∘ ϕ = ϕ ∘ π_A_noum  on both sides.
  rw [L.proj_epi_compat (le_sup_left : A ≤ A ⊔ B)
        ((L.noumenalAction (A ⊔ B)).act (L.transProduct hd U V) N_AB)]
  rw [L.proj_epi_compat (le_sup_left : A ≤ A ⊔ B) N_AB]
  -- Goal: ϕ(π_A_noum ((U×V) ⋆ N_AB)) = U · ϕ(π_A_noum N_AB)
  -- Step 4: π_A_noum ∘ (U×V) ⋆ = U ⋆ ∘ π_A_noum (noumenal no-signalling).
  rw [L.noumenalProj_left_transProduct hd U V N_AB]
  -- Goal: ϕ(U ⋆ π_A_noum N_AB) = U · ϕ(π_A_noum N_AB)
  -- Step 5: epi.intertwines (forward direction).
  rw [(L.epi A).intertwines]

/-- Right-side analog of `no_signalling_of_LR`. -/
theorem no_signalling_right_of_LR
    {A B : L.Sys} (hd : Disjoint A B)
    (U : L.Trans A) (V : L.Trans B) (ρ : L.Phenomenal (A ⊔ B)) :
    L.phenomenalProj (le_sup_right : B ≤ A ⊔ B)
        ((L.phenomenalAction (A ⊔ B)).act (L.transProduct hd U V) ρ)
      = (L.phenomenalAction B).act V
          (L.phenomenalProj (le_sup_right : B ≤ A ⊔ B) ρ) := by
  obtain ⟨N_AB, hN_AB⟩ := L.epi_surjective (A ⊔ B) ρ
  subst hN_AB
  rw [← (L.epi (A ⊔ B)).intertwines (L.transProduct hd U V) N_AB]
  rw [L.proj_epi_compat (le_sup_right : B ≤ A ⊔ B)
        ((L.noumenalAction (A ⊔ B)).act (L.transProduct hd U V) N_AB)]
  rw [L.proj_epi_compat (le_sup_right : B ≤ A ⊔ B) N_AB]
  rw [L.noumenalProj_right_transProduct hd U V N_AB]
  rw [(L.epi B).intertwines]

/-! ## 4.  The forgetful map: every LR theory has a NS shadow. -/

/-- **Theorem (easy direction, paper Section 4 intro + Theorem 3.12).**

    Every `LocalRealisticTheory` admits a `NoSignallingTheory`
    shadow.  The shadow is constructed by forgetting the noumenal
    layer and inheriting all phenomenal data from `L`. -/
theorem hasNoSignallingShadow_holds (L : LocalRealisticTheory) :
    L.HasNoSignallingShadow := by
  refine ⟨{
    Sys := L.Sys
    latticeSys := L.latticeSys
    Phenomenal := L.Phenomenal
    phenomenal_nonempty := L.phenomenal_nonempty
    Trans := L.Trans
    monoidTrans := L.monoidTrans
    phenomenalAction := L.phenomenalAction
    phenomenalProj := @L.phenomenalProj
    phenomenalProj_surjective := @L.phenomenalProj_surjective
    phenomenalProj_comp := @L.phenomenalProj_comp
    transProduct := @L.transProduct
    no_signalling := no_signalling_of_LR L
    no_signalling_right := no_signalling_right_of_LR L
    transProduct_mul := transProduct_mul_of_LR L
    transProduct_one := transProduct_one_of_LR L
  }, ?_⟩
  -- Discharge `IsNoSignallingShadow`.
  refine ⟨rfl, ?_⟩
  refine ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end LocalRealisticTheory

end UnifiedTheory.LayerC.LocalRealisticAxioms
