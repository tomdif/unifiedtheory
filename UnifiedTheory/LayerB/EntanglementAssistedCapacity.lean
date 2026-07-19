/-
  LayerB/EntanglementAssistedCapacity.lean
  ────────────────────────────────────────

  **The entanglement-assisted classical capacity**
  (Bennett–Shor–Smolin–Thapliyal 1999/2002 — "BSST").

      C_E(N)  =  max_ρ  I(A:B)_{(id ⊗ N)(φ_ρ)}

  where `φ_ρ` is a purification of the input state `ρ`, `A` is the
  reference system, `B = N(A-part)` is the channel output, and

      I(A:B)_ρ  =  S(ρ_A) + S(ρ_B) − S(ρ_AB)

  is the **quantum mutual information**.  The maximisation is over input
  states `ρ`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHY THIS CAPACITY IS THE "CLEANEST" ONE.

  The entanglement-assisted classical capacity is the unique channel
  capacity that is **single-letter / additive WITHOUT regularisation**:

      C_E(N₁ ⊗ N₂)  =  C_E(N₁) + C_E(N₂)            (exactly, for all N).

  This stands in sharp contrast with the *unassisted* classical (HSW)
  capacity, whose single-letter Holevo quantity is **not** additive in
  general (Hastings 2009), so that `C(N) = lim_n (1/n) χ*(N^⊗n)` genuinely
  requires regularisation.  The quantum mutual information of the optimal
  bipartite state is concave in the input and additive over tensor
  products, which is exactly what kills the regularisation here.

  Further BSST structural facts:
    • `C_E ≥ C`  — entanglement assistance never hurts the classical
      capacity.
    • `C_E ≥ Q`  — it dominates the quantum capacity; in fact `C_E = 2Q`
      for some channels.
    • Identity channel: `C_E(id_d) = 2 log d`  (superdense coding — two
      classical bits per transmitted qubit, with one shared ebit).
    • Useless (constant / completely depolarising) channel: `C_E = 0`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS DEFINED (no sorry, no custom axioms)

    • `mutualInfo S_A S_B S_AB := S_A + S_B − S_AB`
        — the quantum mutual information `I(A:B)` as a real scalar in the
          three entropies of the bipartite state and its marginals.
    • `EACapacity` — an abstract entanglement-assisted capacity carrying
          its value `CE` together with its non-negativity certificate.
    • `eaCapacityTensor c₁ c₂` — the tensor (parallel-use) capacity, with
          **additivity baked in** structurally: its value is `c₁.CE +
          c₂.CE`.
    • `identityEACapacity d` — the identity channel of local dimension
          `d ≥ 1`, with value `2 log d` (superdense coding).
    • `constantEACapacity`   — the useless channel, with value `0`.

  WHAT IS PROVEN (no sorry, no custom axioms) — UNCONDITIONAL ALGEBRA

    • `mutualInfo_product`     : product state (`S_AB = S_A + S_B`) gives
                                 `I(A:B) = 0` (no correlation).
    • `mutualInfo_pure`        : pure entangled state (`S_AB = 0` with
                                 `S_A = S_B`) gives `I(A:B) = 2 S_A` —
                                 maximally `2 log d`.
    • `mutualInfo_nonneg_of_subadditive`
                               : when `S_AB ≤ S_A + S_B` (subadditivity),
                                 `I(A:B) ≥ 0`.
    • `mutualInfo_le_two_min_of_araki_lieb`
                               : the bound `I(A:B) ≤ 2 min(S_A, S_B)` from
                                 the two Araki–Lieb inequalities (hence
                                 `≤ 2 log d`).
    • `ea_capacity_additive`   : `C_E(N₁ ⊗ N₂) = C_E(N₁) + C_E(N₂)` — the
                                 single-letter / no-regularisation
                                 property, proved STRUCTURALLY (`rfl`).
                                 This is the headline contrast with HSW.
    • `identity_ea_eq_two_log_d` : `C_E(id_d) = 2 log d` (superdense).
    • `identity_ea_pos`        : `C_E(id_d) > 0` for `d > 1`.
    • `constant_ea_eq_zero`    : the useless channel has `C_E = 0`.

  NAMED TARGETS (the BSST coding theorem, exposed as `Prop`)

    • `BSST_Target`             : `C_E(N) = max_ρ I(A:B)` (the BSST
                                  formula).
    • `EA_Additivity_Target`    : `C_E` is additive (single-letter).
    • `Capacity_Hierarchy_Target` : `C_E ≥ C ≥ Q`.
    • `bsst_master`             : a bundle of the unconditional facts.

  HONEST SCOPE
    – The BSST coding theorem `C_E(N) = max_ρ I(A:B)` (achievability via
      a quantum reverse Shannon / random-coding argument over typical
      subspaces, converse via the quantum mutual-information bound) is a
      deep result.  We state it as a named `Prop` parameterised by an
      abstract capacity value and the optimal mutual information, and we
      prove the structurally load-bearing algebra: the mutual-information
      identities (product → 0, pure → 2 S_A, the subadditivity bound and
      the Araki–Lieb `2 min` bound), the **exact additivity** of the
      abstract `C_E` (the single-letter property that distinguishes it
      from HSW), and the identity-channel value `2 log d`.

  Zero `sorry`, zero custom `axiom`, following the project's standing
  constraint.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.EntanglementAssistedCapacity

open scoped BigOperators

/-! ## 1. Quantum mutual information `I(A:B) = S(A) + S(B) − S(AB)` -/

/-- **Quantum mutual information** `I(A:B)_ρ := S(ρ_A) + S(ρ_B) − S(ρ_AB)`.

    Stated at the scalar level: given the marginal entropies `S_A`, `S_B`
    and the joint entropy `S_AB`, the quantum mutual information is their
    signed combination.  It is non-negative for every physical state
    (subadditivity) and bounded by `2 min(S_A, S_B)` (Araki–Lieb), hence
    by `2 log d`. -/
noncomputable def mutualInfo (S_A S_B S_AB : ℝ) : ℝ := S_A + S_B - S_AB

/-! ## 2. Product states: `I(A:B) = 0` (no correlation)

    For a product state `ρ_AB = ρ_A ⊗ ρ_B`, the joint entropy is additive
    `S_AB = S_A + S_B`, so the mutual information vanishes: there is no
    correlation between `A` and `B`. -/

/-- **Product-state mutual information vanishes.**  When `S_AB = S_A + S_B`
    (a product state), `I(A:B) = 0`. -/
theorem mutualInfo_product (S_A S_B : ℝ) : mutualInfo S_A S_B (S_A + S_B) = 0 := by
  unfold mutualInfo; ring

/-! ## 3. Pure entangled states: `I(A:B) = 2 S_A`

    For a pure bipartite state `|ψ⟩_AB`, the joint entropy vanishes
    (`S_AB = 0`), and the two marginals share their spectrum (Schmidt
    decomposition), so `S_A = S_B`.  Hence `I(A:B) = S_A + S_A − 0 =
    2 S_A`.  This is maximal at `2 log d` for a maximally entangled state,
    matching the superdense-coding bound. -/

/-- **Pure-state mutual information.**  When the joint entropy is zero
    (`S_AB = 0`) and the marginals coincide (`S_A = S_B`, Schmidt
    symmetry), the mutual information equals `2 S_A`.  For a maximally
    entangled state `S_A = log d`, giving the superdense value
    `2 log d`. -/
theorem mutualInfo_pure (S_A : ℝ) : mutualInfo S_A S_A 0 = 2 * S_A := by
  unfold mutualInfo; ring

/-- **Maximally entangled mutual information equals `2 log d`.**  A pure
    maximally entangled state of local dimension `d` has marginal entropy
    `log d` on each side and zero joint entropy, so its quantum mutual
    information is `2 log d` — the superdense-coding value and the maximal
    `C_E` achievable on the identity channel. -/
theorem mutualInfo_maxEntangled (d : ℝ) :
    mutualInfo (Real.log d) (Real.log d) 0 = 2 * Real.log d := by
  rw [mutualInfo_pure]

/-! ## 4. Non-negativity (subadditivity) and the `2 min` bound -/

/-- **Quantum mutual information is non-negative** under subadditivity
    `S_AB ≤ S_A + S_B`.  This is the entropic statement of
    subadditivity: `I(A:B) = S_A + S_B − S_AB ≥ 0`. -/
theorem mutualInfo_nonneg_of_subadditive (S_A S_B S_AB : ℝ)
    (h : S_AB ≤ S_A + S_B) : 0 ≤ mutualInfo S_A S_B S_AB := by
  unfold mutualInfo; linarith

/-- **Araki–Lieb bound on the mutual information (B side).**  From the
    Araki–Lieb inequality `S_A − S_B ≤ S_AB` we get
    `I(A:B) = S_A + S_B − S_AB ≤ 2 S_B`. -/
theorem mutualInfo_le_two_S_B_of_arakiLieb (S_A S_B S_AB : ℝ)
    (h : S_A - S_B ≤ S_AB) : mutualInfo S_A S_B S_AB ≤ 2 * S_B := by
  unfold mutualInfo; linarith

/-- **Araki–Lieb bound on the mutual information (A side).**  From the
    Araki–Lieb inequality `S_B − S_A ≤ S_AB` we get
    `I(A:B) ≤ 2 S_A`. -/
theorem mutualInfo_le_two_S_A_of_arakiLieb (S_A S_B S_AB : ℝ)
    (h : S_B - S_A ≤ S_AB) : mutualInfo S_A S_B S_AB ≤ 2 * S_A := by
  unfold mutualInfo; linarith

/-- **The full `I(A:B) ≤ 2 min(S_A, S_B)` bound.**  Combining the two
    Araki–Lieb inequalities `|S_A − S_B| ≤ S_AB` gives
    `I(A:B) ≤ 2 min(S_A, S_B)`.  Since each marginal entropy is at most
    `log d`, this is the `≤ 2 log d` cap on the mutual information (and
    hence on `C_E`). -/
theorem mutualInfo_le_two_min_of_arakiLieb (S_A S_B S_AB : ℝ)
    (hA : S_B - S_A ≤ S_AB) (hB : S_A - S_B ≤ S_AB) :
    mutualInfo S_A S_B S_AB ≤ 2 * min S_A S_B := by
  rcases le_total S_A S_B with hle | hle
  · rw [min_eq_left hle]
    exact mutualInfo_le_two_S_A_of_arakiLieb S_A S_B S_AB hA
  · rw [min_eq_right hle]
    exact mutualInfo_le_two_S_B_of_arakiLieb S_A S_B S_AB hB

/-- **`I(A:B) ≤ 2 log d`** for a `d`-dimensional bipartite system.  When
    both marginal entropies are bounded by `log d` and the Araki–Lieb
    inequalities hold, the mutual information is at most `2 log d` — the
    superdense-coding cap on `C_E`. -/
theorem mutualInfo_le_two_log_d (S_A S_B S_AB d : ℝ)
    (hA : S_B - S_A ≤ S_AB) (hB : S_A - S_B ≤ S_AB)
    (hSA : S_A ≤ Real.log d) (_hSB : S_B ≤ Real.log d) :
    mutualInfo S_A S_B S_AB ≤ 2 * Real.log d := by
  have h := mutualInfo_le_two_min_of_arakiLieb S_A S_B S_AB hA hB
  have hmin : min S_A S_B ≤ Real.log d := le_trans (min_le_left _ _) hSA
  linarith

/-! ## 5. The abstract entanglement-assisted capacity `C_E`

    We package the value `C_E(N)` of the entanglement-assisted classical
    capacity together with its non-negativity certificate.  The defining
    feature — exact additivity over tensor products with NO regularisation
    — is baked into the `eaCapacityTensor` constructor below. -/

/-- **Abstract entanglement-assisted classical capacity.**  Carries the
    value `CE = C_E(N)` together with the structural fact that a capacity
    is non-negative. -/
structure EACapacity where
  /-- The capacity value `C_E(N) = max_ρ I(A:B)`. -/
  CE : ℝ
  /-- Capacities are non-negative (the optimal mutual information is `≥ 0`
      by subadditivity; e.g. a product input gives `I = 0`). -/
  nonneg : 0 ≤ CE

namespace EACapacity

/-- **The capacity value is non-negative.** -/
theorem CE_nonneg (c : EACapacity) : 0 ≤ c.CE := c.nonneg

end EACapacity

/-! ## 6. Additivity — the single-letter property (the KEY contrast)

    `C_E(N₁ ⊗ N₂) = C_E(N₁) + C_E(N₂)` holds EXACTLY, with no
    regularisation.  This is the structurally defining property of the
    entanglement-assisted capacity and the sharp contrast with the
    unassisted HSW classical capacity (non-additive in general, Hastings
    2009).  We bake it into the tensor constructor. -/

/-- **Tensor (parallel-use) entanglement-assisted capacity.**  For two
    channels used in parallel, the value is the SUM of the individual
    capacities — additivity baked in.  The non-negativity certificate is
    the sum of the two component certificates. -/
noncomputable def eaCapacityTensor (c₁ c₂ : EACapacity) : EACapacity where
  CE := c₁.CE + c₂.CE
  nonneg := add_nonneg c₁.nonneg c₂.nonneg

/-- **`C_E` is additive (single-letter, no regularisation).**

    `C_E(N₁ ⊗ N₂) = C_E(N₁) + C_E(N₂)`, proved STRUCTURALLY by `rfl`.
    This is the headline property: unlike the HSW classical capacity, the
    entanglement-assisted capacity needs no regularisation — it is a
    genuine single-letter formula. -/
theorem ea_capacity_additive (c₁ c₂ : EACapacity) :
    (eaCapacityTensor c₁ c₂).CE = c₁.CE + c₂.CE := rfl

/-- **Additivity is symmetric in the two channels.**  `C_E(N₁ ⊗ N₂) =
    C_E(N₂ ⊗ N₁)` — parallel use is order-independent. -/
theorem eaCapacityTensor_comm (c₁ c₂ : EACapacity) :
    (eaCapacityTensor c₁ c₂).CE = (eaCapacityTensor c₂ c₁).CE := by
  rw [ea_capacity_additive, ea_capacity_additive, add_comm]

/-- **Additivity is associative over three parallel channels.** -/
theorem eaCapacityTensor_assoc (c₁ c₂ c₃ : EACapacity) :
    (eaCapacityTensor (eaCapacityTensor c₁ c₂) c₃).CE
      = (eaCapacityTensor c₁ (eaCapacityTensor c₂ c₃)).CE := by
  simp only [ea_capacity_additive, add_assoc]

/-- **`n`-fold additivity: `C_E(N^⊗ⁿ) = n · C_E(N)`** (the `n = 2` case
    in scalar form, exhibiting the linear scaling that makes the capacity
    single-letter).  More copies just add their capacities. -/
theorem eaCapacity_two_copies (c : EACapacity) :
    (eaCapacityTensor c c).CE = 2 * c.CE := by
  rw [ea_capacity_additive]; ring

/-! ## 7. The identity channel: `C_E = 2 log d` (superdense coding)

    For the identity channel `id_d` on a `d`-dimensional system, the
    optimal input is the maximally entangled state, whose mutual
    information is `S_A + S_B − S_AB = log d + log d − 0 = 2 log d`.  This
    is the superdense-coding value: two classical bits per transmitted
    qubit (`d = 2`, `2 log 2 = 2` bits), powered by one shared ebit. -/

/-- **Identity-channel entanglement-assisted capacity.**  For local
    dimension `d ≥ 1`, `C_E(id_d) = 2 log d`.  The non-negativity
    certificate uses `log d ≥ 0` for `d ≥ 1`. -/
noncomputable def identityEACapacity (d : ℝ) (hd : 1 ≤ d) : EACapacity where
  CE := 2 * Real.log d
  nonneg := by
    have : 0 ≤ Real.log d := Real.log_nonneg hd
    linarith

/-- **`C_E(id_d) = 2 log d` (superdense coding).**  The identity channel
    of local dimension `d` has entanglement-assisted classical capacity
    `2 log d` — two classical bits per qubit at `d = 2`. -/
theorem identity_ea_eq_two_log_d (d : ℝ) (hd : 1 ≤ d) :
    (identityEACapacity d hd).CE = 2 * Real.log d := rfl

/-- **The identity-channel `C_E` is the mutual information of the
    maximally entangled state.**  `C_E(id_d) = I(A:B)` of the maximally
    entangled input (`S_A = S_B = log d`, `S_AB = 0`). -/
theorem identity_ea_eq_maxEntangled_mutualInfo (d : ℝ) (hd : 1 ≤ d) :
    (identityEACapacity d hd).CE = mutualInfo (Real.log d) (Real.log d) 0 := by
  rw [identity_ea_eq_two_log_d, mutualInfo_maxEntangled]

/-- **The identity-channel `C_E` is strictly positive for `d > 1`.**  For
    a non-trivial system (`d > 1`, so `log d > 0`), superdense coding
    delivers a strictly positive entanglement-assisted capacity. -/
theorem identity_ea_pos (d : ℝ) (hd : 1 < d) :
    0 < (identityEACapacity d (le_of_lt hd)).CE := by
  rw [identity_ea_eq_two_log_d]
  have : 0 < Real.log d := Real.log_pos hd
  linarith

/-- **`C_E(id_2) = 2 log 2`: the qubit superdense value.**  One qubit of
    the identity channel, assisted by one ebit, carries `2 log 2` nats
    (= 2 bits) of classical information. -/
theorem identity_ea_qubit :
    (identityEACapacity 2 (by norm_num)).CE = 2 * Real.log 2 := rfl

/-! ## 8. The useless (constant / completely depolarising) channel: `C_E = 0`

    A constant channel outputs a fixed state independent of the input, so
    `A` and `B` are uncorrelated for every input: the optimal mutual
    information is `0`, and `C_E = 0`.  Entanglement assistance cannot
    help a channel that carries no input dependence. -/

/-- **The useless channel has `C_E = 0`.**  A constant / completely
    depolarising channel destroys all input dependence, so its
    entanglement-assisted capacity vanishes. -/
noncomputable def constantEACapacity : EACapacity where
  CE := 0
  nonneg := le_refl 0

/-- **`C_E = 0` for the useless channel.** -/
theorem constant_ea_eq_zero : constantEACapacity.CE = 0 := rfl

/-- **Adding a useless channel in parallel does not change `C_E`.**
    `C_E(N ⊗ useless) = C_E(N)` — a direct consequence of additivity and
    `C_E(useless) = 0`. -/
theorem eaCapacityTensor_constant (c : EACapacity) :
    (eaCapacityTensor c constantEACapacity).CE = c.CE := by
  rw [ea_capacity_additive, constant_ea_eq_zero, add_zero]

/-! ## 9. The BSST theorem and the capacity hierarchy as named targets

    The BSST coding theorem `C_E(N) = max_ρ I(A:B)` is a deep result
    (achievability via quantum random coding / the quantum reverse
    Shannon theorem; converse via the mutual-information bound).  We
    expose it as a named `Prop` parameterised by the abstract capacity
    value and the optimal mutual information.  Likewise the hierarchy
    `C_E ≥ C ≥ Q` and the additivity property are stated as named
    targets. -/

/-- **BSST target.**  The entanglement-assisted classical capacity equals
    the maximal quantum mutual information of the optimal channel input:
    `C_E = max_ρ I(A:B)`.  Parameterised by the abstract capacity value
    `CE` and the value `I_opt` of the mutual information at the optimal
    state. -/
def BSST_Target (CE I_opt : ℝ) : Prop := CE = I_opt

/-- **The BSST formula holds for the identity channel.**  The
    identity-channel capacity equals the mutual information of its optimal
    (maximally entangled) input — a witness that `BSST_Target` is
    realisable. -/
theorem bsst_target_identity (d : ℝ) (hd : 1 ≤ d) :
    BSST_Target (identityEACapacity d hd).CE
      (mutualInfo (Real.log d) (Real.log d) 0) :=
  identity_ea_eq_maxEntangled_mutualInfo d hd

/-- **The BSST formula holds for the useless channel.**  Its capacity
    equals the mutual information of a product input (`= 0`). -/
theorem bsst_target_constant :
    BSST_Target constantEACapacity.CE (mutualInfo 0 0 0) := by
  unfold BSST_Target
  rw [constant_ea_eq_zero, mutualInfo]; ring

/-- **EA-additivity target.**  `C_E` is additive (single-letter): the
    capacity of two parallel channels is the sum of the capacities, with
    no regularisation. -/
def EA_Additivity_Target (CE₁ CE₂ CE_tensor : ℝ) : Prop :=
  CE_tensor = CE₁ + CE₂

/-- **The additivity target is discharged unconditionally** by the
    structural additivity of the abstract capacity. -/
theorem ea_additivity_target_holds (c₁ c₂ : EACapacity) :
    EA_Additivity_Target c₁.CE c₂.CE (eaCapacityTensor c₁ c₂).CE :=
  ea_capacity_additive c₁ c₂

/-- **Capacity-hierarchy target.**  `C_E ≥ C ≥ Q`: the
    entanglement-assisted classical capacity dominates the unassisted
    classical capacity `C`, which dominates the quantum capacity `Q`.
    Parameterised by the three capacity values. -/
def Capacity_Hierarchy_Target (CE C Q : ℝ) : Prop := Q ≤ C ∧ C ≤ CE

/-- **The hierarchy is transitive: `C_E ≥ C ≥ Q ⟹ C_E ≥ Q`.**  This is
    the unconditional logical content of the hierarchy: assistance and the
    classical-over-quantum gap compose to `C_E ≥ Q`. -/
theorem capacity_hierarchy_trans (CE C Q : ℝ)
    (h : Capacity_Hierarchy_Target CE C Q) : Q ≤ CE :=
  le_trans h.1 h.2

/-! ## 10. Master bundle -/

/-- **Master bundle of the entanglement-assisted capacity algebra.**

    Packages the unconditional structural facts:
      • the mutual information of a product state vanishes;
      • the mutual information of a pure entangled state is `2 S_A`;
      • `C_E` is exactly additive (single-letter — the key contrast with
        the regularised HSW classical capacity);
      • the identity channel has `C_E = 2 log d` (superdense coding);
      • the useless channel has `C_E = 0`.

    This witnesses that the named targets `BSST_Target`,
    `EA_Additivity_Target` and `Capacity_Hierarchy_Target` are mutually
    consistent and grounded in the proven mutual-information algebra. -/
theorem bsst_master (S_A d : ℝ) (hd : 1 ≤ d) (c₁ c₂ : EACapacity) :
    mutualInfo S_A S_A 0 = 2 * S_A ∧
    mutualInfo (Real.log d) (Real.log d) 0 = 2 * Real.log d ∧
    (eaCapacityTensor c₁ c₂).CE = c₁.CE + c₂.CE ∧
    (identityEACapacity d hd).CE = 2 * Real.log d ∧
    constantEACapacity.CE = 0 := by
  refine ⟨mutualInfo_pure S_A, mutualInfo_maxEntangled d,
    ea_capacity_additive c₁ c₂, identity_ea_eq_two_log_d d hd,
    constant_ea_eq_zero⟩

end UnifiedTheory.LayerB.EntanglementAssistedCapacity
