/-
  LayerB/DevetakWinter.lean
  ─────────────────────────

  **The Devetak–Winter hashing bound** (Devetak–Winter 2005):

      D_→(ρ_AB)  ≥  I_c(A⟩B)_ρ  =  S(ρ_B) − S(ρ_AB).

  The *one-way distillable entanglement* `D_→` of a bipartite state
  `ρ_AB` is at least its **coherent information**

      I_c(A⟩B)_ρ  :=  S(ρ_B)  −  S(ρ_AB).

  The hashing protocol of Devetak and Winter achieves the rate
  `max(0, I_c)` — the *hashing rate*.  Concretely:

    • For a **pure** bipartite state, `S(ρ_AB) = 0`, so
      `I_c = S(ρ_B) = S(ρ_A)` = the *entropy of entanglement* — the
      pure-state distillable entanglement.
    • For a **product** state `ρ_A ⊗ ρ_B`, `S(ρ_AB) = S(ρ_A) + S(ρ_B)`,
      so `I_c = S(ρ_B) − S(ρ_A) − S(ρ_B) = −S(ρ_A) ≤ 0`: hashing gives
      `0`, consistent with no distillable entanglement.
    • For a **maximally entangled** state of local dimension `d`,
      `S(ρ_A) = log d` and `S(ρ_AB) = 0`, so `I_c = log d` (one ebit per
      Bell pair when `d = 2`).
    • For **separable** states, `I_c ≤ 0`, so `max(0, I_c) = 0` —
      consistent with bound entanglement.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS DEFINED (no sorry, no custom axioms)

    • `coherentInfo S_B S_AB := S_B − S_AB`
        — the state coherent information `I_c(A⟩B)` as a real scalar in
          terms of the marginal entropy `S_B` and joint entropy `S_AB`.
    • `hashingRate S_B S_AB := max 0 (coherentInfo S_B S_AB)`
        — the Devetak–Winter hashing rate.

  WHAT IS PROVEN (no sorry, no custom axioms) — UNCONDITIONAL ALGEBRA

    • `hashingRate_nonneg`            : `0 ≤ hashingRate`.
    • `hashingRate_ge_coherentInfo`   : `coherentInfo ≤ hashingRate`
                                        (the achievable rate is at least
                                         the coherent information).
    • `coherentInfo_pure`             : pure state (`S_AB = 0`) gives
                                        `I_c = S_A` = entropy of
                                        entanglement.
    • `coherentInfo_product`          : product state gives `I_c = −S_A`.
    • `coherentInfo_product_nonpos`   : product state with `S_A ≥ 0` gives
                                        `I_c ≤ 0`.
    • `hashingRate_product_eq_zero`   : product state with `S_A ≥ 0`
                                        gives hashing rate `0`.
    • `coherentInfo_maxEntangled`     : maximally entangled state gives
                                        `I_c = log d`.
    • `coherentInfo_pos_of_entangled` : `S_B > S_AB ⟹ I_c > 0`.
    • `hashingRate_eq_coherentInfo_of_pos`
                                      : when `I_c ≥ 0`,
                                        `hashingRate = I_c`.
    • `hashingRate_eq_zero_of_nonpos` : when `I_c ≤ 0`, `hashingRate = 0`.

  NAMED TARGETS (the achievability theorem, exposed as `Prop`)

    • `DevetakWinter_Target`          : `D_→ ≥ I_c` for the given data.
    • `Hashing_Achievability_Target`  : the hashing protocol achieves
                                        rate `max(0, I_c)`.
    • `devetak_winter_master`         : a bundle of the unconditional
                                        algebra, witnessing the targets'
                                        consistency.

  HONEST SCOPE
    – The achievability of `D_→ ≥ I_c` (Devetak–Winter 2005) is a deep
      coding theorem (random hashing on typical subspaces, one-way
      classical communication, decoupling).  We state it as a named
      `Prop` `DevetakWinter_Target`, parameterised by an abstract
      distillable-rate functional `D_→`, and the achievability claim
      `Hashing_Achievability_Target`.  We do **not** build the LOCC
      protocol or the asymptotic typicality machinery here.
    – Everything about the *coherent-information / hashing-rate algebra*
      (pure → `S_A`, product → `−S_A ≤ 0`, maxEnt → `log d`, hashing
      `≥ I_c`, hashing `≥ 0`) is proved **unconditionally** as real
      arithmetic.  These are the structurally load-bearing facts that
      make the hashing bound meaningful.

  Zero `sorry`, zero custom `axiom`, following the project's standing
  constraint.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.DevetakWinter

open scoped BigOperators

/-! ## 1. Coherent information `I_c(A⟩B) = S(B) − S(AB)` -/

/-- **Coherent information** `I_c(A⟩B)_ρ := S(ρ_B) − S(ρ_AB)`.

    Stated at the scalar level: given the marginal entropy `S_B` and the
    joint entropy `S_AB`, the coherent information is their difference.
    It can be negative (separable / classically-correlated states) or
    positive (entangled states). -/
noncomputable def coherentInfo (S_B S_AB : ℝ) : ℝ := S_B - S_AB

/-- **The Devetak–Winter hashing rate** `max(0, I_c(A⟩B))`: the rate the
    hashing protocol achieves.  It is always non-negative and equals the
    coherent information exactly when the latter is non-negative. -/
noncomputable def hashingRate (S_B S_AB : ℝ) : ℝ := max 0 (coherentInfo S_B S_AB)

/-! ## 2. Basic algebra of the hashing rate (unconditional) -/

/-- **The hashing rate is non-negative.**  `max 0 x ≥ 0` for any `x`. -/
theorem hashingRate_nonneg (S_B S_AB : ℝ) : 0 ≤ hashingRate S_B S_AB :=
  le_max_left _ _

/-- **The hashing rate dominates the coherent information.**

    `coherentInfo ≤ max 0 coherentInfo = hashingRate`.  This is the
    structural content of "the achievable hashing rate is at least the
    coherent information". -/
theorem hashingRate_ge_coherentInfo (S_B S_AB : ℝ) :
    coherentInfo S_B S_AB ≤ hashingRate S_B S_AB :=
  le_max_right _ _

/-- **When `I_c ≥ 0` the hashing rate equals the coherent information.** -/
theorem hashingRate_eq_coherentInfo_of_pos (S_B S_AB : ℝ)
    (h : 0 ≤ coherentInfo S_B S_AB) :
    hashingRate S_B S_AB = coherentInfo S_B S_AB :=
  max_eq_right h

/-- **When `I_c ≤ 0` the hashing rate is zero.** -/
theorem hashingRate_eq_zero_of_nonpos (S_B S_AB : ℝ)
    (h : coherentInfo S_B S_AB ≤ 0) :
    hashingRate S_B S_AB = 0 :=
  max_eq_left h

/-! ## 3. Pure states: `I_c = S_A` = entropy of entanglement

    For a pure bipartite state `|ψ⟩_AB`, the joint entropy vanishes
    (`S_AB = 0`), and the two marginals share their spectrum
    (Schmidt decomposition), so `S_A = S_B`.  Hence
    `I_c = S_B − 0 = S_B = S_A` — the *entropy of entanglement*. -/

/-- **Pure-state coherent information.**  When the joint entropy is zero
    (`S_AB = 0`), the coherent information equals the marginal entropy
    `S_A` (= `S_B` by Schmidt symmetry) — the *entropy of entanglement*. -/
theorem coherentInfo_pure (S_A : ℝ) : coherentInfo S_A 0 = S_A := by
  unfold coherentInfo; ring

/-- **Pure-state hashing rate** equals the entropy of entanglement when
    the latter is non-negative (which it always is for a von Neumann
    entropy). -/
theorem hashingRate_pure (S_A : ℝ) (h : 0 ≤ S_A) :
    hashingRate S_A 0 = S_A := by
  unfold hashingRate
  rw [coherentInfo_pure]
  exact max_eq_right h

/-! ## 4. Product states: `I_c = −S_A ≤ 0`

    For a product state `ρ_AB = ρ_A ⊗ ρ_B`, the joint entropy is additive
    `S_AB = S_A + S_B`, so
    `I_c = S_B − (S_A + S_B) = −S_A ≤ 0`.  Hashing therefore gives `0`,
    consistent with a product state having no distillable entanglement. -/

/-- **Product-state coherent information.**  For `S_AB = S_A + S_B`,
    `I_c = −S_A`. -/
theorem coherentInfo_product (S_A S_B : ℝ) :
    coherentInfo S_B (S_A + S_B) = -S_A := by
  unfold coherentInfo; ring

/-- **Product-state coherent information is non-positive.**  With
    `S_A ≥ 0` (von Neumann entropy is non-negative), `I_c = −S_A ≤ 0`. -/
theorem coherentInfo_product_nonpos (S_A S_B : ℝ) (h : 0 ≤ S_A) :
    coherentInfo S_B (S_A + S_B) ≤ 0 := by
  rw [coherentInfo_product]
  linarith

/-- **Product-state hashing rate is zero.**  Hashing on a product state
    yields rate `0`, consistent with no distillable entanglement. -/
theorem hashingRate_product_eq_zero (S_A S_B : ℝ) (h : 0 ≤ S_A) :
    hashingRate S_B (S_A + S_B) = 0 :=
  hashingRate_eq_zero_of_nonpos S_B (S_A + S_B)
    (coherentInfo_product_nonpos S_A S_B h)

/-! ## 5. Maximally entangled states: `I_c = log d`

    For a maximally entangled state of local dimension `d`, the marginal
    on each side is the maximally mixed state `I/d`, with entropy
    `S_A = S_B = log d`; and the global state is pure, `S_AB = 0`.  Hence
    `I_c = log d − 0 = log d` (one ebit per Bell pair for `d = 2`,
    since `log 2 = 1` ebit). -/

/-- **Maximally entangled coherent information equals `log d`.**  With
    marginal entropy `log d` and pure joint state (`S_AB = 0`),
    `I_c = log d`. -/
theorem coherentInfo_maxEntangled (d : ℝ) :
    coherentInfo (Real.log d) 0 = Real.log d := by
  unfold coherentInfo; ring

/-- **Maximally entangled hashing rate equals `log d`** when `d ≥ 1`
    (so that `log d ≥ 0`).  This is the achievable distillation rate of a
    maximally entangled state — `log 2 = 1` ebit per Bell pair. -/
theorem hashingRate_maxEntangled (d : ℝ) (hd : 1 ≤ d) :
    hashingRate (Real.log d) 0 = Real.log d := by
  unfold hashingRate
  rw [coherentInfo_maxEntangled]
  exact max_eq_right (Real.log_nonneg hd)

/-! ## 6. Sign of the coherent information -/

/-- **Coherent information is positive when `S_B > S_AB`.**  This is the
    entangled regime, where the hashing bound delivers a strictly
    positive distillation rate. -/
theorem coherentInfo_pos_of_entangled (S_B S_AB : ℝ) (h : S_AB < S_B) :
    0 < coherentInfo S_B S_AB := by
  unfold coherentInfo; linarith

/-- **Coherent information is non-positive when `S_B ≤ S_AB`** (separable
    / classically-correlated regime). -/
theorem coherentInfo_nonpos_of_separable (S_B S_AB : ℝ) (h : S_B ≤ S_AB) :
    coherentInfo S_B S_AB ≤ 0 := by
  unfold coherentInfo; linarith

/-- **In the entangled regime the hashing rate equals the coherent
    information and is strictly positive.** -/
theorem hashingRate_eq_coherentInfo_of_entangled (S_B S_AB : ℝ)
    (h : S_AB < S_B) :
    hashingRate S_B S_AB = coherentInfo S_B S_AB :=
  hashingRate_eq_coherentInfo_of_pos S_B S_AB
    (le_of_lt (coherentInfo_pos_of_entangled S_B S_AB h))

/-! ## 7. The Devetak–Winter theorem as named targets

    The achievability `D_→(ρ) ≥ I_c(A⟩B)` (Devetak–Winter 2005) is a
    deep one-way LOCC coding theorem.  We expose it as a named `Prop`,
    parameterised by an abstract distillable-rate functional `D_arrow`
    and the entropies `S_B`, `S_AB` of the state.

    The achievability statement `Hashing_Achievability_Target` says the
    hashing protocol achieves the rate `max(0, I_c)` — i.e. `D_→` is at
    least the hashing rate, which (since the hashing rate ≥ I_c) implies
    the bound. -/

/-- **Devetak–Winter target.**  The one-way distillable entanglement
    `D_→` of a state with marginal entropy `S_B` and joint entropy `S_AB`
    is at least its coherent information `I_c(A⟩B) = S_B − S_AB`.

    Parameterised by an abstract rate functional `D_arrow : ℝ`
    (the value `D_→(ρ_AB)`). -/
def DevetakWinter_Target (D_arrow S_B S_AB : ℝ) : Prop :=
  coherentInfo S_B S_AB ≤ D_arrow

/-- **Hashing achievability target.**  The hashing protocol achieves the
    rate `max(0, I_c)`: the distillable entanglement is at least the
    hashing rate. -/
def Hashing_Achievability_Target (D_arrow S_B S_AB : ℝ) : Prop :=
  hashingRate S_B S_AB ≤ D_arrow

/-- **Achievability implies the hashing bound.**  If the hashing protocol
    achieves the rate `max(0, I_c)` (`Hashing_Achievability_Target`),
    then the Devetak–Winter bound `D_→ ≥ I_c` follows unconditionally,
    because the hashing rate dominates the coherent information.

    This is the one logical step the unconditional algebra DOES close:
    the achievability of the *hashing rate* is strictly stronger than the
    coherent-information bound, and the gap is exactly
    `hashingRate − coherentInfo = max(0, I_c) − I_c ≥ 0`. -/
theorem devetakWinter_of_hashing_achievability
    (D_arrow S_B S_AB : ℝ)
    (h : Hashing_Achievability_Target D_arrow S_B S_AB) :
    DevetakWinter_Target D_arrow S_B S_AB :=
  le_trans (hashingRate_ge_coherentInfo S_B S_AB) h

/-! ## 8. Master bundle -/

/-- **Master bundle of the Devetak–Winter hashing-bound algebra.**

    Packages the unconditional structural facts:
      • the hashing rate is non-negative;
      • the hashing rate dominates the coherent information;
      • achievability of the hashing rate implies the `D_→ ≥ I_c` bound.

    This witnesses that the named targets `DevetakWinter_Target` and
    `Hashing_Achievability_Target` are mutually consistent and that the
    weaker (coherent-information) bound is a consequence of the stronger
    (hashing-rate) achievability. -/
theorem devetak_winter_master (S_B S_AB : ℝ) :
    (0 ≤ hashingRate S_B S_AB) ∧
    (coherentInfo S_B S_AB ≤ hashingRate S_B S_AB) ∧
    (∀ D_arrow : ℝ, Hashing_Achievability_Target D_arrow S_B S_AB →
        DevetakWinter_Target D_arrow S_B S_AB) := by
  refine ⟨hashingRate_nonneg S_B S_AB, hashingRate_ge_coherentInfo S_B S_AB, ?_⟩
  intro D_arrow h
  exact devetakWinter_of_hashing_achievability D_arrow S_B S_AB h

/-- **Specialisation: the pure-state hashing bound.**  For a pure
    bipartite state (`S_AB = 0`) with non-negative entropy of
    entanglement `S_A`, any rate `D_→` achieving the hashing rate equals
    `D_→ ≥ S_A` — the pure-state distillable entanglement is the entropy
    of entanglement. -/
theorem devetak_winter_pure (D_arrow S_A : ℝ)
    (h : Hashing_Achievability_Target D_arrow S_A 0) :
    S_A ≤ D_arrow := by
  have hb : DevetakWinter_Target D_arrow S_A 0 :=
    devetakWinter_of_hashing_achievability D_arrow S_A 0 h
  rw [DevetakWinter_Target, coherentInfo_pure] at hb
  exact hb

end UnifiedTheory.LayerB.DevetakWinter
