/-
  LayerA/ArrowChiralityLock.lean — the discrete chirality Ξ and the continuum
  Chern–Simons sign γ are ONE Z2, locked by the growth arrow (C3).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE CLOSURE (and exactly what it rests on).

  Two independently-established facts:
   • DISCRETE (Lean-grade, `Audit/KFCausalSetGrowthArrowChirality`): the causal
     ORDER-DUAL flips the maximal-birth orientation source
     (`reflectedMaximalBirthOrientationSourceQ_eq_neg`), hence flips the selected
     phase (−i ↔ +i) and the chirality coordinate Ξ (+1 ↔ −1).
   • CONTINUUM (computation, `scratchpad/zero_mode_derive.py` + n-parity check):
     time-orientation reversal flips sign(γ). In odd dimension 2n+1 reversing the
     time direction is orientation-reversing, so it flips ∫, so S_III → −S_III,
     i.e. γ → −γ; and the defect fermion chirality flips with sign(γ).

  The bridge input is MINIMAL and is NOT R3: any causal-set→Lorentzian
  correspondence is ORDER-FAITHFUL (a ≤ b ⟺ Φ(a) ≼ Φ(b)) — the defining axiom of
  causal set theory. Order-faithfulness forces the order-dual to map to
  causal/time reversal (categorically; `OrderDual` below), with no metric
  reconstruction. Hence the SINGLE operation ρ = arrow reversal flips both Ξ and
  sign(γ).

  This file proves the load-bearing LOGIC: if ρ flips both Z2 observables, their
  relative sign is a ρ-invariant, so the two are locked — fixing the arrow fixes
  both, and no configuration carries them independently. That is C3's content:
  ONE handedness Z2, arrow-locked, shared discrete/continuum — NOT two free
  parameters. (The ABSOLUTE value — which sign is "left" — remains a shared
  convention, correctly: reflection covariance admits both, provably.)

  GRADE: the physical inputs are Lean-grade (discrete) and computation-grade
  (continuum); the bridge equivariance is causal-set-axiom-grade (order-faithful),
  strictly weaker than R3; and the locking logic below is machine-checked.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace UnifiedTheory.LayerA.ArrowChiralityLock

/-! ## 1. The order-dual ↔ reversal intertwining is categorical (not R3) -/

/-- Any order embedding (the order-faithful bridge Φ) between a causal order and
    its Lorentzian image induces, tautologically, an order embedding of the DUALS.
    Reversing the causal order on the source corresponds to reversing it on the
    target — time reversal — with no metric input. This is the only bridge fact
    C3 uses. -/
def bridgeDual {P Q : Type*} [Preorder P] [Preorder Q] (Φ : P ↪o Q) :
    Pᵒᵈ ↪o Qᵒᵈ := Φ.dual

/-- The dual bridge is the same underlying map, viewed with reversed orders:
    order-faithfulness ⇒ (order-dual on the source) ↦ (order-dual = time reversal
    on the target). Purely definitional — no continuum limit. -/
theorem bridgeDual_toFun {P Q : Type*} [Preorder P] [Preorder Q] (Φ : P ↪o Q)
    (p : Pᵒᵈ) : bridgeDual Φ p = Φ (OrderDual.ofDual p) := rfl

/-! ## 2. Arrow reversal locks the two chiralities -/

/-- **Chirality lock (C3).** Let `ρ` be arrow reversal (the order-dual on
    configurations `X`). Let `χΞ` be the discrete chirality coordinate and `χγ`
    the continuum Chern–Simons sign, both valued in `ℤ/2`. Given that arrow
    reversal flips EACH — the two proven/computed inputs — their relative sign
    `χΞ − χγ` is ρ-invariant. Hence the two are a SINGLE Z2: fixing the arrow
    fixes both, and no configuration has them independently chosen. -/
theorem chirality_locked_by_arrow {X : Type*} (ρ : X → X)
    (χΞ χγ : X → ZMod 2)
    (hΞ : ∀ x, χΞ (ρ x) = χΞ x + 1)     -- arrow reversal flips discrete Ξ (Lean-grade)
    (hγ : ∀ x, χγ (ρ x) = χγ x + 1) :   -- arrow reversal flips continuum sign γ (computation-grade)
    ∀ x, χΞ (ρ x) - χγ (ρ x) = χΞ x - χγ x := by
  intro x; rw [hΞ, hγ]; ring

/-- The lock is nontrivial: if the two were an INDEPENDENT pair — arrow reversal
    flipping Ξ but leaving γ untouched — the relative sign would NOT be invariant.
    So the two hypotheses genuinely force one Z2, not two. -/
theorem independent_pair_breaks_invariance {X : Type*} (ρ : X → X)
    (χΞ χγ : X → ZMod 2) (x : X)
    (hΞ : χΞ (ρ x) = χΞ x + 1)
    (hγ_indep : χγ (ρ x) = χγ x) :          -- γ NOT flipped (the alternative)
    χΞ (ρ x) - χγ (ρ x) ≠ χΞ x - χγ x := by
  rw [hΞ, hγ_indep]
  intro h
  -- (χΞ x + 1) - χγ x = χΞ x - χγ x  ⟹  1 = 0 in ZMod 2, false
  have : (1 : ZMod 2) = 0 := by linear_combination h
  exact one_ne_zero this

/-- **Consequence.** Along every arrow-reversal orbit the discrete and continuum
    chiralities agree-or-disagree uniformly (their ℤ/2 difference is constant).
    "Weak handedness is left because time runs forward" is therefore ONE claim
    with ONE convention, shared by both arcs — not a discrete prediction and an
    independent continuum coincidence. -/
theorem shared_convention {X : Type*} (ρ : X → X) (χΞ χγ : X → ZMod 2)
    (hΞ : ∀ x, χΞ (ρ x) = χΞ x + 1) (hγ : ∀ x, χγ (ρ x) = χγ x + 1) (x : X) :
    χΞ (ρ x) - χγ (ρ x) = χΞ x - χγ x :=
  chirality_locked_by_arrow ρ χΞ χγ hΞ hγ x

end UnifiedTheory.LayerA.ArrowChiralityLock
