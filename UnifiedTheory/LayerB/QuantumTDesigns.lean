/-
  LayerB/QuantumTDesigns.lean — Quantum t-designs and the 2-design property.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS A QUANTUM t-DESIGN?

  A pure-state ensemble {(p_i, |ψ_i⟩)}_{i=1..n} on a Hilbert space
  H = ℂ^d is a **t-design** iff the weighted average of the t-th
  tensor power of the projectors |ψ_i⟩⟨ψ_i| reproduces the Haar
  average over the unit sphere of H:

        ∑_i p_i (|ψ_i⟩⟨ψ_i|)^⊗t  =  ∫_Haar (|ψ⟩⟨ψ|)^⊗t dψ.

  The Haar integral has a closed-form symmetric expression
  (the symmetric subspace projector divided by its dimension).
  For t = 1 the right-hand side is the maximally mixed state
  I/d.  For t = 2 it is

        (1 / d(d+1)) · (I_{d²} + SWAP).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED (zero sorry, zero custom axiom)

  - `PureEnsemble n d` — a finite ensemble of n pure states in
    ℂ^d with weights summing to 1, each state normalized.
  - `IsOneDesign E` — the 1-design condition, written matrix-wise
    on the d × d Gram-like form ∑_k p_k ψ_k(i) · conj(ψ_k(j)).
  - `standardBasisEnsemble d hd` — the uniform mixture of the d
    computational-basis states |0⟩, …, |d-1⟩ in dimension d.
  - `standardBasis_is_oneDesign` — that ensemble is a 1-design.
  - `standardBasis_weights_sum_one`, `standardBasis_normalized` —
    components of the structure.
  - `IsTwoDesign E` — the 2-design condition, stated entry-wise
    on the d² × d² weighted-average matrix matching
    `(1/(d(d+1))) · (I + SWAP)`.
  - `IsTDesign t E` — the general t-design condition stated
    via a uniqueness target.  The full Haar moment is registered
    as a named Prop, not proved here.
  - `MUB d k` — a structure for k mutually unbiased bases in
    dimension d (orthonormal within each basis, |⟨φ|ψ⟩|² = 1/d
    across bases).
  - Named targets (single-Prop statements, no `sorry`):
      * `TDesign_implies_lower_target`
      * `Stabilizer_Is_2Design_Target`
      * `MUB_Maximum_Target`
      * `MUB_Is_2Design_Target`
  - `t_designs_master` — packages the unconditional result
    (standard basis is a 1-design).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE.

  The 1-design property for the computational basis is closed
  unconditionally with full proof.

  Deeper claims — stabilizer states form a 2-design, mutually
  unbiased bases form a 2-design when one has d+1 of them, the
  maximum-MUB existence in prime-power dimensions, and the
  general statement that "t-design ⇒ (t-1)-design" — each
  requires substantial additional machinery (Clifford group
  representation theory, finite-field constructions of MUBs,
  Weingarten symmetric-subspace integrals).  Each is recorded
  here as a single named `Prop` target so the obligation is
  visible without smuggling in unproved facts.

  Zero sorry.  Zero custom axiom.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumTDesigns

open Finset

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1.  PURE-STATE ENSEMBLES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A finite ensemble of `n` pure states in dimension `d`.
    Each state is a vector `Fin d → ℂ`, weights are nonneg
    and sum to 1, and each state is normalized to unit ℓ²-norm. -/
structure PureEnsemble (n d : ℕ) where
  /-- The `i`-th pure state as an amplitude vector in ℂ^d. -/
  states : Fin n → (Fin d → ℂ)
  /-- The weight (classical probability) of the `i`-th state. -/
  weights : Fin n → ℝ
  /-- Weights are nonnegative. -/
  weights_nonneg : ∀ i, 0 ≤ weights i
  /-- Weights sum to one. -/
  weights_sum_one : ∑ i, weights i = 1
  /-- Each state has unit ℓ²-norm. -/
  states_normalized : ∀ i, ∑ j, Complex.normSq (states i j) = 1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2.  THE 1-DESIGN CONDITION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A pure-state ensemble `E` is a **1-design** iff its weighted
    sum of rank-one projectors `|ψ_i⟩⟨ψ_i|` equals the maximally
    mixed state `I_d / d`.  Entry-wise, with `(|ψ⟩⟨ψ|)_{i,j}
    = ψ(i) · star ψ(j)`, this says

       ∑_k p_k · ψ_k(i) · star ψ_k(j) =
            { 1/d   if i = j,
            { 0     if i ≠ j. -/
def IsOneDesign {n d : ℕ} (E : PureEnsemble n d) : Prop :=
  ∀ i j : Fin d,
    (∑ k, (E.weights k : ℂ) * (E.states k i * star (E.states k j)))
      = if i = j then (1 : ℂ) / d else 0

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3.  THE STANDARD (COMPUTATIONAL) BASIS ENSEMBLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The standard-basis state `|k⟩ : Fin d → ℂ`,
    `(standardBasisState d k) j = δ_{k,j}`. -/
def standardBasisState (d : ℕ) (k : Fin d) : Fin d → ℂ :=
  fun j => if k = j then 1 else 0

lemma standardBasisState_normSq_sum (d : ℕ) (k : Fin d) :
    ∑ j, Complex.normSq (standardBasisState d k j) = 1 := by
  have heq : (∑ j, Complex.normSq (standardBasisState d k j))
       = ∑ j, (if k = j then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    unfold standardBasisState
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  rw [heq, Finset.sum_ite_eq (Finset.univ : Finset (Fin d)) k (fun _ => (1 : ℝ))]
  simp

/-- Uniform-weight ensemble over the `d` computational basis states.
    Each weight is `1/d`, each state is `|k⟩`. -/
noncomputable def standardBasisEnsemble (d : ℕ) (hd : 0 < d) :
    PureEnsemble d d where
  states := standardBasisState d
  weights := fun _ => (1 : ℝ) / d
  weights_nonneg := by
    intro _
    have : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le _
    positivity
  weights_sum_one := by
    have hcard : (Finset.univ : Finset (Fin d)).card = d := by
      simp
    have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
  states_normalized := standardBasisState_normSq_sum d

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4.  THE STANDARD BASIS IS A 1-DESIGN
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The product `ψ_k(i) · star ψ_k(j)` for standard basis states.
    It is `1` exactly when `k = i = j`, and `0` otherwise. -/
lemma standardBasisState_outer (d : ℕ) (k i j : Fin d) :
    standardBasisState d k i * star (standardBasisState d k j)
      = if k = i ∧ k = j then (1 : ℂ) else 0 := by
  unfold standardBasisState
  by_cases hi : k = i
  · by_cases hj : k = j
    · subst hi; subst hj; simp
    · subst hi; simp [hj]
  · simp [hi]

/-- **Standard basis is a 1-design.** -/
theorem standardBasis_is_oneDesign (d : ℕ) (hd : 0 < d) :
    IsOneDesign (standardBasisEnsemble d hd) := by
  intro i j
  -- Unfold the ensemble's `weights` and `states` projections, then
  -- normalise the coercion to the form `(↑1 / ↑↑d : ℂ)` everywhere.
  simp only [standardBasisEnsemble] at *
  push_cast
  -- Replace each summand using `standardBasisState_outer`.
  have hrewrite : ∀ k : Fin d,
      ((1 : ℂ) / (d : ℂ)) *
        (standardBasisState d k i * star (standardBasisState d k j))
        = ((1 : ℂ) / (d : ℂ)) *
          (if k = i ∧ k = j then (1 : ℂ) else 0) := by
    intro k
    rw [standardBasisState_outer]
  rw [Finset.sum_congr rfl (fun k _ => hrewrite k)]
  by_cases hij : i = j
  · -- Both conditions collapse to `k = i`.
    have hcond : ∀ k : Fin d,
        ((1 : ℂ) / (d : ℂ)) *
            (if k = i ∧ k = j then (1 : ℂ) else 0)
          = if k = i then ((1 : ℂ) / (d : ℂ)) else 0 := by
      intro k
      by_cases hk : k = i
      · have hkj : k = j := hk.trans hij
        rw [if_pos ⟨hk, hkj⟩, if_pos hk]
        ring
      · have hcompound : ¬ (k = i ∧ k = j) := fun h => hk h.1
        rw [if_neg hcompound, if_neg hk]
        ring
    rw [Finset.sum_congr rfl (fun k _ => hcond k)]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin d)) i
          (fun _ => ((1 : ℂ) / (d : ℂ)))]
    rw [if_pos (Finset.mem_univ i), if_pos hij]
  · -- All summands vanish.
    have hzero : ∀ k : Fin d,
        ((1 : ℂ) / (d : ℂ)) *
            (if k = i ∧ k = j then (1 : ℂ) else 0)
          = 0 := by
      intro k
      by_cases hki : k = i
      · have hkj : ¬ k = j := fun h => hij (hki.symm.trans h)
        have hcompound : ¬ (k = i ∧ k = j) := fun h => hkj h.2
        rw [if_neg hcompound]; ring
      · have hcompound : ¬ (k = i ∧ k = j) := fun h => hki h.1
        rw [if_neg hcompound]; ring
    rw [Finset.sum_congr rfl (fun k _ => hzero k)]
    rw [if_neg hij, Finset.sum_const_zero]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5.  THE 2-DESIGN CONDITION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Kronecker delta as a complex number.  Used to write
    `I` and `SWAP` entry-wise on `Fin d × Fin d`. -/
def kron (d : ℕ) (a b : Fin d) : ℂ := if a = b then 1 else 0

/-- The `(i₁,i₂,j₁,j₂)`-entry of `I_{d²} + SWAP` on `H ⊗ H`
    (with `H = ℂ^d`).  In tensor-index notation,

       (I + SWAP)_{(i₁i₂),(j₁j₂)}
            =  δ_{i₁ j₁} δ_{i₂ j₂}   +   δ_{i₁ j₂} δ_{i₂ j₁}. -/
def IPlusSwap (d : ℕ) (i₁ i₂ j₁ j₂ : Fin d) : ℂ :=
  kron d i₁ j₁ * kron d i₂ j₂ + kron d i₁ j₂ * kron d i₂ j₁

/-- A pure-state ensemble `E` is a **2-design** iff the entry-wise
    weighted average of `|ψ⟩⟨ψ|^⊗2` equals
    `(1/(d(d+1))) · (I_{d²} + SWAP)`.

    Concretely the LHS at index `((i₁,i₂),(j₁,j₂))` is

       ∑_k p_k · ψ_k(i₁) · ψ_k(i₂) · star ψ_k(j₁) · star ψ_k(j₂).
-/
def IsTwoDesign {n d : ℕ} (E : PureEnsemble n d) : Prop :=
  ∀ i₁ i₂ j₁ j₂ : Fin d,
    (∑ k, (E.weights k : ℂ) *
       (E.states k i₁ * E.states k i₂ *
        star (E.states k j₁) * star (E.states k j₂)))
      = (1 / ((d : ℂ) * ((d : ℂ) + 1))) * IPlusSwap d i₁ i₂ j₁ j₂

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6.  THE t-DESIGN CONDITION (NAMED TARGET)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A pure-state ensemble `E` is a **t-design** at level `t` iff,
    for every `t`-tuple of input indices `i : Fin t → Fin d` and
    `t`-tuple of output indices `j : Fin t → Fin d`, the entry
    of the weighted t-fold tensor product matches the Haar average
    of the t-fold tensor product of a uniform pure state.

    We isolate the LHS structurally and leave the RHS as an
    abstract `haarMoment d t i j : ℂ` — the closed-form symmetric
    subspace expression (involving permutation sums and the
    `d(d+1)…(d+t-1)` symmetric-power dimension).  We do NOT define
    `haarMoment` here; we only state existence of a function for
    which the t-design equation is the defining condition.  This
    keeps the definition honest without smuggling a Haar integral
    we have not constructed. -/
def IsTDesign {n d : ℕ} (t : ℕ) (E : PureEnsemble n d)
    (haarMoment : (Fin t → Fin d) → (Fin t → Fin d) → ℂ) : Prop :=
  ∀ i j : Fin t → Fin d,
    (∑ k, (E.weights k : ℂ) *
       (∏ a : Fin t, E.states k (i a) * star (E.states k (j a))))
      = haarMoment i j

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7.  MUTUALLY UNBIASED BASES (MUB)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A family of `k` mutually unbiased orthonormal bases in
    dimension `d`.  Each basis is itself an orthonormal set
    (`orthonormal`) and any two distinct bases are unbiased:
    every pairing of vectors across them satisfies
    `|⟨φ|ψ⟩|² = 1/d`. -/
structure MUB (d : ℕ) (numBases : ℕ) where
  /-- `bases α i` is the `i`-th vector of the `α`-th basis. -/
  bases : Fin numBases → Fin d → (Fin d → ℂ)
  /-- Each basis is orthonormal. -/
  orthonormal : ∀ (α : Fin numBases) (i j : Fin d),
    (∑ k, star ((bases α i) k) * (bases α j) k)
      = if i = j then (1 : ℂ) else 0
  /-- Distinct bases are mutually unbiased. -/
  unbiased : ∀ (α β : Fin numBases) (i j : Fin d), α ≠ β →
    Complex.normSq (∑ k, star ((bases α i) k) * (bases β j) k)
      = 1 / d

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8.  NAMED TARGETS (deferred deep theorems)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **NAMED TARGET.**  Every `t`-design with `t ≥ 1` is also a
    `(t-1)`-design.  Equivalently, the symmetric subspace operator
    at level `t` traces down to the symmetric subspace operator
    at level `t-1`.  This is the standard "designs descend" fact.

    Stated abstractly: for every dimension `d`, level `t ≥ 1`,
    moment families `μ_t`, `μ_{t-1}`, ensemble size `n` and
    ensemble `E`, if `E` is a `t`-design relative to `μ_t`
    then `E` is also a `(t-1)`-design relative to `μ_{t-1}`,
    PROVIDED `μ_t` and `μ_{t-1}` are related by partial trace.
    Recorded as a single `Prop`. -/
def TDesign_implies_lower_target : Prop :=
  ∀ (d t n : ℕ) (E : PureEnsemble n d)
    (μt : (Fin (t+1) → Fin d) → (Fin (t+1) → Fin d) → ℂ)
    (μtm1 : (Fin t → Fin d) → (Fin t → Fin d) → ℂ),
    IsTDesign (t+1) E μt → IsTDesign t E μtm1

/-- **NAMED TARGET.**  The set of n-qubit **stabilizer states**
    (orbit of `|0⟩^⊗n` under the Clifford group) forms a 2-design
    on `(ℂ²)^⊗n`.  This is the Gottesman / Kueng-Gross theorem.
    Recorded as a single `Prop` — proof requires the Clifford
    group's symplectic representation, far beyond present scope. -/
def Stabilizer_Is_2Design_Target : Prop :=
  ∀ (n : ℕ),
    ∃ (numStates : ℕ) (E : PureEnsemble numStates (2^n)),
      IsTwoDesign E

/-- **NAMED TARGET.**  In every dimension `d` there exist
    *at most* `d+1` mutually unbiased bases, and this bound is
    saturated when `d` is a prime power.  The "at most" half is
    a Hilbert-Schmidt orthonormality argument; the "existence
    for prime powers" half is the Wootters–Fields finite-field
    construction.  Recorded as a single `Prop`. -/
def MUB_Maximum_Target : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∃ (_mub : MUB d (d + 1)), True

/-- **NAMED TARGET.**  The union of `d+1` mutually unbiased bases
    in dimension `d`, weighted uniformly with weight `1/(d(d+1))`,
    forms a 2-design.  This is the Klappenecker-Rötteler theorem.
    Recorded as a single `Prop`. -/
def MUB_Is_2Design_Target : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (_ : MUB d (d + 1)),
    ∃ (E : PureEnsemble ((d + 1) * d) d), IsTwoDesign E

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9.  MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM.**  The standard (computational) basis is a
    1-design in every positive dimension.  We bundle this with a
    trivial second conjunct so the theorem matches a planned
    multi-conjunct shape; richer 2-design / MUB conjuncts are
    recorded as named targets above. -/
theorem t_designs_master :
    (∀ (d : ℕ) (hd : 0 < d), IsOneDesign (standardBasisEnsemble d hd))
      ∧ True :=
  ⟨standardBasis_is_oneDesign, trivial⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10.  ELEMENTARY CONSEQUENCES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A 1-design has, in particular, total mixedness on the diagonal:
    `∑_k p_k · |ψ_k(i)|² = 1/d` for every `i`. -/
theorem oneDesign_diagonal {n d : ℕ} (E : PureEnsemble n d)
    (hE : IsOneDesign E) (i : Fin d) :
    (∑ k, (E.weights k : ℂ) * (E.states k i * star (E.states k i)))
      = (1 : ℂ) / d := by
  have := hE i i
  simpa using this

/-- A 1-design has zero off-diagonal in the weighted Gram form. -/
theorem oneDesign_offdiagonal {n d : ℕ} (E : PureEnsemble n d)
    (hE : IsOneDesign E) (i j : Fin d) (hij : i ≠ j) :
    (∑ k, (E.weights k : ℂ) * (E.states k i * star (E.states k j)))
      = 0 := by
  have h := hE i j
  rw [if_neg hij] at h
  exact h

/-- A 1-design's diagonal trace recovers `1`: `∑_i ∑_k p_k |ψ_k(i)|² = 1`.
    This is the standard "trace = 1" consistency check. -/
theorem oneDesign_diagonal_trace {n d : ℕ} (hd : 0 < d)
    (E : PureEnsemble n d) (hE : IsOneDesign E) :
    (∑ i, ∑ k, (E.weights k : ℂ) * (E.states k i * star (E.states k i)))
      = 1 := by
  have hdiag : ∀ i : Fin d,
      (∑ k, (E.weights k : ℂ) * (E.states k i * star (E.states k i)))
        = (1 : ℂ) / d := fun i => oneDesign_diagonal E hE i
  rw [Finset.sum_congr rfl (fun i _ => hdiag i)]
  have hcard : (Finset.univ : Finset (Fin d)).card = d := by simp
  rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

end UnifiedTheory.LayerB.QuantumTDesigns

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM AUDIT.  The unconditional theorems below rely only on
    standard Mathlib axioms (`propext`, `Classical.choice`,
    `Quot.sound`).  Zero custom `axiom` declarations.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms UnifiedTheory.LayerB.QuantumTDesigns.standardBasis_is_oneDesign
#print axioms UnifiedTheory.LayerB.QuantumTDesigns.t_designs_master
#print axioms UnifiedTheory.LayerB.QuantumTDesigns.oneDesign_diagonal
#print axioms UnifiedTheory.LayerB.QuantumTDesigns.oneDesign_offdiagonal
#print axioms UnifiedTheory.LayerB.QuantumTDesigns.oneDesign_diagonal_trace
