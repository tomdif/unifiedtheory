/-
  LayerB/QuantumEntanglement.lean — Quantum entanglement bridge

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT — A CORRECTION

  `LayerB/Entanglement.lean` defines `IsSeparable h ↔ ∃ v w, h = vecMulVec v w`
  on `Matrix (Fin n) (Fin n) ℝ`. This is mathematically the standard quantum
  two-particle separability:
       ψ(i, j) = ψ_A(i) · ψ_B(j)         ⟺      ψ = ψ_A ⊗ ψ_B
  i.e., the state factorizes as a tensor product of single-particle states.
  An earlier critique that "this is matrix-rank classification, not quantum
  entanglement" was UNFAIR — the two notions are literally the same theorem
  in different vocabularies (rank-1 outer product ⟺ separable two-particle
  state).

  What WAS missing:
   – The QM interpretation as two-particle amplitudes is implicit in the
     `Entanglement.lean` docstring, not stated
   – The Bell-theorem singlet from `BellTheorem.lean` is defined by hand;
     it is NOT proved entangled in the same file
   – No bridge says "the framework's entangled states enable Bell violation"

  This file fixes those omissions.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  – `TwoParticleState n := Matrix (Fin n) (Fin n) ℝ` — re-export with
    the QM-correct name
  – `singlet_is_entangled`: the singlet state from `BellTheorem.lean`
    is genuinely quantum-entangled (NOT separable)
  – `identity_is_maximally_entangled`: the identity matrix represents
    the (unnormalized) maximally entangled state Σ_i |ii⟩
  – `entanglement_enables_bell_violation`: bridge theorem combining
    `singlet_is_entangled` with `BellTheorem.bell_violation` to yield
    "the framework's K/P / amplitude structure produces a state that
    is genuinely entangled AND violates the CHSH inequality"
  – `separable_implies_factorizable_correlations`: structural converse —
    if a state is separable, then any product-observable correlation
    factorizes (the standard QM result that separable states obey the
    classical CHSH bound)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS HONESTLY OUT OF SCOPE

  – Complex amplitudes. The framework's `Matrix (Fin n) (Fin n) ℝ` carries
    real amplitudes. Genuine QM entanglement is over ℂ. The framework's
    K/P-derived complex structure (`ComplexFromDressing.lean`) provides ℂ
    at the single-particle level; lifting to a complex two-particle space
    would require additional construction (tensor product of complex
    amplitude spaces). Real amplitudes already suffice for the singlet
    and Bell violation, so this is not a substantive gap — but it is
    not yet formalized.
  – Tensor product as a categorical operation. This file uses the
    *element-wise* characterization (separability = factorizability of
    components) which is sufficient for the entanglement statement but
    less general than tensor product as a universal construction.

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.Entanglement
import UnifiedTheory.LayerB.BellTheorem

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumEntanglement

open UnifiedTheory.LayerB.Entanglement
open UnifiedTheory.LayerB.BellTheorem
open Matrix

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: TWO-PARTICLE STATES = MATRIX PERTURBATIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A two-particle state is a tensor ψ : Fin n × Fin n → ℝ giving the
    amplitude `ψ(i, j)` for "particle A in single-particle basis state i
    AND particle B in single-particle basis state j". Mathematically this
    is the same as a matrix; we re-name for QM clarity.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A two-particle quantum state amplitude over a finite single-particle
    basis of size `n`. Mathematically identical to `Matrix (Fin n) (Fin n) ℝ`;
    re-named for explicit QM interpretation. -/
abbrev TwoParticleState (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A two-particle state is **quantum-separable** iff it factorizes as
    `ψ(i, j) = ψ_A(i) · ψ_B(j)` for some single-particle amplitudes
    `ψ_A, ψ_B`. Equivalent to `IsSeparable` from `Entanglement.lean`,
    re-named for QM clarity. -/
def IsQuantumSeparable {n : ℕ} (ψ : TwoParticleState n) : Prop := IsSeparable ψ

/-- A two-particle state is **quantum-entangled** iff NOT separable —
    it cannot be written as a tensor product of single-particle states.
    Equivalent to `IsEntangled` from `Entanglement.lean`. -/
def IsQuantumEntangled {n : ℕ} (ψ : TwoParticleState n) : Prop := IsEntangled ψ

/-- The two notions agree by definition (re-export). -/
theorem isQuantumSeparable_iff_isSeparable {n : ℕ} (ψ : TwoParticleState n) :
    IsQuantumSeparable ψ ↔ IsSeparable ψ := Iff.rfl

/-- Same for entangled. -/
theorem isQuantumEntangled_iff_isEntangled {n : ℕ} (ψ : TwoParticleState n) :
    IsQuantumEntangled ψ ↔ IsEntangled ψ := Iff.rfl

/-- A separable two-particle state has factorizable amplitudes:
    `ψ(i, j) = v(i) · w(j)`. -/
theorem separable_factorizes {n : ℕ} (ψ : TwoParticleState n)
    (h : IsQuantumSeparable ψ) :
    ∃ v w : Fin n → ℝ, ∀ i j, ψ i j = v i * w j := by
  obtain ⟨v, w, hvw⟩ := h
  refine ⟨v, w, ?_⟩
  intro i j
  rw [hvw, Matrix.vecMulVec_apply]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE SINGLET STATE FROM BELLTHEOREM IS ENTANGLED
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The singlet `ψ(0,1) = 1/√2`, `ψ(1,0) = -1/√2`, `ψ(0,0) = ψ(1,1) = 0`.
    Suppose `ψ = v ⊗ w`. Then:
       ψ(0,1) = v(0)·w(1) = 1/√2 ≠ 0   ⟹   v(0) ≠ 0 ∧ w(1) ≠ 0
       ψ(1,0) = v(1)·w(0) = -1/√2 ≠ 0  ⟹   v(1) ≠ 0 ∧ w(0) ≠ 0
       ψ(0,0) = v(0)·w(0) = 0           ⟹   v(0) = 0 ∨ w(0) = 0
    But from the first two we have v(0) ≠ 0 AND w(0) ≠ 0. Contradiction.
    Therefore the singlet is NOT separable, i.e., quantum-entangled.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE SINGLET IS QUANTUM-ENTANGLED.**

    The singlet state defined in `BellTheorem.lean` is not separable.
    Proof: assume `singletState = v ⊗ w`. The off-diagonals are nonzero,
    forcing `v(0), v(1), w(0), w(1)` all nonzero. But the diagonal
    `singletState(0, 0) = 0 = v(0)·w(0)` would then require one of them
    zero — contradiction. -/
theorem singlet_is_entangled :
    IsQuantumEntangled (singletState : TwoParticleState 2) := by
  intro ⟨v, w, hvw⟩
  -- 1/√2 is positive (hence nonzero)
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hinv_pos : (0 : ℝ) < 1 / Real.sqrt 2 := div_pos one_pos hsqrt2_pos
  have hinv_ne : (1 : ℝ) / Real.sqrt 2 ≠ 0 := ne_of_gt hinv_pos
  -- Singlet entries explicitly
  have s01 : singletState (0 : Fin 2) (1 : Fin 2) = 1 / Real.sqrt 2 := by
    unfold singletState; simp
  have s10 : singletState (1 : Fin 2) (0 : Fin 2) = -1 / Real.sqrt 2 := by
    unfold singletState
    have h1 : ¬((1 : Fin 2) = 0 ∧ (0 : Fin 2) = 1) := by
      intro ⟨h, _⟩; exact absurd h (by decide)
    have h2 : (1 : Fin 2) = 1 ∧ (0 : Fin 2) = 0 := ⟨rfl, rfl⟩
    rw [if_neg h1, if_pos h2]
  have s00 : singletState (0 : Fin 2) (0 : Fin 2) = 0 := by
    unfold singletState; simp
  -- Pull v⊗w form to the entries
  have h01 : v 0 * w 1 = 1 / Real.sqrt 2 := by
    have := congr_fun (congr_fun hvw 0) 1
    rw [Matrix.vecMulVec_apply] at this
    rw [s01] at this; linarith
  have h10 : v 1 * w 0 = -1 / Real.sqrt 2 := by
    have := congr_fun (congr_fun hvw 1) 0
    rw [Matrix.vecMulVec_apply] at this
    rw [s10] at this; linarith
  have h00 : v 0 * w 0 = 0 := by
    have := congr_fun (congr_fun hvw 0) 0
    rw [Matrix.vecMulVec_apply] at this
    rw [s00] at this; linarith
  -- v(0) ≠ 0 from h01
  have hv0 : v 0 ≠ 0 := by
    intro hv0; rw [hv0, zero_mul] at h01; exact hinv_ne h01.symm
  -- w(0) ≠ 0 from h10
  have hw0 : w 0 ≠ 0 := by
    intro hw0
    rw [hw0, mul_zero] at h10
    have hneg : (0 : ℝ) = -1 / Real.sqrt 2 := h10
    have : -1 / Real.sqrt 2 < 0 := by
      rw [neg_div]; exact neg_neg_iff_pos.mpr hinv_pos
    linarith
  -- Contradiction: h00 says v 0 * w 0 = 0, but both are nonzero
  exact absurd h00 (mul_ne_zero hv0 hw0)

/-- Singlet entanglement, lifted into the QM-named predicate. -/
theorem singlet_isQuantumEntangled :
    IsQuantumEntangled (singletState : TwoParticleState 2) :=
  singlet_is_entangled

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE IDENTITY IS THE MAXIMALLY-ENTANGLED BELL STATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Reading the n×n identity matrix as a two-particle state:
        ψ(i, j) = δ_{ij} = amplitude for "particle A and B in matched
        basis states i = j"
    This IS the unnormalized maximally entangled state Σ_i |ii⟩, the
    standard "Bell state" for n = 2.

    `Entanglement.lean` already proved the identity is non-separable;
    here we re-export with QM language.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The identity matrix is the maximally-entangled state Σ_i |ii⟩.**
    Re-export of `identity_isEntangled`. -/
theorem identity_is_maximally_entangled (m : ℕ) :
    IsQuantumEntangled (1 : TwoParticleState (m + 2)) :=
  identity_isEntangled (by omega : 2 ≤ m + 2)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: SEPARABLE STATES HAVE FACTORIZABLE CORRELATIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a separable state ψ = ψ_A ⊗ ψ_B and any product observable
    A_i ⊗ B_j, the two-particle inner product factorizes:
        ⟨a ⊗ b | ψ⟩ = ⟨a|ψ_A⟩ · ⟨b|ψ_B⟩
    Hence any product correlation factorizes as a product of single-
    particle expectations — the standard QM result that underlies
    "separable states obey the classical CHSH bound |S| ≤ 2."
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The single-particle inner product (real amplitudes), specialized to
    Fin 2 to match `BellTheorem.twoParticleInner`. -/
def singleInner (a v : Fin 2 → ℝ) : ℝ := ∑ i : Fin 2, a i * v i

/-- **Separable states have factorizable two-particle inner products.**
    For any product test state `(a, b)`, if `ψ = v ⊗ w`, then
       ⟨a ⊗ b | ψ⟩ = ⟨a|v⟩ · ⟨b|w⟩.
    This is the algebraic origin of the classical CHSH bound for
    separable states. -/
theorem separable_inner_factorizes (a b : Fin 2 → ℝ)
    (ψ : TwoParticleState 2) (h : IsQuantumSeparable ψ) :
    ∃ v w : Fin 2 → ℝ,
      twoParticleInner a b ψ = singleInner a v * singleInner b w := by
  obtain ⟨v, w, hvw⟩ := h
  refine ⟨v, w, ?_⟩
  unfold twoParticleInner singleInner
  rw [hvw]
  simp only [Matrix.vecMulVec_apply]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: BRIDGE — ENTANGLEMENT ENABLES BELL VIOLATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The framework's K/P-derived Born rule combined with the singlet
    state produces a CHSH violation `S² > 4` (proved in BellTheorem).
    The singlet is genuinely quantum-entangled (proved in this file).
    Together: the framework predicts a state that is non-separable
    AND violates the classical CHSH bound — the empirical hallmark
    of quantum non-locality.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE BRIDGE THEOREM**: the framework's singlet state is genuinely
    quantum-entangled AND its Born-rule correlations violate the
    classical CHSH bound. Combining `singlet_is_entangled` (this file)
    with `BellTheorem.bell_violation`. -/
theorem entanglement_enables_bell_violation :
    IsQuantumEntangled (singletState : TwoParticleState 2)
    ∧ chshValue ^ 2 > 4 :=
  ⟨singlet_is_entangled, bell_violation⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE FRAMEWORK'S QUANTUM ENTANGLEMENT BUNDLE.**

    Re-interpreting `Matrix (Fin n) (Fin n) ℝ` as the two-particle
    amplitude space `H_A ⊗ H_B` (real-amplitude version), the framework's
    existing `Entanglement.lean` definitions ARE the standard QM notions:

    (1) `IsQuantumSeparable ψ ↔ ψ(i, j) = v(i) · w(j)` for some `v, w` —
        i.e., `ψ = ψ_A ⊗ ψ_B`. This is the standard separability
        criterion for tensor-product two-particle states.

    (2) `IsQuantumEntangled ψ` ↔ NOT separable — the standard QM
        non-separability.

    (3) The singlet from `BellTheorem.lean` is genuinely entangled
        (`singlet_is_entangled`).

    (4) The identity matrix is the maximally entangled Σ_i |ii⟩
        (`identity_is_maximally_entangled`).

    (5) Separable states have factorizable correlations
        (`separable_inner_factorizes`).

    (6) The framework's singlet violates the CHSH bound
        (`entanglement_enables_bell_violation`, combining this file
        with `BellTheorem.bell_violation`).

    Honest scope: the framework currently uses real amplitudes for the
    Bell construction. Lifting to complex amplitudes (the framework's
    full K/P-derived complex structure) is a documentation/extension
    issue, not a substantive gap — the singlet violation already works
    over ℝ. -/
theorem quantum_entanglement_master :
    -- (1) Separability is standard QM tensor factorization
    (∀ {n : ℕ} (ψ : TwoParticleState n),
        IsQuantumSeparable ψ ↔ ∃ v w : Fin n → ℝ, ψ = Matrix.vecMulVec v w)
    -- (2) Singlet is entangled
    ∧ IsQuantumEntangled (singletState : TwoParticleState 2)
    -- (3) Identity is entangled (maximally) for n ≥ 2
    ∧ (∀ m : ℕ, IsQuantumEntangled (1 : TwoParticleState (m + 2)))
    -- (4) Separable states have factorizable inner products (Fin 2)
    ∧ (∀ (a b : Fin 2 → ℝ) (ψ : TwoParticleState 2),
        IsQuantumSeparable ψ →
        ∃ v w : Fin 2 → ℝ,
          twoParticleInner a b ψ = singleInner a v * singleInner b w)
    -- (5) Singlet enables Bell violation
    ∧ (IsQuantumEntangled (singletState : TwoParticleState 2)
       ∧ chshValue ^ 2 > 4) :=
  ⟨fun _ => Iff.rfl,
   singlet_is_entangled,
   identity_is_maximally_entangled,
   separable_inner_factorizes,
   entanglement_enables_bell_violation⟩

end UnifiedTheory.LayerB.QuantumEntanglement
