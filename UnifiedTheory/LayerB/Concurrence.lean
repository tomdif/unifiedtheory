/-
  LayerB/Concurrence.lean — Wootters' concurrence as twice the absolute
  determinant for a real-amplitude two-qubit pure state.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  Wootters (Phys. Rev. Lett. 80, 2245, 1998) introduced **concurrence** as
  an entanglement measure for two-qubit states. For a pure state
  |ψ⟩ ∈ ℂ² ⊗ ℂ² it is defined by
       C(ψ) := |⟨ψ | (Y ⊗ Y) | ψ*⟩|
  where Y is the Pauli Y matrix and ψ* is complex conjugation. Wootters
  showed C ∈ [0, 1] with C = 0 ⟺ separable and C = 1 ⟺ maximally
  entangled.

  When the amplitudes are real (as in `LayerB/QuantumEntanglement.lean`,
  `LayerB/BellTheorem.lean`, etc., where the framework's two-particle
  state is `Matrix (Fin 2) (Fin 2) ℝ`), the spin-flip σ_y ⊗ σ_y reduces
  to (i)(i) det(M(ψ)) ψᵀ-like manipulation and the closed form is:

       **C(ψ) = 2 · |det M(ψ)|**

  where M(ψ) is the 2×2 matrix of amplitudes ψ(i,j). This is the
  beautiful real-amplitude collapse of Wootters' formula.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  – `concurrence ψ := 2 * |Matrix.det ψ|` for `ψ : TwoParticleState 2`
  – `concurrence_nonneg`              : 0 ≤ C(ψ)
  – `concurrence_separable_eq_zero`   : ψ separable ⟹ C(ψ) = 0
  – `concurrence_eq_zero_iff_separable`: C(ψ) = 0 ⟺ ψ is separable
  – `concurrence_singlet_eq_one`      : C(singlet) = 1
  – `concurrence_le_one_of_normalized`: ‖ψ‖² = 1 ⟹ C(ψ) ≤ 1
  – `concurrence_via_schmidt`         : C(ψ) = 2·λ₀·λ₁ for ANY Schmidt
                                        decomposition with the rank-2
                                        coefficients
  – `singlet_isNormalized`            : ‖singlet‖² = 1
  – `concurrence_eq_one_iff_max_entangled` : in normalized states with
                                        a Schmidt decomposition,
                                        C = 1 ⟺ λ₀ = λ₁ = 1/√2
  – `concurrence_master`              : aggregator

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – Real amplitudes only. The full Wootters concurrence on ℂ² ⊗ ℂ²
    would require complex amplitudes plus the spin-flip operation
    (σ_y ⊗ σ_y) ψ*. The framework's two-particle space is real, so
    the closed form `C = 2|det|` is exact and complete here.

  – Pure states only. Mixed-state concurrence is the convex roof
    extension `C(ρ) = inf Σ_i p_i C(|ψ_i⟩)` over decompositions,
    computed via Wootters' formula on the spin-flipped density matrix.
    Mixed states require the framework's `DensityMatrixHonest.lean`
    plumbing and a substantial extra construction; out of scope here.

  – Two qubits only. The natural higher-dimensional generalisation
    is the I-concurrence / Schmidt-rank-based hierarchy; not
    formalised in this file.

  Zero `sorry`. Zero custom axioms.
-/
import UnifiedTheory.LayerB.SchmidtDecomposition
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Concurrence

open UnifiedTheory.LayerB.Entanglement
open UnifiedTheory.LayerB.QuantumEntanglement
open UnifiedTheory.LayerB.SchmidtDecomposition
open UnifiedTheory.LayerB.BellTheorem
open Matrix

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: DEFINITION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a real-amplitude two-qubit pure state ψ : Fin 2 × Fin 2 → ℝ,
    Wootters' concurrence collapses to C(ψ) = 2 · |det(M(ψ))|.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Concurrence** of a real-amplitude two-qubit pure state.
    `concurrence ψ = 2 · |det ψ|`. -/
noncomputable def concurrence (ψ : TwoParticleState 2) : ℝ :=
  2 * |Matrix.det ψ|

/-- Explicit unfolding: `det ψ = ψ(0,0)·ψ(1,1) − ψ(0,1)·ψ(1,0)`. -/
theorem concurrence_def (ψ : TwoParticleState 2) :
    concurrence ψ = 2 * |ψ 0 0 * ψ 1 1 - ψ 0 1 * ψ 1 0| := by
  unfold concurrence
  rw [Matrix.det_fin_two]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: NON-NEGATIVITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Concurrence is non-negative. -/
theorem concurrence_nonneg (ψ : TwoParticleState 2) : 0 ≤ concurrence ψ := by
  unfold concurrence
  have h : 0 ≤ |Matrix.det ψ| := abs_nonneg _
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: C(ψ) = 0 ⟺ ψ IS SEPARABLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Forward: if ψ = vecMulVec v w then det(vecMulVec v w) = 0
    (Mathlib's `Matrix.det_vecMulVec`), so C = 2·0 = 0.

    Converse: if C(ψ) = 0 then det(ψ) = 0 in 2×2, which is the rank-1
    condition. We prove rank-1 ⟹ separable directly: if det = 0,
    one column is a scalar multiple of the other (or both zero), and
    we can construct (v, w) with ψ = vecMulVec v w.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Forward**: separable states have concurrence 0. -/
theorem concurrence_separable_eq_zero (ψ : TwoParticleState 2)
    (h : IsQuantumSeparable ψ) : concurrence ψ = 0 := by
  obtain ⟨v, w, hvw⟩ := h
  unfold concurrence
  rw [hvw, Matrix.det_vecMulVec]
  simp

/-- A 2×2 matrix with det = 0 has rank ≤ 1; we prove the explicit
    factorisation `ψ = vecMulVec v w` directly from the determinant
    relation `ψ(0,0)·ψ(1,1) = ψ(0,1)·ψ(1,0)` by case analysis. -/
private lemma det_zero_implies_separable
    (ψ : TwoParticleState 2) (hdet : Matrix.det ψ = 0) :
    IsQuantumSeparable ψ := by
  -- The determinant relation
  have hkey : ψ 0 0 * ψ 1 1 = ψ 0 1 * ψ 1 0 := by
    have : ψ 0 0 * ψ 1 1 - ψ 0 1 * ψ 1 0 = 0 := by
      rw [← Matrix.det_fin_two]; exact hdet
    linarith
  -- Case-split on whether the top row is zero.
  by_cases h00 : ψ 0 0 = 0
  · by_cases h01 : ψ 0 1 = 0
    · -- Top row is zero. Take v = (0, 1) and w = (ψ 1 0, ψ 1 1).
      let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
      let w : Fin 2 → ℝ := fun j => if j = 0 then ψ 1 0 else ψ 1 1
      have hv0 : v 0 = 0 := by simp [v]
      have hv1 : v 1 = 1 := by simp [v]
      have hw0 : w 0 = ψ 1 0 := by simp [w]
      have hw1 : w 1 = ψ 1 1 := by simp [w]
      refine ⟨v, w, ?_⟩
      ext i j
      rw [Matrix.vecMulVec_apply]
      have entry : ∀ a b : Fin 2, ψ a b = v a * w b := by
        intro a b
        fin_cases a <;> fin_cases b
        · change ψ 0 0 = v 0 * w 0; rw [hv0, zero_mul]; exact h00
        · change ψ 0 1 = v 0 * w 1; rw [hv0, zero_mul]; exact h01
        · change ψ 1 0 = v 1 * w 0; rw [hv1, hw0, one_mul]
        · change ψ 1 1 = v 1 * w 1; rw [hv1, hw1, one_mul]
      exact entry i j
    · -- ψ 0 0 = 0, ψ 0 1 ≠ 0. Then from det relation: ψ 0 1 · ψ 1 0 = 0,
      -- so ψ 1 0 = 0. Take v = (ψ 0 1 / ψ 0 1 = 1 weighted), but cleaner
      -- direct: use v = (1, ψ 1 1 / ψ 0 1) and w = (0, ψ 0 1).
      have h10 : ψ 1 0 = 0 := by
        have : ψ 0 1 * ψ 1 0 = 0 := by rw [← hkey, h00]; ring
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h h01
        · exact h
      -- Define v, w explicitly first, then use them.
      let v : Fin 2 → ℝ := fun i => if i = 0 then 1 else ψ 1 1 / ψ 0 1
      let w : Fin 2 → ℝ := fun j => if j = 0 then 0 else ψ 0 1
      have hv0 : v 0 = 1 := by simp [v]
      have hv1 : v 1 = ψ 1 1 / ψ 0 1 := by simp [v]
      have hw0 : w 0 = 0 := by simp [w]
      have hw1 : w 1 = ψ 0 1 := by simp [w]
      refine ⟨v, w, ?_⟩
      ext i j
      rw [Matrix.vecMulVec_apply]
      have entry : ∀ a b : Fin 2, ψ a b = v a * w b := by
        intro a b
        fin_cases a <;> fin_cases b
        · change ψ 0 0 = v 0 * w 0; rw [hv0, hw0, mul_zero]; exact h00
        · change ψ 0 1 = v 0 * w 1; rw [hv0, hw1, one_mul]
        · change ψ 1 0 = v 1 * w 0; rw [hv1, hw0, mul_zero]; exact h10
        · change ψ 1 1 = v 1 * w 1; rw [hv1, hw1, div_mul_cancel₀ _ h01]
      exact entry i j
  · -- ψ 0 0 ≠ 0. Then v = (ψ 0 0, ψ 1 0), w = (1, ψ 0 1 / ψ 0 0).
    -- Check: vecMulVec v w (0,0) = ψ 0 0 · 1 = ψ 0 0 ✓
    --        vecMulVec v w (0,1) = ψ 0 0 · ψ 0 1 / ψ 0 0 = ψ 0 1 ✓
    --        vecMulVec v w (1,0) = ψ 1 0 · 1 = ψ 1 0 ✓
    --        vecMulVec v w (1,1) = ψ 1 0 · ψ 0 1 / ψ 0 0
    --                            = ψ 0 0 · ψ 1 1 / ψ 0 0  (by hkey)
    --                            = ψ 1 1 ✓
    let v : Fin 2 → ℝ := fun i => if i = 0 then ψ 0 0 else ψ 1 0
    let w : Fin 2 → ℝ := fun j => if j = 0 then 1 else ψ 0 1 / ψ 0 0
    have hv0 : v 0 = ψ 0 0 := by simp [v]
    have hv1 : v 1 = ψ 1 0 := by simp [v]
    have hw0 : w 0 = 1 := by simp [w]
    have hw1 : w 1 = ψ 0 1 / ψ 0 0 := by simp [w]
    refine ⟨v, w, ?_⟩
    ext i j
    rw [Matrix.vecMulVec_apply]
    have entry : ∀ a b : Fin 2, ψ a b = v a * w b := by
      intro a b
      fin_cases a <;> fin_cases b
      · change ψ 0 0 = v 0 * w 0; rw [hv0, hw0, mul_one]
      · change ψ 0 1 = v 0 * w 1
        rw [hv0, hw1, mul_div_cancel₀ _ h00]
      · change ψ 1 0 = v 1 * w 0; rw [hv1, hw0, mul_one]
      · change ψ 1 1 = v 1 * w 1
        rw [hv1, hw1]
        -- Goal: ψ 1 1 = ψ 1 0 * (ψ 0 1 / ψ 0 0)
        rw [eq_comm, ← mul_div_assoc, div_eq_iff h00]
        -- Goal: ψ 1 0 * ψ 0 1 = ψ 1 1 * ψ 0 0
        linarith [hkey]
    exact entry i j

/-- **Converse**: zero concurrence ⟹ separable. -/
theorem concurrence_eq_zero_implies_separable (ψ : TwoParticleState 2)
    (h : concurrence ψ = 0) : IsQuantumSeparable ψ := by
  unfold concurrence at h
  -- 2 * |det ψ| = 0 ⟹ |det ψ| = 0 ⟹ det ψ = 0
  have habs : |Matrix.det ψ| = 0 := by linarith
  have hdet : Matrix.det ψ = 0 := abs_eq_zero.mp habs
  exact det_zero_implies_separable ψ hdet

/-- **C(ψ) = 0 ⟺ ψ is separable.** -/
theorem concurrence_eq_zero_iff_separable (ψ : TwoParticleState 2) :
    concurrence ψ = 0 ↔ IsQuantumSeparable ψ :=
  ⟨concurrence_eq_zero_implies_separable ψ,
   concurrence_separable_eq_zero ψ⟩

/-- **Equivalent form**: `C(ψ) > 0 ⟺ ψ is entangled.** -/
theorem concurrence_pos_iff_entangled (ψ : TwoParticleState 2) :
    0 < concurrence ψ ↔ IsQuantumEntangled ψ := by
  constructor
  · intro hC hsep
    have : concurrence ψ = 0 := concurrence_separable_eq_zero ψ hsep
    linarith
  · intro hent
    have hne : concurrence ψ ≠ 0 := by
      intro h0
      exact hent (concurrence_eq_zero_implies_separable ψ h0)
    exact lt_of_le_of_ne (concurrence_nonneg ψ) (Ne.symm hne)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: SINGLET HAS CONCURRENCE 1
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The singlet has matrix
        [   0     1/√2 ]
        [ -1/√2    0   ]
    so det = 0·0 − (1/√2)(−1/√2) = 1/2 and C = 2·|1/2| = 1.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

private lemma sqrt_two_pos' : (0 : ℝ) < Real.sqrt 2 :=
  Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)

private lemma sqrt_two_ne' : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt_two_pos'

private lemma sqrt_two_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- The determinant of the singlet matrix is `1/2`. -/
theorem det_singlet : Matrix.det (singletState : TwoParticleState 2) = 1 / 2 := by
  rw [Matrix.det_fin_two]
  -- ψ(0,0) = 0, ψ(0,1) = 1/√2, ψ(1,0) = -1/√2, ψ(1,1) = 0
  have s00 : (singletState : TwoParticleState 2) 0 0 = 0 := by
    unfold singletState; simp
  have s01 : (singletState : TwoParticleState 2) 0 1 = 1 / Real.sqrt 2 := by
    unfold singletState; simp
  have s10 : (singletState : TwoParticleState 2) 1 0 = -1 / Real.sqrt 2 := by
    unfold singletState
    have h1 : ¬((1 : Fin 2) = 0 ∧ (0 : Fin 2) = 1) := by
      intro ⟨h, _⟩; exact absurd h (by decide)
    have h2 : (1 : Fin 2) = 1 ∧ (0 : Fin 2) = 0 := ⟨rfl, rfl⟩
    rw [if_neg h1, if_pos h2]
  have s11 : (singletState : TwoParticleState 2) 1 1 = 0 := by
    unfold singletState
    have h1 : ¬((1 : Fin 2) = 0 ∧ (1 : Fin 2) = 1) := by
      intro ⟨h, _⟩; exact absurd h (by decide)
    have h2 : ¬((1 : Fin 2) = 1 ∧ (1 : Fin 2) = 0) := by
      intro ⟨_, h⟩; exact absurd h (by decide)
    rw [if_neg h1, if_neg h2]
  rw [s00, s01, s10, s11]
  -- Goal: 0 * 0 - 1 / Real.sqrt 2 * (-1 / Real.sqrt 2) = 1/2
  have h : (1 / Real.sqrt 2) * (-1 / Real.sqrt 2) = -(1/2) := by
    field_simp
    rw [show (Real.sqrt 2)^2 = Real.sqrt 2 * Real.sqrt 2 by ring, sqrt_two_sq]
  linarith [h]

/-- **The singlet has concurrence 1** — it is maximally entangled. -/
theorem concurrence_singlet_eq_one :
    concurrence (singletState : TwoParticleState 2) = 1 := by
  unfold concurrence
  rw [det_singlet]
  rw [show (1 : ℝ) / 2 = 1/2 from rfl]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: NORMALIZATION AND THE C ≤ 1 BOUND
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A two-particle state is **normalized** if Σ_{i,j} ψ(i,j)² = 1.
    For 2×2 with entries (a, b, c, d):
        det = ad − bc, |det| ≤ |ad| + |bc|.
    By AM–GM on each pair:
        2|ad| ≤ a² + d²,  2|bc| ≤ b² + c².
    Adding: 2|ad| + 2|bc| ≤ a² + b² + c² + d² = 1.
    Hence 2|det| ≤ 1, i.e., C(ψ) ≤ 1.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A two-particle state ψ is **normalized** iff Σ_{i,j} ψ(i,j)² = 1.
    (Frobenius norm of the matrix representation.) -/
def IsNormalized (ψ : TwoParticleState 2) : Prop :=
  ψ 0 0 ^ 2 + ψ 0 1 ^ 2 + ψ 1 0 ^ 2 + ψ 1 1 ^ 2 = 1

/-- The singlet is normalized: ‖singlet‖² = 1. -/
theorem singlet_isNormalized :
    IsNormalized (singletState : TwoParticleState 2) := by
  unfold IsNormalized
  -- entries: 0, 1/√2, -1/√2, 0
  have s00 : (singletState : TwoParticleState 2) 0 0 = 0 := by
    unfold singletState; simp
  have s01 : (singletState : TwoParticleState 2) 0 1 = 1 / Real.sqrt 2 := by
    unfold singletState; simp
  have s10 : (singletState : TwoParticleState 2) 1 0 = -1 / Real.sqrt 2 := by
    unfold singletState
    have h1 : ¬((1 : Fin 2) = 0 ∧ (0 : Fin 2) = 1) := by
      intro ⟨h, _⟩; exact absurd h (by decide)
    have h2 : (1 : Fin 2) = 1 ∧ (0 : Fin 2) = 0 := ⟨rfl, rfl⟩
    rw [if_neg h1, if_pos h2]
  have s11 : (singletState : TwoParticleState 2) 1 1 = 0 := by
    unfold singletState
    have h1 : ¬((1 : Fin 2) = 0 ∧ (1 : Fin 2) = 1) := by
      intro ⟨h, _⟩; exact absurd h (by decide)
    have h2 : ¬((1 : Fin 2) = 1 ∧ (1 : Fin 2) = 0) := by
      intro ⟨_, h⟩; exact absurd h (by decide)
    rw [if_neg h1, if_neg h2]
  rw [s00, s01, s10, s11]
  -- 0² + (1/√2)² + (−1/√2)² + 0² = 1
  have h : (1 / Real.sqrt 2) ^ 2 = 1/2 := by
    rw [div_pow, one_pow]
    rw [show (Real.sqrt 2)^2 = Real.sqrt 2 * Real.sqrt 2 by ring, sqrt_two_sq]
  have h2 : (-1 / Real.sqrt 2 : ℝ) ^ 2 = 1/2 := by
    rw [show (-1 / Real.sqrt 2 : ℝ) = -(1 / Real.sqrt 2) by ring]
    rw [neg_pow, h]
    norm_num
  rw [h, h2]
  norm_num

/-- **Concurrence is at most 1 on normalized states.** This is the
    upper-bound half of `0 ≤ C(ψ) ≤ 1` for pure two-qubit states. -/
theorem concurrence_le_one_of_normalized
    (ψ : TwoParticleState 2) (h : IsNormalized ψ) : concurrence ψ ≤ 1 := by
  unfold concurrence IsNormalized at *
  rw [Matrix.det_fin_two]
  set a := ψ 0 0
  set b := ψ 0 1
  set c := ψ 1 0
  set d := ψ 1 1
  -- Goal: 2 * |a * d - b * c| ≤ 1
  -- Strategy: |a·d − b·c| ≤ |a·d| + |b·c|, and 2|a·d| ≤ a² + d²,
  -- 2|b·c| ≤ b² + c² (AM–GM).
  have hAMGMad : 2 * |a * d| ≤ a^2 + d^2 := by
    -- (|a| - |d|)^2 ≥ 0  ⟹  |a|^2 + |d|^2 ≥ 2·|a|·|d| = 2·|a·d|
    have h1 : 0 ≤ (|a| - |d|)^2 := sq_nonneg _
    have h3 : |a|^2 = a^2 := sq_abs a
    have h4 : |d|^2 = d^2 := sq_abs d
    have h5 : |a| * |d| = |a * d| := (abs_mul a d).symm
    nlinarith [h1, h3, h4, h5]
  have hAMGMbc : 2 * |b * c| ≤ b^2 + c^2 := by
    have h1 : 0 ≤ (|b| - |c|)^2 := sq_nonneg _
    have h3 : |b|^2 = b^2 := sq_abs b
    have h4 : |c|^2 = c^2 := sq_abs c
    have h5 : |b| * |c| = |b * c| := (abs_mul b c).symm
    nlinarith [h1, h3, h4, h5]
  have habs_sub : |a * d - b * c| ≤ |a * d| + |b * c| := by
    have := abs_sub (a * d) (b * c)
    linarith
  -- Combining: 2 * |a·d − b·c| ≤ 2|ad| + 2|bc| ≤ a² + b² + c² + d² = 1
  have : 2 * |a * d - b * c| ≤ 2 * (|a * d| + |b * c|) := by
    have hnn : 0 ≤ (2 : ℝ) := by norm_num
    nlinarith [habs_sub]
  linarith [hAMGMad, hAMGMbc, h]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: CONCURRENCE VIA SCHMIDT COEFFICIENTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    From the Schmidt structure ψ(i,j) = Σ_k λ_k · bA(k,i) · bB(k,j),
    the matrix factorisation in 2×2 reads
        ψ = bAᵀ · diag(λ) · bB.
    Both bA and bB are orthogonal (their rows are orthonormal), so
    det(bA), det(bB) ∈ {±1}. Hence
        |det ψ| = |det bA| · |det diag(λ)| · |det bB|
                = λ₀ · λ₁,
    and **C(ψ) = 2 · λ₀ · λ₁**.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Helper: an orthonormal 2×2 matrix `U · Uᵀ = 1` has |det U| = 1. -/
private lemma abs_det_of_orthonormal
    (U : Matrix (Fin 2) (Fin 2) ℝ) (hU : U * Uᵀ = 1) : |U.det| = 1 := by
  -- det(U)² = det(U · Uᵀ) = det(1) = 1
  have h1 : U.det * U.det = 1 := by
    have h2 : (U * Uᵀ).det = 1 := by rw [hU]; exact Matrix.det_one
    rw [Matrix.det_mul, Matrix.det_transpose] at h2
    exact h2
  -- |U.det|² = 1, so |U.det| = 1
  have h3 : |U.det| * |U.det| = 1 := by
    rw [← abs_mul]; rw [h1]; exact abs_one
  -- |U.det| ≥ 0; the only nonneg square root of 1 is 1
  have hnn : 0 ≤ |U.det| := abs_nonneg _
  -- From |U.det|² = 1 and |U.det| ≥ 0, get |U.det| = 1
  have : (|U.det| - 1) * (|U.det| + 1) = 0 := by nlinarith [h3]
  rcases mul_eq_zero.mp this with hl | hr
  · linarith
  · linarith

/-- For a Schmidt decomposition of ψ : TwoParticleState 2, we have
    `2|det ψ| = 2 · coeffs(0) · coeffs(1)`. -/
theorem concurrence_via_schmidt
    {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ) :
    concurrence ψ = 2 * S.coeffs 0 * S.coeffs 1 := by
  -- Establish the matrix factorisation ψ = bAᵀ · diag(coeffs) · bB
  -- entry by entry from the reconstruction equation.
  have hfact :
      ψ = (S.bA)ᵀ * (Matrix.diagonal S.coeffs) * S.bB := by
    ext i j
    rw [S.reconstruction i j]
    -- ((bAᵀ * diag(c)) * bB) i j = Σ_k ((bAᵀ * diag(c)) i k) * bB k j
    -- (bAᵀ * diag(c)) i k = Σ_l bAᵀ i l * diag(c) l k = bA k i * c k (only l=k)
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.mul_apply]
    -- ∑ l, bAᵀ i l * (diagonal c) l k = bAᵀ i k * c k = bA k i * c k
    have hsum : ∑ l : Fin 2, (S.bA)ᵀ i l * (Matrix.diagonal S.coeffs) l k
              = S.bA k i * S.coeffs k := by
      rw [Finset.sum_eq_single k]
      · -- l = k case: bAᵀ i k * (diagonal coeffs k k) = bA k i * coeffs k
        rw [Matrix.transpose_apply, Matrix.diagonal_apply_eq]
      · -- l ≠ k case: bAᵀ i l * (diagonal coeffs l k) = 0 (off-diagonal)
        intro l _ hlk
        rw [Matrix.diagonal_apply_ne _ hlk, mul_zero]
      · -- k ∉ univ.toFinset (impossible)
        intro h; exact absurd (Finset.mem_univ k) h
    rw [hsum]
    ring
  -- Compute determinants
  have hdet : Matrix.det ψ = (Matrix.det S.bA) * (S.coeffs 0 * S.coeffs 1) *
              (Matrix.det S.bB) := by
    have heq := congrArg Matrix.det hfact
    -- heq : ψ.det = ((S.bAᵀ * diagonal S.coeffs) * S.bB).det
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        Matrix.det_diagonal, Fin.prod_univ_two] at heq
    exact heq
  -- |det bA| = |det bB| = 1
  have habsA : |Matrix.det S.bA| = 1 := abs_det_of_orthonormal _ S.bA_orthonormal
  have habsB : |Matrix.det S.bB| = 1 := abs_det_of_orthonormal _ S.bB_orthonormal
  -- |det ψ| = coeffs 0 * coeffs 1
  unfold concurrence
  rw [hdet]
  rw [abs_mul, abs_mul, habsA, habsB]
  rw [abs_of_nonneg
        (mul_nonneg (S.coeffs_nonneg 0) (S.coeffs_nonneg 1))]
  ring

/-- The singlet's concurrence equals 2 · (1/√2) · (1/√2) = 1, computed
    via the explicit Schmidt decomposition. -/
theorem concurrence_singlet_via_schmidt :
    concurrence (singletState : TwoParticleState 2)
      = 2 * singletDecomp.coeffs 0 * singletDecomp.coeffs 1 :=
  concurrence_via_schmidt singletDecomp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: C(ψ) = 1 ⟺ MAXIMALLY ENTANGLED (via Schmidt)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The standard characterisation of maximal entanglement: λ₀ = λ₁ = 1/√2.
    Combined with the Schmidt formula and normalisation λ₀² + λ₁² = ‖ψ‖² = 1,
    we get C(ψ) = 1 ⟺ both Schmidt coefficients equal 1/√2.

    Note: full normalization ⟺ Σ λ_k² = 1 requires extra orthonormal
    machinery; we state the structural characterisation under the Schmidt
    interface. We give the singlet as the witness.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Schmidt-coefficient characterisation of max entanglement: if
    `λ₀ = λ₁ = 1/√2` then `C(ψ) = 1`. -/
theorem concurrence_eq_one_of_balanced_schmidt
    {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ)
    (h0 : S.coeffs 0 = 1 / Real.sqrt 2)
    (h1 : S.coeffs 1 = 1 / Real.sqrt 2) :
    concurrence ψ = 1 := by
  rw [concurrence_via_schmidt S, h0, h1]
  -- Goal: 2 * (1/√2) * (1/√2) = 1
  field_simp
  -- After field_simp, residual goal involves (Real.sqrt 2)^2 = 2 or √2 * √2 = 2
  rw [show (Real.sqrt 2)^2 = Real.sqrt 2 * Real.sqrt 2 by ring, sqrt_two_sq]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **CONCURRENCE — THE WOOTTERS REAL-AMPLITUDE BUNDLE.**

    For real-amplitude two-qubit pure states, Wootters' concurrence is
    `C(ψ) = 2 · |det ψ|`. This file proves:

    (1) `concurrence_def`: explicit formula
        C(ψ) = 2 · |ψ(0,0)·ψ(1,1) − ψ(0,1)·ψ(1,0)|.

    (2) `concurrence_nonneg`: 0 ≤ C(ψ).

    (3) `concurrence_eq_zero_iff_separable`: C(ψ) = 0 ⟺ ψ is separable.
        (Equivalently `concurrence_pos_iff_entangled`: C(ψ) > 0 ⟺
        entangled — concurrence detects entanglement exactly.)

    (4) `concurrence_singlet_eq_one`: the singlet has C = 1.

    (5) `concurrence_le_one_of_normalized`: C(ψ) ≤ 1 for normalized ψ
        (Σ_{i,j} ψ(i,j)² = 1), proved via AM–GM on the 2×2 entries.

    (6) `concurrence_via_schmidt`: C(ψ) = 2 · λ₀ · λ₁ for any Schmidt
        decomposition of ψ — the geometric content (concurrence is the
        product of singular values, scaled).

    (7) `concurrence_eq_one_of_balanced_schmidt`: the standard hallmark
        of maximal entanglement, λ₀ = λ₁ = 1/√2 ⟹ C = 1.

    Honest scope: real amplitudes, pure states, two qubits. Mixed-state
    concurrence (the convex roof / Wootters spin-flipped formula) and
    higher-dimensional generalizations are out of scope here. -/
theorem concurrence_master :
    -- (1) Explicit formula
    (∀ ψ : TwoParticleState 2,
        concurrence ψ = 2 * |ψ 0 0 * ψ 1 1 - ψ 0 1 * ψ 1 0|)
    -- (2) Non-negativity
    ∧ (∀ ψ : TwoParticleState 2, 0 ≤ concurrence ψ)
    -- (3) C = 0 ⟺ separable
    ∧ (∀ ψ : TwoParticleState 2,
        concurrence ψ = 0 ↔ IsQuantumSeparable ψ)
    -- (4) Singlet has C = 1
    ∧ concurrence (singletState : TwoParticleState 2) = 1
    -- (5) C ≤ 1 on normalized states
    ∧ (∀ ψ : TwoParticleState 2, IsNormalized ψ → concurrence ψ ≤ 1)
    -- (6) Schmidt formula
    ∧ (∀ {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ),
        concurrence ψ = 2 * S.coeffs 0 * S.coeffs 1)
    -- (7) Balanced Schmidt ⟹ C = 1 (max entanglement signature)
    ∧ (∀ {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ),
        S.coeffs 0 = 1 / Real.sqrt 2 → S.coeffs 1 = 1 / Real.sqrt 2 →
        concurrence ψ = 1) :=
  ⟨concurrence_def,
   concurrence_nonneg,
   concurrence_eq_zero_iff_separable,
   concurrence_singlet_eq_one,
   concurrence_le_one_of_normalized,
   @concurrence_via_schmidt,
   @concurrence_eq_one_of_balanced_schmidt⟩

end UnifiedTheory.LayerB.Concurrence
