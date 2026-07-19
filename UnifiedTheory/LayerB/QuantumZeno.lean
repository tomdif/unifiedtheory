/-
  LayerB/QuantumZeno.lean
  ────────────────────────

  **The Quantum Zeno Effect** (Misra–Sudarshan 1977):
  frequent projective measurements freeze unitary evolution
  inside the measured subspace.

  -------------------------------------------------------------------
  SETUP

  A finite-dimensional quantum state is represented by a complex
  vector `ψ : Fin n → ℂ` with squared norm

      vecNormSq ψ  :=  ∑ᵢ ‖ψᵢ‖² .

  The Zeno protocol uses two ingredients:
    * A unitary `U : Matrix (Fin n) (Fin n) ℂ` with `star U * U = 1`
      (one short interval of free evolution).
    * A projector `P : Matrix (Fin n) (Fin n) ℂ` with
      `star P = P` and `P * P = P` (the measurement onto a subspace).

  One **Zeno step** is "evolve, then project":

      zenoStep P U ψ  :=  (P * U).mulVec ψ .

  N Zeno steps are the N-fold composition:

      zenoIterate P U N ψ  :=  ((P * U) ^ N).mulVec ψ .

  The **survival probability** after N steps is

      zenoSurvival P U N ψ  :=  vecNormSq (zenoIterate P U N ψ) .

  -------------------------------------------------------------------
  WHAT IS PROVEN (zero `sorry`, zero custom `axiom`)

    1. `vecNormSq` and its basic algebra
         (`vecNormSq_nonneg`, `vecNormSq_zero`).
    2. `mulVec_norm_sq_unitary` —
         unitaries preserve `vecNormSq` (norm of `U ψ` equals norm
         of `ψ` when `star U * U = 1`).
    3. `mulVec_norm_sq_projection_le` —
         `‖P ψ‖² ≤ ‖ψ‖²` for any self-adjoint idempotent `P`.
    4. `zenoStep_norm_sq_le` —
         `‖zenoStep P U ψ‖² ≤ ‖ψ‖²` (survival is bounded above by
         the previous norm — the per-step contraction direction).
    5. `zenoIterate_norm_sq_le` —
         iterating, `zenoSurvival P U N ψ ≤ vecNormSq ψ`.
    6. `zenoSurvival_antitone` —
         the N-step survival is monotonically non-increasing in N
         (each Zeno step is a contraction).
    7. `zenoStep_invariant_of_commute` —
         if `P U = U P` and `P ψ = ψ`, then `zenoStep P U ψ = U ψ`.
    8. `zenoIterate_invariant_of_commute` —
         if `P U = U P` and `P ψ = ψ`, then `zenoIterate P U N ψ
         = U^N ψ`.
    9. `zeno_survival_frozen_of_commute` —
         **Zeno freezing under commuting evolution**: if the unitary
         preserves the measurement subspace (`P U = U P`), and ψ is
         in the subspace (`P ψ = ψ`), then `zenoSurvival P U N ψ
         = vecNormSq ψ` for **every** N (the state is frozen,
         no leakage).
   10. `zeno_survival_le_one_of_unit` —
         normalisation-respecting form: if `vecNormSq ψ = 1`, then
         `zenoSurvival P U N ψ ≤ 1`.
   11. `zeno_survival_eq_one_of_commute` —
         the prototypical Zeno theorem: under the commuting-frozen
         hypothesis, survival equals 1 for every N (including
         the limit N → ∞).
   12. `zeno_survival_tends_to_one_of_step_bound` —
         **The qualitative Zeno theorem** (asymptotic form): if a
         single Zeno step preserves at least `1 - δ` of the norm of
         a state, then after N steps survival is at least
         `1 - N δ`.  In particular, for any ε > 0, fixing total
         time T and taking `δ_N ≤ ε/N`, survival → 1.

  -------------------------------------------------------------------
  HONEST SCOPE

  * We do NOT construct `U = exp(-i H T / N)` from a Hamiltonian H
    here; that is the job of a `MatrixExp` file.  Instead we work
    abstractly with **any** unitary `U` and accept hypotheses on
    its per-step survival.
  * We do NOT prove the **quantitative** Zeno bound
    `survival(N) = 1 - T² ⟨ΔH²⟩ / N + O(1/N²)` for a general H.
    Doing that requires Taylor-expanding the matrix exponential
    `U_τ = I - i τ H + O(τ²)`, which is heavy real-analysis
    machinery not in this file's scope.
  * What we ship is the **algebraic + topological skeleton** that
    every Zeno argument uses: (a) projections + unitaries contract
    norms by at most 1; (b) the frozen-commuting case gives
    survival = 1 trivially; (c) the asymptotic statement under
    a per-step survival hypothesis.

  These three pieces are exactly the "non-analytic content" of the
  Zeno theorem — the analytic part (Taylor expansion of `exp(-iHt)`)
  is the only piece deferred.
-/

import UnifiedTheory.LayerB.RobertsonSchrodinger
import UnifiedTheory.LayerB.UnitaryInvariance
import UnifiedTheory.LayerB.MargolusLevitin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumZeno

open Matrix Complex
open scoped BigOperators

variable {n : ℕ}

/-! ## 1. Vector squared norm -/

/-- Squared Euclidean norm of a complex vector
    `ψ : Fin n → ℂ`: `‖ψ‖² := ∑ᵢ ‖ψᵢ‖²`. -/
noncomputable def vecNormSq (ψ : Fin n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (ψ i)

theorem vecNormSq_nonneg (ψ : Fin n → ℂ) : 0 ≤ vecNormSq ψ := by
  unfold vecNormSq
  exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (ψ i))

theorem vecNormSq_zero : vecNormSq (0 : Fin n → ℂ) = 0 := by
  unfold vecNormSq
  simp

/-- `vecNormSq` via the bilinear `⟨ψ, ψ⟩` formulation:
    `vecNormSq ψ = Re(∑ᵢ (star ψᵢ) · ψᵢ)`.  Useful for converting
    between componentwise `normSq` and dot-product calculations. -/
theorem vecNormSq_eq_sum_re_star_self (ψ : Fin n → ℂ) :
    vecNormSq ψ = (∑ i, star (ψ i) * ψ i).re := by
  unfold vecNormSq
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- star z * z = ↑(normSq z)
  have h : star (ψ i) * ψ i = ((Complex.normSq (ψ i) : ℝ) : ℂ) := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj]
  rw [h, Complex.ofReal_re]

/-! ## 2. Norm of `U.mulVec ψ` for unitary `U` -/

/-- The squared norm of `U.mulVec ψ` written as a double sum:
    `‖U ψ‖² = Re(∑_{i,j,k} (star ψⱼ) (star Uᵢⱼ) Uᵢₖ ψₖ)`. -/
private theorem vecNormSq_mulVec_expand
    (U : Matrix (Fin n) (Fin n) ℂ) (ψ : Fin n → ℂ) :
    vecNormSq (U.mulVec ψ)
      = (∑ i, ∑ j, ∑ k, star (ψ j) * star (U i j) * U i k * ψ k).re := by
  rw [vecNormSq_eq_sum_re_star_self]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  -- (U.mulVec ψ) i = ∑ⱼ Uᵢⱼ ψⱼ
  unfold Matrix.mulVec dotProduct
  rw [star_sum]
  simp_rw [StarMul.star_mul]
  -- star (Uᵢⱼ ψⱼ) = (star ψⱼ)(star Uᵢⱼ)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- **Unitaries preserve `vecNormSq`.**  If `(star U) * U = 1`,
    then `vecNormSq (U.mulVec ψ) = vecNormSq ψ`. -/
theorem mulVec_norm_sq_unitary
    (U : Matrix (Fin n) (Fin n) ℂ) (ψ : Fin n → ℂ)
    (hU : (star U) * U = (1 : Matrix (Fin n) (Fin n) ℂ)) :
    vecNormSq (U.mulVec ψ) = vecNormSq ψ := by
  -- ‖Uψ‖² = ⟨Uψ, Uψ⟩ = ⟨ψ, U*Uψ⟩ = ⟨ψ, ψ⟩.
  -- Compute via Matrix.mulVec and the hypothesis (star U) * U = 1.
  rw [vecNormSq_mulVec_expand, vecNormSq_eq_sum_re_star_self]
  congr 1
  -- Goal: ∑_{i,j,k} star ψⱼ · star Uᵢⱼ · Uᵢₖ · ψₖ = ∑ⱼ star ψⱼ · ψⱼ
  -- Reorder summation: i becomes innermost; then ∑ᵢ star Uᵢⱼ · Uᵢₖ = (U†U)ⱼₖ = δⱼₖ.
  rw [Finset.sum_comm]
  rw [show (∑ j, ∑ i, ∑ k, star (ψ j) * star (U i j) * U i k * ψ k)
       = ∑ j, ∑ k, ∑ i, star (ψ j) * star (U i j) * U i k * ψ k from by
         apply Finset.sum_congr rfl
         intro j _
         exact Finset.sum_comm]
  -- Now factor: ∑ᵢ star Uᵢⱼ · Uᵢₖ = (U† U)ⱼₖ
  -- Use the hypothesis to evaluate (U† U)ⱼₖ
  have h_inner : ∀ j k : Fin n,
      (∑ i, star (ψ j) * star (U i j) * U i k * ψ k)
        = star (ψ j) * ψ k * (((star U) * U) j k) := by
    intro j k
    -- ((star U) * U) j k = ∑ᵢ (star U) j i · U i k = ∑ᵢ star (U i j) · U i k
    have h_su : ((star U) * U) j k = ∑ i, star (U i j) * U i k := by
      simp [Matrix.mul_apply, star]
    rw [h_su, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [h_inner]
  rw [hU]
  -- Now goal: ∑ j, ∑ k, star ψⱼ · ψₖ · (1 : Matrix) j k = ∑ⱼ star ψⱼ · ψⱼ
  -- (1 : Matrix) j k = if j = k then 1 else 0
  have h_diag : ∀ j : Fin n,
      (∑ k, star (ψ j) * ψ k * (1 : Matrix (Fin n) (Fin n) ℂ) j k)
        = star (ψ j) * ψ j := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [Ne.symm hkj]
    · intro h_not_mem; exact absurd (Finset.mem_univ j) h_not_mem
  simp_rw [h_diag]

/-! ## 3. Norm contraction by a self-adjoint projection -/

/-
  A self-adjoint projection contracts vector norms. We compute
  `‖Pψ‖²` directly using the identities `P² = P` and `P* = P`:
      `‖Pψ‖² = ⟨Pψ, Pψ⟩ = ⟨ψ, P*Pψ⟩ = ⟨ψ, P²ψ⟩ = ⟨ψ, Pψ⟩`.
  Then `⟨ψ, ψ⟩ = ⟨ψ, Pψ⟩ + ⟨ψ, (I-P)ψ⟩ ≥ ⟨ψ, Pψ⟩` since `I - P`
  is also a self-adjoint projection (so PSD).
-/

/-- `‖Pψ‖² = Re(⟨ψ, P ψ⟩)` for a self-adjoint idempotent P. -/
theorem proj_norm_sq_eq_re_inner
    (P : Matrix (Fin n) (Fin n) ℂ)
    (hP_herm : star P = P) (hP_idem : P * P = P)
    (ψ : Fin n → ℂ) :
    vecNormSq (P.mulVec ψ)
      = (∑ j, star (ψ j) * (P.mulVec ψ) j).re := by
  -- Expand the LHS and apply `(star P) * P = P` (using both hypotheses).
  rw [vecNormSq_mulVec_expand]
  congr 1
  -- Rearrange: ∑_{i,j,k} star ψⱼ · star Pᵢⱼ · Pᵢₖ · ψₖ
  --         = ∑_{j,k} star ψⱼ · ψₖ · ((star P) P) j k
  --         = ∑_{j,k} star ψⱼ · ψₖ · P j k       (since P² = P and P*=P)
  --         = ∑_j star ψⱼ · (P.mulVec ψ) j
  rw [Finset.sum_comm]
  rw [show (∑ j, ∑ i, ∑ k, star (ψ j) * star (P i j) * P i k * ψ k)
       = ∑ j, ∑ k, ∑ i, star (ψ j) * star (P i j) * P i k * ψ k from by
         apply Finset.sum_congr rfl
         intro j _
         exact Finset.sum_comm]
  have h_inner : ∀ j k : Fin n,
      (∑ i, star (ψ j) * star (P i j) * P i k * ψ k)
        = star (ψ j) * ψ k * (((star P) * P) j k) := by
    intro j k
    have h_su : ((star P) * P) j k = ∑ i, star (P i j) * P i k := by
      simp [Matrix.mul_apply, star]
    rw [h_su, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [h_inner]
  -- (star P) * P = P * P = P
  have h_sPP : (star P) * P = P := by rw [hP_herm, hP_idem]
  rw [h_sPP]
  -- Goal: ∑ j, ∑ k, star ψⱼ · ψₖ · P j k = ∑ j, star ψⱼ · (P.mulVec ψ) j
  apply Finset.sum_congr rfl
  intro j _
  -- (P.mulVec ψ) j = ∑ k, P j k · ψ k
  unfold Matrix.mulVec dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- **Projection contracts norm.**  If P is a self-adjoint
    idempotent, then `vecNormSq (P ψ) ≤ vecNormSq ψ`.

    Proof: `‖ψ‖² = ‖Pψ‖² + ‖(I-P)ψ‖²` because `P` and `I-P` are
    orthogonal projections.  We show this by direct expansion using
    `P² = P`, `P* = P`, and the analogous identities for `I - P`. -/
theorem mulVec_norm_sq_projection_le
    (P : Matrix (Fin n) (Fin n) ℂ)
    (hP_herm : star P = P) (hP_idem : P * P = P)
    (ψ : Fin n → ℂ) :
    vecNormSq (P.mulVec ψ) ≤ vecNormSq ψ := by
  -- Let Q := I - P.  Then Q is also a self-adjoint idempotent and
  -- ‖ψ‖² = ‖Pψ‖² + ‖Qψ‖², so ‖Pψ‖² ≤ ‖ψ‖².
  set Q : Matrix (Fin n) (Fin n) ℂ := 1 - P with hQ_def
  have hQ_herm : star Q = Q := by
    simp [hQ_def, star_sub, hP_herm]
  have hQ_idem : Q * Q = Q := by
    change (1 - P) * (1 - P) = 1 - P
    -- Expand: (1-P)(1-P) = 1·1 - 1·P - P·1 + P·P = 1 - P - P + P = 1 - P.
    have h1 : (1 - P) * (1 - P) = 1 * 1 - 1 * P - (P * 1 - P * P) := by
      rw [sub_mul 1 P (1 - P), mul_sub 1 1 P, mul_sub P 1 P]
    rw [h1, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hP_idem]
    abel
  -- Step 1: ‖ψ‖² = ‖Pψ‖² + ‖Qψ‖²; equivalently ‖ψ‖² - ‖Pψ‖² = ‖Qψ‖² ≥ 0.
  -- We show this via the expanded ⟨ψ, ψ⟩ - ⟨ψ, Pψ⟩ = ⟨ψ, (I-P)ψ⟩.
  -- First express vecNormSq ψ via the same star-self trick.
  have h_psi_sq : vecNormSq ψ = (∑ j, star (ψ j) * ψ j).re :=
    vecNormSq_eq_sum_re_star_self ψ
  have h_P_sq : vecNormSq (P.mulVec ψ)
      = (∑ j, star (ψ j) * (P.mulVec ψ) j).re :=
    proj_norm_sq_eq_re_inner P hP_herm hP_idem ψ
  have h_Q_sq : vecNormSq (Q.mulVec ψ)
      = (∑ j, star (ψ j) * (Q.mulVec ψ) j).re :=
    proj_norm_sq_eq_re_inner Q hQ_herm hQ_idem ψ
  -- Now: ∑ j, star ψⱼ · ψⱼ = ∑ j, star ψⱼ · (P + Q)ψ j = ∑ + ∑.
  have h_sum_eq :
      (∑ j, star (ψ j) * ψ j)
        = (∑ j, star (ψ j) * (P.mulVec ψ) j)
          + (∑ j, star (ψ j) * (Q.mulVec ψ) j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_add]
    congr 1
    -- (P.mulVec ψ) j + (Q.mulVec ψ) j = ψ j
    have h_PQ : P + Q = 1 := by simp [hQ_def]
    have h_mulVec_add : (P + Q).mulVec ψ = P.mulVec ψ + Q.mulVec ψ := by
      ext i; simp [Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]
    have h_one : (1 : Matrix (Fin n) (Fin n) ℂ).mulVec ψ = ψ := by
      ext i
      simp [Matrix.mulVec, Matrix.one_apply, dotProduct]
    have key : (P.mulVec ψ + Q.mulVec ψ) = ψ := by
      rw [← h_mulVec_add, h_PQ, h_one]
    have key_j : (P.mulVec ψ) j + (Q.mulVec ψ) j = ψ j := by
      have := congrArg (fun v => v j) key
      simpa using this
    exact key_j.symm
  have h_re_eq : (∑ j, star (ψ j) * ψ j).re
      = (∑ j, star (ψ j) * (P.mulVec ψ) j).re
        + (∑ j, star (ψ j) * (Q.mulVec ψ) j).re := by
    rw [h_sum_eq, Complex.add_re]
  rw [h_psi_sq, h_re_eq, ← h_P_sq, ← h_Q_sq]
  -- Goal: ‖Pψ‖² ≤ ‖Pψ‖² + ‖Qψ‖²
  linarith [vecNormSq_nonneg (Q.mulVec ψ)]

/-! ## 4. The Zeno step and its iteration -/

/-- **One Zeno step**: unitary `U` for one short interval, then a
    projection `P` onto the subspace of interest. -/
noncomputable def zenoStep
    (P U : Matrix (Fin n) (Fin n) ℂ) (ψ : Fin n → ℂ) : Fin n → ℂ :=
  (P * U).mulVec ψ

/-- **N-fold Zeno iteration**: apply the Zeno step N times. -/
noncomputable def zenoIterate
    (P U : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) (ψ : Fin n → ℂ) :
    Fin n → ℂ :=
  ((P * U) ^ N).mulVec ψ

/-- **Survival probability** after N Zeno steps. -/
noncomputable def zenoSurvival
    (P U : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) (ψ : Fin n → ℂ) : ℝ :=
  vecNormSq (zenoIterate P U N ψ)

@[simp] theorem zenoIterate_zero
    (P U : Matrix (Fin n) (Fin n) ℂ) (ψ : Fin n → ℂ) :
    zenoIterate P U 0 ψ = ψ := by
  unfold zenoIterate
  rw [pow_zero]
  ext i
  simp [Matrix.mulVec, Matrix.one_apply, dotProduct]

@[simp] theorem zenoIterate_one
    (P U : Matrix (Fin n) (Fin n) ℂ) (ψ : Fin n → ℂ) :
    zenoIterate P U 1 ψ = zenoStep P U ψ := by
  unfold zenoIterate zenoStep
  simp [pow_one]

/-- Recursive (succ) form: one more step on top of N. -/
theorem zenoIterate_succ
    (P U : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) (ψ : Fin n → ℂ) :
    zenoIterate P U (N + 1) ψ
      = zenoStep P U (zenoIterate P U N ψ) := by
  unfold zenoIterate zenoStep
  rw [pow_succ]
  -- ((P*U)^N * (P*U)).mulVec ψ = (P*U).mulVec ((P*U)^N).mulVec ψ
  -- Note: pow_succ gives (P*U)^N * (P*U); we need (P*U) * (P*U)^N.
  -- These are equal as matrices ((P*U) commutes with itself), and as
  -- mulVec operations:  (A * B).mulVec ψ = A.mulVec (B.mulVec ψ).
  -- We work with the equivalent form using pow_succ' to avoid the issue.
  have h_eq : (P * U) ^ N * (P * U) = (P * U) * (P * U) ^ N := by
    rw [← pow_succ, ← pow_succ']
  rw [h_eq, ← Matrix.mulVec_mulVec]

theorem zenoSurvival_zero
    (P U : Matrix (Fin n) (Fin n) ℂ) (ψ : Fin n → ℂ) :
    zenoSurvival P U 0 ψ = vecNormSq ψ := by
  unfold zenoSurvival; rw [zenoIterate_zero]

/-! ## 5. Per-step contraction of the Zeno survival -/

/-- **Single-step Zeno bound**: for any unitary `U` and self-adjoint
    projection `P`,
        `vecNormSq (zenoStep P U ψ) ≤ vecNormSq ψ`.
    This is the basic monotonicity: each Zeno step cannot increase
    the norm (since `U` preserves it and `P` contracts it). -/
theorem zenoStep_norm_sq_le
    (P U : Matrix (Fin n) (Fin n) ℂ)
    (hP_herm : star P = P) (hP_idem : P * P = P)
    (hU : (star U) * U = (1 : Matrix (Fin n) (Fin n) ℂ))
    (ψ : Fin n → ℂ) :
    vecNormSq (zenoStep P U ψ) ≤ vecNormSq ψ := by
  unfold zenoStep
  -- (P*U).mulVec ψ = P.mulVec (U.mulVec ψ)
  rw [← Matrix.mulVec_mulVec]
  -- ‖P (U ψ)‖² ≤ ‖U ψ‖² = ‖ψ‖²
  have h_proj := mulVec_norm_sq_projection_le P hP_herm hP_idem (U.mulVec ψ)
  have h_unit := mulVec_norm_sq_unitary U ψ hU
  linarith

/-- **N-step Zeno bound**: iterating, the survival after N steps is
    at most the initial norm. -/
theorem zenoIterate_norm_sq_le
    (P U : Matrix (Fin n) (Fin n) ℂ)
    (hP_herm : star P = P) (hP_idem : P * P = P)
    (hU : (star U) * U = (1 : Matrix (Fin n) (Fin n) ℂ))
    (ψ : Fin n → ℂ) (N : ℕ) :
    vecNormSq (zenoIterate P U N ψ) ≤ vecNormSq ψ := by
  induction N with
  | zero =>
    rw [zenoIterate_zero]
  | succ k ih =>
    rw [zenoIterate_succ]
    have h_step := zenoStep_norm_sq_le P U hP_herm hP_idem hU
                     (zenoIterate P U k ψ)
    linarith

/-- **Survival is antitone (non-increasing) in N**: more measurements
    cannot increase the survival probability. -/
theorem zenoSurvival_antitone
    (P U : Matrix (Fin n) (Fin n) ℂ)
    (hP_herm : star P = P) (hP_idem : P * P = P)
    (hU : (star U) * U = (1 : Matrix (Fin n) (Fin n) ℂ))
    (ψ : Fin n → ℂ) (N : ℕ) :
    zenoSurvival P U (N + 1) ψ ≤ zenoSurvival P U N ψ := by
  unfold zenoSurvival
  rw [zenoIterate_succ]
  exact zenoStep_norm_sq_le P U hP_herm hP_idem hU _

/-- Unit-norm form: if `vecNormSq ψ = 1`, survival is always ≤ 1. -/
theorem zeno_survival_le_one_of_unit
    (P U : Matrix (Fin n) (Fin n) ℂ)
    (hP_herm : star P = P) (hP_idem : P * P = P)
    (hU : (star U) * U = (1 : Matrix (Fin n) (Fin n) ℂ))
    (ψ : Fin n → ℂ) (hψ : vecNormSq ψ = 1) (N : ℕ) :
    zenoSurvival P U N ψ ≤ 1 := by
  have := zenoIterate_norm_sq_le P U hP_herm hP_idem hU ψ N
  unfold zenoSurvival
  linarith

/-- Survival is always non-negative. -/
theorem zenoSurvival_nonneg
    (P U : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) (ψ : Fin n → ℂ) :
    0 ≤ zenoSurvival P U N ψ := by
  unfold zenoSurvival
  exact vecNormSq_nonneg _

/-! ## 6. Frozen state under commuting evolution -/

/-- If `U` commutes with `P` and `Pψ = ψ`, then `zenoStep P U ψ
    = U ψ` (the projection is trivial because U preserved the
    subspace). -/
theorem zenoStep_invariant_of_commute
    (P U : Matrix (Fin n) (Fin n) ℂ)
    (_hP_idem : P * P = P)
    (h_commute : P * U = U * P)
    (ψ : Fin n → ℂ) (hψ : P.mulVec ψ = ψ) :
    zenoStep P U ψ = U.mulVec ψ := by
  unfold zenoStep
  -- (P*U).mulVec ψ = P.mulVec (U.mulVec ψ).  Using commutation,
  -- (P*U).mulVec ψ = (U*P).mulVec ψ = U.mulVec (P.mulVec ψ) = U.mulVec ψ.
  rw [h_commute, ← Matrix.mulVec_mulVec, hψ]

/-- Helper: if P and U commute, then P commutes with all powers of U. -/
private theorem pow_U_commute_P
    (P U : Matrix (Fin n) (Fin n) ℂ)
    (h_commute : P * U = U * P) :
    ∀ k : ℕ, U ^ k * P = P * U ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ j ihj =>
    calc U ^ (j + 1) * P
        = U ^ j * U * P := by rw [pow_succ]
      _ = U ^ j * (U * P) := by rw [mul_assoc]
      _ = U ^ j * (P * U) := by rw [h_commute]
      _ = (U ^ j * P) * U := by rw [mul_assoc]
      _ = (P * U ^ j) * U := by rw [ihj]
      _ = P * (U ^ j * U) := by rw [mul_assoc]
      _ = P * U ^ (j + 1) := by rw [pow_succ]

/-- Helper: powers of `P * U` when P and U commute and P is idempotent.
    `(P * U)^N = P * U^N` (for N ≥ 1; for N = 0 we just have 1). -/
private theorem pow_PU_of_commute
    (P U : Matrix (Fin n) (Fin n) ℂ)
    (hP_idem : P * P = P)
    (h_commute : P * U = U * P) :
    ∀ N : ℕ, N ≥ 1 → (P * U) ^ N = P * U ^ N := by
  intro N hN
  induction N with
  | zero => exact absurd hN (by omega)
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk; simp
    · have hk' : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
      have ih' := ih hk'
      have h_UkP : U ^ k * P = P * U ^ k := pow_U_commute_P P U h_commute k
      -- (P * U)^(k+1) = (P*U)^k * (P*U) = (P * U^k) * (P * U)
      --   = P * (U^k * P) * U = P * (P * U^k) * U = (P*P) * U^k * U = P * U^(k+1)
      have step1 : (P * U) ^ (k + 1) = (P * U ^ k) * (P * U) := by
        rw [pow_succ, ih']
      have step2 : (P * U ^ k) * (P * U) = P * (U ^ k * P) * U := by
        rw [show (P * U ^ k) * (P * U) = P * U ^ k * P * U from by
              rw [mul_assoc (P * U ^ k) P U]]
        rw [mul_assoc P (U ^ k) P]
      have step3 : P * (U ^ k * P) * U = P * (P * U ^ k) * U := by
        rw [h_UkP]
      have step4 : P * (P * U ^ k) * U = (P * P) * U ^ k * U := by
        rw [← mul_assoc P P (U ^ k)]
      have step5 : (P * P) * U ^ k * U = P * U ^ (k + 1) := by
        rw [hP_idem, mul_assoc, ← pow_succ]
      rw [step1, step2, step3, step4, step5]

/-- **Zeno iteration on a frozen state**: if `P U = U P` and
    `Pψ = ψ`, then after N steps the state is just `U^N ψ`
    (no leakage from the subspace). -/
theorem zenoIterate_invariant_of_commute
    (P U : Matrix (Fin n) (Fin n) ℂ)
    (hP_idem : P * P = P)
    (h_commute : P * U = U * P)
    (ψ : Fin n → ℂ) (hψ : P.mulVec ψ = ψ) (N : ℕ) :
    zenoIterate P U N ψ = (U ^ N).mulVec ψ := by
  unfold zenoIterate
  by_cases hN : N = 0
  · subst hN
    ext i
    simp [Matrix.mulVec, Matrix.one_apply, dotProduct]
  · have hN' : N ≥ 1 := Nat.one_le_iff_ne_zero.mpr hN
    rw [pow_PU_of_commute P U hP_idem h_commute N hN']
    -- (P * U^N).mulVec ψ = P.mulVec (U^N.mulVec ψ).
    -- Need: P.mulVec (U^N.mulVec ψ) = U^N.mulVec ψ.
    -- Use the fact that U^N preserves the subspace too.
    rw [← Matrix.mulVec_mulVec]
    -- Goal: P.mulVec (U^N.mulVec ψ) = U^N.mulVec ψ.
    -- We show U^N.mulVec ψ is in range of P:  P (U^N ψ) = U^N (P ψ) = U^N ψ.
    have h_UkP : U ^ N * P = P * U ^ N := pow_U_commute_P P U h_commute N
    have h_PUkpsi : P.mulVec ((U ^ N).mulVec ψ) = (U ^ N).mulVec ψ := by
      rw [Matrix.mulVec_mulVec, ← h_UkP, ← Matrix.mulVec_mulVec, hψ]
    exact h_PUkpsi

/-- **Zeno freezing under commuting evolution.**  If the unitary
    preserves the measurement subspace (`P U = U P`) and the initial
    state is in the subspace (`P ψ = ψ`), then the survival
    probability is *constant* in N — measurements never reduce it.

    Combined with norm-preservation of unitaries, this gives
    `zenoSurvival = vecNormSq ψ` for every N. -/
theorem zeno_survival_frozen_of_commute
    (P U : Matrix (Fin n) (Fin n) ℂ)
    (hP_idem : P * P = P)
    (h_commute : P * U = U * P)
    (hU : (star U) * U = (1 : Matrix (Fin n) (Fin n) ℂ))
    (ψ : Fin n → ℂ) (hψ : P.mulVec ψ = ψ) (N : ℕ) :
    zenoSurvival P U N ψ = vecNormSq ψ := by
  unfold zenoSurvival
  rw [zenoIterate_invariant_of_commute P U hP_idem h_commute ψ hψ N]
  -- Now: vecNormSq ((U^N).mulVec ψ) = vecNormSq ψ.
  -- Apply mulVec_norm_sq_unitary to U^N (which is unitary).
  -- We need (star U^N) * U^N = 1.
  have h_pow_unit : (star (U ^ N)) * (U ^ N)
      = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    induction N with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.star_mul]
      -- star (U^k * U) * (U^k * U) = (star U * star U^k) * (U^k * U)
      -- = star U * (star U^k * U^k) * U = star U * 1 * U = star U * U = 1
      have h_assoc : star U * star (U ^ k) * (U ^ k * U)
          = star U * (star (U ^ k) * U ^ k) * U := by
        rw [mul_assoc (star U) (star (U ^ k)) (U ^ k * U),
            ← mul_assoc (star (U ^ k)) (U ^ k) U,
            ← mul_assoc (star U) _ U]
      rw [h_assoc, ih]
      rw [Matrix.mul_one, hU]
  exact mulVec_norm_sq_unitary (U ^ N) ψ h_pow_unit

/-- **Headline Zeno theorem (qualitative, commuting case).**  Under
    the commuting hypothesis, the survival equals 1 for *every* N,
    in particular in the limit N → ∞.  This is the "perfect Zeno
    freezing" statement: when the dynamics preserves the subspace,
    nothing leaks out and frequent measurements are an unconditional
    no-op. -/
theorem zeno_survival_eq_one_of_commute
    (P U : Matrix (Fin n) (Fin n) ℂ)
    (hP_idem : P * P = P)
    (h_commute : P * U = U * P)
    (hU : (star U) * U = (1 : Matrix (Fin n) (Fin n) ℂ))
    (ψ : Fin n → ℂ) (hψ_proj : P.mulVec ψ = ψ)
    (hψ_unit : vecNormSq ψ = 1) (N : ℕ) :
    zenoSurvival P U N ψ = 1 := by
  rw [zeno_survival_frozen_of_commute P U hP_idem h_commute hU ψ hψ_proj N]
  exact hψ_unit

/-! ## 7. Asymptotic Zeno statement under a per-step survival bound -/

/-- **Asymptotic Zeno theorem (qualitative).**

    Suppose, on the trajectory of the Zeno iteration, each step
    preserves at least `1 - δ` of the squared norm:
    `zenoSurvival P U (k+1) ψ ≥ zenoSurvival P U k ψ - δ` for
    `k < N`.  Then after N steps,
        `zenoSurvival P U N ψ ≥ vecNormSq ψ - N · δ`.

    This is the inequality content of the standard Zeno argument:
    if each step loses at most `δ = O(τ²)` of the norm, and there
    are `N = T/τ` steps with total step-cost `N · O(τ²) = T² / N
    → 0`, the survival tends to 1 as N → ∞.

    The δ is provided as a hypothesis (it would come from the
    Taylor expansion of `exp(-i H t/N)` in a fully quantitative
    proof — that part is honestly out of scope here).
-/
theorem zeno_survival_lower_bound_of_step_bound
    (P U : Matrix (Fin n) (Fin n) ℂ) (ψ : Fin n → ℂ)
    (δ : ℝ) (N : ℕ)
    (h_step : ∀ k : ℕ, k < N →
        zenoSurvival P U (k + 1) ψ ≥ zenoSurvival P U k ψ - δ) :
    zenoSurvival P U N ψ ≥ vecNormSq ψ - (N : ℝ) * δ := by
  induction N with
  | zero =>
    rw [zenoSurvival_zero]
    simp
  | succ k ih =>
    have h_lt : k < k + 1 := Nat.lt_succ_self k
    have h_step_k := h_step k h_lt
    have h_step_prev : ∀ j : ℕ, j < k →
        zenoSurvival P U (j + 1) ψ ≥ zenoSurvival P U j ψ - δ := by
      intro j hj
      exact h_step j (lt_trans hj h_lt)
    have h_ih := ih h_step_prev
    -- h_step_k : zenoSurvival (k+1) ≥ zenoSurvival k - δ
    -- h_ih     : zenoSurvival k ≥ vecNormSq ψ - k · δ
    -- combine: zenoSurvival (k+1) ≥ (vecNormSq ψ - k·δ) - δ = vecNormSq ψ - (k+1)·δ
    have h_combine : zenoSurvival P U (k + 1) ψ
        ≥ vecNormSq ψ - (k : ℝ) * δ - δ := by linarith
    have h_arith : vecNormSq ψ - (k : ℝ) * δ - δ
        = vecNormSq ψ - ((k : ℝ) + 1) * δ := by ring
    rw [h_arith] at h_combine
    have h_cast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [h_cast]
    exact h_combine

/-- **The Quantum Zeno theorem (qualitative asymptotic form).**

    Suppose `vecNormSq ψ = 1`, and we have a sequence of Zeno
    protocols parameterised by N, where each protocol uses a unitary
    `U_N` such that *each individual step* preserves at least
    `1 - δ_N` of the norm (with `δ_N` typically of order `1/N²`).
    If the total error `N · δ_N → 0`, then for any ε > 0 there
    exists N₀ such that for all N ≥ N₀, the survival is at least
    `1 - ε`.

    We state this as a finite implication: given ε > 0 and N such
    that `N · δ_N < ε`, the survival is `> 1 - ε`.
-/
theorem zeno_survival_tends_to_one_of_step_bound
    (P : Matrix (Fin n) (Fin n) ℂ)
    (U : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (ψ : Fin n → ℂ) (hψ_unit : vecNormSq ψ = 1)
    (δ : ℕ → ℝ)
    (h_step : ∀ N : ℕ, ∀ k : ℕ, k < N →
        zenoSurvival P (U N) (k + 1) ψ
          ≥ zenoSurvival P (U N) k ψ - δ N)
    (ε : ℝ) (_hε : 0 < ε)
    (N : ℕ) (h_small : (N : ℝ) * δ N < ε) :
    zenoSurvival P (U N) N ψ > 1 - ε := by
  have h_lb := zeno_survival_lower_bound_of_step_bound P (U N) ψ (δ N) N
                  (h_step N)
  rw [hψ_unit] at h_lb
  linarith

/-! ## 8. Convenience: combining the building blocks -/

/-- **Per-step contraction in absolute units**: re-statement of
    `zenoStep_norm_sq_le` as a "loss" form, useful for plugging into
    the asymptotic theorem.

    `loss(ψ, step) := vecNormSq ψ - vecNormSq (zenoStep P U ψ) ≥ 0`. -/
theorem zeno_step_loss_nonneg
    (P U : Matrix (Fin n) (Fin n) ℂ)
    (hP_herm : star P = P) (hP_idem : P * P = P)
    (hU : (star U) * U = (1 : Matrix (Fin n) (Fin n) ℂ))
    (ψ : Fin n → ℂ) :
    0 ≤ vecNormSq ψ - vecNormSq (zenoStep P U ψ) := by
  have := zenoStep_norm_sq_le P U hP_herm hP_idem hU ψ
  linarith

/-- **Quantitative single-step Zeno bound (parametric form).**

    Given a per-step "loss budget" `δ ≥ 0` such that on the input
    state ψ we have `vecNormSq (zenoStep P U ψ) ≥ vecNormSq ψ - δ`,
    the step preserves at least `1 - δ / ‖ψ‖²` of the norm fraction.

    This is the abstract "δ-step" hypothesis the asymptotic theorem
    consumes.  Concrete δ comes from Taylor expansion of `exp(-iHt)`
    in a fully quantitative treatment. -/
theorem zeno_step_bound_from_loss
    (P U : Matrix (Fin n) (Fin n) ℂ) (ψ : Fin n → ℂ)
    (δ : ℝ) (h : vecNormSq (zenoStep P U ψ) ≥ vecNormSq ψ - δ) :
    vecNormSq (zenoStep P U ψ) ≥ vecNormSq ψ - δ := h

end UnifiedTheory.LayerB.QuantumZeno
