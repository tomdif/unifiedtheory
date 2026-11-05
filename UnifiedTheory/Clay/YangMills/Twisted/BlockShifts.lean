/- Two facts about orthogonal shifts that need not commute, with no reference to the lattice size.
A Weitzenböck inequality whose error is the commutator of the shifts, and a block Poincaré inequality
for running averages of length `L`. Together they bound the curl-divergence form below by `1/(8L²)`
once the running averages are penalized and the commutator is small. -/
import UnifiedTheory.Clay.YangMills.Twisted.CommutingShifts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.BlockShifts
open CommutingShifts
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Weitzenböck with a commutator error -/

/-- The defect of the mixed adjoint identity is an inner product with the commutator. -/
theorem cross_eq (A B : Shift E) (x y : E) :
    ⟪A.Dstar x, B.Dstar y⟫ - ⟪B.D x, A.D y⟫ =
      ⟪A.T (B.T (A.S x)) - B.T (A.T (A.S x)), A.T y⟫ := by
  have a (u v : E) : ⟪A.S u, v⟫ = ⟪u, A.T v⟫ := by
    rw [real_inner_comm, ← A.adj, real_inner_comm]
  rw [← a]
  have h1 : A.S (A.T (B.T (A.S x)) - B.T (A.T (A.S x))) = B.T (A.S x) - A.S (B.T x) := by
    rw [map_sub, A.left, A.right]
  rw [h1, inner_sub_left]
  simp only [Shift.D, Shift.Dstar, inner_sub_left, inner_sub_right]
  have a1 : ⟪A.S x, B.S y⟫ = ⟪B.T (A.S x), y⟫ := (B.adj _ _).symm
  have a2 := a x y
  have a3 : ⟪x, B.S y⟫ = ⟪B.T x, y⟫ := (B.adj _ _).symm
  have a4 := (a (B.T x) y).symm
  rw [a1, a2, a3, a4]
  ring

/-- The defect of the mixed adjoint identity is controlled by the commutator. -/
theorem cross_error (A B : Shift E) (κ : ℝ)
    (hκ : ∀ x, ‖A.T (B.T x) - B.T (A.T x)‖ ≤ κ * ‖x‖) (x y : E) :
    |⟪A.Dstar x, B.Dstar y⟫ - ⟪B.D x, A.D y⟫| ≤ κ * ‖x‖ * ‖y‖ := by
  rw [cross_eq]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [A.norm_T]
  have := hκ (A.S x)
  rw [A.norm_S] at this
  exact mul_le_mul_of_nonneg_right this (norm_nonneg y)

/-- **Weitzenböck inequality for one field.** If the mixed adjoint identity holds on `ω` to within `κ`,
the curl and divergence control all covariant differences up to `4κ` times the norm. -/
theorem weitzenbock_of_cross (A : Fin 4 → Shift E) (κ : ℝ) (hκ0 : 0 ≤ κ) (ω : Fin 4 → E)
    (hbd' : ∀ μ ν, |⟪(A μ).Dstar (ω μ), (A ν).Dstar (ω ν)⟫ - ⟪(A ν).D (ω μ), (A μ).D (ω ν)⟫| ≤
      κ * ‖ω μ‖ * ‖ω ν‖) :
    ∑ μ, ∑ ν, ‖(A ν).D (ω μ)‖ ^ 2 ≤ curlEnergy A ω + ‖div A ω‖ ^ 2 + 4 * κ * ∑ μ, ‖ω μ‖ ^ 2 := by
  set e : Fin 4 → Fin 4 → ℝ := fun μ ν =>
    ⟪(A μ).Dstar (ω μ), (A ν).Dstar (ω ν)⟫ - ⟪(A ν).D (ω μ), (A μ).D (ω ν)⟫ with he
  have hbd (μ ν : Fin 4) : |e μ ν| ≤ κ * ‖ω μ‖ * ‖ω ν‖ := hbd' μ ν
  have hdiag (μ : Fin 4) : e μ μ = 0 := by
    have : ⟪(A μ).Dstar (ω μ), (A μ).Dstar (ω μ)⟫ = ⟪(A μ).D (ω μ), (A μ).D (ω μ)⟫ := by
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, Shift.norm_Dstar]
    simp only [he, this, sub_self]
  have hid : curlEnergy A ω + ‖div A ω‖ ^ 2 = ∑ μ, ∑ ν, ‖(A ν).D (ω μ)‖ ^ 2 + ∑ μ, ∑ ν, e μ ν := by
    have hd : ‖div A ω‖ ^ 2 = ∑ μ, ∑ ν, ⟪(A μ).Dstar (ω μ), (A ν).Dstar (ω ν)⟫ := by
      rw [← real_inner_self_eq_norm_sq, div, sum_inner]
      simp only [inner_sum]
    have hx (μ ν : Fin 4) : ⟪(A μ).Dstar (ω μ), (A ν).Dstar (ω ν)⟫ =
        ⟪(A ν).D (ω μ), (A μ).D (ω ν)⟫ + e μ ν := by
      simp only [he]
      ring
    have hd2 (μ : Fin 4) : ⟪(A μ).D (ω μ), (A μ).D (ω μ)⟫ = ‖(A μ).D (ω μ)‖ ^ 2 :=
      real_inner_self_eq_norm_sq _
    rw [hd]
    simp only [hx, curlEnergy, curl, norm_sub_sq_real]
    simp only [Fin.sum_univ_four, hd2]
    simp (decide := true) only [if_true, if_false]
    simp only [real_inner_comm]
    ring_nf
  have hsum : -(4 * κ * ∑ μ, ‖ω μ‖ ^ 2) ≤ ∑ μ, ∑ ν, e μ ν := by
    have h1 : -(κ * (∑ μ, ‖ω μ‖) ^ 2) ≤ ∑ μ, ∑ ν, e μ ν := by
      have : (∑ μ, ‖ω μ‖) ^ 2 = ∑ μ, ∑ ν, ‖ω μ‖ * ‖ω ν‖ := by
        rw [sq, Finset.sum_mul_sum]
      rw [this, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun μ _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun ν _ => ?_
      have := (abs_le.1 (hbd μ ν)).1
      linarith only [this]
    have h2 : (∑ μ, ‖ω μ‖) ^ 2 ≤ 4 * ∑ μ, ‖ω μ‖ ^ 2 := by
      simp only [Fin.sum_univ_four]
      generalize ‖ω 0‖ = a
      generalize ‖ω 1‖ = b
      generalize ‖ω 2‖ = c
      generalize ‖ω 3‖ = f
      nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - f), sq_nonneg (b - c),
        sq_nonneg (b - f), sq_nonneg (c - f)]
    have h3 := mul_le_mul_of_nonneg_left h2 hκ0
    linarith only [h1, h3]
  rw [hid]
  linarith only [hsum]

/-- **Weitzenböck inequality.** If the shifts commute to within `κ`, the curl and divergence control
all covariant differences up to `4κ` times the norm. -/
theorem weitzenbock_le (A : Fin 4 → Shift E) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ μ ν x, ‖(A μ).T ((A ν).T x) - (A ν).T ((A μ).T x)‖ ≤ κ * ‖x‖) (ω : Fin 4 → E) :
    ∑ μ, ∑ ν, ‖(A ν).D (ω μ)‖ ^ 2 ≤ curlEnergy A ω + ‖div A ω‖ ^ 2 + 4 * κ * ∑ μ, ‖ω μ‖ ^ 2 :=
  weitzenbock_of_cross A κ hκ0 ω fun μ ν => cross_error _ _ κ (hκ μ ν) _ _

/-! ### Running averages -/

variable (A : Shift E)

/-- Iterates of the shift. -/
def spow (j : ℕ) : E →ₗ[ℝ] E := A.T ^ j

theorem norm_pow (j : ℕ) (x : E) : ‖spow A j x‖ = ‖x‖ := by
  induction j with
  | zero => simp [spow]
  | succ j ih =>
    have : spow A (j + 1) x = A.T (spow A j x) := by
      simp only [spow, pow_succ', Module.End.mul_apply]
    rw [this, A.norm_T, ih]

theorem sub_pow_le (j : ℕ) (x : E) : ‖x - spow A j x‖ ≤ j * ‖A.D x‖ := by
  induction j with
  | zero => simp [spow]
  | succ j ih =>
    have e : x - spow A (j + 1) x = (x - spow A j x) - spow A j (A.D x) := by
      have : spow A (j + 1) x = spow A j (A.T x) := by
        simp only [spow, pow_succ, Module.End.mul_apply]
      rw [this, Shift.D, map_sub]
      abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow A]
    push_cast
    linarith only [ih]

/-- The running average of length `L`. -/
noncomputable def savg (L : ℕ) (x : E) : E := (1 / (L : ℝ)) • ∑ j ∈ Finset.range L, spow A j x

theorem norm_avg_le (L : ℕ) (hL : 1 ≤ L) (x : E) : ‖savg A L x‖ ≤ ‖x‖ := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  unfold savg
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h : ‖∑ j ∈ Finset.range L, spow A j x‖ ≤ L * ‖x‖ := by
    refine (norm_sum_le _ _).trans ?_
    simp [norm_pow A]
  calc 1 / (L : ℝ) * ‖∑ j ∈ Finset.range L, spow A j x‖
      ≤ 1 / (L : ℝ) * (L * ‖x‖) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = ‖x‖ := by field_simp

theorem sub_avg_le (L : ℕ) (hL : 1 ≤ L) (x : E) : ‖x - savg A L x‖ ≤ L * ‖A.D x‖ := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have e : x - savg A L x = (1 / (L : ℝ)) • ∑ j ∈ Finset.range L, (x - spow A j x) := by
    unfold savg
    rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul]
    rw [one_div, inv_mul_cancel₀ hL0.ne', one_smul]
  rw [e, norm_smul, Real.norm_of_nonneg (by positivity)]
  have h : ‖∑ j ∈ Finset.range L, (x - spow A j x)‖ ≤ L * (L * ‖A.D x‖) := by
    refine (norm_sum_le _ _).trans ?_
    have hj : ∀ j ∈ Finset.range L, ‖x - spow A j x‖ ≤ L * ‖A.D x‖ := by
      intro j hj
      refine (sub_pow_le A j x).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact_mod_cast (Finset.mem_range.1 hj).le
    simpa using Finset.sum_le_sum hj
  calc 1 / (L : ℝ) * ‖∑ j ∈ Finset.range L, (x - spow A j x)‖
      ≤ 1 / (L : ℝ) * (L * (L * ‖A.D x‖)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = L * ‖A.D x‖ := by field_simp

/-- The ordered product of the four running averages. -/
noncomputable def blockAvg (A : Fin 4 → Shift E) (L : ℕ) (x : E) : E :=
  savg (A 0) L (savg (A 1) L (savg (A 2) L (savg (A 3) L x)))

theorem sub_blockAvg_le (A : Fin 4 → Shift E) (L : ℕ) (hL : 1 ≤ L) (x : E) :
    ‖x - blockAvg A L x‖ ≤ L * ∑ ν, ‖(A ν).D x‖ := by
  -- Moving each average out costs at most its own difference, since each average is a contraction.
  have step (B : Shift E) (y z : E) : ‖y - savg B L z‖ ≤ ‖y - savg B L y‖ + ‖y - z‖ := by
    have hl : ∀ u v : E, savg B L u - savg B L v = savg B L (u - v) := by
      intro u v
      simp only [savg, map_sub, Finset.sum_sub_distrib, smul_sub]
    have e : y - savg B L z = (y - savg B L y) + savg B L (y - z) := by
      rw [← hl]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := norm_avg_le B L hL (y - z)
    linarith only [this]
  have h3 := sub_avg_le (A 3) L hL x
  have h2 := sub_avg_le (A 2) L hL x
  have h1 := sub_avg_le (A 1) L hL x
  have h0 := sub_avg_le (A 0) L hL x
  have s2 := step (A 2) x (savg (A 3) L x)
  have s1 := step (A 1) x (savg (A 2) L (savg (A 3) L x))
  have s0 := step (A 0) x (savg (A 1) L (savg (A 2) L (savg (A 3) L x)))
  unfold blockAvg
  rw [Fin.sum_univ_four]
  linarith only [h0, h1, h2, h3, s0, s1, s2]

/-- **Block Poincaré inequality.** Independent of any spectral gap of the shifts. -/
theorem block_poincare (A : Fin 4 → Shift E) (L : ℕ) (hL : 1 ≤ L) (x : E) :
    ‖x‖ ^ 2 ≤ 2 * ‖blockAvg A L x‖ ^ 2 + 8 * (L : ℝ) ^ 2 * ∑ ν, ‖(A ν).D x‖ ^ 2 := by
  have h := sub_blockAvg_le A L hL x
  have hx : ‖x‖ ≤ ‖blockAvg A L x‖ + L * ∑ ν, ‖(A ν).D x‖ := by
    have := norm_sub_norm_le x (blockAvg A L x)
    linarith only [this, h]
  have hsq : (∑ ν, ‖(A ν).D x‖) ^ 2 ≤ 4 * ∑ ν, ‖(A ν).D x‖ ^ 2 := by
    simp only [Fin.sum_univ_four]
    generalize ‖(A 0).D x‖ = a
    generalize ‖(A 1).D x‖ = b
    generalize ‖(A 2).D x‖ = c
    generalize ‖(A 3).D x‖ = f
    nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - f), sq_nonneg (b - c),
      sq_nonneg (b - f), sq_nonneg (c - f)]
  set p := ‖blockAvg A L x‖
  set q := (L : ℝ) * ∑ ν, ‖(A ν).D x‖ with hq
  have hp0 : 0 ≤ p := norm_nonneg _
  have hq0 : 0 ≤ q := by
    rw [hq]
    positivity
  have h1 : ‖x‖ ^ 2 ≤ (p + q) ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hx 2
  have h2 : q ^ 2 ≤ (L : ℝ) ^ 2 * (4 * ∑ ν, ‖(A ν).D x‖ ^ 2) := by
    rw [hq, mul_pow]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  nlinarith only [h1, h2, sq_nonneg (p - q)]

/-- **The blocked fluctuation form is coercive at the block scale.** The constant depends on `L` and
the commutator bound `κ` only. Nothing here sees a spectral gap or a lattice size. -/
theorem block_coercive_of_cross (A : Fin 4 → Shift E) (L : ℕ) (hL : 1 ≤ L) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (ω : Fin 4 → E)
    (hbd : ∀ μ ν, |⟪(A μ).Dstar (ω μ), (A ν).Dstar (ω ν)⟫ - ⟪(A ν).D (ω μ), (A μ).D (ω ν)⟫| ≤
      κ * ‖ω μ‖ * ‖ω ν‖) :
    (1 / (8 * (L : ℝ) ^ 2) - 4 * κ) * ∑ μ, ‖ω μ‖ ^ 2 ≤
      curlEnergy A ω + ‖div A ω‖ ^ 2 + 1 / (4 * (L : ℝ) ^ 2) * ∑ μ, ‖blockAvg A L (ω μ)‖ ^ 2 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hW := weitzenbock_of_cross A κ hκ0 ω hbd
  have hP : ∑ μ, ‖ω μ‖ ^ 2 ≤ 2 * ∑ μ, ‖blockAvg A L (ω μ)‖ ^ 2 +
      8 * (L : ℝ) ^ 2 * ∑ μ, ∑ ν, ‖(A ν).D (ω μ)‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun μ _ => block_poincare A L hL (ω μ)
  have hc : 0 < 1 / (8 * (L : ℝ) ^ 2) := by positivity
  have hm := mul_le_mul_of_nonneg_left hP hc.le
  have e : 1 / (8 * (L : ℝ) ^ 2) * (2 * ∑ μ, ‖blockAvg A L (ω μ)‖ ^ 2 +
      8 * (L : ℝ) ^ 2 * ∑ μ, ∑ ν, ‖(A ν).D (ω μ)‖ ^ 2) =
      1 / (4 * (L : ℝ) ^ 2) * ∑ μ, ‖blockAvg A L (ω μ)‖ ^ 2 + ∑ μ, ∑ ν, ‖(A ν).D (ω μ)‖ ^ 2 := by
    field_simp
    ring
  rw [e] at hm
  rw [sub_mul]
  linarith only [hm, hW]

theorem block_coercive (A : Fin 4 → Shift E) (L : ℕ) (hL : 1 ≤ L) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ μ ν x, ‖(A μ).T ((A ν).T x) - (A ν).T ((A μ).T x)‖ ≤ κ * ‖x‖) (ω : Fin 4 → E) :
    (1 / (8 * (L : ℝ) ^ 2) - 4 * κ) * ∑ μ, ‖ω μ‖ ^ 2 ≤
      curlEnergy A ω + ‖div A ω‖ ^ 2 + 1 / (4 * (L : ℝ) ^ 2) * ∑ μ, ‖blockAvg A L (ω μ)‖ ^ 2 :=
  block_coercive_of_cross A L hL κ hκ0 ω fun μ ν => cross_error _ _ κ (hκ μ ν) _ _

/-! ### The split into rough and smooth parts -/

theorem spow_succ (A : Shift E) (j : ℕ) (x : E) : spow A (j + 1) x = A.T (spow A j x) := by
  simp only [spow, pow_succ', Module.End.mul_apply]

/-- The difference of a running average telescopes, so its norm has the factor `1/L`. -/
theorem D_savg_le (A : Shift E) (L : ℕ) (hL : 1 ≤ L) (x : E) :
    ‖A.D (savg A L x)‖ ≤ 2 / (L : ℝ) * ‖x‖ := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum : A.T (∑ j ∈ Finset.range L, spow A j x) - ∑ j ∈ Finset.range L, spow A j x =
      spow A L x - x := by
    rw [map_sum, ← Finset.sum_sub_distrib]
    simp only [← spow_succ]
    rw [Finset.sum_range_sub (fun j => spow A j x)]
    simp [spow]
  have e : A.D (savg A L x) = (1 / (L : ℝ)) • (spow A L x - x) := by
    unfold Shift.D savg
    rw [map_smul, ← smul_sub, hsum]
  rw [e, norm_smul, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖spow A L x - x‖ ≤ 2 * ‖x‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow]
    linarith only []
  calc 1 / (L : ℝ) * ‖spow A L x - x‖ ≤ 1 / (L : ℝ) * (2 * ‖x‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 / (L : ℝ) * ‖x‖ := by ring

theorem comm_spow (A B : Shift E) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ x, ‖B.T (A.T x) - A.T (B.T x)‖ ≤ κ * ‖x‖) (j : ℕ) (y : E) :
    ‖B.T (spow A j y) - spow A j (B.T y)‖ ≤ j * κ * ‖y‖ := by
  induction j with
  | zero => simp [spow]
  | succ j ih =>
    have e : B.T (spow A (j + 1) y) - spow A (j + 1) (B.T y) =
        (B.T (A.T (spow A j y)) - A.T (B.T (spow A j y))) +
          A.T (B.T (spow A j y) - spow A j (B.T y)) := by
      rw [spow_succ, spow_succ, map_sub]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [A.norm_T]
    have h := hκ (spow A j y)
    rw [norm_pow] at h
    push_cast
    linarith only [h, ih]

/-- Moving a difference past an average in another direction costs `L κ`. -/
theorem D_savg_move (A B : Shift E) (L : ℕ) (hL : 1 ≤ L) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ x, ‖B.T (A.T x) - A.T (B.T x)‖ ≤ κ * ‖x‖) (y : E) :
    ‖B.D (savg A L y)‖ ≤ ‖B.D y‖ + L * κ * ‖y‖ := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have e : B.D (savg A L y) = savg A L (B.D y) +
      (1 / (L : ℝ)) • ∑ j ∈ Finset.range L, (B.T (spow A j y) - spow A j (B.T y)) := by
    unfold Shift.D savg
    rw [map_smul, map_sum]
    simp only [map_sub, Finset.sum_sub_distrib, smul_sub]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_avg_le A L hL (B.D y)
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h2 : ‖∑ j ∈ Finset.range L, (B.T (spow A j y) - spow A j (B.T y))‖ ≤
      L * (L * κ * ‖y‖) := by
    refine (norm_sum_le _ _).trans ?_
    have hj : ∀ j ∈ Finset.range L, ‖B.T (spow A j y) - spow A j (B.T y)‖ ≤ L * κ * ‖y‖ := by
      intro j hj
      refine (comm_spow A B κ hκ0 hκ j y).trans ?_
      have hjL : (j : ℝ) ≤ L := by exact_mod_cast (Finset.mem_range.1 hj).le
      have := mul_nonneg hκ0 (norm_nonneg y)
      nlinarith only [hjL, this]
    simpa using Finset.sum_le_sum hj
  have h3 : 1 / (L : ℝ) * ‖∑ j ∈ Finset.range L, (B.T (spow A j y) - spow A j (B.T y))‖ ≤
      L * κ * ‖y‖ := by
    calc _ ≤ 1 / (L : ℝ) * (L * (L * κ * ‖y‖)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by field_simp
  linarith only [h1, h3]

/-- **The smooth part of the split has gradient `1/L`.** The block average of `x` varies at scale `L`,
up to the commutator, and never has more gradient than `x` itself, up to the commutator. -/
theorem smooth_grad (A : Fin 4 → Shift E) (L : ℕ) (hL : 1 ≤ L) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ μ ν x, ‖(A μ).T ((A ν).T x) - (A ν).T ((A μ).T x)‖ ≤ κ * ‖x‖) (x : E) (i : Fin 4) :
    ‖(A i).D (blockAvg A L x)‖ ≤ (2 / (L : ℝ) + 3 * L * κ) * ‖x‖ ∧
      ‖(A i).D (blockAvg A L x)‖ ≤ ‖(A i).D x‖ + 4 * L * κ * ‖x‖ := by
  have hLnn : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hc := mul_nonneg (mul_nonneg hLnn hκ0) (norm_nonneg x)
  have hc2 : (0:ℝ) ≤ 2 / (L : ℝ) * ‖x‖ := by positivity
  set y3 := savg (A 3) L x with hy3
  set y2 := savg (A 2) L y3 with hy2
  set y1 := savg (A 1) L y2 with hy1
  have n3 : ‖y3‖ ≤ ‖x‖ := norm_avg_le _ L hL x
  have n2 : ‖y2‖ ≤ ‖x‖ := (norm_avg_le _ L hL y3).trans n3
  have n1 : ‖y1‖ ≤ ‖x‖ := (norm_avg_le _ L hL y2).trans n2
  have mv (a b : Fin 4) (y : E) (hy : ‖y‖ ≤ ‖x‖) :
      ‖(A b).D (savg (A a) L y)‖ ≤ ‖(A b).D y‖ + L * κ * ‖x‖ := by
    refine (D_savg_move (A a) (A b) L hL κ hκ0 (hκ b a) y).trans ?_
    have := mul_le_mul_of_nonneg_left hy (mul_nonneg hLnn hκ0)
    linarith only [this]
  have tl (a : Fin 4) (y : E) (hy : ‖y‖ ≤ ‖x‖) : ‖(A a).D (savg (A a) L y)‖ ≤ 2 / (L : ℝ) * ‖x‖ :=
    (D_savg_le (A a) L hL y).trans (mul_le_mul_of_nonneg_left hy (by positivity))
  have e : blockAvg A L x = savg (A 0) L y1 := rfl
  rw [e]
  have m0 := mv 0 i y1 n1
  have m1 := mv 1 i y2 n2
  have m2 := mv 2 i y3 n3
  have m3 := mv 3 i x le_rfl
  have ex : (2 / (L : ℝ) + 3 * L * κ) * ‖x‖ = 2 / (L : ℝ) * ‖x‖ + 3 * (L * κ * ‖x‖) := by ring
  have ex4 : 4 * (L : ℝ) * κ * ‖x‖ = 4 * (L * κ * ‖x‖) := by ring
  rw [ex, ex4]
  refine ⟨?_, by linarith only [m0, m1, m2, m3]⟩
  fin_cases i
  · have t := tl 0 y1 n1
    simp only [Fin.zero_eta] at *
    linarith only [t, hc]
  · have t := tl 1 y2 n2
    simp only [Fin.mk_one] at *
    linarith only [t, m0, hc]
  · have t := tl 2 y3 n3
    change ‖(A 2).D (savg (A 0) L y1)‖ ≤ _
    have m0' : ‖(A 2).D (savg (A 0) L y1)‖ ≤ ‖(A 2).D y1‖ + L * κ * ‖x‖ := mv 0 2 y1 n1
    have m1' : ‖(A 2).D y1‖ ≤ ‖(A 2).D y2‖ + L * κ * ‖x‖ := mv 1 2 y2 n2
    linarith only [t, m0', m1', hc]
  · have t := tl 3 x le_rfl
    change ‖(A 3).D (savg (A 0) L y1)‖ ≤ _
    have m0' : ‖(A 3).D (savg (A 0) L y1)‖ ≤ ‖(A 3).D y1‖ + L * κ * ‖x‖ := mv 0 3 y1 n1
    have m1' : ‖(A 3).D y1‖ ≤ ‖(A 3).D y2‖ + L * κ * ‖x‖ := mv 1 3 y2 n2
    have m2' : ‖(A 3).D y2‖ ≤ ‖(A 3).D y3‖ + L * κ * ‖x‖ := mv 2 3 y3 n3
    linarith only [t, m0', m1', m2', hc]

end UnifiedTheory.Clay.YangMills.Twisted.BlockShifts
