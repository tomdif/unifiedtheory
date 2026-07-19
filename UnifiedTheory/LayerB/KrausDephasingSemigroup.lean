/-
  LayerB/KrausDephasingSemigroup.lean
  ────────────────────────────────────

  The dephasing semigroup: composing two dephasing channels at
  parameters γ₁, γ₂ gives a dephasing channel at parameter γ₁·γ₂.

  Combined with the new `compose` infrastructure, this gives the
  N-fold decoherence collapse:

      (dephasingKraus γ) ∘ ⋯ ∘ (dephasingKraus γ)  (N times)
        ≅  dephasingKraus (γ^N)                     (on apply)

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `mul_mem_neg_one_one_of_abs_le_one`:  if |γ₁| ≤ 1 and |γ₂| ≤ 1
       then γ₁·γ₂ ∈ [-1, 1] (the dephasingKraus parameter constraint
       is preserved under composition).
    2. `dephasingKraus_compose_apply` (the semigroup law on apply):
          (compose (dephasingKraus γ₁) (dephasingKraus γ₂)).apply ρ
            = (dephasingKraus (γ₁ * γ₂)).apply ρ.
    3. `nfoldCompose` recursive N-fold self-composition.
    4. `dephasingKraus_pow_apply` (N-fold decoherence collapse):
          (nfoldCompose N (dephasingKraus γ)).apply ρ
            = (dephasingKraus (γ^N)).apply ρ.

  Physical reading:  multi-step dephasing collapses to one effective
  dephasing parameter γ^N — exactly the discrete-time signature of
  the continuous Lindblad equation `dρ/dt = (1/2)(σ_z ρ σ_z − ρ)`
  with γ = e^{-Γt}.
-/

import UnifiedTheory.LayerB.KrausLindbladBridge
import UnifiedTheory.LayerB.KrausComposition

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Kraus

open Matrix Complex
open scoped ComplexOrder

/-! ## 1. Parameter range is preserved under multiplication -/

/-- If γ₁, γ₂ ∈ [-1, 1] then γ₁·γ₂ ∈ [-1, 1]. -/
theorem mul_mem_neg_one_one {γ₁ γ₂ : ℝ}
    (hγ₁_le : γ₁ ≤ 1) (hγ₁_ge : -1 ≤ γ₁)
    (hγ₂_le : γ₂ ≤ 1) (hγ₂_ge : -1 ≤ γ₂) :
    γ₁ * γ₂ ≤ 1 ∧ -1 ≤ γ₁ * γ₂ := by
  have h_abs₁ : |γ₁| ≤ 1 := abs_le.mpr ⟨hγ₁_ge, hγ₁_le⟩
  have h_abs₂ : |γ₂| ≤ 1 := abs_le.mpr ⟨hγ₂_ge, hγ₂_le⟩
  have h_abs_mul : |γ₁ * γ₂| ≤ 1 := by
    rw [abs_mul]
    calc |γ₁| * |γ₂| ≤ 1 * 1 := by
          apply mul_le_mul h_abs₁ h_abs₂ (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  exact ⟨(abs_le.mp h_abs_mul).2, (abs_le.mp h_abs_mul).1⟩

/-! ## 2. The semigroup law on the dephasing channel -/

/-- **Dephasing semigroup law.**  Composing two dephasing channels
    multiplies their parameters:

        (dephasingKraus γ₁) ∘ (dephasingKraus γ₂)  ≅  dephasingKraus (γ₁ · γ₂)

    (equality at the level of the induced map on density matrices). -/
theorem dephasingKraus_compose_apply
    (γ₁ γ₂ : ℝ)
    (hγ₁_le : γ₁ ≤ 1) (hγ₁_ge : -1 ≤ γ₁)
    (hγ₂_le : γ₂ ≤ 1) (hγ₂_ge : -1 ≤ γ₂)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (compose (dephasingKraus γ₁ hγ₁_le hγ₁_ge)
             (dephasingKraus γ₂ hγ₂_le hγ₂_ge)).apply ρ
      = (dephasingKraus (γ₁ * γ₂)
          (mul_mem_neg_one_one hγ₁_le hγ₁_ge hγ₂_le hγ₂_ge).1
          (mul_mem_neg_one_one hγ₁_le hγ₁_ge hγ₂_le hγ₂_ge).2).apply ρ := by
  -- LHS via compose_apply: outer dephasing applied to inner dephasing output
  rw [compose_apply]
  -- Expand inner dephasing
  rw [dephasingKraus_apply_formula γ₂ hγ₂_le hγ₂_ge ρ]
  -- Expand outer dephasing applied to the linear combination
  rw [dephasingKraus_apply_formula γ₁ hγ₁_le hγ₁_ge]
  -- Expand RHS dephasing
  rw [dephasingKraus_apply_formula (γ₁ * γ₂) _ _ ρ]
  -- LHS: α₁²·(α₂²·ρ + β₂²·σρσ) + β₁²·σ·(α₂²·ρ + β₂²·σρσ)·σ
  -- Distribute and use σ² = I; then identify coefficients.
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add,
             Matrix.add_mul, Matrix.mul_add]
  -- Replace pauliZ * (pauliZ * ρ * pauliZ) * pauliZ with ρ
  rw [show pauliZ * (pauliZ * ρ * pauliZ) * pauliZ = ρ from by
        -- Re-associate to (pauliZ * pauliZ) * ρ * (pauliZ * pauliZ) = I * ρ * I = ρ
        rw [Matrix.mul_assoc pauliZ ρ pauliZ,
            ← Matrix.mul_assoc pauliZ pauliZ (ρ * pauliZ),
            pauliZ_mul_self, Matrix.one_mul,
            Matrix.mul_assoc ρ pauliZ pauliZ,
            pauliZ_mul_self, Matrix.mul_one]]
  -- Combine smul towers (smul_smul : a • b • x = (a*b) • x)
  simp_rw [smul_smul]
  -- Group like terms and identify coefficients
  have h_coeff_diag : (((1 + γ₁) / 2 : ℝ) : ℂ) * (((1 + γ₂) / 2 : ℝ) : ℂ)
                     + (((1 - γ₁) / 2 : ℝ) : ℂ) * (((1 - γ₂) / 2 : ℝ) : ℂ)
                     = (((1 + γ₁ * γ₂) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h_coeff_off : (((1 + γ₁) / 2 : ℝ) : ℂ) * (((1 - γ₂) / 2 : ℝ) : ℂ)
                    + (((1 - γ₁) / 2 : ℝ) : ℂ) * (((1 + γ₂) / 2 : ℝ) : ℂ)
                    = (((1 - γ₁ * γ₂) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [show ∀ (a b c d : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ),
        a • X + b • Y + (c • Y + d • X) = (a + d) • X + (b + c) • Y from by
        intros a b c d X Y
        rw [add_smul, add_smul]
        abel]
  rw [h_coeff_diag, h_coeff_off]

/-! ## 3. N-fold self-composition -/

/-- `nfoldCompose N K` is the N-fold self-composition of K, with
    `nfoldCompose 0 K = identity` and
    `nfoldCompose (N+1) K = compose (nfoldCompose N K) K`
    (K applied first, then N more times).  Defined structurally so the
    type `KrausRepresentation m m (k^N)` matches `Nat.pow_succ` directly. -/
noncomputable def nfoldCompose {m k : ℕ} :
    (N : ℕ) → KrausRepresentation m m k → KrausRepresentation m m (k ^ N)
  | 0, _ => KrausRepresentation.identity m
  | N + 1, K => compose (nfoldCompose N K) K

/-! ## 4. N-fold decoherence collapses to one effective parameter -/

/-- Helper: γ^N stays in [-1, 1] when γ ∈ [-1, 1]. -/
theorem pow_mem_neg_one_one {γ : ℝ} (hγ_le : γ ≤ 1) (hγ_ge : -1 ≤ γ) (N : ℕ) :
    γ ^ N ≤ 1 ∧ -1 ≤ γ ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
    have h_abs : |γ ^ (n + 1)| ≤ 1 := by
      rw [pow_succ, abs_mul]
      have h_abs_n : |γ ^ n| ≤ 1 := abs_le.mpr ⟨ih.2, ih.1⟩
      have h_abs_γ : |γ| ≤ 1 := abs_le.mpr ⟨hγ_ge, hγ_le⟩
      calc |γ ^ n| * |γ| ≤ 1 * 1 :=
            mul_le_mul h_abs_n h_abs_γ (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    exact ⟨(abs_le.mp h_abs).2, (abs_le.mp h_abs).1⟩

/-- **N-fold decoherence collapse.**  N applications of the dephasing
    channel with parameter γ produce the dephasing channel with
    parameter γ^N:

        (nfoldCompose N (dephasingKraus γ)).apply ρ
          = (dephasingKraus (γ^N)).apply ρ .

    Stated with `∀ ρ` quantified inside so the inductive hypothesis
    can be applied to substituted arguments. -/
theorem dephasingKraus_pow_apply
    (γ : ℝ) (hγ_le : γ ≤ 1) (hγ_ge : -1 ≤ γ) (N : ℕ) :
    ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      (nfoldCompose N (dephasingKraus γ hγ_le hγ_ge)).apply ρ
        = (dephasingKraus (γ ^ N)
            (pow_mem_neg_one_one hγ_le hγ_ge N).1
            (pow_mem_neg_one_one hγ_le hγ_ge N).2).apply ρ := by
  induction N with
  | zero =>
    intro ρ
    -- Reduce both sides via the formula (which doesn't carry the bound proofs)
    change (KrausRepresentation.identity 2).apply ρ
        = (dephasingKraus (γ ^ 0) _ _).apply ρ
    rw [KrausRepresentation.identity_apply, dephasingKraus_apply_formula]
    -- Goal: ρ = ((1 + γ^0)/2 : ℂ) • ρ + ((1 - γ^0)/2 : ℂ) • (pauliZ * ρ * pauliZ)
    rw [show γ ^ 0 = (1 : ℝ) from pow_zero γ]
    rw [show ((1 + 1 : ℝ) / 2 : ℝ) = (1 : ℝ) from by norm_num,
        show ((1 - 1 : ℝ) / 2 : ℝ) = (0 : ℝ) from by norm_num]
    simp [one_smul, zero_smul, add_zero]
  | succ n ih =>
    intro ρ
    -- nfoldCompose (n+1) = compose (nfoldCompose n K) K
    change ((compose (nfoldCompose n (dephasingKraus γ hγ_le hγ_ge))
                   (dephasingKraus γ hγ_le hγ_ge))).apply ρ
       = (dephasingKraus (γ ^ (n + 1)) _ _).apply ρ
    rw [compose_apply, ih]
    -- Now: (dephasingKraus γ^n).apply ((dephasingKraus γ).apply ρ) = ...
    rw [show (dephasingKraus (γ ^ n) _ _).apply ((dephasingKraus γ hγ_le hγ_ge).apply ρ)
          = (compose (dephasingKraus (γ ^ n) _ _) (dephasingKraus γ hγ_le hγ_ge)).apply ρ
          from (compose_apply _ _ _).symm]
    rw [dephasingKraus_compose_apply]
    -- Now both sides have dephasingKraus _ via apply.  Unfold via formula
    -- to dodge the dependent proof terms.
    rw [dephasingKraus_apply_formula, dephasingKraus_apply_formula]
    -- Substitute γ^n * γ = γ^(n+1)
    rw [show γ ^ n * γ = γ ^ (n + 1) from (pow_succ γ n).symm]

end UnifiedTheory.LayerB.Kraus
