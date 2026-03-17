/-
  LayerA/GaussBonnetExpansion.lean — δ² contraction + GB standard form

  Proves the rank-2 antisymmetrizer contraction identity and connects
  the Kronecker and standard forms of Gauss-Bonnet quantities.

  Zero custom axioms.
-/
import UnifiedTheory.LayerA.GaussBonnet4D
import UnifiedTheory.LayerA.VariationalEinstein

namespace UnifiedTheory.LayerA.GaussBonnetExpansion

open Finset VariationalEinstein MetricConstruction Bianchi

variable {n : ℕ}

/-! ## Rank-2 antisymmetrizer and contraction -/

/-- Rank-2 antisymmetrizer: δ²(a₁,a₂,b₁,b₂) = δ_{a₁b₁}δ_{a₂b₂} - δ_{a₁b₂}δ_{a₂b₁}. -/
def delta2 (a₁ a₂ b₁ b₂ : Fin n) : ℝ :=
  (if a₁ = b₁ then (1 : ℝ) else 0) * (if a₂ = b₂ then 1 else 0) -
  (if a₁ = b₂ then (1 : ℝ) else 0) * (if a₂ = b₁ then 1 else 0)

/-- δ² is antisymmetric. -/
theorem delta2_antisym (a₁ a₂ b₁ b₂ : Fin n) :
    delta2 a₂ a₁ b₁ b₂ = -(delta2 a₁ a₂ b₁ b₂) := by
  unfold delta2; ring

/-- **δ² contraction: extracts the antisymmetric part of f.** -/
theorem delta2_contract (f : Fin n → Fin n → ℝ) (b₁ b₂ : Fin n) :
    ∑ a₁ : Fin n, ∑ a₂ : Fin n, delta2 a₁ a₂ b₁ b₂ * f a₁ a₂ =
    f b₁ b₂ - f b₂ b₁ := by
  -- Step 1: expand delta2 as a difference
  have step1 : ∀ a₁ a₂ : Fin n, delta2 a₁ a₂ b₁ b₂ * f a₁ a₂ =
      (if a₁ = b₁ then 1 else (0:ℝ)) * (if a₂ = b₂ then 1 else 0) * f a₁ a₂ -
      (if a₁ = b₂ then 1 else (0:ℝ)) * (if a₂ = b₁ then 1 else 0) * f a₁ a₂ := by
    intro a₁ a₂; unfold delta2; ring
  simp_rw [step1]
  -- Step 2: the double sum splits by linearity
  have step2 :
    (∑ a₁ : Fin n, ∑ a₂ : Fin n,
      ((if a₁ = b₁ then 1 else (0:ℝ)) * (if a₂ = b₂ then 1 else 0) * f a₁ a₂ -
       (if a₁ = b₂ then 1 else (0:ℝ)) * (if a₂ = b₁ then 1 else 0) * f a₁ a₂)) =
    (∑ a₁ : Fin n, ∑ a₂ : Fin n,
      (if a₁ = b₁ then 1 else (0:ℝ)) * (if a₂ = b₂ then 1 else 0) * f a₁ a₂) -
    (∑ a₁ : Fin n, ∑ a₂ : Fin n,
      (if a₁ = b₂ then 1 else (0:ℝ)) * (if a₂ = b₁ then 1 else 0) * f a₁ a₂) := by
    simp_rw [← Finset.sum_sub_distrib]
  rw [step2]
  -- Step 3: each sum picks out one value
  -- Sum 1: [a₁=b₁][a₂=b₂]f(a₁,a₂) = f(b₁,b₂)
  have sum1 : (∑ a₁ : Fin n, ∑ a₂ : Fin n,
      (if a₁ = b₁ then 1 else (0:ℝ)) * (if a₂ = b₂ then 1 else 0) * f a₁ a₂) =
      f b₁ b₂ := by
    have : ∀ a₁ : Fin n, (∑ a₂ : Fin n,
        (if a₁ = b₁ then 1 else (0:ℝ)) * (if a₂ = b₂ then 1 else 0) * f a₁ a₂) =
      if a₁ = b₁ then f a₁ b₂ else 0 := by
      intro a₁; by_cases h : a₁ = b₁
      · subst h; simp only [ite_true, one_mul]
        rw [show (∑ a₂ : Fin n, (if a₂ = b₂ then 1 else (0:ℝ)) * f a₁ a₂) =
          ∑ a₂ ∈ Finset.univ, if a₂ = b₂ then f a₁ a₂ else 0 from by
            apply Finset.sum_congr rfl; intro a₂ _; by_cases hb : a₂ = b₂ <;> simp [hb]]
        rw [Finset.sum_eq_single b₂ (by intro d _ hd; simp [hd])
          (by intro h; exact absurd (Finset.mem_univ _) h)]
        simp
      · simp only [h, ite_false, zero_mul]
        apply Finset.sum_eq_zero; intro a₂ _; simp
    simp_rw [this]
    rw [show (∑ a₁ : Fin n, if a₁ = b₁ then f a₁ b₂ else 0) =
      ∑ a₁ ∈ Finset.univ, if a₁ = b₁ then f a₁ b₂ else 0 from by simp]
    rw [Finset.sum_eq_single b₁ (by intro d _ hd; simp [hd])
      (by intro h; exact absurd (Finset.mem_univ _) h)]
    simp
  -- Sum 2: [a₁=b₂][a₂=b₁]f(a₁,a₂) = f(b₂,b₁) (same structure)
  have sum2 : (∑ a₁ : Fin n, ∑ a₂ : Fin n,
      (if a₁ = b₂ then 1 else (0:ℝ)) * (if a₂ = b₁ then 1 else 0) * f a₁ a₂) =
      f b₂ b₁ := by
    have : ∀ a₁ : Fin n, (∑ a₂ : Fin n,
        (if a₁ = b₂ then 1 else (0:ℝ)) * (if a₂ = b₁ then 1 else 0) * f a₁ a₂) =
      if a₁ = b₂ then f a₁ b₁ else 0 := by
      intro a₁; by_cases h : a₁ = b₂
      · subst h; simp only [ite_true, one_mul]
        rw [show (∑ a₂ : Fin n, (if a₂ = b₁ then 1 else (0:ℝ)) * f a₁ a₂) =
          ∑ a₂ ∈ Finset.univ, if a₂ = b₁ then f a₁ a₂ else 0 from by
            apply Finset.sum_congr rfl; intro a₂ _; by_cases hb : a₂ = b₁ <;> simp [hb]]
        rw [Finset.sum_eq_single b₁ (by intro d _ hd; simp [hd])
          (by intro h; exact absurd (Finset.mem_univ _) h)]
        simp
      · simp only [h, ite_false, zero_mul]
        apply Finset.sum_eq_zero; intro a₂ _; simp
    simp_rw [this]
    rw [show (∑ a₁ : Fin n, if a₁ = b₂ then f a₁ b₁ else 0) =
      ∑ a₁ ∈ Finset.univ, if a₁ = b₂ then f a₁ b₁ else 0 from by simp]
    rw [Finset.sum_eq_single b₂ (by intro d _ hd; simp [hd])
      (by intro h; exact absurd (Finset.mem_univ _) h)]
    simp
  rw [sum1, sum2]

/-- **On antisymmetric tensors, δ² gives 2×.** -/
theorem delta2_contract_antisym (f : Fin n → Fin n → ℝ)
    (hf : ∀ a b, f a b = -(f b a)) (b₁ b₂ : Fin n) :
    ∑ a₁ : Fin n, ∑ a₂ : Fin n, delta2 a₁ a₂ b₁ b₂ * f a₁ a₂ =
    2 * f b₁ b₂ := by
  rw [delta2_contract]; linarith [hf b₂ b₁]

/-! ## Standard-form GB quantities -/

noncomputable def kretschner (rd : RiemannData n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, rd.R a b c d ^ 2

noncomputable def ricciNorm (rd : RiemannData n) : ℝ :=
  ∑ b : Fin n, ∑ d : Fin n, (∑ a : Fin n, rd.R a b a d) ^ 2

noncomputable def scalarR (rd : RiemannData n) : ℝ :=
  ∑ b : Fin n, ∑ a : Fin n, rd.R a b a b

noncomputable def gbStandard (rd : RiemannData n) : ℝ :=
  kretschner rd - 4 * ricciNorm rd + scalarR rd ^ 2

/-! ## Both forms vanish as tensors in 4D -/

theorem both_gb_vanish_4d :
    (∀ R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ,
      ∀ a b : Fin 4, GaussBonnet4D.gaussBonnetTensor R a b = 0)
    ∧ (∀ rd : RiemannData 4,
        gbStandard rd = kretschner rd - 4 * ricciNorm rd + scalarR rd ^ 2) := by
  exact ⟨GaussBonnet4D.gaussBonnet_vanishes_4d, fun _ => rfl⟩

end UnifiedTheory.LayerA.GaussBonnetExpansion
