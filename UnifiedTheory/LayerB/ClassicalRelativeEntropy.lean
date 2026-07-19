/-
  LayerB/ClassicalRelativeEntropy.lean
  ─────────────────────────────────────

  Classical (scalar) relative entropy / Kullback-Leibler divergence,
  built on `ProbabilityVector α` from `ClassicalEntropy.lean`.

  We use a *safe* per-term function

      klTerm p q  :=  if p = 0 then 0 else p · log(p / q)

  so the zero-mass terms drop out cleanly without invoking the
  `Real.log 0 = 0` convention.  (It happens that in Mathlib the two
  formulas agree numerically; we still keep the guard for readable
  zero handling.)

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `klTerm p q`        — safe per-term.
    2. `klDivergence P Q`  — scalar KL divergence.
    3. `IsAbsolutelyContinuous P Q`
                            — `P_i ≠ 0 → Q_i ≠ 0` on every index.
    4. `klDivergence_congr`           — extensionality.
    5. `klDivergence_self_eq_zero`    — KL(P‖P) = 0.
    6. `klDivergence_delta`           — KL(δ_{i₀}‖Q) = −log Q(i₀),
                                         assuming Q(i₀) ≠ 0.
    7. `klDivergence_uniform`         — KL(P‖U_n) = log n − H(P).
    8. `klDivergence_product_add`     — KL(P₁⊗P₂‖Q₁⊗Q₂)
                                         = KL(P₁‖Q₁) + KL(P₂‖Q₂),
                                         assuming P₁ ≪ Q₁ and P₂ ≪ Q₂.

  Full Gibbs inequality (KL ≥ 0) is intentionally deferred to a
  follow-up file; the current pass is purely algebraic / additive.

  Downstream files will reuse `klDivergence` as the scalar engine
  for diagonal and spectral (commuting-basis) quantum relative
  entropy, and ultimately for the classical-channel DPI.
-/

import UnifiedTheory.LayerB.ClassicalEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.ClassicalRelativeEntropy

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ## 1. The safe per-term function -/

/-- The Kullback–Leibler per-term:
      `klTerm p q = 0`                       if `p = 0`,
      `klTerm p q = p · log(p / q)`          otherwise.
    The guard avoids relying on the `Real.log 0 = 0` convention
    when `p = 0`. -/
noncomputable def klTerm (p q : ℝ) : ℝ :=
  if p = 0 then 0 else p * Real.log (p / q)

@[simp]
lemma klTerm_zero_left (q : ℝ) : klTerm 0 q = 0 := by
  unfold klTerm; rw [if_pos rfl]

lemma klTerm_of_ne_zero {p : ℝ} (hp : p ≠ 0) (q : ℝ) :
    klTerm p q = p * Real.log (p / q) := by
  unfold klTerm; rw [if_neg hp]

/-- The guard is convention-only: numerically `klTerm` agrees with
    the naive formula because Mathlib chooses `0 · _ = 0`. -/
lemma klTerm_eq (p q : ℝ) : klTerm p q = p * Real.log (p / q) := by
  by_cases h : p = 0
  · rw [h, klTerm_zero_left, zero_mul]
  · exact klTerm_of_ne_zero h q

/-- KL term against self vanishes for all `p` (including `p = 0`). -/
lemma klTerm_self (p : ℝ) : klTerm p p = 0 := by
  by_cases h : p = 0
  · rw [h, klTerm_zero_left]
  · rw [klTerm_of_ne_zero h, div_self h, Real.log_one, mul_zero]

/-! ## 2. The KL divergence -/

/-- Classical Kullback–Leibler divergence `KL(P‖Q)`. -/
noncomputable def klDivergence (P Q : ProbabilityVector α) : ℝ :=
  ∑ i, klTerm (P.p i) (Q.p i)

/-- `P` is *absolutely continuous* w.r.t. `Q` if `Q` vanishes only
    where `P` does. -/
def IsAbsolutelyContinuous (P Q : ProbabilityVector α) : Prop :=
  ∀ i, P.p i ≠ 0 → Q.p i ≠ 0

/-! ## 3. Extensionality / congr -/

theorem klDivergence_congr (P P' Q Q' : ProbabilityVector α)
    (hP : ∀ i, P.p i = P'.p i) (hQ : ∀ i, Q.p i = Q'.p i) :
    klDivergence P Q = klDivergence P' Q' := by
  unfold klDivergence
  apply Finset.sum_congr rfl
  intro i _
  rw [hP i, hQ i]

/-! ## 4. KL of a distribution against itself is zero -/

theorem klDivergence_self_eq_zero (P : ProbabilityVector α) :
    klDivergence P P = 0 := by
  unfold klDivergence
  apply Finset.sum_eq_zero
  intro i _
  exact klTerm_self (P.p i)

/-! ## 5. KL of a delta against an arbitrary distribution -/

/-- **Delta KL identity:** `KL(δ_{i₀} ‖ Q) = −log Q(i₀)`, provided
    `Q(i₀) ≠ 0`. -/
theorem klDivergence_delta [DecidableEq α]
    (Q : ProbabilityVector α) (i₀ : α) (hQ : Q.p i₀ ≠ 0) :
    klDivergence (delta α i₀) Q = -Real.log (Q.p i₀) := by
  unfold klDivergence
  rw [Finset.sum_eq_single i₀]
  · -- The surviving term at `i = i₀`
    have h_delta_pos : (delta α i₀).p i₀ = 1 := by
      change (if i₀ = i₀ then (1 : ℝ) else 0) = 1
      simp
    rw [h_delta_pos, klTerm_of_ne_zero one_ne_zero, one_mul,
        Real.log_div one_ne_zero hQ, Real.log_one, zero_sub]
  · -- Off-support terms vanish (delta is zero there)
    intro j _ hj
    have h_delta_zero : (delta α i₀).p j = 0 := by
      change (if j = i₀ then (1 : ℝ) else 0) = 0
      simp [hj]
    rw [h_delta_zero, klTerm_zero_left]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## 6. KL against the uniform distribution -/

/-- Per-term identity for KL against uniform:
    `klTerm (P.p i) (1/n) = P.p i · log P.p i + P.p i · log n`
    (holds even at `P.p i = 0` because both sides are zero there). -/
private lemma klTerm_against_uniform_term
    {n : ℕ} (P : ProbabilityVector (Fin n)) (hn : 0 < n) (i : Fin n) :
    klTerm (P.p i) ((1 : ℝ) / (n : ℝ))
      = P.p i * Real.log (P.p i) + P.p i * Real.log n := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  by_cases hpi : P.p i = 0
  · rw [hpi, klTerm_zero_left]
    ring
  · rw [klTerm_of_ne_zero hpi]
    have h_div : P.p i / ((1 : ℝ) / (n : ℝ)) = P.p i * n := by
      field_simp
    rw [h_div, Real.log_mul hpi hn_ne]
    ring

/-- **Uniform KL identity:** `KL(P ‖ U_n) = log n − H(P)`. -/
theorem klDivergence_uniform {n : ℕ}
    (P : ProbabilityVector (Fin n)) (hn : 0 < n) :
    klDivergence P (uniform n hn) = Real.log n - shannonEntropy P := by
  unfold klDivergence shannonEntropy
  -- Each summand splits as `P.p i · log P.p i + P.p i · log n`
  have h_per : ∀ i, klTerm (P.p i) ((uniform n hn).p i)
                  = P.p i * Real.log (P.p i) + P.p i * Real.log n := by
    intro i
    -- `(uniform n hn).p i = 1 / n` by definition
    change klTerm (P.p i) ((1 : ℝ) / (n : ℝ))
         = P.p i * Real.log (P.p i) + P.p i * Real.log n
    exact klTerm_against_uniform_term P hn i
  simp_rw [h_per]
  rw [Finset.sum_add_distrib]
  -- ∑ P.p i · log n = log n · ∑ P.p i = log n
  rw [← Finset.sum_mul, P.sum_one, one_mul]
  ring

/-! ## 7. Product additivity (the key for downstream DPI) -/

/-- Per-term split under absolute continuity:
    `klTerm (p₁q₁ , Q₁(i)·Q₂(j))` factors additively into a
    `log(P₁/Q₁)`-part and a `log(P₂/Q₂)`-part. -/
private lemma klTerm_product_split
    (p₁ p₂ q₁ q₂ : ℝ)
    (h₁ : p₁ ≠ 0 → q₁ ≠ 0) (h₂ : p₂ ≠ 0 → q₂ ≠ 0) :
    klTerm (p₁ * p₂) (q₁ * q₂)
      = p₁ * p₂ * Real.log (p₁ / q₁) + p₁ * p₂ * Real.log (p₂ / q₂) := by
  by_cases hp₁ : p₁ = 0
  · rw [hp₁, zero_mul, klTerm_zero_left]; ring
  by_cases hp₂ : p₂ = 0
  · rw [hp₂, mul_zero, klTerm_zero_left]; ring
  have hq₁ : q₁ ≠ 0 := h₁ hp₁
  have hq₂ : q₂ ≠ 0 := h₂ hp₂
  have hprod_p : p₁ * p₂ ≠ 0 := mul_ne_zero hp₁ hp₂
  have hprod_q : q₁ * q₂ ≠ 0 := mul_ne_zero hq₁ hq₂
  rw [klTerm_of_ne_zero hprod_p]
  -- (p₁p₂)/(q₁q₂) = (p₁/q₁) · (p₂/q₂)
  have h_div : p₁ * p₂ / (q₁ * q₂) = (p₁ / q₁) * (p₂ / q₂) := by
    field_simp
  rw [h_div]
  -- log((p₁/q₁)(p₂/q₂)) = log(p₁/q₁) + log(p₂/q₂)
  have hr₁ : p₁ / q₁ ≠ 0 := div_ne_zero hp₁ hq₁
  have hr₂ : p₂ / q₂ ≠ 0 := div_ne_zero hp₂ hq₂
  rw [Real.log_mul hr₁ hr₂]
  ring

/-- **Product additivity of KL divergence** (the scalar analogue
    of additivity of relative entropy under independent tensoring):

      KL(P₁ ⊗ P₂ ‖ Q₁ ⊗ Q₂) = KL(P₁ ‖ Q₁) + KL(P₂ ‖ Q₂)

    under absolute continuity in each factor. -/
theorem klDivergence_product_add
    (P₁ Q₁ : ProbabilityVector α) (P₂ Q₂ : ProbabilityVector β)
    (hAC₁ : IsAbsolutelyContinuous P₁ Q₁)
    (hAC₂ : IsAbsolutelyContinuous P₂ Q₂) :
    klDivergence (productDistribution P₁ P₂) (productDistribution Q₁ Q₂)
      = klDivergence P₁ Q₁ + klDivergence P₂ Q₂ := by
  unfold klDivergence
  -- Per-term split for the product distribution
  have h_per : ∀ ij : α × β,
      klTerm ((productDistribution P₁ P₂).p ij)
              ((productDistribution Q₁ Q₂).p ij)
        = P₁.p ij.1 * P₂.p ij.2 * Real.log (P₁.p ij.1 / Q₁.p ij.1)
          + P₁.p ij.1 * P₂.p ij.2 * Real.log (P₂.p ij.2 / Q₂.p ij.2) := by
    intro ij
    change klTerm (P₁.p ij.1 * P₂.p ij.2) (Q₁.p ij.1 * Q₂.p ij.2) = _
    exact klTerm_product_split _ _ _ _ (hAC₁ ij.1) (hAC₂ ij.2)
  simp_rw [h_per]
  rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type]
  congr 1
  · -- First half:  ∑ i ∑ j  P₁ i · P₂ j · log(P₁ i / Q₁ i)
    --             = ∑ i, klTerm(P₁ i, Q₁ i)
    calc (∑ i, ∑ j, P₁.p i * P₂.p j * Real.log (P₁.p i / Q₁.p i))
        = ∑ i, P₁.p i * Real.log (P₁.p i / Q₁.p i) := by
              apply Finset.sum_congr rfl; intro i _
              calc (∑ j, P₁.p i * P₂.p j * Real.log (P₁.p i / Q₁.p i))
                  = ∑ j, P₂.p j * (P₁.p i * Real.log (P₁.p i / Q₁.p i)) := by
                        apply Finset.sum_congr rfl; intro j _; ring
                _ = (∑ j, P₂.p j) * (P₁.p i * Real.log (P₁.p i / Q₁.p i)) := by
                        rw [← Finset.sum_mul]
                _ = P₁.p i * Real.log (P₁.p i / Q₁.p i) := by
                        rw [P₂.sum_one, one_mul]
      _ = ∑ i, klTerm (P₁.p i) (Q₁.p i) := by
              apply Finset.sum_congr rfl; intro i _
              rw [klTerm_eq]
  · -- Second half: ∑ i ∑ j  P₁ i · P₂ j · log(P₂ j / Q₂ j)
    --             = ∑ j, klTerm(P₂ j, Q₂ j)
    calc (∑ i, ∑ j, P₁.p i * P₂.p j * Real.log (P₂.p j / Q₂.p j))
        = ∑ i, P₁.p i * (∑ j, P₂.p j * Real.log (P₂.p j / Q₂.p j)) := by
              apply Finset.sum_congr rfl; intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro j _; ring
      _ = (∑ i, P₁.p i) * (∑ j, P₂.p j * Real.log (P₂.p j / Q₂.p j)) := by
              rw [← Finset.sum_mul]
      _ = ∑ j, P₂.p j * Real.log (P₂.p j / Q₂.p j) := by
              rw [P₁.sum_one, one_mul]
      _ = ∑ j, klTerm (P₂.p j) (Q₂.p j) := by
              apply Finset.sum_congr rfl; intro j _
              rw [klTerm_eq]

end UnifiedTheory.LayerB.ClassicalRelativeEntropy
