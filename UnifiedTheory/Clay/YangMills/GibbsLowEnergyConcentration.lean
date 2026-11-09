/- Quantitative low-energy concentration from an actual positive-measure
low-energy event. The normalization and expectation estimates are proved,
not assumed. The Wilson application must construct the event uniformly in volume. -/
import UnifiedTheory.Clay.YangMills.LocalGibbsComparison
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsLowEnergyConcentration
noncomputable section
open MeasureTheory LocalGibbsComparison

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def weight (D : X → ℝ) (b : ℝ) (x : X) : ℝ := Real.exp (-b * D x)

theorem weight_continuous (D : X → ℝ) (hD : Continuous D) (b : ℝ) :
    Continuous (weight D b) := Real.continuous_exp.comp (continuous_const.mul hD)

theorem partition_lower (D : X → ℝ) (hD : Continuous D)
    (b : ℝ) (hb : 0 ≤ b) (eps p : ℝ) (A : Set X) (hA : MeasurableSet A)
    (hpA : p ≤ μ.real A) (hgood : ∀ x ∈ A, D x ≤ eps) :
    p * Real.exp (-b * eps) ≤ ∫ x, weight D b x ∂μ := by
  have hi := (weight_continuous D hD b).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  calc
    p * Real.exp (-b * eps) ≤ μ.real A * Real.exp (-b * eps) :=
      mul_le_mul_of_nonneg_right hpA (Real.exp_pos _).le
    _ = ∫ x in A, Real.exp (-b * eps) ∂μ := by
      rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ x in A, weight D b x ∂μ := by
      apply setIntegral_mono_on (integrable_const _) hi.integrableOn hA
      intro x hx
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hgood x hx) (neg_nonpos.mpr hb)
    _ ≤ ∫ x, weight D b x ∂μ :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))

/-- The concentration estimate keeps the normalization explicit, so a
uniform-in-volume lower bound for the good event can be substituted directly. -/
theorem expectation_bound (D : X → ℝ) (hD : Continuous D)
    (b : ℝ) (hb : 0 ≤ b) (eps : ℝ) (heps : 0 ≤ eps)
    (M : ℝ) (hM : 0 ≤ M) (hDM : ∀ x, D x ≤ M)
    (p : ℝ) (hp : 0 < p) (A : Set X) (hA : MeasurableSet A)
    (hpA : p ≤ μ.real A) (hgood : ∀ x ∈ A, D x ≤ eps) :
    (∫ x, D x ∂weightedLaw μ (weight D b)) ≤
      2 * eps + (M / p) * Real.exp (-b * eps) := by
  have hlow := partition_lower μ D hD b hb eps p A hA hpA hgood
  have hz : 0 < ∫ x, weight D b x ∂μ :=
    (mul_pos hp (Real.exp_pos _)).trans_le hlow
  have hw := weight_continuous D hD b
  have hi := hw.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hnum : (∫ x, weight D b x * D x ∂μ) ≤
      2 * eps * (∫ x, weight D b x ∂μ) + M * Real.exp (-b * (2 * eps)) := by
    have hic : Integrable (fun x =>
        2 * eps * weight D b x + M * Real.exp (-b * (2 * eps))) μ :=
      ((continuous_const.mul hw).add continuous_const).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc
      (∫ x, weight D b x * D x ∂μ) ≤
          ∫ x, 2 * eps * weight D b x + M * Real.exp (-b * (2 * eps)) ∂μ := by
        apply integral_mono
          ((hw.mul hD).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hic
        intro x
        change weight D b x * D x ≤
          2 * eps * weight D b x + M * Real.exp (-b * (2 * eps))
        by_cases h : D x ≤ 2 * eps
        · have he := mul_le_mul_of_nonneg_left h (Real.exp_pos (-b * D x)).le
          have hn := mul_nonneg hM (Real.exp_pos (-b * (2 * eps))).le
          dsimp only [weight] at *
          nlinarith
        · have he : weight D b x ≤ Real.exp (-b * (2 * eps)) := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonpos_left (le_of_lt (lt_of_not_ge h)) (neg_nonpos.mpr hb)
          have hprod := mul_le_mul_of_nonneg_left (hDM x) (Real.exp_pos (-b * D x)).le
          have heprod := mul_le_mul_of_nonneg_right he hM
          have hn : 0 ≤ 2 * eps * weight D b x :=
            mul_nonneg (mul_nonneg (by norm_num) heps) (Real.exp_pos _).le
          dsimp only [weight] at heprod hn ⊢
          nlinarith
      _ = _ := by
        rw [integral_add (hi.const_mul _) (integrable_const _), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
  rw [weighted_integral μ (weight D b) hw.measurable
    (fun x => (Real.exp_pos _).le) hz D]
  apply (div_le_iff₀ hz).mpr
  have hfactor := mul_le_mul_of_nonneg_left hlow
    (mul_nonneg (div_nonneg hM hp.le) (Real.exp_pos (-b * eps)).le)
  have hexp : Real.exp (-b * (2 * eps)) =
      Real.exp (-b * eps) * Real.exp (-b * eps) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hid : (M / p * Real.exp (-b * eps)) * (p * Real.exp (-b * eps)) =
      M * Real.exp (-b * (2 * eps)) := by
    rw [hexp]
    field_simp
  rw [hid] at hfactor
  nlinarith

/-- Four links and six plaquettes per vertex give a volume-independent bound
once the low-energy product event has its actual Haar lower bound. -/
theorem volume_uniform_expectation_bound (D : X → ℝ) (hD : Continuous D)
    (beta : ℝ) (hbeta : 0 ≤ beta) (eps : ℝ) (heps : 0 ≤ eps)
    (M : ℝ) (hM : 0 ≤ M) (hDM : ∀ x, D x ≤ M)
    (q : ℝ) (hq : 0 < q) (V : ℕ) (hV : 0 < V)
    (A : Set X) (hA : MeasurableSet A)
    (hpA : q ^ (4 * V) ≤ μ.real A) (hgood : ∀ x ∈ A, D x ≤ eps)
    (hr : Real.exp (-6 * beta * eps) / q ^ 4 ≤ 1) :
    (∫ x, D x ∂weightedLaw μ (weight D (6 * beta * V))) ≤
      2 * eps + M * (Real.exp (-6 * beta * eps) / q ^ 4) := by
  have hb : 0 ≤ 6 * beta * (V : ℝ) := by positivity
  have h := expectation_bound μ D hD (6 * beta * V) hb eps heps M hM hDM
    (q ^ (4 * V)) (pow_pos hq _) A hA hpA hgood
  have hexp : Real.exp (-(6 * beta * (V : ℝ)) * eps) =
      (Real.exp (-6 * beta * eps)) ^ V := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hid : (M / q ^ (4 * V)) * Real.exp (-(6 * beta * (V : ℝ)) * eps) =
      M * (Real.exp (-6 * beta * eps) / q ^ 4) ^ V := by
    rw [hexp, div_pow, ← pow_mul]
    ring
  rw [hid] at h
  apply h.trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ hM
  have hr0 : 0 ≤ Real.exp (-6 * beta * eps) / q ^ 4 := by positivity
  cases V with
  | zero => omega
  | succ n =>
      rw [pow_succ]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 hr) hr0

end
end UnifiedTheory.Clay.YangMills.GibbsLowEnergyConcentration
