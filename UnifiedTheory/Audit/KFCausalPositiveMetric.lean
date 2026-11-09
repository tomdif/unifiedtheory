/-
  A positive finite-dimensional metric with exact two-sided moment control.

  This formalizes the resolved observable in POSITIVE_SPECTRAL_METRIC.md.
  The Hermitian field and coupling are inputs; no microscopic field limit,
  Einstein constraint algebra, or physical identification is assumed proved.
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPositiveMetric
noncomputable section
open scoped BigOperators
open Matrix

/-- The scalar chart, with the physical coupling kept explicit. -/
def scalarMetric (g x : ℝ) : ℝ := (Real.sqrt (1 + (g * x / 2)^2) + g * x / 2)^2

theorem scalarMetric_pos (g x : ℝ) : 0 < scalarMetric g x := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + (g * x / 2)^2 by positivity)
  have hn := Real.sqrt_nonneg (1 + (g * x / 2)^2)
  have : 0 < Real.sqrt (1 + (g * x / 2)^2) + g * x / 2 := by nlinarith
  exact sq_pos_of_pos this

theorem scalarMetric_mul_neg (g x : ℝ) : scalarMetric g x * scalarMetric (-g) x = 1 := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + (g * x / 2)^2 by positivity)
  have he : (-g * x / 2)^2 = (g * x / 2)^2 := by ring
  unfold scalarMetric
  rw [he]
  nlinarith [sq_nonneg (Real.sqrt (1 + (g * x / 2)^2) - g * x / 2)]

theorem scalarMetric_add_neg (g x : ℝ) :
    scalarMetric g x + scalarMetric (-g) x = 2 + g^2 * x^2 := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + (g * x / 2)^2 by positivity)
  have he : (-g * x / 2)^2 = (g * x / 2)^2 := by ring
  unfold scalarMetric
  rw [he]
  nlinarith

theorem continuous_scalarMetric (g : ℝ) : Continuous (scalarMetric g) := by
  unfold scalarMetric
  fun_prop

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Spectral construction on a real symmetric matrix; meaningful for Hermitian H. -/
def metric (g : ℝ) (H : Matrix n n ℝ) : Matrix n n ℝ := cfc (scalarMetric g) H

theorem metric_posDef (g : ℝ) {H : Matrix n n ℝ} (hH : H.IsHermitian) :
    (metric g H).PosDef := by
  rw [metric, hH.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  apply (Unitary.isUnit_coe.posDef_star_right_conjugate_iff).2
  apply Matrix.PosDef.diagonal
  intro i
  exact scalarMetric_pos g (hH.eigenvalues i)

theorem metric_mul_neg (g : ℝ) {H : Matrix n n ℝ} (hH : H.IsHermitian) :
    metric g H * metric (-g) H = 1 := by
  unfold metric
  rw [← cfc_mul _ _ _ (continuous_scalarMetric g).continuousOn
    (continuous_scalarMetric (-g)).continuousOn]
  have he : (fun x => scalarMetric g x * scalarMetric (-g) x) = fun _ => (1 : ℝ) :=
    funext (scalarMetric_mul_neg g)
  rw [he]
  exact cfc_const_one ℝ H (ha := (show IsSelfAdjoint H from hH))

/-- This is the ordinary matrix inverse, not a separately named proxy. -/
theorem metric_inv (g : ℝ) {H : Matrix n n ℝ} (hH : H.IsHermitian) :
    (metric g H)⁻¹ = metric (-g) H :=
  Matrix.inv_eq_right_inv (metric_mul_neg g hH)

/-- Exact matrix identity, valid in every finite dimension and at every coupling. -/
theorem metric_add_inv (g : ℝ) {H : Matrix n n ℝ} (hH : H.IsHermitian) :
    metric g H + (metric g H)⁻¹ = (2 : ℝ) • (1 : Matrix n n ℝ) + g^2 • H^2 := by
  rw [metric_inv g hH]
  unfold metric
  rw [← cfc_add H _ _ (continuous_scalarMetric g).continuousOn
    (continuous_scalarMetric (-g)).continuousOn]
  have he : (fun x => scalarMetric g x + scalarMetric (-g) x) =
      fun x => 2 + g^2 * x^2 := funext (scalarMetric_add_neg g)
  have ha : IsSelfAdjoint H := hH
  rw [he, cfc_const_add 2 (fun x : ℝ => g^2 * x^2) H (ha := ha),
    cfc_const_mul (g^2) (fun x : ℝ => x^2) H, cfc_pow_id H 2 (ha := ha)]
  simp [Algebra.algebraMap_eq_smul_one]

/-- For a real symmetric field, the trace of its square is its squared Frobenius norm. -/
theorem trace_sq_eq_sum_entries {H : Matrix n n ℝ} (hH : H.IsHermitian) :
    (H^2).trace = ∑ i, ∑ j, (H i j)^2 := by
  have hs : ∀ i j, H j i = H i j := by
    intro i j
    simpa using congrFun (congrFun hH.eq i) j
  simp [Matrix.trace, Matrix.diag, pow_two, Matrix.mul_apply, hs]

theorem trace_metric_add_inv (g : ℝ) {H : Matrix n n ℝ} (hH : H.IsHermitian) :
    (metric g H).trace + ((metric g H)⁻¹).trace =
      2 * Fintype.card n + g^2 * (∑ i, ∑ j, (H i j)^2) := by
  rw [← Matrix.trace_add, metric_add_inv g hH, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, trace_sq_eq_sum_entries hH]
  simp

/-- A finite ensemble needs only its second moment, with no distributional ansatz. -/
theorem weighted_metric_moment {s : Type*} [Fintype s]
    (w : s → ℝ) (hw : ∑ a, w a = 1) (g : ℝ)
    (H : s → Matrix n n ℝ) (hH : ∀ a, (H a).IsHermitian) :
    (∑ a, w a * ((metric g (H a)).trace + ((metric g (H a))⁻¹).trace)) =
      2 * Fintype.card n + g^2 * ∑ a, w a * (∑ i, ∑ j, (H a i j)^2) := by
  simp_rw [trace_metric_add_inv g (hH _), mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Separate metric and inverse bounds follow from positivity of both terms. -/
theorem trace_metric_bounds (g : ℝ) {H : Matrix n n ℝ} (hH : H.IsHermitian) :
    0 ≤ (metric g H).trace ∧ 0 ≤ ((metric g H)⁻¹).trace ∧
      (metric g H).trace ≤ 2 * Fintype.card n + g^2 * (∑ i, ∑ j, (H i j)^2) ∧
      ((metric g H)⁻¹).trace ≤ 2 * Fintype.card n + g^2 * (∑ i, ∑ j, (H i j)^2) := by
  have hq := (metric_posDef g hH).posSemidef.trace_nonneg
  have hi := (metric_posDef g hH).inv.posSemidef.trace_nonneg
  have he := trace_metric_add_inv g hH
  exact ⟨hq, hi, by linarith, by linarith⟩

open MeasureTheory in
/-- For any probability distribution, a finite field second moment implies
finite metric and inverse trace means. Measurability is explicit; Gaussianity
and exponential integrability are not required. -/
theorem integrable_metric_and_inverse {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℝ) (H : Ω → Matrix n n ℝ) (hH : ∀ ω, (H ω).IsHermitian)
    (hq : AEStronglyMeasurable (fun ω => (metric g (H ω)).trace) μ)
    (hi : AEStronglyMeasurable (fun ω => ((metric g (H ω))⁻¹).trace) μ)
    (hsecond : Integrable (fun ω => ∑ i, ∑ j, (H ω i j)^2) μ) :
    Integrable (fun ω => (metric g (H ω)).trace) μ ∧
      Integrable (fun ω => ((metric g (H ω))⁻¹).trace) μ := by
  have hmajor := (integrable_const (2 * (Fintype.card n : ℝ))).add (hsecond.const_mul (g^2))
  constructor
  · apply hmajor.mono' hq
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (trace_metric_bounds g (hH ω)).1]
      exact (trace_metric_bounds g (hH ω)).2.2.1
  · apply hmajor.mono' hi
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (trace_metric_bounds g (hH ω)).2.1]
      exact (trace_metric_bounds g (hH ω)).2.2.2

open MeasureTheory in
theorem expected_metric_add_inverse {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℝ) (H : Ω → Matrix n n ℝ) (hH : ∀ ω, (H ω).IsHermitian)
    (hq : AEStronglyMeasurable (fun ω => (metric g (H ω)).trace) μ)
    (hi : AEStronglyMeasurable (fun ω => ((metric g (H ω))⁻¹).trace) μ)
    (hsecond : Integrable (fun ω => ∑ i, ∑ j, (H ω i j)^2) μ) :
    (∫ ω, (metric g (H ω)).trace ∂μ) + (∫ ω, ((metric g (H ω))⁻¹).trace ∂μ) =
      2 * Fintype.card n + g^2 * ∫ ω, (∑ i, ∑ j, (H ω i j)^2) ∂μ := by
  obtain ⟨hqi, hii⟩ := integrable_metric_and_inverse μ g H hH hq hi hsecond
  rw [← integral_add hqi hii]
  simp_rw [trace_metric_add_inv g (hH _)]
  rw [integral_add (integrable_const _) (hsecond.const_mul _)]
  simp [integral_const_mul]

#print axioms metric_posDef
#print axioms metric_inv
#print axioms metric_add_inv
#print axioms weighted_metric_moment
#print axioms integrable_metric_and_inverse
#print axioms expected_metric_add_inverse

end
end UnifiedTheory.Audit.KFCausalPositiveMetric
