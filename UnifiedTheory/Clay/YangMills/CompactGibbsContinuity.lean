/- Finite compact Gibbs expectations depend continuously on continuous
parameters and observables. Positive partitions and the normalized integral
formula are proved; no continuum tuning or ultraviolet bracket is assumed. -/
import UnifiedTheory.Clay.YangMills.GibbsCoordinateTransport
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CompactGibbsContinuity
noncomputable section
open MeasureTheory LocalGibbsComparison
open scoped ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def law (S : X → ℝ) : Measure X := weightedLaw μ (fun x => Real.exp (-S x))

theorem partition_positive (S : X → ℝ) (hS : Continuous S) :
    0 < ∫ x, Real.exp (-S x) ∂μ :=
  integral_exp_pos ((Real.continuous_exp.comp hS.neg).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

theorem law_probability (S : X → ℝ) (hS : Continuous S) : IsProbabilityMeasure (law μ S) :=
  weightedLaw_probability μ _ (Real.continuous_exp.comp hS.neg).measurable
    ((Real.continuous_exp.comp hS.neg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (fun x => (Real.exp_pos _).le) (partition_positive μ S hS)

/-- The normalized complex expectation keeps the real positive partition
explicit, including when the observable depends on the parameter. -/
theorem expectation_formula (S : X → ℝ) (hS : Continuous S) (F : X → ℂ) :
    (∫ x, F x ∂law μ S) =
      (∫ x, Real.exp (-S x) ∂μ)⁻¹ • ∫ x, Real.exp (-S x) • F x ∂μ := by
  unfold law weightedLaw
  rw [integral_smul_measure]
  have hw : Measurable (fun x => ENNReal.ofReal (Real.exp (-S x))) :=
    (Real.continuous_exp.comp hS.neg).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (partition_positive μ S hS).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem compact_integral_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [SecondCountableTopology E]
    (F : ℝ → X → E) (hF : Continuous F.uncurry) :
    Continuous (fun b => ∫ x, F b x ∂μ) := by
  simpa only [Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous hF (isCompact_univ : IsCompact (Set.univ : Set X))

/-- Genuine compact Gibbs continuity, with joint parameter dependence allowed
in both the action and observable. -/
theorem expectation_continuous (S : ℝ → X → ℝ) (hS : Continuous S.uncurry)
    (F : ℝ → X → ℂ) (hF : Continuous F.uncurry) :
    Continuous (fun b => ∫ x, F b x ∂law μ (S b)) := by
  have hs (b : ℝ) : Continuous (S b) := hS.comp (continuous_const.prodMk continuous_id)
  have hw : Continuous (fun z : ℝ × X => Real.exp (-S z.1 z.2)) :=
    Real.continuous_exp.comp hS.neg
  have hpart := compact_integral_continuous μ (fun b x => Real.exp (-S b x)) hw
  have hnum := compact_integral_continuous μ (fun b x => Real.exp (-S b x) • F b x)
    (hw.smul hF)
  have h := (hpart.inv₀ (fun b => (partition_positive μ (S b) (hs b)).ne')).smul hnum
  simpa only [expectation_formula μ _ (hs _)] using h

end
end UnifiedTheory.Clay.YangMills.CompactGibbsContinuity
