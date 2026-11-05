/- Finite-regulator nontriviality: Gibbs laws have the same null sets as
Haar link measure, and every nonconstant continuous observable has positive
variance. No regulator-uniform positive lower bound is inferred. -/
import UnifiedTheory.Clay.YangMills.RegulatedGaugeOrientation
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsFullSupport
noncomputable section
open MeasureTheory RegulatedGauge
open scoped ENNReal

variable (V : Type*) [Quiver V] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Fintype (Edge V)]

instance compactHaar_openPos : Measure.IsOpenPosMeasure (compactHaar G) := by
  unfold compactHaar
  infer_instance

instance reference_openPos : Measure.IsOpenPosMeasure (referenceMeasure G V) := by
  unfold referenceMeasure
  infer_instance

omit [SecondCountableTopology G] in
theorem gibbs_absolutelyContinuous (S : Configuration V G → ℝ) :
    gibbsMeasure V G S ≪ referenceMeasure G V :=
  Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

theorem reference_absolutelyContinuous (S : Configuration V G → ℝ) (hS : Continuous S) :
    referenceMeasure G V ≪ gibbsMeasure V G S := by
  have hd : AEMeasurable (gibbsDensity V G S) (referenceMeasure G V) :=
    (Real.continuous_exp.comp hS.neg).measurable.ennreal_ofReal.aemeasurable
  have hn : ∀ᵐ U ∂referenceMeasure G V, gibbsDensity V G S U ≠ 0 :=
    Filter.Eventually.of_forall (fun U => (ENNReal.ofReal_pos.mpr (Real.exp_pos (-S U))).ne')
  exact (withDensity_absolutelyContinuous' hd hn).trans
    (Measure.absolutelyContinuous_smul (ENNReal.inv_ne_zero.mpr (gibbsPartition_ne_top V G S hS)))

theorem gibbs_null_iff (S : Configuration V G → ℝ) (hS : Continuous S)
    (A : Set (Configuration V G)) :
    gibbsMeasure V G S A = 0 ↔ referenceMeasure G V A = 0 :=
  ⟨fun h => reference_absolutelyContinuous V G S hS h,
   fun h => gibbs_absolutelyContinuous V G S h⟩

theorem gibbs_openPos (S : Configuration V G → ℝ) (hS : Continuous S) :
    Measure.IsOpenPosMeasure (gibbsMeasure V G S) :=
  (reference_absolutelyContinuous V G S hS).isOpenPosMeasure

theorem nonzero_observable_normSq_integral_pos
    (S : Configuration V G → ℝ) (hS : Continuous S)
    (F : Configuration V G → ℂ) (hF : Continuous F)
    (U : Configuration V G) (hU : F U ≠ 0) :
    0 < ∫ x, ‖F x‖ ^ 2 ∂gibbsMeasure V G S := by
  letI := gibbsMeasure_probability V G S hS
  letI := gibbs_openPos V G S hS
  have hc : Continuous (fun x => ‖F x‖ ^ 2) := hF.norm.pow 2
  exact integral_pos_of_integrable_nonneg_nonzero hc
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun x => sq_nonneg _) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hU))

def variance (S : Configuration V G → ℝ) (F : Configuration V G → ℂ) : ℝ :=
  ∫ U, ‖F U - ∫ x, F x ∂gibbsMeasure V G S‖ ^ 2 ∂gibbsMeasure V G S

/-- Strict variance for every nonconstant continuous observable at finite
regulator, without assuming a lower bound uniform in regulator or coupling. -/
theorem variance_pos (S : Configuration V G → ℝ) (hS : Continuous S)
    (F : Configuration V G → ℂ) (hF : Continuous F)
    (U W : Configuration V G) (hne : F U ≠ F W) : 0 < variance V G S F := by
  let m := ∫ x, F x ∂gibbsMeasure V G S
  have hex : ∃ x, F x - m ≠ 0 := by
    by_cases hu : F U - m = 0
    · refine ⟨W, ?_⟩
      intro hw
      exact hne ((sub_eq_zero.mp hu).trans (sub_eq_zero.mp hw).symm)
    · exact ⟨U, hu⟩
  obtain ⟨x, hx⟩ := hex
  exact nonzero_observable_normSq_integral_pos V G S hS
    (fun y => F y - m) (hF.sub continuous_const) x hx

end
end UnifiedTheory.Clay.YangMills.GibbsFullSupport
