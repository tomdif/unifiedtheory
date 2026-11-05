/- Ineligible reset backgrounds are charged to local energy under the
same measure, including an arbitrary nonnegative continuous source weight.
The exact exterior marginal is retained in the probability statement. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchBackgroundReset

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchCoverage
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonPatchLocalEnergy
open WilsonPatchComplementTail WilsonPatchEligibility WilsonPatchBackgroundReset
open WilsonPatchExteriorDecomposition

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def ineligible (S : Finset (SpatialVertex n × Fin 3)) (u w : Slice n) : Set (Outside n S) :=
  {b | threshold < backgroundCost n S (background n S u b) u w}

theorem ineligible_measurable (S : Finset (SpatialVertex n × Fin 3)) (u w : Slice n) :
    MeasurableSet (ineligible n S u w) :=
  measurableSet_lt measurable_const
    ((cost_continuous n S u w).comp (background_continuous n S u)).measurable

theorem ineligible_energy (S : Finset (SpatialVertex n × Fin 3)) (u w v : Slice n)
    (hv : outsideOf n S v ∈ ineligible n S u w) :
    threshold ≤ 70 * localEnergy n S v u w :=
  (show threshold < backgroundCost n S (reset n S u v) u w from hv).le.trans
    (reset_cost_bound n S u w v)

/-- This bound holds for any finite measure on the same field space and
keeps its full source weight. It does not replace the measure by Haar. -/
theorem weighted_coverage (S : Finset (SpatialVertex n × Fin 3)) (u w : Slice n)
    (μ : Measure (Slice n)) [IsFiniteMeasure μ] (W : Slice n → ℝ)
    (hW : Continuous W) (hW0 : ∀ v, 0 ≤ W v) :
    (∫ v in (outsideOf n S) ⁻¹' ineligible n S u w, W v ∂μ) ≤
      (70 / threshold) * ∫ v, localEnergy n S v u w * W v ∂μ := by
  let E := (outsideOf n S) ⁻¹' ineligible n S u w
  have hE : MeasurableSet E := (outside_continuous n S).measurable (ineligible_measurable n S u w)
  have hL := (local_continuous n S u w).mul hW
  have hiW := hW.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hiL := hL.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hh : threshold * (∫ v in E, W v ∂μ) ≤
      70 * ∫ v, localEnergy n S v u w * W v ∂μ := by
    calc
      _ = ∫ v in E, threshold * W v ∂μ := (integral_const_mul _ _).symm
      _ ≤ ∫ v in E, 70 * (localEnergy n S v u w * W v) ∂μ := by
        apply setIntegral_mono_on (hiW.const_mul _).integrableOn
          (hiL.const_mul _).integrableOn hE
        intro v hv
        have hb := mul_le_mul_of_nonneg_right (ineligible_energy n S u w v hv) (hW0 v)
        simp only [Pi.mul_apply]
        nlinarith only [hb]
      _ ≤ ∫ v, 70 * (localEnergy n S v u w * W v) ∂μ :=
        setIntegral_le_integral (hiL.const_mul _) (Filter.Eventually.of_forall
          (fun v => mul_nonneg (by norm_num) (mul_nonneg (local_nonneg n S v u w) (hW0 v))))
      _ = _ := integral_const_mul _ _
  calc
    _ ≤ (70 * ∫ v, localEnergy n S v u w * W v ∂μ) / threshold :=
      (le_div_iff₀ threshold_pos).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by ring

/-- The full sourced Gibbs law pushes to precisely the already constructed
exterior marginal, including its integrated interior partition. -/
theorem outside_preserving (S : Finset (SpatialVertex n × Fin 3))
    (A : Slice n → ℝ) (hA : Continuous A) :
    MeasurePreserving (outsideOf n S)
      (CompactGibbsContinuity.law (WilsonSlabOperator.measure n) A) (outsideLaw n S A) := by
  refine ⟨(outside_continuous n S).measurable, ?_⟩
  rw [← (split_preserving n S A hA).map_eq,
    Measure.map_map
      (μ := CompactGibbsContinuity.law
        ((outsideHaar n S).prod (WilsonPatchConditioning.haar n S)) (splitAction n S A))
      (outside_continuous n S).measurable
      (WilsonBlockMarginal.assemble S).measurable]
  change Measure.map (outsideOf n S ∘ WilsonBlockMarginal.assemble S) _ =
    Measure.map Prod.fst _
  congr 1
  funext z
  exact outside_assemble n S z

theorem probability_bound (S : Finset (SpatialVertex n × Fin 3)) (u w : Slice n)
    (A : Slice n → ℝ) (hA : Continuous A) :
    (outsideLaw n S A).real (ineligible n S u w) ≤
      (70 / threshold) * ∫ v, localEnergy n S v u w
        ∂CompactGibbsContinuity.law (WilsonSlabOperator.measure n) A := by
  letI := CompactGibbsContinuity.law_probability (WilsonSlabOperator.measure n) A hA
  have hp := outside_preserving n S A hA
  rw [measureReal_def, ← hp.map_eq,
    Measure.map_apply hp.measurable (ineligible_measurable n S u w)]
  have hh := weighted_coverage n S u w
    (CompactGibbsContinuity.law (WilsonSlabOperator.measure n) A)
    (fun _ => 1) continuous_const (fun _ => by norm_num)
  simpa only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def] using hh

end
end UnifiedTheory.Clay.YangMills.WilsonPatchCoverage
