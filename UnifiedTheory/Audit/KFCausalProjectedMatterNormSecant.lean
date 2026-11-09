/- A norm secant for actual charge means, not an average of diagonal
quadratic responses. The transported initial vector is constructed and
all Bochner integrability follows from the actual structured orbits. -/
import UnifiedTheory.Audit.KFCausalStructuredTransportedMatterOrbit
import UnifiedTheory.Audit.KFCausalProjectedMatterCommutatorResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedMatterNormSecant
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (fieldWeight slopeWeight)
open UnifiedTheory.Audit.KFCausalStructuredPolynomialShearOrbit (weightedInput weightedFirst)
open UnifiedTheory.Audit.KFCausalProjectedMatterShearGraphs (meanWeightedInput meanWeightedFirst)
open UnifiedTheory.Audit.KFCausalStructuredTransportedMatterOrbit
  (transportedInput endpointValues endpoint_sum endpoint_continuous)
open UnifiedTheory.Audit.KFCausalTransportedSecantMean (endpoint gap)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root)
open UnifiedTheory.Audit.KFCausalClockSecantMultiplier (operator operator_norm_sq)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian (meanInput)
open UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage (matterIndex)
open UnifiedTheory.Audit.KFCausalProjectedMatterCommutatorResponse
  (mean_field_eq correctedOutput weightedShearOutput slopeOutput weightedExpectation)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)
local notation "M" => operator ε h hε hb hh
local notation "W" => root ε hε h hb hh

def meanInitial (l : Transverse →L[ℝ] ℝ) (i : Fin 2) : Hilbert :=
  ∫ θ, transportedInput ε h hε hh hb S l i (2*Real.pi*θ) 0 ∂angleMeasure

theorem mean_secant (l : Transverse →L[ℝ] ℝ) (i : Fin 2) :
    (‖M (meanWeightedInput ε h hε hh hb S (fieldWeight l i) 1)‖^2-
      ‖M (meanInitial ε h hε hh hb S l i)‖^2)/2 ≤
      (inner ℂ (W (meanWeightedInput ε h hε hh hb S (fieldWeight l i) 1))
        (W (meanWeightedFirst ε h hε hh hb S (fieldWeight l i) 1+
          (-Complex.I*(h:ℂ)) • meanWeightedInput ε h hε hh hb S (slopeWeight l i) 1))).re := by
  let one : Interval := ⟨1,by constructor <;> norm_num⟩
  let zero : Interval := ⟨0,by constructor <;> norm_num⟩
  have ht : Integrable (fun θ => transportedInput ε h hε hh hb S l i (2*Real.pi*θ) 0) angleMeasure :=
    (continuous_angle_memLp _ ((KFCausalStructuredTransportedMatterOrbit.angle_continuous
      ε h hε hh hb S l i zero).comp (continuous_const.mul continuous_id))).integrable (by norm_num)
  have hu : Integrable (fun θ => weightedInput ε h hε hh hb S (fieldWeight l i) (2*Real.pi*θ) 1) angleMeasure :=
    (continuous_angle_memLp _ ((KFCausalStructuredPolynomialShearOrbit.angle_continuous
      ε h hε hh hb S (fieldWeight l i) one).1.comp (continuous_const.mul continuous_id))).integrable (by norm_num)
  have hv : Integrable (fun θ => weightedFirst ε h hε hh hb S (fieldWeight l i) (2*Real.pi*θ) 1) angleMeasure :=
    (continuous_angle_memLp _ ((KFCausalStructuredPolynomialShearOrbit.angle_continuous
      ε h hε hh hb S (fieldWeight l i) one).2.comp (continuous_const.mul continuous_id))).integrable (by norm_num)
  have hd : Integrable (fun θ => (-Complex.I*(h:ℂ)) •
      weightedInput ε h hε hh hb S (slopeWeight l i) (2*Real.pi*θ) 1) angleMeasure :=
    (continuous_angle_memLp _ (((KFCausalStructuredPolynomialShearOrbit.angle_continuous
      ε h hε hh hb S (slopeWeight l i) one).1.comp
      (continuous_const.mul continuous_id)).const_smul (-Complex.I*(h:ℂ)))).integrable (by norm_num)
  have hc : Continuous (fun θ => endpointValues ε h hε hh hb S l i (2*Real.pi*θ)) :=
    (endpoint_continuous ε h hε hh hb S l i).comp (continuous_const.mul continuous_id)
  have hm : ∀ θ, endpointValues ε h hε hh hb S l i (2*Real.pi*θ) ∈
      Submodule.span ℂ (Set.range (endpoint ε h hε hb hh l i)) := by
    intro θ
    rw [endpoint_sum]
    exact Submodule.sum_mem _ (fun r _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self _)))
  have he := KFCausalTransportedSecantMean.mean_gap ε h hε hb hh l i _
    ((continuous_angle_memLp _ hc).integrable (by norm_num)) hm
  have hj : Integrable (fun θ => weightedFirst ε h hε hh hb S (fieldWeight l i) (2*Real.pi*θ) 1+
      (-Complex.I*(h:ℂ)) • weightedInput ε h hε hh hb S (slopeWeight l i) (2*Real.pi*θ) 1) angleMeasure :=
    hv.add hd
  have hmval : (∫ θ, endpointValues ε h hε hh hb S l i (2*Real.pi*θ) ∂angleMeasure) =
      (meanInitial ε h hε hh hb S l i,
       (meanWeightedInput ε h hε hh hb S (fieldWeight l i) 1,
        meanWeightedFirst ε h hε hh hb S (fieldWeight l i) 1+
          (-Complex.I*(h:ℂ)) • meanWeightedInput ε h hε hh hb S (slopeWeight l i) 1)) := by
    unfold endpointValues
    rw [integral_pair ht (hu.prodMk hj),integral_pair hu hj,
      integral_add hv hd,integral_smul]
    rfl
  rw [hmval] at he
  exact sub_nonneg.mp he

theorem projected_secant (i : Fin 2) :
    (‖M (meanInput ε h hε hh hb S (matterIndex i))‖^2-
      ‖M (meanInitial ε h hε hh hb S pointField i)‖^2)/2 ≤
      weightedExpectation ε h hε hh hb S i := by
  have he := mean_secant ε h hε hh hb S pointField i
  rw [mean_field_eq] at he
  exact he

theorem projected_norm_lower (i : Fin 2) :
    -(ε/8)*‖meanInitial ε h hε hh hb S pointField i‖^2 ≤
      weightedExpectation ε h hε hh hb S i := by
  have he := projected_secant ε h hε hh hb S i
  have hn := operator_norm_sq ε h hε hb hh (meanInitial ε h hε hh hb S pointField i)
  nlinarith [sq_nonneg ‖M (meanInput ε h hε hh hb S (matterIndex i))‖]

#print axioms mean_secant
#print axioms projected_secant
#print axioms projected_norm_lower
end
end UnifiedTheory.Audit.KFCausalProjectedMatterNormSecant
