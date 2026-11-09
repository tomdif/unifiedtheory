/- Actual projected matter responses with their field-shear commutator.
The real correction is absorbed by the positive longitudinal response,
leaving a derived weighted slope moment, not an assumed energy bound. -/
import UnifiedTheory.Audit.KFCausalProjectedFieldSlopeMultiplier
import UnifiedTheory.Audit.KFCausalProjectedStructuredVacuumSign
import UnifiedTheory.Audit.KFCausalMatterLongitudinalAbsorption

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedMatterCommutatorResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse
  (StructuredState input momentumOutput inputOrbit momentumOrbit inputOrbit_graph momentumOrbit_graph
    inputOrbit_continuous momentumOrbit_continuous)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian (meanInput meanMomentum factorRate)
open UnifiedTheory.Audit.KFCausalStructuredShearMean (meanInputAt meanShearAt mean_input_one)
open UnifiedTheory.Audit.KFCausalProjectedMatterShearGraphs
  (meanWeightedInput meanWeightedFirst fieldPower_closed mean_field_graph mean_first_field_graph mean_corrected_shear_graph)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (fieldWeight slopeWeight)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower weighted_weak_response)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (pureCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse (response)
open UnifiedTheory.Audit.KFCausalFieldShearResponseCorrection (derivativeCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root)
open UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight (moment)
open UnifiedTheory.Audit.KFCausalMatterScalarAbsorption (coefficient)
open UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage (matterIndex factor_matter)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)
local notation "G" => meanInput ε h hε hh hb S 7
local notation "M" => meanMomentum ε h hε hh hb S 7
local notation "J" => meanShearAt ε h hε hh hb S 1
local notation "W" => root ε hε h hb hh

def weightedShearOutput (i : Fin 2) : Hilbert := meanWeightedFirst ε h hε hh hb S (fieldWeight pointField i) 1
def slopeOutput (i : Fin 2) : Hilbert := meanWeightedInput ε h hε hh hb S (slopeWeight pointField i) 1
def correctedOutput (i : Fin 2) : Hilbert :=
  weightedShearOutput ε h hε hh hb S i+(-Complex.I*(h:ℂ)) • slopeOutput ε h hε hh hb S i
def weightedExpectation (i : Fin 2) : ℝ :=
  (inner ℂ (W (meanInput ε h hε hh hb S (matterIndex i))) (W (correctedOutput ε h hε hh hb S i))).re
def absorbedLower (i : Fin 2) : ℝ := (4/ε^2)*weightedExpectation ε h hε hh hb S i-
  coefficient ε h*moment ε hε (slopeOutput ε h hε hh hb S i)

theorem orbit_field_graphs (i : Fin 2) (θ : ℝ) :
    (inputOrbit ε h hε hh hb S 7 θ,inputOrbit ε h hε hh hb S (matterIndex i) θ) ∈ (fieldPower pointField i).graph ∧
    (momentumOrbit ε h hε hh hb S 7 θ,momentumOrbit ε h hε hh hb S (matterIndex i) θ) ∈ (fieldPower pointField i).graph := by
  have hi := inputOrbit_graph ε h hε hh hb S θ (matterIndex i)
  have hm := momentumOrbit_graph ε h hε hh hb S θ (matterIndex i)
  rw [factor_matter] at hi hm
  obtain ⟨gi,hti,hfi⟩ := (composition_graph _ _ _ _).mp hi
  obtain ⟨gm,htm,hfm⟩ := (composition_graph _ _ _ _).mp hm
  have ei := (orderedExponential ε hε h).mem_graph_snd_inj' hti (inputOrbit_graph ε h hε hh hb S θ 7) rfl
  have em := (orderedExponential ε hε h).mem_graph_snd_inj' htm (momentumOrbit_graph ε h hε hh hb S θ 7) rfl
  dsimp only at ei em
  exact ⟨ei ▸ hfi,em ▸ hfm⟩

theorem projected_field_graphs (i : Fin 2) :
    (G,meanInput ε h hε hh hb S (matterIndex i)) ∈ (fieldPower pointField i).graph ∧
    (M,meanMomentum ε h hε hh hb S (matterIndex i)) ∈ (fieldPower pointField i).graph :=
  ⟨KFCausalProjectedKineticResponse.integral_closed_graph _ (fieldPower_closed pointField i) _ _
      (inputOrbit_continuous ε h hε hh hb S 7) (inputOrbit_continuous ε h hε hh hb S (matterIndex i))
      (fun θ => (orbit_field_graphs ε h hε hh hb S i θ).1),
    KFCausalProjectedKineticResponse.integral_closed_graph _ (fieldPower_closed pointField i) _ _
      (momentumOrbit_continuous ε h hε hh hb S 7) (momentumOrbit_continuous ε h hε hh hb S (matterIndex i))
      (fun θ => (orbit_field_graphs ε h hε hh hb S i θ).2)⟩

theorem mean_field_eq (i : Fin 2) : meanWeightedInput ε h hε hh hb S (fieldWeight pointField i) 1 =
    meanInput ε h hε hh hb S (matterIndex i) := by
  have hg := mean_field_graph ε h hε hh hb S pointField i ⟨1,by constructor <;> norm_num⟩
  change (meanInputAt ε h hε hh hb S 1,meanWeightedInput ε h hε hh hb S (fieldWeight pointField i) 1) ∈ _ at hg
  rw [mean_input_one] at hg
  exact (fieldPower pointField i).mem_graph_snd_inj' hg (projected_field_graphs ε h hε hh hb S i).1 rfl

theorem projected_shear_graph (i : Fin 2) :
    (meanInput ε h hε hh hb S (matterIndex i),correctedOutput ε h hε hh hb S i) ∈
      (KFCausalTransverseShearMomentum.shearMomentum h).graph := by
  have hg := mean_corrected_shear_graph ε h hε hh hb S pointField i ⟨1,by constructor <;> norm_num⟩
  change (meanWeightedInput ε h hε hh hb S (fieldWeight pointField i) 1,correctedOutput ε h hε hh hb S i) ∈ _ at hg
  rw [mean_field_eq] at hg
  exact hg

theorem projected_slope_coe (i : Fin 2) : slopeOutput ε h hε hh hb S i =ᵐ[volume]
    fun x => powerSlope pointField i x*G x := by
  have he := KFCausalProjectedFieldSlopeMultiplier.mean_slope_coe ε h hε hh hb S pointField i
    ⟨1,by constructor <;> norm_num⟩
  change slopeOutput ε h hε hh hb S i =ᵐ[volume] fun x => powerSlope pointField i x*meanInputAt ε h hε hh hb S 1 x at he
  rw [mean_input_one] at he
  exact he

theorem matter_response (i : Fin 2) : factorRate ε h hε hh hb S (matterIndex i) =
    response ε hε h hb (meanInput ε h hε hh hb S (matterIndex i)) (weightedShearOutput ε h hε hh hb S i) := by
  apply weighted_weak_response ε h hε hh hb pointField i G (M+pureCorrection ε hε h hb G J) M J
    _ _ _ (KFCausalProjectedStructuredVacuumSign.mean_pure_graph ε h hε hh hb S)
    (by abel) (projected_field_graphs ε h hε hh hb S i).1 (projected_field_graphs ε h hε hh hb S i).2
    (mean_first_field_graph ε h hε hh hb S pointField i ⟨1,by constructor <;> norm_num⟩)

theorem corrected_response (i : Fin 2) : factorRate ε h hε hh hb S (matterIndex i) =
    KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb (meanInput ε h hε hh hb S (matterIndex i))+
      (4/ε^2)*weightedExpectation ε h hε hh hb S i-
        derivativeCorrection ε hε h hb (meanInput ε h hε hh hb S (matterIndex i)) (slopeOutput ε h hε hh hb S i) := by
  rw [matter_response]
  exact KFCausalFieldShearResponseCorrection.corrected_response ε hε h hb hh _ _ _
    (projected_shear_graph ε h hε hh hb S i)

theorem correction_absorption (i : Fin 2) :
    |derivativeCorrection ε hε h hb (meanInput ε h hε hh hb S (matterIndex i)) (slopeOutput ε h hε hh hb S i)| ≤
      KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb (meanInput ε h hε hh hb S (matterIndex i))+
        coefficient ε h*moment ε hε (slopeOutput ε h hε hh hb S i) :=
  KFCausalMatterLongitudinalAbsorption.field_absorption ε hε h hb pointField i G _ _
    (projected_field_graphs ε h hε hh hb S i).1 (projected_slope_coe ε h hε hh hb S i)

theorem absorbed_lower (i : Fin 2) : absorbedLower ε h hε hh hb S i ≤ factorRate ε h hε hh hb S (matterIndex i) := by
  have he := (le_abs_self (derivativeCorrection ε hε h hb (meanInput ε h hε hh hb S (matterIndex i))
    (slopeOutput ε h hε hh hb S i))).trans (correction_absorption ε h hε hh hb S i)
  have hr := corrected_response ε h hε hh hb S i
  unfold absorbedLower
  linarith only [he,hr]

#print axioms orbit_field_graphs
#print axioms projected_field_graphs
#print axioms mean_field_eq
#print axioms projected_shear_graph
#print axioms projected_slope_coe
#print axioms matter_response
#print axioms corrected_response
#print axioms correction_absorption
#print axioms absorbed_lower
end
end UnifiedTheory.Audit.KFCausalProjectedMatterCommutatorResponse
