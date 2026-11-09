/- Lower bounds for the actual coherent matter response after absorption
of its real derivative correction. All derivative outputs and their angle
integrability are derived. Weighted shear and the remaining derivative
moment still require a sufficient comparison with Hamiltonian energy. -/
import UnifiedTheory.Audit.KFCausalMatterLongitudinalAbsorption

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalActualMatterAbsorbedLower
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope)
open UnifiedTheory.Audit.KFCausalFieldShearResponseCorrection (derivativeCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage (matterIndex factor_matter longitudinalMean)
open UnifiedTheory.Audit.KFCausalAveragedMatterShearCorrection (weightedMean correctionMean)
open UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition (rate)
open UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight (moment moment_continuous)
open UnifiedTheory.Audit.KFCausalMatterScalarAbsorption (coefficient)
open UnifiedTheory.Audit.KFCausalMatterLongitudinalAbsorption (field_absorption average_absorption)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) (hh : h ≠ 0)
local notation "W" => root ε hε h hb hh
local notation "responseL" => KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb

theorem actual_weak_lower (a : ℝ) (ha : 0 < a) (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
    (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) (b g jg u v : Hilbert)
    (hB : (f,b) ∈ (pureMomentum ε hε h).graph) (hg : (f,g) ∈ (orderedExponential ε hε h).graph)
    (hjg : (g,jg) ∈ (shearMomentum h).graph)
    (hu : (f,u) ∈ (matterFactor ε hε h (fieldPower l i)).graph)
    (hv : (b,v) ∈ (matterFactor ε hε h (fieldPower l i)).graph) :
    ∃ j d : Hilbert, (jg,j) ∈ (fieldPower l i).graph ∧
      d =ᵐ[volume] (fun x => powerSlope l i x*g x) ∧
      (u,j+(-Complex.I*(h:ℂ)) • d) ∈ (shearMomentum h).graph ∧
      (-2/h)*(inner ℂ u v).im = responseL u+
        (4/ε^2)*(inner ℂ (W u) (W (j+(-Complex.I*(h:ℂ)) • d))).re-
        derivativeCorrection ε hε h hb u d ∧
      (4/ε^2)*(inner ℂ (W u) (W (j+(-Complex.I*(h:ℂ)) • d))).re-
        coefficient ε h*moment ε hε d ≤ (-2/h)*(inner ℂ u v).im := by
  obtain ⟨j,d,hj,hd,hk,hr,_⟩ :=
    KFCausalCoherentMatterShearCorrection.actual_response_with_derivative
      ε a h hε ha hh hb l i f hf b g jg u v hB hg hjg hu hv
  obtain ⟨g',ht,hF⟩ := (composition_graph _ _ _ _).mp hu
  have eg : g' = g := (orderedExponential ε hε h).mem_graph_snd_inj' ht hg rfl
  have hF' : (g,u) ∈ (fieldPower l i).graph := eg ▸ hF
  refine ⟨j,d,hj,hd,hk,hr,?_⟩
  have hE := (le_abs_self (derivativeCorrection ε hε h hb u d)).trans
    (field_absorption ε hε h hb l i g u d hF' hd)
  linarith only [hr,hE]

theorem actual_average_lower (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ coherentSpan ε a h hε ha hh) (b : Hilbert)
    (hB : (f,b) ∈ (pureMomentum ε hε h).graph) (g k : Fin 8 → ℝ → Hilbert)
    (hOut : ∀ θ i,
      (action h hh (2*Real.pi*θ) f,g i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph ∧
      (action h hh (2*Real.pi*θ) b,k i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph)
    (hc : ∀ i, Continuous (g i) ∧ Continuous (k i)) :
    ∃ (q : ℝ → Hilbert) (j d : Fin 2 → ℝ → Hilbert),
      (∀ θ, (g 7 θ,q θ) ∈ (shearMomentum h).graph) ∧
      (∀ θ i, (q θ,j i θ) ∈ (fieldPower pointField i).graph) ∧
      (∀ i, Continuous (d i)) ∧
      (∀ θ i, d i θ =ᵐ[volume] fun x => powerSlope pointField i x*g 7 θ x) ∧
      (∀ θ i, (g (matterIndex i) θ,j i θ+(-Complex.I*(h:ℂ)) • d i θ) ∈ (shearMomentum h).graph) ∧
      (∀ i, Integrable (fun θ => moment ε hε (d i θ)) angleMeasure) ∧
      (∀ i, rate h g k (matterIndex i) = longitudinalMean ε h hε hb g i+
        weightedMean ε h hε hb hh g j d i-correctionMean ε h hε hb g d i) ∧
      (∀ i, |correctionMean ε h hε hb g d i| ≤ longitudinalMean ε h hε hb g i+
        coefficient ε h*(∫ θ, moment ε hε (d i θ) ∂angleMeasure)) ∧
      (∀ i, weightedMean ε h hε hb hh g j d i-
        coefficient ε h*(∫ θ, moment ε hε (d i θ) ∂angleMeasure) ≤ rate h g k (matterIndex i)) := by
  obtain ⟨q,j,d,hq,hj,hd,hrep,hk,_,_,hr,_⟩ :=
    KFCausalAveragedMatterShearCorrection.actual_average ε h hε hb hh a ha f hf b hB g k hOut hc
  have hF (θ : ℝ) (i : Fin 2) : (g 7 θ,g (matterIndex i) θ) ∈ (fieldPower pointField i).graph := by
    have hM := (hOut θ (matterIndex i)).1
    rw [factor_matter] at hM
    obtain ⟨g',ht,hF'⟩ := (composition_graph _ _ _ _).mp hM
    have eg : g' = g 7 θ := (orderedExponential ε hε h).mem_graph_snd_inj' ht (hOut θ 7).1 rfl
    exact eg ▸ hF'
  have hbound (i : Fin 2) := average_absorption ε hε h hb pointField i
    (g 7) (g (matterIndex i)) (d i) (fun θ => hF θ i) (fun θ => hrep θ i) (hc _).1 (hd i)
  have hMI (i : Fin 2) : Integrable (fun θ => moment ε hε (d i θ)) angleMeasure :=
    (continuous_angle_memLp _ ((moment_continuous ε hε).comp (hd i))).integrable (by norm_num)
  refine ⟨q,j,d,hq,hj,hd,hrep,hk,hMI,hr,hbound,?_⟩
  intro i
  have hE := (le_abs_self (correctionMean ε h hε hb g d i)).trans (hbound i)
  change correctionMean ε h hε hb g d i ≤ longitudinalMean ε h hε hb g i+
    coefficient ε h*(∫ θ, moment ε hε (d i θ) ∂angleMeasure) at hE
  linarith only [hr i,hE]

#print axioms actual_weak_lower
#print axioms actual_average_lower
end
end UnifiedTheory.Audit.KFCausalActualMatterAbsorbedLower
