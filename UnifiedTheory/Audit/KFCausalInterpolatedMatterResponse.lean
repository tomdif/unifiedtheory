/- Combine charge-averaged interpolation with the actual matter response
after longitudinal absorption. The three remaining terms are the signed
initial expectation, the interpolation cost, and the terminal weighted
derivative moment. Their sufficient energy control remains unproved. -/
import UnifiedTheory.Audit.KFCausalAveragedMatterInterpolation
import UnifiedTheory.Audit.KFCausalActualMatterAbsorbedLower

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalInterpolatedMatterResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage (matterIndex factor_matter)
open UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition (rate)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root)
open UnifiedTheory.Audit.KFCausalMatterScalarAbsorption (coefficient)
open UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight (moment)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalCoherentMatterInterpolationOrbit

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "W" => root ε hε h hb hh

theorem actual_average_lower (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b : Hilbert) (hB : (f,b) ∈ (pureMomentum ε hε h).graph)
    (g k : Fin 8 → ℝ → Hilbert)
    (hOut : ∀ θ i,
      (action h hh (2*Real.pi*θ) f,g i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph ∧
      (action h hh (2*Real.pi*θ) b,k i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph)
    (hc : ∀ i, Continuous (g i) ∧ Continuous (k i)) :
    ∃ (n : ℕ) (p : Fin n → Joint 2 4) (z : Fin n → ℂ) (d : Fin 2 → ℝ → Hilbert),
      f = ∑ r, z r • state ε a h hε ha hh (p r) ∧
      (∀ i, Continuous (d i)) ∧
      (∀ θ i, d i θ =ᵐ[volume] fun x => powerSlope pointField i x*g 7 θ x) ∧
      (∀ i, Integrable (fun θ => moment ε hε (d i θ)) angleMeasure) ∧
      (∀ i, Integrable (fun θ => expectation ε a h hε ha hh hb pointField i p z W θ 0) angleMeasure ∧
        Integrable (pathCost ε a h hε ha hh hb pointField i p z W) angleMeasure ∧
        (4/ε^2)*(∫ θ, expectation ε a h hε ha hh hb pointField i p z W θ 0 ∂angleMeasure)-
          (h^2/ε^3)*(∫ θ, pathCost ε a h hε ha hh hb pointField i p z W θ ∂angleMeasure)-
          coefficient ε h*(∫ θ, moment ε hε (d i θ) ∂angleMeasure) ≤ rate h g k (matterIndex i)) := by
  obtain ⟨q,j,d,hq,hj,hd,hrep,hk,hMI,hr,habs,hlower⟩ :=
    KFCausalActualMatterAbsorbedLower.actual_average_lower ε hε h hb hh a ha f hf b hB g k hOut hc
  obtain ⟨n,p,z,hf'⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f hf
  have hg' (θ : ℝ) :
      (action h hh (2*Real.pi*θ) (∑ r, z r • state ε a h hε ha hh (p r)),g 7 θ) ∈
        (orderedExponential ε hε h).graph := by
    rw [← hf']
    exact (hOut θ 7).1
  have hF (θ : ℝ) (i : Fin 2) : (g 7 θ,g (matterIndex i) θ) ∈ (fieldPower pointField i).graph := by
    have hM := (hOut θ (matterIndex i)).1
    rw [factor_matter] at hM
    obtain ⟨g',ht,hF'⟩ := (composition_graph _ _ _ _).mp hM
    have eg : g' = g 7 θ := (orderedExponential ε hε h).mem_graph_snd_inj' ht (hOut θ 7).1 rfl
    exact eg ▸ hF'
  refine ⟨n,p,z,d,hf',hd,hrep,hMI,?_⟩
  intro i
  refine ⟨expectation_angle_integrable ε a h hε ha hh hb pointField i p z W 0,
    pathCost_angle_integrable ε a h hε ha hh hb pointField i p z W,?_⟩
  have hi := KFCausalAveragedMatterInterpolation.physical_average_lower ε a h hε ha hh hb
    pointField i p z (g 7) (g (matterIndex i)) (fun θ => j i θ+(-Complex.I*(h:ℂ)) • d i θ)
    hg' (fun θ => hF θ i) (fun θ => hk θ i)
  dsimp only at hi
  have hl := hlower i
  change (∫ θ, (4/ε^2)*(inner ℂ (W (g (matterIndex i) θ))
      (W (j i θ+(-Complex.I*(h:ℂ)) • d i θ))).re ∂angleMeasure)-
    coefficient ε h*(∫ θ, moment ε hε (d i θ) ∂angleMeasure) ≤ rate h g k (matterIndex i) at hl
  rw [integral_const_mul] at hl
  linarith only [hi,hl]

#print axioms actual_average_lower
end
end UnifiedTheory.Audit.KFCausalInterpolatedMatterResponse
