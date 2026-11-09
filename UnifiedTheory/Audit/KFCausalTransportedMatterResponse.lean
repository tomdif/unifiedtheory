/- Charge-averaged matter response using the transported initial pairing.
Only the signed initial term and the exact terminal derivative moment
remain. Their integrability is derived, not assumed; energy control is
not asserted. -/
import UnifiedTheory.Audit.KFCausalTransportedChargeInitial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalTransportedMatterResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
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
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root rootValue root_coe)
open UnifiedTheory.Audit.KFCausalMatterScalarAbsorption (coefficient)
open UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight (moment)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalTransportedChargeInitial (expectation expectation_integrable)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "S" => coherentSpan ε a h hε ha hh
local notation "W" => root ε hε h hb hh

def lower (f : S) (d : Fin 2 → ℝ → Hilbert) (i : Fin 2) : ℝ :=
  (4/ε^2)*(∫ θ, expectation ε a h hε ha hh hb pointField i W f θ ∂angleMeasure)-
    coefficient ε h*(∫ θ, moment ε hε (d i θ) ∂angleMeasure)

theorem actual_average_lower (f : S) (b : Hilbert)
    (hB : ((f:Hilbert),b) ∈ (pureMomentum ε hε h).graph)
    (g k : Fin 8 → ℝ → Hilbert)
    (hOut : ∀ θ i,
      (action h hh (2*Real.pi*θ) (f:Hilbert),g i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph ∧
      (action h hh (2*Real.pi*θ) b,k i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph)
    (hc : ∀ i, Continuous (g i) ∧ Continuous (k i)) :
    ∃ d : Fin 2 → ℝ → Hilbert,
      (∀ i, Continuous (d i)) ∧
      (∀ θ i, d i θ =ᵐ[volume] fun x => powerSlope pointField i x*g 7 θ x) ∧
      (∀ i, Integrable (fun θ => moment ε hε (d i θ)) angleMeasure) ∧
      (∀ i, Integrable (expectation ε a h hε ha hh hb pointField i W f) angleMeasure ∧
        lower ε a h hε ha hh hb f d i ≤ rate h g k (matterIndex i)) := by
  obtain ⟨q,j,d,hq,hj,hd,hrep,hk,hMI,hr,habs,hlower⟩ :=
    KFCausalActualMatterAbsorbedLower.actual_average_lower ε hε h hb hh a ha f f.property b hB g k hOut hc
  have hg (θ : ℝ) : (action h hh (2*Real.pi*θ) (f:Hilbert),g 7 θ) ∈
      (orderedExponential ε hε h).graph := (hOut θ 7).1
  have hF (θ : ℝ) (i : Fin 2) : (g 7 θ,g (matterIndex i) θ) ∈ (fieldPower pointField i).graph := by
    have hM := (hOut θ (matterIndex i)).1
    rw [factor_matter] at hM
    obtain ⟨g',ht,hF'⟩ := (composition_graph _ _ _ _).mp hM
    have eg : g' = g 7 θ := (orderedExponential ε hε h).mem_graph_snd_inj' ht (hg θ) rfl
    exact eg ▸ hF'
  refine ⟨d,hd,hrep,hMI,?_⟩
  intro i
  refine ⟨expectation_integrable ε a h hε ha hh hb pointField i W f,?_⟩
  have hi := (KFCausalTransportedChargeInitial.actual_average_lower ε a h hε ha hh hb pointField i
    W (fun s => (rootValue ε h s:ℂ)) (root_coe ε hε h hb hh) f
    (g 7) (g (matterIndex i)) (fun θ => j i θ+(-Complex.I*(h:ℂ)) • d i θ)
    hg (fun θ => hF θ i) (fun θ => hk θ i)).2.2.2
  have hl := hlower i
  change (∫ θ, (4/ε^2)*(inner ℂ (W (g (matterIndex i) θ))
      (W (j i θ+(-Complex.I*(h:ℂ)) • d i θ))).re ∂angleMeasure)-
    coefficient ε h*(∫ θ, moment ε hε (d i θ) ∂angleMeasure) ≤ rate h g k (matterIndex i) at hl
  rw [integral_const_mul] at hl
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 4/ε^2)) _).trans hl

#print axioms actual_average_lower
end
end UnifiedTheory.Audit.KFCausalTransportedMatterResponse
