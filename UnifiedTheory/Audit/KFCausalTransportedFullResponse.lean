/- The transported two-term matter bound reaches the actual averaged
energy-form response of a coherent state and its pure-clock momentum.
All form lifts and factor outputs are constructed. This is a fixed-time
form estimate; neither an energy comparison nor an evolution identity
is assumed or concluded. -/
import UnifiedTheory.Audit.KFCausalTransportedMatterResponse
import UnifiedTheory.Audit.KFCausalCoherentFullResponseReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalTransportedFullResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight (moment)
open UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition (rate)
open UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage (matterIndex)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalTransportedMatterResponse (lower)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ)
local notation "S" => coherentSpan ε a h hε ha hh
local notation "hp" => hamiltonian_bound ε h hb
local notation "Full" => AveragedSpace ε hε h hp hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hp hh mass2 quartic vacuum t
local notation "out" => energyOutput ε hε h hp hh mass2 quartic vacuum t
local notation "F" => energyFactor ε hε h modelDirections pointField

theorem exists_actual_bound (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) (f : S) :
    ∃ (b : Hilbert) (u v : Full) (g k : Fin 8 → ℝ → Hilbert) (d : Fin 2 → ℝ → Hilbert),
      ((f:Hilbert),b) ∈ (pureMomentum ε hε h).graph ∧ embed u = (f:Hilbert) ∧ embed v = b ∧
      (∀ θ i, (action h hh (2*Real.pi*θ) (f:Hilbert),g i θ) ∈ (F i).graph ∧
        (action h hh (2*Real.pi*θ) b,k i θ) ∈ (F i).graph) ∧
      (∀ i, Continuous (g i) ∧ Continuous (k i)) ∧
      (∀ i, Continuous (d i)) ∧
      (∀ θ i, d i θ =ᵐ[volume] fun x => powerSlope pointField i x*g 7 θ x) ∧
      (∀ i, Integrable (fun θ => moment ε hε (d i θ)) angleMeasure) ∧
      (∀ i, lower ε a h hε ha hh hb f d i ≤ rate h g k (matterIndex i)) ∧
      (-2/h)*(inner ℂ (out u) (out v)).im =
        KFCausalCoherentFullResponseReduction.fullRate mass2 quartic vacuum t h g k ∧
      Real.exp (2*t)*(mass2/2*lower ε a h hε ha hh hb f d 0+
        quartic/4*lower ε a h hε ha hh hb f d 1)-‖(f:Hilbert)‖^2/2 ≤
        (-2/h)*(inner ℂ (out u) (out v)).im := by
  exact (KFCausalCoherentFullResponseReduction.exists_actual_reduction ε h hε hh hb
    mass2 quartic vacuum t hm hq hvac a ha f f.property).elim fun b hx =>
    hx.elim fun u hx => hx.elim fun v hx => hx.elim fun g hx => hx.elim fun k hx =>
      (KFCausalTransportedMatterResponse.actual_average_lower ε a h hε ha hh hb f b hx.1 g k
        hx.2.2.2.1 hx.2.2.2.2.1).elim fun d hy => by
      have h5 : lower ε a h hε ha hh hb f d 0 ≤ rate h g k 5 := (hy.2.2.2 0).2
      have h6 : lower ε a h hε ha hh hb f d 1 ≤ rate h g k 6 := (hy.2.2.2 1).2
      have hm' := mul_le_mul_of_nonneg_left h5 (div_nonneg hm (by norm_num : (0:ℝ) ≤ 2))
      have hq' := mul_le_mul_of_nonneg_left h6 (div_nonneg hq (by norm_num : (0:ℝ) ≤ 4))
      have hs := mul_le_mul_of_nonneg_left (add_le_add hm' hq') (Real.exp_pos (2*t)).le
      exact ⟨b,u,v,g,k,d,hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2.1,hy.1,hy.2.1,hy.2.2.1,
        fun i => (hy.2.2.2 i).2,hx.2.2.2.2.2.1,
        (sub_le_sub_right hs (‖(f:Hilbert)‖^2/2)).trans hx.2.2.2.2.2.2⟩

#print axioms exists_actual_bound
end
end UnifiedTheory.Audit.KFCausalTransportedFullResponse
