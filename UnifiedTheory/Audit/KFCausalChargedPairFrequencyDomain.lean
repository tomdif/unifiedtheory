/- Frequency modulation of the actual paired quadratic packet.
The bounded phase multiplier commutes with charge. Its pure-clock momentum
and all factor graphs are constructed from directional source outputs. -/
import UnifiedTheory.Audit.KFCausalPairedSpanDomain
import UnifiedTheory.Audit.KFCausalNeutralMixedClockCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedPairFrequencyDomain
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalNeutralMixedClockCharge (phaseOperator phase_measurable phase_bound)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalClockChargeMultiplier (clockMultiplier_coe multiplier_action)
open KFCausalStandingChargeOperator (zeroSector)
open KFCausalPhysicalCircleAction (action)
open KFCausalChargedPairDomain (combine directions)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalClockFloorPureClockKinetic (correction)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)

theorem phase_preserves_zero (h : ℝ) (hh : h ≠ 0) (p : ℝ) (f : Hilbert)
    (hf : f ∈ zeroSector h hh) : phaseOperator p f ∈ zeroSector h hh := by
  change ∀ θ, action h hh θ f = f at hf
  change ∀ θ, action h hh θ (phaseOperator p f) = phaseOperator p f
  intro θ
  unfold phaseOperator
  rw [← multiplier_action,hf θ]

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)

theorem directional_frequency (C : ℂ) (p : ℝ) (d : Transverse) (n : ℕ) :
    KFCausalDirectionalGaussianDomain.input ε a h hε ha hh C p d n =
      phaseOperator p (KFCausalDirectionalGaussianDomain.input ε a h hε ha hh C 0 d n) := by
  apply Lp.ext
  filter_upwards [KFCausalDirectionalGaussianDomain.input_coe ε a h hε ha hh C p d n,
    KFCausalDirectionalGaussianDomain.input_coe ε a h hε ha hh C 0 d n,
    clockMultiplier_coe (fun s : ℝ => clockPhase p (s:ℂ)) (phase_measurable p) (phase_bound p)
      (KFCausalDirectionalGaussianDomain.input ε a h hε ha hh C 0 d n)] with x hi h0 hm
  change _ = (KFCausalClockChargeMultiplier.clockMultiplier _ _ _ _) x
  rw [hi,hm,h0]
  simp only [KFCausalDirectionalGaussianStates.profile,
    KFCausalClockFloorCoherentDerivative.physicalProfile,
    KFCausalClockFloorCoherentDerivative.clockMultiplier,clockPhase,
    Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one]
  ring

theorem centered_zeroSector (p : ℝ) :
    KFCausalDirectionalGaussianDomain.input ε a h hε ha hh 1 p 0 0 ∈ zeroSector h hh := by
  rw [directional_frequency]
  apply phase_preserves_zero h hh p
  change KFCausalPairedSpanDomain.baseState ε a h hε ha hh ∈ zeroSector h hh
  rw [KFCausalPairedSpanDomain.baseState_eq_trial]
  exact KFCausalClockFloorInvariantTrial.trialState_mem_zeroSector ε a h hε ha hh

variable (p : ℝ)

def state : Hilbert :=
  combine (fun i => KFCausalDirectionalGaussianDomain.input ε a h hε ha hh 1 p (directions i) 2)
def momentum : Hilbert :=
  combine (fun i => KFCausalDirectionalClockMomentum.momentum ε a h hε ha hh p (directions i) 1 2)
def output (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  combine (fun i => KFCausalDirectionalGaussianDomain.output
    ε a h hε ha hh 1 p (directions i) 2 hb v l j)
def momentumOutput (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  combine (fun i => KFCausalDirectionalClockMomentum.factor
    ε a h hε ha hh p (directions i) 1 hb 2 v l j)

theorem state_frequency :
    state ε a h hε ha hh p = phaseOperator p (KFCausalChargedPairDomain.state ε a h hε ha hh) := by
  have he : (fun i : Fin 4 => KFCausalDirectionalGaussianDomain.input ε a h hε ha hh 1 p (directions i) 2) =
      (fun i => phaseOperator p (KFCausalDirectionalGaussianDomain.input ε a h hε ha hh 1 0 (directions i) 2)) := by
    funext i
    exact directional_frequency ε a h hε ha hh 1 p (directions i) 2
  unfold state
  rw [he]
  simp only [KFCausalChargedPairDomain.state,combine,map_smul,map_add,map_sub]

theorem state_zeroSector : state ε a h hε ha hh p ∈ zeroSector h hh := by
  rw [state_frequency]
  exact phase_preserves_zero h hh p _ (KFCausalChargedPairCharge.state_zeroSector ε a h hε ha hh)

theorem momentum_graph :
    (state ε a h hε ha hh p,momentum ε a h hε ha hh p) ∈ (pureMomentum ε hε h).graph := by
  have hg (i : Fin 4) := KFCausalDirectionalClockMomentum.momentum_graph
    ε a h hε ha hh p (directions i) 1 2
  exact (pureMomentum ε hε h).graph.smul_mem (1/4:ℂ)
    ((pureMomentum ε hε h).graph.add_mem
      ((pureMomentum ε hε h).graph.sub_mem
        ((pureMomentum ε hε h).graph.sub_mem (hg 0) (hg 1)) (hg 2)) (hg 3))

theorem momentum_zeroSector : momentum ε a h hε ha hh p ∈ zeroSector h hh :=
  KFCausalPureClockZeroProjection.output_zeroSector ε hε h hh _ _
    (momentum_graph ε a h hε ha hh p) (state_zeroSector ε a h hε ha hh p)

theorem output_graph (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (state ε a h hε ha hh p,output ε a h hε ha hh p hb v l j) ∈
      (energyFactor ε hε h v l j).graph := by
  have hg (i : Fin 4) := KFCausalDirectionalGaussianDomain.output_graph
    ε a h hε ha hh 1 p (directions i) 2 hb v l j
  exact (energyFactor ε hε h v l j).graph.smul_mem (1/4:ℂ)
    ((energyFactor ε hε h v l j).graph.add_mem
      ((energyFactor ε hε h v l j).graph.sub_mem
        ((energyFactor ε hε h v l j).graph.sub_mem (hg 0) (hg 1)) (hg 2)) (hg 3))

theorem momentumOutput_graph (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (momentum ε a h hε ha hh p,momentumOutput ε a h hε ha hh p hb v l j) ∈
      (energyFactor ε hε h v l j).graph := by
  have hg (i : Fin 4) := KFCausalDirectionalClockMomentum.factor_graph
    ε a h hε ha hh p (directions i) 1 hb 2 v l j
  exact (energyFactor ε hε h v l j).graph.smul_mem (1/4:ℂ)
    ((energyFactor ε hε h v l j).graph.add_mem
      ((energyFactor ε hε h v l j).graph.sub_mem
        ((energyFactor ε hε h v l j).graph.sub_mem (hg 0) (hg 1)) (hg 2)) (hg 3))

theorem clock_composition_graph (hb : |h| ≤ 2*Real.pi*ε/3) :
    (output ε a h hε ha hh p hb modelDirections pointField 0,
      momentumOutput ε a h hε ha hh p hb modelDirections pointField 0-
        correction ε hε h (output ε a h hε ha hh p hb modelDirections pointField 0)) ∈
      (pureMomentum ε hε h).graph := by
  have hg (i : Fin 4) := KFCausalDirectionalClockComposition.composition_graph
    ε a h hε ha hh hb 1 p (directions i) 2
  have hs := (pureMomentum ε hε h).graph.smul_mem (1/4:ℂ)
    ((pureMomentum ε hε h).graph.add_mem
      ((pureMomentum ε hε h).graph.sub_mem
        ((pureMomentum ε hε h).graph.sub_mem (hg 0) (hg 1)) (hg 2)) (hg 3))
  convert hs using 1
  congr 1
  simp only [output,momentumOutput,combine,Prod.add_def,Prod.sub_def,
    map_smul,map_add,map_sub,smul_add,smul_sub]
  abel

#print axioms phase_preserves_zero
#print axioms directional_frequency
#print axioms centered_zeroSector
#print axioms state_frequency
#print axioms state_zeroSector
#print axioms momentum_graph
#print axioms momentum_zeroSector
#print axioms output_graph
#print axioms momentumOutput_graph
#print axioms clock_composition_graph
end
end UnifiedTheory.Audit.KFCausalChargedPairFrequencyDomain
