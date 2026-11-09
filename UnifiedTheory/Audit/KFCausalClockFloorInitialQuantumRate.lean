/- The actual charge-averaged quantum clock-defect rate converges at the
initial time. This uses the constructed propagator's exact derivative,
not a substituted classical evolution or assumed force convergence. -/
import UnifiedTheory.Audit.KFCausalClockFloorInitialDriftSeed
import UnifiedTheory.Audit.KFCausalAveragedFixedPairing
import UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialQuantumRate
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroSector)
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalDynamics
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftSeed
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow_initial)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput (classicalOutput)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (hbar : ℝ) (hh : hbar ≠ 0)
  (hb : |hbar| ≤ 2*Real.pi*ε/3) (hh1 : |hbar| ≤ 1)
  (mass2 quartic vacuum s : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
local notation "V₀" => FormSpace ε hε hbar hh hb mass2 quartic vacuum 0
local notation "J" => embedding ε hε hbar hh hb mass2 quartic vacuum 0
local notation "w₀" => state ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv
local notation "out" => normalizedJoint ε a hbar hε ha hh hb modelDirections pointField mass2 quartic vacuum s

theorem initial_output_pairing (B : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert) :
    inner ℂ (evolvingOutput ε hε hbar hh hb mass2 quartic vacuum s s w₀)
      (B.compLp (evolvingOutput ε hε hbar hh hb mass2 quartic vacuum s s w₀)) =
        inner ℂ out (B out) := by
  let baseData := KFCausalClockFloorFormHamiltonian.formData ε hε hbar
    (hamiltonian_bound ε hbar hb) mass2 quartic vacuum s
  let v₀ := KFCausalClockFloorFormHamiltonian.commonFormVector ε hε hbar
    (hamiltonian_bound ε hbar hb) mass2 quartic vacuum s
    (trialCommon ε a hbar hε ha hh hb modelDirections pointField)
  let r : ℝ := ‖trialState ε a hbar hε ha hh‖⁻¹
  let v := r • v₀
  have hjv : KFCausalClosedGraphForm.embedding baseData v = unitTrial ε a hbar hε ha hh :=
    (KFCausalClosedGraphForm.embedding baseData).map_smul_of_tower r v₀
  have hzv : KFCausalClosedGraphForm.embedding baseData v ∈ zeroSector hbar hh :=
    Eq.mpr (congrArg (fun z : Hilbert => z ∈ zeroSector hbar hh) hjv)
      (unitTrial_zeroSector ε a hbar hε ha hh)
  have lift := KFCausalAveragedFixedEnergy.exists_fixed_lift
    (H := Hilbert) («E» := KFCausalClosedGraphForm.FormSpace baseData)
    (K := Output (Fin 8) Hilbert)
    (KFCausalPhysicalCircleAction.group hbar hh) (2*Real.pi)
    (KFCausalClosedGraphForm.embedding baseData) (KFCausalClosedGraphForm.energyOutput baseData)
    (KFCausalClosedGraphForm.embedding_injective baseData) (by positivity)
  let hl := lift v hzv
  let u := Classical.choose hl
  have hu := (Classical.choose_spec hl).1
  let g := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε hbar hh hb mass2 quartic vacuum s u
  have hj : J (formTransfer ε hε hbar hh hb mass2 quartic vacuum s 0 g) = unitTrial ε a hbar hε ha hh :=
    (transfer_embedding ε hε hbar hh hb mass2 quartic vacuum s 0 g).trans (hu.trans hjv)
  have hs : w₀ = formTransfer ε hε hbar hh hb mass2 quartic vacuum s 0 g :=
    embedding_injective ε hε hbar hh hb mass2 quartic vacuum 0
      ((state_embedding ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv).trans hj.symm)
  have hout : evolvingOutput ε hε hbar hh hb mass2 quartic vacuum s s w₀ =
      KFCausalClockFloorAveragedEnergy.energyOutput ε hε hbar (hamiltonian_bound ε hbar hb) hh
        mass2 quartic vacuum s u := by
    have hf := formFlow_initial ε hε hbar hh hb mass2 quartic vacuum s w₀
    have ht := (congrArg (formTransfer ε hε hbar hh hb mass2 quartic vacuum 0 s)
      (hf.trans hs)).trans (transfer_inverse ε hε hbar hh hb mass2 quartic vacuum s 0 g)
    exact congrArg (energyOutput ε hε hbar hh hb mass2 quartic vacuum s) ht
  have hp := @KFCausalAveragedFixedPairing.fixed_pairing
    Hilbert (KFCausalClosedGraphForm.FormSpace baseData) (Output (Fin 8) Hilbert)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (KFCausalPhysicalCircleAction.group hbar hh) (2*Real.pi)
    (KFCausalClosedGraphForm.embedding baseData) (KFCausalClosedGraphForm.energyOutput baseData)
    (KFCausalClosedGraphForm.embedding_injective baseData) u v hu hzv B
  have he : KFCausalClosedGraphForm.energyOutput baseData v = out :=
    (KFCausalClosedGraphForm.energyOutput baseData).map_smul_of_tower r v₀
  exact (congrArg (fun z => inner ℂ z (B.compLp z)) hout).trans
    (hp.trans (congrArg (fun z => inner ℂ z (B z)) he))

theorem classical_initial_rate : classicalRate ε hε hbar hh hb mass2 quartic vacuum s s w₀ =
    (inner ℂ out (classicalOutput ε hε out)).re :=
  congrArg Complex.re (initial_output_pairing ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv
    (classicalOutput ε hε))

omit hbar hh hb hh1 in
theorem classical_initial_rate_tendsto
    (h : ℕ → ℝ) (hn : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => classicalRate ε hε (h n) (hn n) (hb n) mass2 quartic vacuum s s
      (state ε a hε ha (h n) (hn n) (hb n) (h1 n) mass2 quartic vacuum s hm hq hv))
      atTop (𝓝 (initialClassicalDrift ε a vacuum s)) := by
  simp_rw [classical_initial_rate]
  exact normalizedJoint_drift_limit ε a hε ha h hn hb hz modelDirections pointField mass2 quartic vacuum s hm hq hv

omit hbar hh hb hh1 in
theorem exact_initial_rate_tendsto
    (h : ℕ → ℝ) (hn : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => exactRate ε hε (h n) (hn n) (hb n) mass2 quartic vacuum s s
      (state ε a hε ha (h n) (hn n) (hb n) (h1 n) mass2 quartic vacuum s hm hq hv))
      atTop (𝓝 (initialClassicalDrift ε a vacuum s)) := by
  have herr : Tendsto (fun n => exactRate ε hε (h n) (hn n) (hb n) mass2 quartic vacuum s s
      (state ε a hε ha (h n) (hn n) (hb n) (h1 n) mass2 quartic vacuum s hm hq hv)-
    classicalRate ε hε (h n) (hn n) (hb n) mass2 quartic vacuum s s
      (state ε a hε ha (h n) (hn n) (hb n) (h1 n) mass2 quartic vacuum s hm hq hv)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => by
      simpa only [Real.norm_eq_abs,rateError] using
        rateError_uniform_bound ε a hε ha mass2 quartic vacuum s hm hq hv (h n) (hn n) (hb n) (h1 n)
          0 s (by simp))
    simpa only [abs_zero,mul_zero] using hz.abs.const_mul (windowConstant ε a mass2 quartic vacuum s 0)
  have ht := herr.add (classical_initial_rate_tendsto ε a hε ha mass2 quartic vacuum s hm hq hv h hn hb h1 hz)
  simpa only [sub_add_cancel,zero_add] using ht

#print axioms initial_output_pairing
#print axioms classical_initial_rate
#print axioms classical_initial_rate_tendsto
#print axioms exact_initial_rate_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorInitialQuantumRate
