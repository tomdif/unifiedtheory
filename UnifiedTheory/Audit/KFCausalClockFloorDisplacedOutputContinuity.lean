/- Continuity of the actual evolving energy output and its classical
clock-coefficient pairing, needed for integration of the rate error. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedOutputContinuity
noncomputable section
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport (timeOutput timeOutput_apply staticOutput growingOutput)
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling (selected_apply)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (staticOutputLp growingOutputLp)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow)
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution (formFlow_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest (evolvingOutput classicalRate)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState (referenceState)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates (comparisonRate)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput (classicalOutput)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

theorem timeOutput_split (s t : ℝ) :
    timeOutput s t = staticOutput+(Real.exp (t-s):ℂ) • growingOutput := by
  apply ContinuousLinearMap.ext
  intro y
  apply PiLp.ext
  intro i
  by_cases hi : i.val < 3 <;> simp [timeOutput_apply,staticOutput,growingOutput,selected_apply,hi]

theorem timeOutputLp_split (s t : ℝ) :
    timeOutputLp s t = staticOutputLp+(Real.exp (t-s):ℂ) • growingOutputLp := by
  rw [timeOutputLp,timeOutput_split,ContinuousLinearMap.add_compLpL,ContinuousLinearMap.smul_compLpL]
  rfl

theorem evolvingOutput_continuous (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (w : FormSpace ε hε h hh hb m g κ 0) :
    Continuous (fun t => evolvingOutput ε hε h hh hb m g κ s t w) := by
  have hc := (energyOutput ε hε h hh hb m g κ 0).continuous.comp
    (formFlow_continuous ε hε h hh hb m g κ s w)
  simp_rw [evolvingOutput,transfer_energyOutput,timeOutputLp_split,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply]
  exact (staticOutputLp.continuous.comp hc).add
    ((show Continuous (fun t : ℝ => (Real.exp (t-0):ℂ)) by fun_prop).smul (growingOutputLp.continuous.comp hc))

theorem comparisonRate_continuous (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration) :
    Continuous (comparisonRate ε a h hε ha hh hb m g κ s p) := by
  have hc := evolvingOutput_continuous ε hε h hh hb m g κ s (referenceState ε a h hε ha hh hb m g κ s p)
  exact Complex.continuous_re.comp (hc.inner ((classicalOutput ε hε).compLpL 2 _ |>.continuous.comp hc))

#print axioms timeOutput_split
#print axioms timeOutputLp_split
#print axioms evolvingOutput_continuous
#print axioms comparisonRate_continuous

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedOutputContinuity
