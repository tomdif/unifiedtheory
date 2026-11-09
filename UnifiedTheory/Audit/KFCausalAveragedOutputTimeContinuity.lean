/- Joint time/state continuity of the actual averaged energy output. -/
import UnifiedTheory.Audit.KFCausalAveragedOutputRescaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalAveragedOutputTimeContinuity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

theorem timeOutputLp_split (s t : ℝ) (y : EnergyOutputSpace) :
    timeOutputLp s t y = staticOutputLp y+(Real.exp (t-s):ℂ) • growingOutputLp y := by
  apply Lp.ext
  filter_upwards [(timeOutput s t).coeFn_compLp y,staticOutput.coeFn_compLp y,
    growingOutput.coeFn_compLp y,
    Lp.coeFn_add (staticOutputLp y) ((Real.exp (t-s):ℂ) • growingOutputLp y),
    Lp.coeFn_smul (Real.exp (t-s):ℂ) (growingOutputLp y)] with θ ht hs hg ha hm
  change (timeOutput s t).compLp y θ = _
  rw [ht,ha]
  simp only [Pi.add_apply,hm,Pi.smul_apply]
  change timeOutput s t (y θ) = staticOutput.compLp y θ+(Real.exp (t-s):ℂ) • growingOutput.compLp y θ
  rw [hs,hg]
  apply PiLp.ext
  intro i
  simp only [timeOutput_apply,PiLp.add_apply,PiLp.smul_apply,staticOutput,growingOutput,selected_apply]
  split_ifs <;> simp_all

theorem timeOutputLp_continuous (s : ℝ) :
    Continuous (fun p : ℝ × EnergyOutputSpace => timeOutputLp s p.1 p.2) := by
  simp only [timeOutputLp_split]
  exact (staticOutputLp.continuous.comp continuous_snd).add
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_fst.sub continuous_const))).smul
      (growingOutputLp.continuous.comp continuous_snd))

#print axioms timeOutputLp_split
#print axioms timeOutputLp_continuous
end
end UnifiedTheory.Audit.KFCausalAveragedOutputTimeContinuity
