/- A jointly continuous extension of the divided physical squeeze rate.
Compact-interval integration preserves its zero-parameter limit on every
actual finite-energy trajectory, without generator moments. -/
import UnifiedTheory.Audit.KFCausalSqueezeNormalizedOutput
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeBalance
import UnifiedTheory.Audit.KFCausalAveragedOutputTimeContinuity
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSqueezeNormalizedRate
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow)
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution (formFlow_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing (timeOutput)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeBalance (outputRate)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy (OutputSpace variation)
open UnifiedTheory.Audit.KFCausalSqueezeNormalizedOutput
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)

private theorem continuous_rate (c : ℂ) (q : ℝ → OutputSpace) (hq0 : Continuous q) :
    Continuous (fun p : ℝ × ℝ => c*inner ℂ (q p.2) (normalizedLp p.1 (q p.2))) := by
  have hq : Continuous (fun p : ℝ × ℝ => q p.2) := hq0.comp continuous_snd
  have hn := normalizedLp_joint_continuous.comp (continuous_fst.prodMk hq)
  exact (continuous_const (y := c)).mul (hq.inner (𝕜 := ℂ) hn)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k

def output (s t : ℝ) (w : V) : OutputSpace := timeOutput ε hε h hne hh m g k t (F s t w)
def signedVariation (s t : ℝ) (w : V) : ℝ := variation (output ε hε h hne hh m g k s t w)
def normalizedRate (a s t : ℝ) (w : V) : ℂ :=
  coefficient h * inner ℂ (output ε hε h hne hh m g k s t w)
    (normalizedLp a (output ε hε h hne hh m g k s t w))

theorem output_continuous (s : ℝ) (w : V) : Continuous (fun t => output ε hε h hne hh m g k s t w) := by
  have hf := (energyOutput ε hε h hne hh m g k 0).continuous.comp
    (formFlow_continuous ε hε h hne hh m g k s w)
  have hc := (KFCausalAveragedOutputTimeContinuity.timeOutputLp_continuous 0).comp
    (continuous_id.prodMk hf)
  have he : (fun t => output ε hε h hne hh m g k s t w) =
      fun t => KFCausalClockFloorAveragedOutputTransport.timeOutputLp 0 t
        (energyOutput ε hε h hne hh m g k 0 (F s t w)) := by
    funext t
    unfold output timeOutput
    rw [transfer_energyOutput]
  exact hc.congr (fun t => congrFun he.symm t)

theorem normalizedRate_joint_continuous (s : ℝ) (w : V) :
    Continuous (fun p : ℝ × ℝ => normalizedRate ε hε h hne hh m g k p.1 s p.2 w) := by
  exact continuous_rate (coefficient h) (fun t => output ε hε h hne hh m g k s t w)
    (output_continuous ε hε h hne hh m g k s w)

theorem normalizedRate_zero (s t : ℝ) (w : V) : normalizedRate ε hε h hne hh m g k 0 s t w =
    coefficient h * (signedVariation ε hε h hne hh m g k s t w : ℂ) := by
  unfold normalizedRate signedVariation
  rw [normalized_pairing_zero]

theorem outputRate_normalized (a s t : ℝ) (w : V) : outputRate ε hε h hne hh m g k a s t w =
    (a:ℂ)*normalizedRate ε hε h hne hh m g k a s t w := by
  unfold outputRate normalizedRate output
  rw [difference_normalized,ContinuousLinearMap.smul_apply,inner_smul_right]
  ring

theorem normalizedIntegral_continuous (s b c : ℝ) (w : V) :
    Continuous (fun a => ∫ t in b..c, normalizedRate ε hε h hne hh m g k a s t w) := by
  have hc (x y : ℝ) : Continuous (fun a => ∫ t in Set.Ioc x y,
      normalizedRate ε hε h hne hh m g k a s t w) := by
    simp_rw [← integral_Icc_eq_integral_Ioc]
    exact continuous_parametric_integral_of_continuous
      (normalizedRate_joint_continuous ε hε h hne hh m g k s w) isCompact_Icc
  exact (hc b c).sub (hc c b)

theorem normalizedIntegral_limit (s b c : ℝ) (w : V) :
    Tendsto (fun a => ∫ t in b..c, normalizedRate ε hε h hne hh m g k a s t w) (𝓝 0)
      (𝓝 (coefficient h * ∫ t in b..c, (signedVariation ε hε h hne hh m g k s t w : ℂ))) := by
  simpa only [normalizedRate_zero,intervalIntegral.integral_const_mul] using
    (normalizedIntegral_continuous ε hε h hne hh m g k s b c w).tendsto (0:ℝ)

#print axioms output_continuous
#print axioms normalizedRate_joint_continuous
#print axioms normalizedRate_zero
#print axioms outputRate_normalized
#print axioms normalizedIntegral_continuous
#print axioms normalizedIntegral_limit
end
end UnifiedTheory.Audit.KFCausalClockFloorSqueezeNormalizedRate
