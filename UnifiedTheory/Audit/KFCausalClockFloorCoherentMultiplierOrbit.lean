/- A fixed configuration multiplier preserves continuous sourced-Gaussian
orbits whenever its product with the uniform Gaussian majorant is in L2.
This applies after the exact complex longitudinal shift. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral
import UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentMultiplierOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentParameters
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (configurationLine configurationLine_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates (grouping)
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates (weightedFunction coordinates_toLp_coe)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalChargeModulationFlow
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)

def baseLine (ε a hbar y : ℝ) : Configuration → ℂ :=
  KFCausalClockFloorShiftedOutput.configurationLine ε a (groundWidth hbar/2) (neutralWidth hbar/2) y

theorem baseLine_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) : MemLp (baseLine ε a hbar y) 2 volume :=
  KFCausalClockFloorShiftedOutput.configurationLine_memLp ε a _ _ y hε ha
    (by have := groundWidth_positive hbar hh; positivity)
    (by have := neutralWidth_positive hbar hh; positivity)
    (by have := neutralWidth_bound hbar; linarith) hy

def orbitConstant (hbar : ℝ) (k : Joint 2 4) : ℝ :=
  Real.exp ((2*Real.pi*‖k‖)*Real.pi/3+
    (4*Real.pi^2*‖k‖^2)*positionConstant (groundWidth hbar) (neutralWidth hbar)/2)

def modifiedLine (ε a hbar y : ℝ) (m : Configuration → ℂ) (k : Joint 2 4) (x : Configuration) : ℂ :=
  m x*(amplitudeConstant hbar k*configurationLine ε a (groundWidth hbar) (neutralWidth hbar)
    (clockFrequency k) (sourceCoefficients hbar k) y x)

theorem modifiedLine_bound (ε a hbar : ℝ) (hε : 0 < ε) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (m : Configuration → ℂ) (θ : ℝ) (k : Joint 2 4) (x : Configuration) :
    ‖modifiedLine ε a hbar y m (parameter θ k) x‖ ≤ orbitConstant hbar k*‖m x*baseLine ε a hbar y x‖ := by
  have h := mul_le_mul_of_nonneg_left (orbit_line_bound ε a hbar hε hh θ k y hy (grouping x)) (norm_nonneg (m x))
  simpa only [modifiedLine,baseLine,KFCausalClockFloorShiftedOutput.configurationLine,configurationLine,
    orbitConstant,norm_mul,mul_left_comm] using h

theorem modifiedLine_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (m : Configuration → ℂ) (hm : AEStronglyMeasurable m volume)
    (hbase : MemLp (fun x => m x*baseLine ε a hbar y x) 2 volume) (k : Joint 2 4) :
    MemLp (modifiedLine ε a hbar y m k) 2 volume := by
  have hl := configurationLine_memLp ε a (groundWidth hbar) (neutralWidth hbar)
    (clockFrequency k) (sourceCoefficients hbar k) y hε ha (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) hy
  apply (hbase.const_mul (orbitConstant hbar k:ℂ)).of_le
    (hm.mul (hl.const_mul (amplitudeConstant hbar k)).aestronglyMeasurable)
  filter_upwards [] with x
  have h := modifiedLine_bound ε a hbar hε hh y hy m 0 k x
  simpa only [parameter_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (show 0 < orbitConstant hbar k from Real.exp_pos _)] using h

theorem modifiedLine_orbit_continuous (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (m : Configuration → ℂ) (hm : AEStronglyMeasurable m volume)
    (hbase : MemLp (fun x => m x*baseLine ε a hbar y x) 2 volume) (k : Joint 2 4) :
    Continuous (fun θ => (modifiedLine_memLp ε a hbar hε ha hh y hy m hm hbase (parameter θ k)).toLp
      (modifiedLine ε a hbar y m (parameter θ k))) := by
  have hp : Continuous (fun θ : ℝ => parameter θ k) :=
    parameter_continuous.comp (f := fun θ : ℝ => (θ,k)) (continuous_id.prodMk continuous_const)
  have hC := (amplitudeConstant_continuous hbar).comp hp
  have hp' := clockFrequency_continuous.comp hp
  have hb := (sourceCoefficients_continuous hbar).comp hp
  apply KFCausalDominatedL2Continuity.continuous_toLp _ _
    (fun x => (orbitConstant hbar k:ℂ)*(m x*baseLine ε a hbar y x)) (hbase.const_mul _)
  · intro θ
    filter_upwards [] with x
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0 < orbitConstant hbar k from Real.exp_pos _)] using
      modifiedLine_bound ε a hbar hε hh y hy m θ k x
  · filter_upwards [] with x
    unfold modifiedLine configurationLine line trial coherentPacket source clockPhase
    fun_prop

def outputState (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (m : Configuration → ℂ) (hm : AEStronglyMeasurable m volume)
    (hbase : MemLp (fun x => m x*baseLine ε a hbar y x) 2 volume) (k : Joint 2 4) : Hilbert :=
  coordinates ε hε ((modifiedLine_memLp ε a hbar hε ha hh y hy m hm hbase k).toLp (modifiedLine ε a hbar y m k))

theorem outputState_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (m : Configuration → ℂ) (hm : AEStronglyMeasurable m volume)
    (hbase : MemLp (fun x => m x*baseLine ε a hbar y x) 2 volume) (k : Joint 2 4) :
    outputState ε a hbar hε ha hh y hy m hm hbase k =ᵐ[volume]
      weightedFunction ε hε (modifiedLine ε a hbar y m k) := coordinates_toLp_coe ε hε _ _

theorem outputState_orbit_continuous (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (m : Configuration → ℂ) (hm : AEStronglyMeasurable m volume)
    (hbase : MemLp (fun x => m x*baseLine ε a hbar y x) 2 volume) (k : Joint 2 4) :
    Continuous (fun θ => outputState ε a hbar hε ha hh y hy m hm hbase (parameter θ k)) :=
  (coordinates ε hε).continuous.comp (modifiedLine_orbit_continuous ε a hbar hε ha hh y hy m hm hbase k)

#print axioms baseLine_memLp
#print axioms modifiedLine_bound
#print axioms modifiedLine_memLp
#print axioms modifiedLine_orbit_continuous
#print axioms outputState_coe
#print axioms outputState_orbit_continuous

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentMultiplierOrbit
