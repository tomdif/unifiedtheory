/- Applying the half-clock weight to the actual pure-momentum clock
coefficient preserves L2. The chart moment uses half-width damping. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredHalfClockLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumAmplitudes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalHalfMomentumClockAmplitude
noncomputable section
open MeasureTheory
open KFCausalCorrelatedClusteredHalfClockLimit (amplitude amplitude_continuous amplitude_memLp)
open KFCausalClockFloorFullGaussian (clockFactor)
open KFCausalClockFloorTrialClockEnergy (halfClockFunction)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalRegularizedLongitudinalChart (chart)
open KFCausalGaussianClockMoment (moment_bound bound bound_positive clockFunction_half)
open KFCausalPureClockOutputMultipliers (coefficient)
open KFCausalCorrelatedClusteredMomentumAmplitudes (coefficient_continuous coefficient_bound)

theorem halfAmplitude_factor (ε a p s : ℝ) (hε : 0 < ε) :
    amplitude ε a p s = clockFactor (a/2) (chart ε s:ℂ)*amplitude ε (a/2) p s := by
  unfold amplitude halfClockFunction
  rw [clockFunction_half ε a s hε]
  ring

theorem moment_continuous (ε a p : ℝ) :
    Continuous (fun s => (chart ε s:ℂ)*amplitude ε a p s) := by
  have ht : Continuous (fun s => (chart ε s:ℂ)) := by unfold chart; fun_prop
  exact ht.mul (amplitude_continuous ε a p)

theorem moment_memLp (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    MemLp (fun s => (chart ε s:ℂ)*amplitude ε a p s) 2 volume := by
  apply ((amplitude_memLp ε (a/2) p hε (by positivity)).const_mul (bound a 0:ℂ)).of_le
    (moment_continuous ε a p).aestronglyMeasurable
  filter_upwards [] with s
  rw [halfAmplitude_factor ε a p s hε,← mul_assoc]
  have hm := mul_le_mul_of_nonneg_right (moment_bound a (chart ε s) 0 ha)
    (norm_nonneg (amplitude ε (a/2) p s))
  simpa only [Complex.ofReal_zero,zero_mul,add_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (bound_positive a 0 ha)] using hm

def momentumAmplitude (ε a p h s : ℝ) : ℂ :=
  (-Complex.I*(h:ℂ))*((coefficient ε p s-2*(a:ℂ)*(chart ε s:ℂ))*amplitude ε a p s)

theorem momentumAmplitude_continuous (ε a p h : ℝ) (hε : 0 < ε) :
    Continuous (momentumAmplitude ε a p h) := by
  have ht : Continuous (fun s => (chart ε s:ℂ)) := by unfold chart; fun_prop
  exact continuous_const.mul (((coefficient_continuous ε p hε).sub (continuous_const.mul ht)).mul
    (amplitude_continuous ε a p))

theorem momentumAmplitude_memLp (ε a p h : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    MemLp (momentumAmplitude ε a p h) 2 volume := by
  let B := ‖(p:ℂ)*Complex.I-1‖/ε+1/(8*ε)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb : MemLp (fun s => coefficient ε p s*amplitude ε a p s) 2 volume := by
    apply ((amplitude_memLp ε a p hε ha).const_mul (B:ℂ)).of_le
      ((coefficient_continuous ε p hε).mul (amplitude_continuous ε a p)).aestronglyMeasurable
    filter_upwards [] with s
    simp only [Pi.mul_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_right (coefficient_bound ε p hε s) (norm_nonneg (amplitude ε a p s))
  have hm := (hb.sub ((moment_memLp ε a p hε ha).const_mul (2*(a:ℂ)))).const_mul (-Complex.I*(h:ℂ))
  convert hm using 1
  funext s
  simp only [momentumAmplitude,Pi.sub_apply]
  ring

theorem momentumAmplitude_identity (ε a p h s : ℝ) :
    momentumAmplitude ε a p h s = (Real.sqrt (Real.exp s+ε):ℂ)*
      ((-Complex.I*(h:ℂ))*KFCausalCorrelatedClusteredMomentumAmplitudes.amplitude ε a p s) := by
  unfold momentumAmplitude amplitude halfClockFunction KFCausalCorrelatedClusteredMomentumAmplitudes.amplitude
    KFCausalCorrelatedClusteredInputProfiles.inputAmplitude
  ring

def amplitudes {m : ℕ} (ε h : ℝ) (a p : Fin m → ℝ) (s : ℝ) (i : Fin m) : ℂ :=
  momentumAmplitude ε (a i) (p i) h s

#print axioms halfAmplitude_factor
#print axioms moment_continuous
#print axioms moment_memLp
#print axioms momentumAmplitude_continuous
#print axioms momentumAmplitude_memLp
#print axioms momentumAmplitude_identity
end
end UnifiedTheory.Audit.KFCausalHalfMomentumClockAmplitude
