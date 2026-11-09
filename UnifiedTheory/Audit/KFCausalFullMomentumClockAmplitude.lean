/- Full-clock amplitudes for both the physical input and its pure-clock
momentum. Their L2 bounds are derived using Gaussian chart moments. -/
import UnifiedTheory.Audit.KFCausalHalfMomentumClockAmplitude
import UnifiedTheory.Audit.KFCausalGaussianClockSquare
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumAmplitudes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalFullMomentumClockAmplitude
noncomputable section
open MeasureTheory
open KFCausalGaussianClockSquare (fullClockFunction fullClockFunction_memLp)
open KFCausalClockFloorInvariantTrial (clockFunction_continuous)
open KFCausalClockFloorFullGaussian (clockFactor)
open KFCausalClockFloorCoherentDerivative (clockMultiplier_memLp)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalRegularizedLongitudinalChart (chart)
open KFCausalGaussianClockMoment (moment_bound bound bound_positive clockFunction_half)
open KFCausalPureClockOutputMultipliers (coefficient)
open KFCausalCorrelatedClusteredMomentumAmplitudes (coefficient_continuous coefficient_bound)

def amplitude (ε a p s : ℝ) : ℂ := clockPhase p (s:ℂ)*fullClockFunction ε a s

theorem amplitude_continuous (ε a p : ℝ) : Continuous (amplitude ε a p) := by
  have hc : Continuous (fun s : ℝ => clockPhase p (s:ℂ)) := by unfold clockPhase; fun_prop
  have hf : Continuous (fullClockFunction ε a) :=
    (by fun_prop : Continuous (fun s : ℝ => ((Real.exp s+ε:ℝ):ℂ))).mul (clockFunction_continuous ε a)
  exact hc.mul hf

theorem amplitude_memLp (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    MemLp (amplitude ε a p) 2 volume := by
  have hm := clockMultiplier_memLp 1 p (fullClockFunction ε a) (fullClockFunction_memLp ε a hε ha)
  change MemLp (fun s : ℝ => 1*clockPhase p (s:ℂ)*fullClockFunction ε a s) 2 volume at hm
  simpa only [one_mul] using hm

theorem amplitude_factor (ε a p s : ℝ) (hε : 0 < ε) :
    amplitude ε a p s = clockFactor (a/2) (chart ε s:ℂ)*amplitude ε (a/2) p s := by
  unfold amplitude fullClockFunction
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
  rw [amplitude_factor ε a p s hε,← mul_assoc]
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
    momentumAmplitude ε a p h s = ((Real.exp s+ε:ℝ):ℂ)*
      ((-Complex.I*(h:ℂ))*KFCausalCorrelatedClusteredMomentumAmplitudes.amplitude ε a p s) := by
  unfold momentumAmplitude amplitude fullClockFunction KFCausalCorrelatedClusteredMomentumAmplitudes.amplitude
    KFCausalCorrelatedClusteredInputProfiles.inputAmplitude
  ring

theorem amplitude_half_identity (ε a p s : ℝ) (hε : 0 < ε) :
    amplitude ε a p s = (Real.sqrt (Real.exp s+ε):ℂ)*KFCausalCorrelatedClusteredHalfClockLimit.amplitude ε a p s := by
  have hs : (Real.sqrt (Real.exp s+ε):ℂ)^2 = ((Real.exp s+ε:ℝ):ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ Real.exp s+ε by positivity)
  unfold amplitude fullClockFunction KFCausalCorrelatedClusteredHalfClockLimit.amplitude
    KFCausalClockFloorTrialClockEnergy.halfClockFunction
  rw [← hs]
  ring

theorem momentumAmplitude_half_identity (ε a p h s : ℝ) (hε : 0 < ε) :
    momentumAmplitude ε a p h s = (Real.sqrt (Real.exp s+ε):ℂ)*
      KFCausalHalfMomentumClockAmplitude.momentumAmplitude ε a p h s := by
  unfold momentumAmplitude KFCausalHalfMomentumClockAmplitude.momentumAmplitude
  rw [amplitude_half_identity ε a p s hε]
  ring

def amplitudes {m : ℕ} (ε h : ℝ) (a p : Fin m → ℝ) (s : ℝ) (i : Fin m) : ℂ :=
  momentumAmplitude ε (a i) (p i) h s

#print axioms amplitude_continuous
#print axioms amplitude_memLp
#print axioms amplitude_half_identity
#print axioms momentumAmplitude_half_identity
#print axioms amplitude_factor
#print axioms moment_continuous
#print axioms moment_memLp
#print axioms momentumAmplitude_continuous
#print axioms momentumAmplitude_memLp
#print axioms momentumAmplitude_identity
end
end UnifiedTheory.Audit.KFCausalFullMomentumClockAmplitude
