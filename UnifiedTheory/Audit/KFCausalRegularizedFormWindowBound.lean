/- Cutoff-independent bounds in the fixed reference form space, on every
compact time window. The physical smoothing map is a contraction. -/
import UnifiedTheory.Audit.KFCausalRegularizedSmoothedTrajectory

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedFormWindowBound
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedFormTimeControl
open UnifiedTheory.Audit.KFCausalRegularizedHamiltonian
open UnifiedTheory.Audit.KFCausalRegularizedShiftedResolvent
open UnifiedTheory.Audit.KFCausalRegularizedYosida
open UnifiedTheory.Audit.KFCausalRegularizedYosidaDynamics
open UnifiedTheory.Audit.KFCausalRegularizedSmoothedTrajectory
open UnifiedTheory.Audit.KFCausalYosidaApproximation

theorem smoothedState_norm_le (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) : ‖smoothedState ε hε hbar coupling a ha s t f‖ ≤ ‖f‖ := by
  rw [smoothedState_resolvent]
  have hc := scaled_resolvent_contraction (homogeneousHamiltonian ε hε hbar coupling t)
    (shiftedResolvent ε hε hbar coupling a t) a ha
    (homogeneous_resolves ε hε hbar coupling a t ha)
    (homogeneous_positive ε hε hbar coupling t) (dynamics ε hε hbar coupling a ha s t f)
  exact hc.trans_eq (dynamics_norm ε hε hbar coupling a ha s t f)

theorem reference_energy_window (ε : ℝ) (hε : 0 < ε) (hbar coupling T t : ℝ)
    (hT : 0 ≤ T) (ht : |t| ≤ T) (u : FormSpace ε hε hbar coupling 0) :
    timeEnergy ε hε hbar coupling 0 u ≤ Real.exp (2*T)*timeEnergy ε hε hbar coupling t u := by
  have h1 : 1 ≤ Real.exp (2*T) := Real.one_le_exp (by positivity)
  have ht' := (abs_le.mp ht).1
  have h2 : 1 ≤ Real.exp (2*T)*Real.exp (2*t) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have ha := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖clockPart ε hε hbar coupling u‖)
  have hb := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖momentumPart ε hε hbar coupling u‖)
  simp only [timeEnergy,mul_zero,Real.exp_zero,one_mul]
  nlinarith

def windowEnergy (ε : ℝ) (hε : 0 < ε) (hbar coupling s T : ℝ)
    (w : FormSpace ε hε hbar coupling 0) : ℝ :=
  Real.exp (2*(T+|s|))*timeEnergy ε hε hbar coupling s w

def windowRadius (ε : ℝ) (hε : 0 < ε) (hbar coupling s T : ℝ)
    (w : FormSpace ε hε hbar coupling 0) : ℝ :=
  Real.sqrt (‖embedding ε hε hbar coupling 0 w‖^2 +
    Real.exp (2*T)*windowEnergy ε hε hbar coupling s T w)

theorem windowEnergy_nonneg (ε : ℝ) (hε : 0 < ε) (hbar coupling s T : ℝ)
    (w : FormSpace ε hε hbar coupling 0) : 0 ≤ windowEnergy ε hε hbar coupling s T w :=
  mul_nonneg (Real.exp_pos _).le (timeEnergy_nonneg ε hε hbar coupling s w)

theorem energy_le_window (ε : ℝ) (hε : 0 < ε) (hbar coupling s T t : ℝ)
    (ht : |t| ≤ T) (w : FormSpace ε hε hbar coupling 0) :
    Real.exp (2*|t-s|)*timeEnergy ε hε hbar coupling s w ≤
      windowEnergy ε hε hbar coupling s T w := by
  apply mul_le_mul_of_nonneg_right _ (timeEnergy_nonneg ε hε hbar coupling s w)
  apply Real.exp_le_exp.mpr
  have hh : |t-s| ≤ |t|+|s| := by simpa using abs_sub_le t 0 s
  linarith

theorem smoothed_window_energy (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s T t : ℝ) (ht : |t| ≤ T) (w : FormSpace ε hε hbar coupling 0) :
    timeEnergy ε hε hbar coupling t
      (smoothedLift ε hε hbar coupling a ha s t (embedding ε hε hbar coupling 0 w)) ≤
      windowEnergy ε hε hbar coupling s T w :=
  (smoothed_uniform_form_bound ε hε hbar coupling a ha s t w).trans
    (energy_le_window ε hε hbar coupling s T t ht w)

theorem smoothed_window_norm (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s T t : ℝ) (hT : 0 ≤ T) (ht : |t| ≤ T) (w : FormSpace ε hε hbar coupling 0) :
    ‖smoothedLift ε hε hbar coupling a ha s t (embedding ε hε hbar coupling 0 w)‖ ≤
      windowRadius ε hε hbar coupling s T w := by
  let u := smoothedLift ε hε hbar coupling a ha s t (embedding ε hε hbar coupling 0 w)
  have hn : ‖u‖^2 = ‖embedding ε hε hbar coupling 0 u‖^2 + timeEnergy ε hε hbar coupling 0 u := by
    rw [reference_norm_identity,timeEnergy]
    simp only [mul_zero,Real.exp_zero,one_mul,add_assoc]
  have hp := smoothedState_norm_le ε hε hbar coupling a ha s t (embedding ε hε hbar coupling 0 w)
  change ‖embedding ε hε hbar coupling 0 u‖ ≤ ‖embedding ε hε hbar coupling 0 w‖ at hp
  have hq := (reference_energy_window ε hε hbar coupling T t hT ht u).trans
    (mul_le_mul_of_nonneg_left (smoothed_window_energy ε hε hbar coupling a ha s T t ht w)
      (Real.exp_pos _).le)
  have hs : ‖u‖^2 ≤ ‖embedding ε hε hbar coupling 0 w‖^2 +
      Real.exp (2*T)*windowEnergy ε hε hbar coupling s T w := by
    rw [hn]
    exact add_le_add (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hp) hq
  change ‖u‖ ≤ Real.sqrt _
  exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans hs)).mpr hs

theorem smoothed_window_defect (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s T t : ℝ) (ht : |t| ≤ T) (w : FormSpace ε hε hbar coupling 0) :
    ‖dynamics ε hε hbar coupling a ha s t (embedding ε hε hbar coupling 0 w)-
      smoothedState ε hε hbar coupling a ha s t (embedding ε hε hbar coupling 0 w)‖^2 ≤
      windowEnergy ε hε hbar coupling s T w/a :=
  (smoothed_uniform_defect_bound ε hε hbar coupling a ha s t w).trans
    (div_le_div_of_nonneg_right (energy_le_window ε hε hbar coupling s T t ht w) ha.le)

#print axioms smoothedState_norm_le
#print axioms reference_energy_window
#print axioms smoothed_window_energy
#print axioms smoothed_window_norm
#print axioms smoothed_window_defect

end
end UnifiedTheory.Audit.KFCausalRegularizedFormWindowBound
