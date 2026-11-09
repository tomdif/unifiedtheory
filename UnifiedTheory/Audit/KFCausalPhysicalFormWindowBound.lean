/- Cutoff-independent bounds in the fixed reference form space, on every
compact time window. The physical smoothing map is a contraction. -/
import UnifiedTheory.Audit.KFCausalPhysicalFormGeometry
import UnifiedTheory.Audit.KFCausalPhysicalSmoothedTrajectory

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPhysicalFormWindowBound
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalPhysicalFormTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormGeometry
open UnifiedTheory.Audit.KFCausalPhysicalFormTimeControl
open UnifiedTheory.Audit.KFCausalPhysicalFormHamiltonian
open UnifiedTheory.Audit.KFCausalPhysicalShiftedResolvent
open UnifiedTheory.Audit.KFCausalPhysicalYosida
open UnifiedTheory.Audit.KFCausalPhysicalYosidaDynamics
open UnifiedTheory.Audit.KFCausalPhysicalSmoothedTrajectory
open UnifiedTheory.Audit.KFCausalYosidaApproximation

theorem smoothedState_norm_le (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) : ‖smoothedState ε hε hbar hh mass2 quartic vacuum a ha s t f‖ ≤ ‖f‖ := by
  rw [smoothedState_resolvent]
  have hc := scaled_resolvent_contraction (hamiltonian ε hε hbar hh mass2 quartic vacuum t)
    (shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t) a ha
    (physical_resolves ε hε hbar hh mass2 quartic vacuum a t ha)
    (hamiltonian_positive ε hε hbar hh mass2 quartic vacuum t) (dynamics ε hε hbar hh mass2 quartic vacuum a ha s t f)
  exact hc.trans_eq (dynamics_norm ε hε hbar hh mass2 quartic vacuum a ha s t f)

theorem reference_energy_window (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum T t : ℝ)
    (hT : 0 ≤ T) (ht : |t| ≤ T) (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    timeEnergy ε hε hbar hh mass2 quartic vacuum 0 u ≤ Real.exp (2*T)*timeEnergy ε hε hbar hh mass2 quartic vacuum t u := by
  have h1 : 1 ≤ Real.exp (2*T) := Real.one_le_exp (by positivity)
  have ht' := (abs_le.mp ht).1
  have h2 : 1 ≤ Real.exp (2*T)*Real.exp (2*t) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have ha := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖staticPart ε hε hbar hh mass2 quartic vacuum u‖)
  have hb := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖growingPart ε hε hbar hh mass2 quartic vacuum u‖)
  simp only [timeEnergy,mul_zero,Real.exp_zero,one_mul]
  nlinarith

def windowEnergy (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s T : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) : ℝ :=
  Real.exp (2*(T+|s|))*timeEnergy ε hε hbar hh mass2 quartic vacuum s w

def windowRadius (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s T : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) : ℝ :=
  Real.sqrt (‖embedding ε hε hbar hh mass2 quartic vacuum 0 w‖^2 +
    Real.exp (2*T)*windowEnergy ε hε hbar hh mass2 quartic vacuum s T w)

theorem windowEnergy_nonneg (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s T : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) : 0 ≤ windowEnergy ε hε hbar hh mass2 quartic vacuum s T w :=
  mul_nonneg (Real.exp_pos _).le (timeEnergy_nonneg ε hε hbar hh mass2 quartic vacuum s w)

theorem energy_le_window (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s T t : ℝ)
    (ht : |t| ≤ T) (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    Real.exp (2*|t-s|)*timeEnergy ε hε hbar hh mass2 quartic vacuum s w ≤
      windowEnergy ε hε hbar hh mass2 quartic vacuum s T w := by
  apply mul_le_mul_of_nonneg_right _ (timeEnergy_nonneg ε hε hbar hh mass2 quartic vacuum s w)
  apply Real.exp_le_exp.mpr
  have hpair : |t-s| ≤ |t|+|s| := by simpa using abs_sub_le t 0 s
  linarith

theorem smoothed_window_energy (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s T t : ℝ) (ht : |t| ≤ T) (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    timeEnergy ε hε hbar hh mass2 quartic vacuum t
      (smoothedLift ε hε hbar hh mass2 quartic vacuum a ha s t (embedding ε hε hbar hh mass2 quartic vacuum 0 w)) ≤
      windowEnergy ε hε hbar hh mass2 quartic vacuum s T w :=
  (smoothed_uniform_form_bound ε hε hbar hh mass2 quartic vacuum a ha s t w).trans
    (energy_le_window ε hε hbar hh mass2 quartic vacuum s T t ht w)

theorem smoothed_window_norm (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s T t : ℝ) (hT : 0 ≤ T) (ht : |t| ≤ T) (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    ‖smoothedLift ε hε hbar hh mass2 quartic vacuum a ha s t (embedding ε hε hbar hh mass2 quartic vacuum 0 w)‖ ≤
      windowRadius ε hε hbar hh mass2 quartic vacuum s T w := by
  let u := smoothedLift ε hε hbar hh mass2 quartic vacuum a ha s t (embedding ε hε hbar hh mass2 quartic vacuum 0 w)
  have hn : ‖u‖^2 = ‖embedding ε hε hbar hh mass2 quartic vacuum 0 u‖^2 + timeEnergy ε hε hbar hh mass2 quartic vacuum 0 u := by
    rw [reference_norm_identity,timeEnergy]
    simp only [mul_zero,Real.exp_zero,one_mul,add_assoc]
  have hp := smoothedState_norm_le ε hε hbar hh mass2 quartic vacuum a ha s t (embedding ε hε hbar hh mass2 quartic vacuum 0 w)
  change ‖embedding ε hε hbar hh mass2 quartic vacuum 0 u‖ ≤ ‖embedding ε hε hbar hh mass2 quartic vacuum 0 w‖ at hp
  have hq := (reference_energy_window ε hε hbar hh mass2 quartic vacuum T t hT ht u).trans
    (mul_le_mul_of_nonneg_left (smoothed_window_energy ε hε hbar hh mass2 quartic vacuum a ha s T t ht w)
      (Real.exp_pos _).le)
  have hs : ‖u‖^2 ≤ ‖embedding ε hε hbar hh mass2 quartic vacuum 0 w‖^2 +
      Real.exp (2*T)*windowEnergy ε hε hbar hh mass2 quartic vacuum s T w := by
    rw [hn]
    exact add_le_add (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hp) hq
  change ‖u‖ ≤ Real.sqrt _
  exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans hs)).mpr hs

theorem smoothed_window_defect (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s T t : ℝ) (ht : |t| ≤ T) (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    ‖dynamics ε hε hbar hh mass2 quartic vacuum a ha s t (embedding ε hε hbar hh mass2 quartic vacuum 0 w)-
      smoothedState ε hε hbar hh mass2 quartic vacuum a ha s t (embedding ε hε hbar hh mass2 quartic vacuum 0 w)‖^2 ≤
      windowEnergy ε hε hbar hh mass2 quartic vacuum s T w/a :=
  (smoothed_uniform_defect_bound ε hε hbar hh mass2 quartic vacuum a ha s t w).trans
    (div_le_div_of_nonneg_right (energy_le_window ε hε hbar hh mass2 quartic vacuum s T t ht w) ha.le)

#print axioms smoothedState_norm_le
#print axioms reference_energy_window
#print axioms smoothed_window_energy
#print axioms smoothed_window_norm
#print axioms smoothed_window_defect

end
end UnifiedTheory.Audit.KFCausalPhysicalFormWindowBound
