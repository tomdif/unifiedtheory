/- Quantitative approximation of the actual full quantum propagator.
The residual is derived from a separately smoothed full trajectory;
no unproved Hamiltonian-domain propagation or residual premise is used. -/
import UnifiedTheory.Audit.KFCausalClockFloorSmoothedFullDerivative
import UnifiedTheory.Audit.KFCausalTwoScaleResolventResidual

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorYosidaErrorRate
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian hamiltonian_positive)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalClockFloorResolventTests
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolvent
open UnifiedTheory.Audit.KFCausalClockFloorSmoothedFullDerivative
open UnifiedTheory.Audit.KFCausalStrongResidualCalculus

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "Y" => averagedYosida ε hε h hne hh m g k
local notation "A" => generator ε hε h hne hh m g k
local notation "R" => regularizer ε hε h hne hh m g k
local notation "S" => UnifiedTheory.Audit.KFCausalClockFloorMovingResolvent.derivative ε hε h hne hh m g k
local notation "E" => timeEnergy ε hε h hne hh m g k
local notation "D" => dynamics ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

def budget (s T : ℝ) (w : V) : ℝ := Real.exp (2*T)*E s w
def residual (a b s t : ℝ) (w : V) : Hilbert :=
  S b t (U s t (J w))+c • (Y b t (U s t (J w))-Y a t (R b t (U s t (J w))))

theorem flow_energy_window (s T z : ℝ) (hz : |z-s| ≤ T) (w : V) :
    E z (F s z w) ≤ budget ε hε h hne hh m g k s T w :=
  (formFlow_energy_bound ε hε h hne hh m g k s z w).trans
    (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz (by norm_num)))
      (timeEnergy_nonneg ε hε h hne hh m g k s w))

theorem smoothed_hamiltonian_error (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (x : V) :
    ‖Y a t (R b t (J x))-Y b t (J x)‖ ≤ 2*b*Real.sqrt (E t x/(4*a)) := by
  have hr := KFCausalTwoScaleResolventResidual.residual_bound
    (hamiltonian ε hε h hne hh m g k t)
    (shiftedResolvent ε hε h hne hh m g k a t)
    (shiftedResolvent ε hε h hne hh m g k b t) a b hb
    (averaged_resolves ε hε h hne hh m g k a t ha)
    (averaged_resolves ε hε h hne hh m g k b t hb)
    (shiftedResolvent_left ε hε h hne hh m g k a t ha)
    (shiftedResolvent_left ε hε h hne hh m g k b t hb)
    (hamiltonian_positive ε hε h hne hh m g k t) (J x)
  have hs : ‖J x-R a t (J x)‖ ≤ Real.sqrt (E t x/(4*a)) := by
    rw [norm_sub_rev]
    exact regularizer_error_norm ε hε h hne hh m g k a t ha x
  exact hr.trans (mul_le_mul_of_nonneg_left hs (by positivity))

theorem smoothed_equation (a b : ℝ) (hb : 0 < b) (s t : ℝ) (w : V) :
    HasDerivAt (fun z => R b z (U s z (J w)))
      (A a t (R b t (U s t (J w)))+residual ε hε h hne hh m g k a b s t w) t := by
  apply (smoothed_derivative ε hε h hne hh m g k b hb s t w).congr_deriv
  change S b t (U s t (J w))+c • Y b t (U s t (J w)) =
    c • Y a t (R b t (U s t (J w)))+
      (S b t (U s t (J w))+c • (Y b t (U s t (J w))-Y a t (R b t (U s t (J w)))))
  rw [smul_sub]
  abel

theorem residual_window_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (s T z : ℝ) (hz : |z-s| ≤ T) (w : V) :
    ‖residual ε hε h hne hh m g k a b s z w‖ ≤
      Real.sqrt (budget ε hε h hne hh m g k s T w/b)+
        |1/h| *(2*b*Real.sqrt (budget ε hε h hne hh m g k s T w/(4*a))) := by
  let B := budget ε hε h hne hh m g k s T w
  have he := flow_energy_window ε hε h hne hh m g k s T z hz w
  have hs : ‖S b z (U s z (J w))‖ ≤ Real.sqrt (B/b) := by
    rw [evolution_embedding]
    exact (derivative_error_norm ε hε h hne hh m g k b z hb (F s z w)).trans
      (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right he hb.le))
  have hy : ‖Y b z (U s z (J w))-Y a z (R b z (U s z (J w)))‖ ≤
      2*b*Real.sqrt (B/(4*a)) := by
    rw [norm_sub_rev,evolution_embedding]
    exact (smoothed_hamiltonian_error ε hε h hne hh m g k a b z ha hb (F s z w)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
        (div_le_div_of_nonneg_right he (by positivity))) (by positivity))
  have hc : ‖c‖ = |1/h| := by
    simp only [norm_mul,norm_neg,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul]
  exact (norm_add_le _ _).trans (add_le_add hs (by
    rw [norm_smul,hc]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)))

theorem smoothing_window_bound (b : ℝ) (hb : 0 < b) (s T z : ℝ)
    (hz : |z-s| ≤ T) (w : V) :
    ‖R b z (U s z (J w))-U s z (J w)‖ ≤
      Real.sqrt (budget ε hε h hne hh m g k s T w/(4*b)) := by
  rw [evolution_embedding]
  exact (regularizer_error_norm ε hε h hne hh m g k b z hb (F s z w)).trans
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
      (flow_energy_window ε hε h hne hh m g k s T z hz w) (by positivity)))

theorem two_scale_error (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (s T t : ℝ) (hT : 0 ≤ T) (ht : |t-s| ≤ T) (w : V) :
    ‖D a ha s t (J w)-U s t (J w)‖ ≤
      2*Real.sqrt (budget ε hε h hne hh m g k s T w/(4*b))+
      (Real.sqrt (budget ε hε h hne hh m g k s T w/b)+
        |1/h| *(2*b*Real.sqrt (budget ε hε h hne hh m g k s T w/(4*a))))*T := by
  let B := budget ε hε h hne hh m g k s T w
  let C := Real.sqrt (B/b)+|1/h| *(2*b*Real.sqrt (B/(4*a)))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hr := residual_error_bound (A a) (generator_continuous ε hε h hne hh m g k a ha)
    (fun z => generator_skew ε hε h hne hh m g k a z ha)
    (fun z => R b z (U s z (J w))) (fun z => residual ε hε h hne hh m g k a b s z w)
    (fun z => smoothed_equation ε hε h hne hh m g k a b hb s z w) s t C (J w)
    (fun z hz => residual_window_bound ε hε h hne hh m g k a b ha hb s T z
      ((abs_sub_left_of_mem_uIcc hz).trans ht) w)
  have hi := smoothing_window_bound ε hε h hne hh m g k b hb s T s
    (by simpa only [sub_self,abs_zero] using hT) w
  have hi' : ‖J w-R b s (U s s (J w))‖ ≤ Real.sqrt (B/(4*b)) := by
    have hu : U s s (J w) = J w := by
      rw [evolution_embedding,formFlow_initial]
    calc
      _ = ‖U s s (J w)-R b s (U s s (J w))‖ :=
        congrArg (fun q : Hilbert => ‖q-R b s (U s s (J w))‖) hu.symm
      _ = ‖R b s (U s s (J w))-U s s (J w)‖ := norm_sub_rev _ _
      _ ≤ Real.sqrt (B/(4*b)) := hi
  have he := smoothing_window_bound ε hε h hne hh m g k b hb s T t ht w
  have hn := norm_sub_le_norm_sub_add_norm_sub
    (D a ha s t (J w)) (R b t (U s t (J w))) (U s t (J w))
  have hc := mul_le_mul_of_nonneg_left ht hC
  change ‖D a ha s t (J w)-R b t (U s t (J w))‖ ≤
    ‖J w-R b s (U s s (J w))‖+C*|t-s| at hr
  change _ ≤ 2*Real.sqrt (B/(4*b))+C*T
  linarith only [hr,hi',he,hn,hc]

#print axioms flow_energy_window
#print axioms smoothed_hamiltonian_error
#print axioms smoothed_equation
#print axioms residual_window_bound
#print axioms smoothing_window_bound
#print axioms two_scale_error
end
end UnifiedTheory.Audit.KFCausalClockFloorYosidaErrorRate
