/- Finite-window physical error bound for the actual full flow and the
full Hamiltonian frozen at the window start. This does not identify the
frozen-to-growing limit or establish long-time scattering/clock recovery. -/
import UnifiedTheory.Audit.KFCausalClockFloorFrozenComparison

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFrozenErrorBound
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorAveragedRegularity (staticMap growingMap)
open KFCausalClockFloorAveragedFormFlow (formFlow formFlow_initial)
open KFCausalClockFloorFastTimeEnergy (physicalTime physicalTime_continuous exp_neg_physicalTime)
open KFCausalClockFloorRescaledEnergy (scaledEnergy scaled_split scaled_antitone staticLoss staticEnergy)
open KFCausalClockFloorFrozenComparison

private theorem split_value (e a b u : ℝ) (he : e=u⁻¹) : e*a+b=b+a/u := by rw [he]; ring

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "A" => staticMap ε hε h hne hb m g k
local notation "B" => growingMap ε hε h hne hb m g k
local notation "a" => actual ε hε h hne hb m g k
local notation "b" => frozen ε hε h hne hb m g k
local notation "q" => KFCausalClockFloorFrozenFastEvolution.energy ε hε h hne hb m g k
local notation "d" => discrepancy ε hε h hne hb m g k
local notation "slopeAt" => slope ε hε h hne hb m g k

theorem actual_energy_identity (U u : ℝ) (hu : 0 < u) (v : V) :
    scaledEnergy ε hε h hne hb m g k (physicalTime U) (physicalTime u) v=q u (a U u v) :=
  (scaled_split ε hε h hne hb m g k (physicalTime U) (physicalTime u) v).trans
    (split_value (Real.exp (-2*physicalTime u)) (‖A (a U u v)‖^2) (‖B (a U u v)‖^2) u (exp_neg_physicalTime u hu))

theorem actual_energy_bound (U u : ℝ) (hU : 0 < U) (hu : U ≤ u) (v : V) :
    q u (a U u v) ≤ q U v := by
  have ht : physicalTime U ≤ physicalTime u :=
    div_le_div_of_nonneg_right (Real.log_le_log hU hu) (by norm_num)
  have he := scaled_antitone ε hε h hne hb m g k (physicalTime U) v ht
  have hi : q U (a U U v)=q U v :=
    congrArg (q U) (formFlow_initial ε hε h hne hb m g k (physicalTime U) v)
  exact (actual_energy_identity ε hε h hne hb m g k U u (hU.trans_le hu) v).symm.le.trans
    (he.trans ((actual_energy_identity ε hε h hne hb m g k U U hU v).trans hi).le)

theorem actual_static_bound (U u : ℝ) (hU : 0 < U) (hu : U ≤ u) (v : V) :
    ‖A (a U u v)‖^2 ≤ u*q U v := by
  have he := actual_energy_bound ε hε h hne hb m g k U u hU hu v
  change ‖B (a U u v)‖^2+‖A (a U u v)‖^2/u ≤ q U v at he
  have hs : ‖A (a U u v)‖^2/u ≤ q U v := by linarith only [he,sq_nonneg ‖B (a U u v)‖]
  exact ((div_le_iff₀ (hU.trans_le hu)).mp hs).trans_eq (mul_comm _ _)

theorem discrepancy_slope_bound (U u : ℝ) (hU : 0 < U) (hu : U ≤ u) (v : V) :
    |slopeAt U u v| ≤ q U v*(u-U)/(|h| *U) := by
  have hE : 0 ≤ q U v := add_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hU.le)
  exact KFCausalSplitFormComparison.slope_bound h U u (q U v) hU hu hE _ _
    (actual_static_bound ε hε h hne hb m g k U u hU hu v)
    (KFCausalClockFloorFrozenFastEvolution.static_energy_bound ε hε h hne hb m g k U (u-U) hU v)

theorem discrepancy_continuous (U : ℝ) (v : V) :
    ContinuousOn (fun u => d U u v) (Set.Ioi 0) := by
  have ha := (KFCausalClockFloorStrongFormEvolution.formFlow_continuous ε hε h hne hb m g k
    (physicalTime U) v).comp_continuousOn physicalTime_continuous
  have hb' := (frozen_continuous ε hε h hne hb m g k U v).continuousOn (s := Set.Ioi 0)
  exact ((J).continuous.comp_continuousOn ha |>.sub ((J).continuous.comp_continuousOn hb')).norm.pow 2

theorem finite_window_bound (U T : ℝ) (hU : 0 < U) (hT : 0 ≤ T) (v : V) :
    d U (U+T) v ≤ q U v*T^2/(2*|h| *U) := by
  have hc := (discrepancy_continuous ε hε h hne hb m g k U v).mono
    (show Set.Icc U (U+T) ⊆ Set.Ioi 0 from fun _ hu => hU.trans_le hu.1)
  have he := KFCausalSplitFormComparison.quadratic_bound (fun u => d U u v) (fun u => slopeAt U u v)
    U T (q U v/(|h| *U)) hT hc (discrepancy_initial ε hε h hne hb m g k U v)
    (fun u hu => discrepancy_derivative ε hε h hne hb m g k U u hU (hU.trans hu.1) v)
    (fun u hu => (le_abs_self _).trans
      ((discrepancy_slope_bound ε hε h hne hb m g k U u hU hu.1.le v).trans_eq (by ring)))
  exact he.trans_eq (by ring)

theorem late_window_error (T : ℝ) (hT : 0 ≤ T) (v : V) :
    Tendsto (fun U => d U (U+T) v) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) _
    (tendsto_id.const_div_atTop (q 1 v*T^2/(2*|h|)))
  filter_upwards [eventually_ge_atTop (1:ℝ)] with U hU
  have hp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hq : q U v ≤ q 1 v := by
    change ‖B v‖^2+‖A v‖^2/U ≤ ‖B v‖^2+‖A v‖^2/1
    exact add_le_add le_rfl (div_le_div_of_nonneg_left (sq_nonneg _) zero_lt_one hU)
  exact (finite_window_bound ε hε h hne hb m g k U T hp hT v).trans
    ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq (sq_nonneg T))
      (by positivity : 0 ≤ 2*|h| *U)).trans_eq (by simp only [id_eq]; ring))

#print axioms actual_energy_identity
#print axioms actual_energy_bound
#print axioms actual_static_bound
#print axioms discrepancy_slope_bound
#print axioms discrepancy_continuous
#print axioms finite_window_bound
#print axioms late_window_error
end
end UnifiedTheory.Audit.KFCausalClockFloorFrozenErrorBound
