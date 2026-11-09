/- Full moving-state freezing controlled by the actual energy lost on
the interval. No momentum domain or bound on a discarded factor is used. -/
import UnifiedTheory.Audit.KFCausalLossSensitiveComparison
import UnifiedTheory.Audit.KFCausalClockFloorMovingDissipation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorLossSensitiveFreeze
noncomputable section
open Filter
open scoped Topology
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorFastTimeEnergy (physicalTime fastEnergy fastLoss)
open KFCausalClockFloorFrozenComparison (actual discrepancy slope)
open KFCausalClockFloorFrozenErrorBound (actual_energy_identity)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "aState" => actual ε hε h hne hb m g k
local notation "q" => KFCausalClockFloorFrozenFastEvolution.energy ε hε h hne hb m g k
local notation "d" => discrepancy ε hε h hne hb m g k
local notation "S" => slope ε hε h hne hb m g k
local notation "P" => KFCausalClockFloorMovingFreeze.actual ε hε h hne hb m g k
local notation "Q" => KFCausalClockFloorMovingFreeze.frozen ε hε h hne hb m g k

def trace (a u : ℝ) (v : V) : ℝ := fastEnergy ε hε h hne hb m g k (physicalTime a) u v
local notation "e" => trace ε hε h hne hb m g k

theorem trace_identity (a u : ℝ) (hu : 0 < u) (v : V) : e a u v=q u (aState a u v) :=
  actual_energy_identity ε hε h hne hb m g k a u hu v

theorem trace_initial (a : ℝ) (ha : 0 < a) (v : V) : e a a v=q a v := by
  rw [trace_identity ε hε h hne hb m g k a a ha]
  exact congrArg (q a) (KFCausalClockFloorAveragedFormFlow.formFlow_initial ε hε h hne hb m g k (physicalTime a) v)

theorem trace_restart (a U u : ℝ) (hu : 0 < u) (v : V) :
    e U u (aState a U v)=e a u v := by
  rw [trace_identity ε hε h hne hb m g k U u hu,trace_identity ε hε h hne hb m g k a u hu]
  exact congrArg (q u) (KFCausalClockFloorAveragedFormFlow.formFlow_compose ε hε h hne hb m g k
    (physicalTime a) (physicalTime U) (physicalTime u) v)

theorem trace_antitone (a : ℝ) (v : V) : AntitoneOn (fun u => e a u v) (Set.Ioi 0) := by
  intro u hu z _ huz
  exact KFCausalClockFloorRescaledEnergy.scaled_antitone ε hε h hne hb m g k (physicalTime a) v
    (div_le_div_of_nonneg_right (Real.log_le_log hu huz) (by norm_num))

theorem trace_limit (a : ℝ) (v : V) : ∃ b : ℝ, Tendsto (fun u => e a u v) atTop (𝓝 b) := by
  obtain ⟨b,_,_,ht⟩ := KFCausalClockFloorFastTimeEnergy.fastEnergy_limit ε hε h hne hb m g k (physicalTime a) v
  exact ⟨b,ht⟩

theorem trace_nonnegative (a u : ℝ) (v : V) : 0 ≤ e a u v :=
  KFCausalClockFloorRescaledEnergy.scaled_nonnegative ε hε h hne hb m g k (physicalTime a) (physicalTime u) v

theorem finite_window_bound (U L eta : ℝ) (hU : 0 < U) (hL : 0 ≤ L) (he : 0 < eta) (v : V) :
    d U (U+L) v ≤ L/(2*|h| *eta)*(e U U v-e U (U+L) v)+eta*q U v*L^2/(2*|h| *U) := by
  have hd := KFCausalLossSensitiveComparison.energy_drop_bound (fun u => d U u v) (fun u => e U u v)
    (fun u => S U u v) (fun u => fastLoss ε hε h hne hb m g k (physicalTime U) u v)
    U L (L/(2*|h| *eta)) (eta*q U v*L/(2*|h| *U)) hL
    ((KFCausalClockFloorFrozenErrorBound.discrepancy_continuous ε hε h hne hb m g k U v).mono
      (fun _ hu => hU.trans_le hu.1))
    (fun u hu => (KFCausalClockFloorFastTimeEnergy.fastEnergy_derivative ε hε h hne hb m g k
      (physicalTime U) u (hU.trans_le hu.1) v).continuousAt.continuousWithinAt)
    (KFCausalClockFloorFrozenComparison.discrepancy_initial ε hε h hne hb m g k U v)
    (fun u hu => KFCausalClockFloorFrozenComparison.discrepancy_derivative ε hε h hne hb m g k
      U u hU (hU.trans hu.1) v)
    (fun u hu => KFCausalClockFloorFastTimeEnergy.fastEnergy_derivative ε hε h hne hb m g k
      (physicalTime U) u (hU.trans hu.1) v) ?_
  · exact hd.trans_eq (by ring)
  · intro u hu
    exact (le_abs_self _).trans (KFCausalLossSensitiveComparison.slope_bound h U u L eta (q U v)
      hU hu.1.le (by linarith only [hu.2]) he _ _
      (KFCausalClockFloorFrozenFastEvolution.static_energy_bound ε hε h hne hb m g k U (u-U) hU v))

theorem moving_window_bound (a U L eta t : ℝ) (hU : 0 < U) (ht : 0 ≤ t) (htL : t ≤ L)
    (he : 0 < eta) (v : V) :
    ‖P a U t (J v)-Q a U t (J v)‖^2 ≤
      L/(2*|h| *eta)*(e a U v-e a (U+L) v)+eta*e a U v*L^2/(2*|h| *U) := by
  have hL : 0 ≤ L := ht.trans htL
  rw [KFCausalClockFloorMovingFreeze.form_error_identity]
  have hi := finite_window_bound ε hε h hne hb m g k U t eta hU ht he (aState a U v)
  rw [trace_restart ε hε h hne hb m g k a U U hU,
    trace_restart ε hε h hne hb m g k a U (U+t) (by linarith),
    ← trace_identity ε hε h hne hb m g k a U hU] at hi
  have hm := trace_antitone ε hε h hne hb m g k a v
  have hdrop : e a U v-e a (U+t) v ≤ e a U v-e a (U+L) v := by
    have hm' := hm (show 0 < U+t by linarith) (show 0 < U+L by linarith)
      (show U+t ≤ U+L by linarith)
    linarith only [hm']
  have hn : 0 ≤ e a U v-e a (U+L) v := sub_nonneg.mpr
    (hm hU (show 0 < U+L by linarith) (show U ≤ U+L by linarith))
  apply hi.trans
  apply add_le_add
  · exact (mul_le_mul_of_nonneg_left hdrop (by positivity)).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right htL (by positivity)) hn)
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by nlinarith : t^2 ≤ L^2) (mul_nonneg he.le (trace_nonnegative ε hε h hne hb m g k a U v))) (by positivity)

#print axioms trace_identity
#print axioms trace_initial
#print axioms trace_restart
#print axioms trace_antitone
#print axioms trace_limit
#print axioms trace_nonnegative
#print axioms finite_window_bound
#print axioms moving_window_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorLossSensitiveFreeze
