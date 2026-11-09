/- The actual positive weighted-clock lower bound persists uniformly
on late full frozen windows whenever the proved physical error vanishes. -/
import UnifiedTheory.Audit.KFCausalClockFloorPersistentWeightedClock
import UnifiedTheory.Audit.KFCausalClockFloorSelectedSpectrum

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSelectedWeightedClock
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorWeightedClockControl (weighted)
open KFCausalClockFloorFastTimeEnergy (physicalTime physicalTime_tendsto)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "H" => weighted ε hε
local notation "P" => KFCausalClockFloorMovingFreeze.actual ε hε h hne hb m g k
local notation "Q" => KFCausalClockFloorMovingFreeze.frozen ε hε h hne hb m g k
local notation "rho" => KFCausalClockFloorResidualDefect.residual ε hε h hne hb m g k
local notation "F" => KFCausalClockFloorFrozenFastEvolution.evolution ε hε h hne hb m g k
local notation "aState" => KFCausalClockFloorFrozenComparison.actual ε hε h hne hb m g k

theorem frozen_embedding (a U t : ℝ) (v : V) :
    J (F U t (aState a U v))=Q a U t (J v) := by
  rw [KFCausalClockFloorFrozenFastEvolution.evolution_embedding]
  change _=KFCausalClockFloorFrozenFastEvolution.physical ε hε h hne hb m g k U t
    (KFCausalClockFloorAveragedEvolution.evolution ε hε h hne hb m g k (physicalTime a) (physicalTime U) (J v))
  rw [KFCausalClockFloorAveragedEvolution.evolution_embedding]
  rfl

theorem sequence_lower_bound (a : ℝ) (f : Hilbert) (U L : ℕ → ℝ)
    (hpos : ∀ n, 0 < U n ∧ 0 ≤ L n) (hU : Tendsto U atTop atTop)
    (herr : TendstoUniformlyOn (fun n r => P a (U n) (r*L n) f-Q a (U n) (r*L n) f)
      (fun _ => 0) atTop (Set.Icc 0 1))
    (hp : 0 < rho (physicalTime a) f) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop, ∀ r ∈ Set.Icc (0:ℝ) 1,
      η ≤ ‖H (Q a (U n) (r*L n) f)‖ := by
  obtain ⟨η,hη,hlower⟩ := KFCausalClockFloorPersistentWeightedClock.persistent_weight
    ε hε h hne hb m g k (physicalTime a) f hp
  refine ⟨η/2,by positivity,?_⟩
  rw [Metric.tendstoUniformlyOn_iff] at herr
  filter_upwards [herr (η/2/(‖H‖+1)) (by positivity),
    (physicalTime_tendsto.comp hU).eventually (eventually_ge_atTop (physicalTime a))] with n hn ht
  intro r hr
  have htt : physicalTime (U n) ≤ physicalTime (U n+r*L n) :=
    div_le_div_of_nonneg_right (Real.log_le_log (hpos n).1
      (le_add_of_nonneg_right (mul_nonneg hr.1 (hpos n).2))) (by norm_num)
  have hl := hlower (physicalTime (U n+r*L n)) (ht.trans htt)
  change η ≤ ‖H (P a (U n) (r*L n) f)‖ at hl
  have he := hn r hr
  rw [dist_zero_left] at he
  have he' := (lt_div_iff₀ (by positivity : 0 < ‖H‖+1)).mp he
  have hd := norm_sub_norm_le (H (P a (U n) (r*L n) f)) (H (Q a (U n) (r*L n) f))
  rw [← map_sub] at hd
  have hc := (H).le_opNorm (P a (U n) (r*L n) f-Q a (U n) (r*L n) f)
  nlinarith only [hl,he',hd,hc,norm_nonneg (P a (U n) (r*L n) f-Q a (U n) (r*L n) f)]

#print axioms frozen_embedding
#print axioms sequence_lower_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorSelectedWeightedClock
