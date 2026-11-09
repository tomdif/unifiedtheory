/- The actual time-dependent full dynamics approaches the growing
unitary group on every fixed bounded forward fast-time interval, for
every fixed physical Hilbert input. This is a local late-time limit,
not scattering or clock recovery. -/
import UnifiedTheory.Audit.KFCausalClockFloorFrozenGrowingLimit
import UnifiedTheory.Audit.KFCausalClockFloorFrozenErrorBound
import UnifiedTheory.Audit.KFCausalDenseUnitaryUniformComparison

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorLateTimeAutonomy
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorFastTimeEnergy (physicalTime)
open KFCausalClockFloorAveragedEvolution (evolution evolution_embedding)
open KFCausalClockFloorAveragedRegularity (staticMap growingMap)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "A" => staticMap ε hε h hne hb m g k
local notation "B" => growingMap ε hε h hne hb m g k
local notation "F" => KFCausalClockFloorFrozenFastEvolution.physical ε hε h hne hb m g k
local notation "G" => KFCausalClockFloorGrowingEvolution.evolution ε hε h hne hb m g k
local notation "q" => KFCausalClockFloorFrozenFastEvolution.energy ε hε h hne hb m g k
local notation "d" => KFCausalClockFloorFrozenComparison.discrepancy ε hε h hne hb m g k

def actual (U t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  evolution ε hε h hne hb m g k (physicalTime U) (physicalTime (U+t))
local notation "P" => actual ε hε h hne hb m g k

theorem form_error_identity (U t : ℝ) (v : V) :
    ‖P U t (J v)-F U t (J v)‖^2=d U (U+t) v := by
  have ha := evolution_embedding ε hε h hne hb m g k (physicalTime U) (physicalTime (U+t)) v
  have hf := KFCausalClockFloorFrozenFastEvolution.evolution_embedding ε hε h hne hb m g k U t v
  have he : F U t (J v)=J (KFCausalClockFloorFrozenComparison.frozen ε hε h hne hb m g k U (U+t) v) := by
    simpa only [KFCausalClockFloorFrozenComparison.frozen,add_sub_cancel_left] using hf.symm
  exact congrArg₂ (fun x y : Hilbert => ‖x-y‖^2) ha he

theorem form_error_square_bound (U L t : ℝ) (hU : 1 ≤ U) (ht : t ∈ Set.Icc 0 L) (v : V) :
    ‖P U t (J v)-F U t (J v)‖^2 ≤ (q 1 v*L^2/(2*|h|))/U := by
  have hu : 0 < U := zero_lt_one.trans_le hU
  have hq : q U v ≤ q 1 v := by
    change ‖B v‖^2+‖A v‖^2/U ≤ ‖B v‖^2+‖A v‖^2/1
    exact add_le_add le_rfl (div_le_div_of_nonneg_left (sq_nonneg _) zero_lt_one hU)
  have hn : 0 ≤ q 1 v := add_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) zero_le_one)
  have ht2 : t^2 ≤ L^2 := by nlinarith [ht.1,ht.2]
  have he := KFCausalClockFloorFrozenErrorBound.finite_window_bound ε hε h hne hb m g k U t hu ht.1 v
  exact (form_error_identity ε hε h hne hb m g k U t v).le.trans (he.trans
    ((div_le_div_of_nonneg_right (mul_le_mul hq ht2 (sq_nonneg t) hn)
      (by positivity : 0 ≤ 2*|h| *U)).trans_eq (by ring)))

theorem form_uniform_error (v : V) (L : ℝ) :
    TendstoUniformlyOn (fun U t => P U t (J v)-F U t (J v)) (fun _ => 0)
      atTop (Set.Icc 0 L) := by
  apply KFCausalDenseUnitaryUniformComparison.uniform_zero_of_square_bound
    (fun U t => P U t (J v)-F U t (J v)) (fun U => (q 1 v*L^2/(2*|h|))/U) atTop (Set.Icc 0 L)
    _ (tendsto_id.const_div_atTop (q 1 v*L^2/(2*|h|)))
  filter_upwards [eventually_ge_atTop (1:ℝ)] with U hU
  intro t ht
  exact form_error_square_bound ε hε h hne hb m g k U L t hU ht v

theorem uniform_error (f : Hilbert) (L : ℝ) :
    TendstoUniformlyOn (fun U t => P U t f-F U t f) (fun _ => 0) atTop (Set.Icc 0 L) :=
  KFCausalDenseUnitaryUniformComparison.uniform_error_of_dense J
    (KFCausalClockFloorAveragedFormGeometry.embedding_dense ε hε h hne hb m g k 0)
    P F atTop (Set.Icc 0 L) (fun v => form_uniform_error ε hε h hne hb m g k v L) f

theorem uniform_limit (f : Hilbert) (L : ℝ) (hL : 0 ≤ L) :
    TendstoUniformlyOn (fun U t => P U t f) (fun t => G t f) atTop (Set.Icc 0 L) := by
  have hf := (KFCausalClockFloorFrozenGrowingLimit.uniform_limit ε hε h hne hb m g k f L hL).mono
    (show Set.Icc 0 L ⊆ Set.Icc (-L) L from fun t ht => ⟨by linarith [ht.1],ht.2⟩)
  change TendstoUniformlyOn (fun u t => F u t f) (fun t => G t f) atTop (Set.Icc 0 L) at hf
  have he := uniform_error ε hε h hne hb m g k f L
  have hs := he.add hf
  change TendstoUniformlyOn (fun U t => (P U t f-F U t f)+F U t f)
    (fun t => (0:Hilbert)+G t f) atTop (Set.Icc 0 L) at hs
  simpa only [zero_add,sub_add_cancel] using hs

theorem strong_limit (f : Hilbert) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun U => P U t f) atTop (𝓝 (G t f)) :=
  (uniform_limit ε hε h hne hb m g k f t ht).tendsto_at ⟨ht,le_rfl⟩

#print axioms form_error_identity
#print axioms form_error_square_bound
#print axioms form_uniform_error
#print axioms uniform_error
#print axioms uniform_limit
#print axioms strong_limit
end
end UnifiedTheory.Audit.KFCausalClockFloorLateTimeAutonomy
