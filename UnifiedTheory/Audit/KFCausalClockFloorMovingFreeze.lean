/- The full dynamics can be frozen along its own moving states on
windows of length ell(U) with ell(U)^2/U tending to zero. This retains
the full frozen Hamiltonian and does not replace it by the growing one. -/
import UnifiedTheory.Audit.KFCausalClockFloorLateTimeAutonomy
import UnifiedTheory.Audit.KFCausalGrowingTimeWindows

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorMovingFreeze
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorFastTimeEnergy (physicalTime)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorAveragedEvolution (evolution evolution_embedding evolution_compose)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "E" => evolution ε hε h hne hb m g k
local notation "F" => KFCausalClockFloorFrozenFastEvolution.physical ε hε h hne hb m g k
local notation "q" => KFCausalClockFloorFrozenFastEvolution.energy ε hε h hne hb m g k
local notation "aState" => KFCausalClockFloorFrozenComparison.actual ε hε h hne hb m g k
local notation "d" => KFCausalClockFloorFrozenComparison.discrepancy ε hε h hne hb m g k

def actual (a U t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert := E (physicalTime a) (physicalTime (U+t))
def frozen (a U t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  (E (physicalTime a) (physicalTime U)).trans (F U t)
local notation "P" => actual ε hε h hne hb m g k
local notation "Q" => frozen ε hε h hne hb m g k

theorem form_error_identity (a U t : ℝ) (v : V) :
    ‖P a U t (J v)-Q a U t (J v)‖^2=d U (U+t) (aState a U v) := by
  have hc := congrArg (fun T : Hilbert →L[ℂ] Hilbert => T (J v))
    (evolution_compose ε hε h hne hb m g k (physicalTime a) (physicalTime U) (physicalTime (U+t)))
  change E (physicalTime U) (physicalTime (U+t)) (E (physicalTime a) (physicalTime U) (J v))=
    E (physicalTime a) (physicalTime (U+t)) (J v) at hc
  change ‖E (physicalTime a) (physicalTime (U+t)) (J v)-F U t (E (physicalTime a) (physicalTime U) (J v))‖^2=_
  rw [← hc,evolution_embedding]
  exact KFCausalClockFloorLateTimeAutonomy.form_error_identity ε hε h hne hb m g k U t (aState a U v)

theorem form_error_square_bound (a U t : ℝ) (ha : 0 < a) (hU : a ≤ U) (ht : 0 ≤ t) (v : V) :
    ‖P a U t (J v)-Q a U t (J v)‖^2 ≤ q a v*t^2/(2*|h| *U) := by
  have hu : 0 < U := ha.trans_le hU
  rw [form_error_identity]
  exact (KFCausalClockFloorFrozenErrorBound.finite_window_bound ε hε h hne hb m g k
    U t (ha.trans_le hU) ht (aState a U v)).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (KFCausalClockFloorFrozenErrorBound.actual_energy_bound
        ε hε h hne hb m g k a U ha hU v) (sq_nonneg t)) (by positivity))

theorem form_window_error (a : ℝ) (ha : 0 < a) (v : V) (ell : ℝ → ℝ)
    (hpos : ∀ᶠ U in atTop, 0 ≤ ell U)
    (hsmall : Tendsto (fun U => ell U^2/U) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun U r => P a U (r*ell U) (J v)-Q a U (r*ell U) (J v))
      (fun _ => 0) atTop (Set.Icc 0 1) := by
  apply KFCausalDenseUnitaryUniformComparison.uniform_zero_of_square_bound
    (fun U r => P a U (r*ell U) (J v)-Q a U (r*ell U) (J v))
    (fun U => (q a v/(2*|h|))*(ell U^2/U)) atTop (Set.Icc 0 1) _
    (by simpa only [mul_zero] using hsmall.const_mul (q a v/(2*|h|)))
  filter_upwards [eventually_ge_atTop a,hpos] with U hU hp
  have hu : 0 < U := ha.trans_le hU
  intro r hr
  have ht : 0 ≤ r*ell U := mul_nonneg hr.1 hp
  have hle : r*ell U ≤ ell U := by nlinarith [hr.2]
  have hs : (r*ell U)^2 ≤ ell U^2 := by nlinarith
  have hq : 0 ≤ q a v := add_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) ha.le)
  exact (form_error_square_bound ε hε h hne hb m g k a U (r*ell U) ha hU ht v).trans
    ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hq)
      (by positivity : 0 ≤ 2*|h| *U)).trans_eq (by ring))

theorem window_error (a : ℝ) (ha : 0 < a) (f : Hilbert) (ell : ℝ → ℝ)
    (hpos : ∀ᶠ U in atTop, 0 ≤ ell U)
    (hsmall : Tendsto (fun U => ell U^2/U) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun U r => P a U (r*ell U) f-Q a U (r*ell U) f)
      (fun _ => 0) atTop (Set.Icc 0 1) :=
  KFCausalDenseUnitaryUniformComparison.uniform_error_of_dense J
    (KFCausalClockFloorAveragedFormGeometry.embedding_dense ε hε h hne hb m g k 0)
    (fun U r => P a U (r*ell U)) (fun U r => Q a U (r*ell U)) atTop (Set.Icc 0 1)
    (fun v => form_window_error ε hε h hne hb m g k a ha v ell hpos hsmall) f

theorem fixed_window_error (a : ℝ) (ha : 0 < a) (f : Hilbert) (L : ℝ) (hL : 0 ≤ L) :
    TendstoUniformlyOn (fun U r => P a U (r*L) f-Q a U (r*L) f)
      (fun _ => 0) atTop (Set.Icc 0 1) :=
  window_error ε hε h hne hb m g k a ha f (fun _ => L) (Eventually.of_forall (fun _ => hL))
    (tendsto_id.const_div_atTop (L^2))

theorem quarter_window_error (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    TendstoUniformlyOn
      (fun U r => P a U (r*KFCausalGrowingTimeWindows.quarterWindow U) f-
        Q a U (r*KFCausalGrowingTimeWindows.quarterWindow U) f)
      (fun _ => 0) atTop (Set.Icc 0 1) :=
  window_error ε hε h hne hb m g k a ha f KFCausalGrowingTimeWindows.quarterWindow
    (Eventually.of_forall KFCausalGrowingTimeWindows.quarterWindow_nonneg)
    KFCausalGrowingTimeWindows.quarterWindow_square_ratio

#print axioms form_error_identity
#print axioms form_error_square_bound
#print axioms form_window_error
#print axioms window_error
#print axioms fixed_window_error
#print axioms quarter_window_error
end
end UnifiedTheory.Audit.KFCausalClockFloorMovingFreeze
