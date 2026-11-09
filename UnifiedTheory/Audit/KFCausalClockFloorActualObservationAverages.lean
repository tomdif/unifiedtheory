/- Actual and full frozen dynamics have the same limiting averages of
every fixed bounded squared-norm observation on normalized late windows. -/
import UnifiedTheory.Audit.KFCausalUniformObservationAverages
import UnifiedTheory.Audit.KFCausalClockFloorSelectedWeightedClock

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorActualObservationAverages
noncomputable section
open Filter MeasureTheory
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorFastTimeEnergy (physicalTime)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "E" => KFCausalClockFloorAveragedEvolution.evolution ε hε h hne hb m g k
local notation "P" => KFCausalClockFloorMovingFreeze.actual ε hε h hne hb m g k
local notation "Q" => KFCausalClockFloorMovingFreeze.frozen ε hε h hne hb m g k
local notation "F" => KFCausalClockFloorFrozenFastEvolution.evolution ε hε h hne hb m g k
local notation "aState" => KFCausalClockFloorFrozenComparison.actual ε hε h hne hb m g k

theorem actual_continuousOn (a U L : ℝ) (hU : 0 < U) (hL : 0 ≤ L) (f : Hilbert) :
    ContinuousOn (fun r => P a U (r*L) f) (Set.Icc (0:ℝ) 1) := by
  have ht : ContinuousOn (fun r : ℝ => physicalTime (U+r*L)) (Set.Icc (0:ℝ) 1) := by
    apply ContinuousOn.div_const
    apply ((continuous_const.add (continuous_id.mul continuous_const)).continuousOn).log
    intro r hr
    exact (show 0 < U+r*L from add_pos_of_pos_of_nonneg hU (mul_nonneg hr.1 hL)).ne'
  exact (KFCausalClockFloorAveragedEvolution.evolution_strong_continuous
    ε hε h hne hb m g k (physicalTime a) f).comp_continuousOn ht

theorem frozen_continuous (a U L : ℝ) (f : Hilbert) :
    Continuous (fun r => Q a U (r*L) f) :=
  (KFCausalClockFloorFrozenEvolution.evolution_continuous ε hε h hne hb m g k
    (physicalTime U) (1/(2*h*U)) (E (physicalTime a) (physicalTime U) f)).comp
      (show Continuous (fun r : ℝ => r*L) by fun_prop)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def actualAverage (A : Hilbert →L[ℂ] K) (a U L : ℝ) (f : Hilbert) : ℝ :=
  ∫ r in (0:ℝ)..1, ‖A (P a U (r*L) f)‖^2

def frozenAverage (A : Hilbert →L[ℂ] K) (a U L : ℝ) (f : Hilbert) : ℝ :=
  ∫ r in (0:ℝ)..1, ‖A (Q a U (r*L) f)‖^2

theorem actual_rescale (A : Hilbert →L[ℂ] K) (a U L : ℝ) (hL : L ≠ 0) (f : Hilbert) :
    actualAverage ε hε h hne hb m g k A a U L f=
      (∫ t in 0..L, ‖A (P a U t f)‖^2)/L := by
  rw [actualAverage,intervalIntegral.integral_comp_mul_right (fun t => ‖A (P a U t f)‖^2) hL]
  simp only [zero_mul,one_mul,smul_eq_mul,div_eq_mul_inv]
  exact mul_comm _ _

theorem frozen_rescale (A : Hilbert →L[ℂ] K) (a U L : ℝ) (hL : L ≠ 0) (f : Hilbert) :
    frozenAverage ε hε h hne hb m g k A a U L f=
      (∫ t in 0..L, ‖A (Q a U t f)‖^2)/L := by
  rw [frozenAverage,intervalIntegral.integral_comp_mul_right (fun t => ‖A (Q a U t f)‖^2) hL]
  simp only [zero_mul,one_mul,smul_eq_mul,div_eq_mul_inv]
  exact mul_comm _ _

theorem frozen_form_average (A : Hilbert →L[ℂ] K) (a U L : ℝ) (hL : L ≠ 0) (v : V) :
    frozenAverage ε hε h hne hb m g k A a U L (J v)=
      (∫ t in 0..L, ‖A (J (F U t (aState a U v)))‖^2)/L := by
  rw [frozen_rescale ε hε h hne hb m g k A a U L hL]
  congr 1
  exact intervalIntegral.integral_congr (fun t _ => congrArg (fun f : Hilbert => ‖A f‖^2)
    (KFCausalClockFloorSelectedWeightedClock.frozen_embedding ε hε h hne hb m g k a U t v).symm)

theorem comparison_limit (A : Hilbert →L[ℂ] K) (a : ℝ) (f : Hilbert) (U L : ℕ → ℝ)
    (hpos : ∀ n, 0 < U n ∧ 0 ≤ L n)
    (herr : TendstoUniformlyOn (fun n r => P a (U n) (r*L n) f-Q a (U n) (r*L n) f)
      (fun _ => 0) atTop (Set.Icc 0 1)) :
    Tendsto (fun n => actualAverage ε hε h hne hb m g k A a (U n) (L n) f-
      frozenAverage ε hε h hne hb m g k A a (U n) (L n) f) atTop (𝓝 0) := by
  apply KFCausalUniformObservationAverages.average_difference_limit A
    (fun n r => P a (U n) (r*L n) f) (fun n r => Q a (U n) (r*L n) f) ‖f‖ (norm_nonneg f)
    (fun n r _ => (P a (U n) (r*L n)).norm_map f |>.le)
    (fun n r _ => (Q a (U n) (r*L n)).norm_map f |>.le) _ _ herr
  · intro n
    exact ((A.continuous.comp_continuousOn
      (actual_continuousOn ε hε h hne hb m g k a (U n) (L n) (hpos n).1 (hpos n).2 f)).norm.pow 2).intervalIntegrable_of_Icc zero_le_one
  · intro n
    exact (((A.continuous.comp (frozen_continuous ε hε h hne hb m g k a (U n) (L n) f)).norm).pow 2).intervalIntegrable 0 1

#print axioms actual_continuousOn
#print axioms frozen_continuous
#print axioms actual_rescale
#print axioms frozen_rescale
#print axioms frozen_form_average
#print axioms comparison_limit
end
end UnifiedTheory.Audit.KFCausalClockFloorActualObservationAverages
