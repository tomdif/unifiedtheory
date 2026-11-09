/- Total ordered clock dissipation vanishes on derived reachable-state
frozen windows with L^2/U tending to infinity and L/U tending to zero.
This is a selected sequence, not a uniform-in-start-time assertion. -/
import UnifiedTheory.Audit.KFCausalClockFloorSelectedFreeze
import UnifiedTheory.Audit.KFCausalClockFloorFrozenDefectPlateau

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSelectedDissipation
noncomputable section
open Filter MeasureTheory
open scoped Topology
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorFastTimeEnergy (physicalTime physicalTime_tendsto)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "aState" => KFCausalClockFloorFrozenComparison.actual ε hε h hne hb m g k
local notation "P" => KFCausalClockFloorMovingFreeze.actual ε hε h hne hb m g k
local notation "Q" => KFCausalClockFloorMovingFreeze.frozen ε hε h hne hb m g k
local notation "E" => KFCausalClockFloorAveragedEvolution.evolution ε hε h hne hb m g k
local notation "F" => KFCausalClockFloorFrozenFastEvolution.evolution ε hε h hne hb m g k
local notation "X" => KFCausalClockFloorFrozenClockLoss.expectation ε hε
local notation "D" => KFCausalClockFloorDefectOperator.defectOperator ε hε
local notation "det" => KFCausalClockFloorMovingDissipation.detector ε hε h hne hb m g k
local notation "rho" => KFCausalClockFloorResidualDefect.residual ε hε h hne hb m g k

theorem sequence_residual (a : ℝ) (v : V) (U L : ℕ → ℝ)
    (hpos : ∀ n, 0 < U n ∧ 0 ≤ L n) (hU : Tendsto U atTop atTop)
    (herr : TendstoUniformlyOn (fun n r => P a (U n) (r*L n) (J v)-Q a (U n) (r*L n) (J v))
      (fun _ => 0) atTop (Set.Icc 0 1)) :
    TendstoUniformlyOn (fun n r => ‖D (Q a (U n) (r*L n) (J v))‖)
      (fun _ => rho (physicalTime a) (J v)) atTop (Set.Icc 0 1) := by
  have hs := (KFCausalClockFloorResidualDefect.norm_limit ε hε h hne hb m g k (physicalTime a) (J v)).comp
    (physicalTime_tendsto.comp hU)
  rw [Metric.tendstoUniformlyOn_iff] at herr ⊢
  intro eta heta
  filter_upwards [herr (eta/2) (by positivity),hs.eventually
    (gt_mem_nhds (show rho (physicalTime a) (J v) < rho (physicalTime a) (J v)+eta/2 by linarith))]
    with n hn hsN
  intro r hr
  have ht : physicalTime (U n) ≤ physicalTime (U n+r*L n) :=
    div_le_div_of_nonneg_right (Real.log_le_log (hpos n).1
      (le_add_of_nonneg_right (mul_nonneg hr.1 (hpos n).2))) (by norm_num)
  have hhi := KFCausalClockFloorDefectMonotonicity.evolution_defect_antitone ε hε h hne hb m g k
    (physicalTime a) (J v) ht
  have hlo := (KFCausalClockFloorResidualDefect.residual_bounds ε hε h hne hb m g k
    (physicalTime a) (physicalTime (U n+r*L n)) (J v)).2
  have he := hn r hr
  rw [dist_zero_left] at he
  have hab := abs_le.mp (KFCausalClockFloorFrozenDefectPlateau.defect_norm_difference ε hε
    (P a (U n) (r*L n) (J v)) (Q a (U n) (r*L n) (J v)))
  change ‖D (E (physicalTime a) (physicalTime (U n)) (J v))‖ < rho (physicalTime a) (J v)+eta/2 at hsN
  change ‖D (P a (U n) (r*L n) (J v))‖ ≤ ‖D (E (physicalTime a) (physicalTime (U n)) (J v))‖ at hhi
  change rho (physicalTime a) (J v) ≤ ‖D (P a (U n) (r*L n) (J v))‖ at hlo
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [hab.2],by linarith [hab.1]⟩

theorem sequence_clock_drop (a : ℝ) (v : V) (U L : ℕ → ℝ)
    (hL : ∀ n, 0 ≤ L n) (hU : Tendsto U atTop atTop)
    (herr : Tendsto (fun n => P a (U n) (L n) (J v)-Q a (U n) (L n) (J v)) atTop (𝓝 0)) :
    Tendsto (fun n => X (E (physicalTime a) (physicalTime (U n)) (J v))-
      X (Q a (U n) (L n) (J v))) atTop (𝓝 0) := by
  obtain ⟨b,hb'⟩ := KFCausalClockFloorMovingDissipation.actual_expectation_limit ε hε h hne hb m g k
    (physicalTime a) v
  have hend : Tendsto (fun n => U n+L n) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right (hL n)) hU
  have hactual : Tendsto (fun n => X (E (physicalTime a) (physicalTime (U n)) (J v))-
      X (P a (U n) (L n) (J v))) atTop (𝓝 0) := by
    simpa only [sub_self] using (hb'.comp (physicalTime_tendsto.comp hU)).sub
      (hb'.comp (physicalTime_tendsto.comp hend))
  have herror : Tendsto (fun n => X (P a (U n) (L n) (J v))-X (Q a (U n) (L n) (J v)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (show Tendsto (fun n => (2*‖J v‖)*‖P a (U n) (L n) (J v)-Q a (U n) (L n) (J v)‖)
        atTop (𝓝 0) from by simpa only [norm_zero,mul_zero] using herr.norm.const_mul (2*‖J v‖))
    have hi := KFCausalMassObservableDerivative.quadratic_difference_bound D
      (KFCausalClockFloorDefectOperator.defectOperator_norm_le ε hε)
      (P a (U n) (L n) (J v)) (Q a (U n) (L n) (J v))
    simpa only [KFCausalClockFloorFrozenClockLoss.expectation,Real.norm_eq_abs,
      (P a (U n) (L n)).norm_map,(Q a (U n) (L n)).norm_map,← two_mul] using hi
  simpa only [sub_add_sub_cancel,add_zero] using hactual.add herror

theorem sequence_total_limit (a : ℝ) (v : V) (U L : ℕ → ℝ)
    (hpos : ∀ n, 0 < U n ∧ 0 ≤ L n) (hU : Tendsto U atTop atTop)
    (herr : Tendsto (fun n => P a (U n) (L n) (J v)-Q a (U n) (L n) (J v)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t in 0..L n, det (F (U n) t (aState a (U n) v))) atTop (𝓝 0) := by
  have hd := sequence_clock_drop ε hε h hne hb m g k a v U L (fun n => (hpos n).2) hU herr
  have hint (n : ℕ) : (∫ t in 0..L n, det (F (U n) t (aState a (U n) v))) =
      ∫ t in 0..L n, KFCausalClockFloorFrozenClockLoss.dissipation ε hε h hne hb m g k
        (U n) t (aState a (U n) v) := intervalIntegral.integral_congr (fun t _ =>
    (KFCausalClockFloorMovingDissipation.dissipation_rescaling ε hε h hne hb m g k (U n) t (hpos n).1 _).symm)
  apply squeeze_zero (fun n => ?_) (fun n => ?_)
    (show Tendsto (fun n => 32*(X (E (physicalTime a) (physicalTime (U n)) (J v))-
      X (Q a (U n) (L n) (J v)))) atTop (𝓝 0) from by simpa only [mul_zero] using hd.const_mul 32)
  · rw [hint]
    exact intervalIntegral.integral_nonneg_of_forall (hpos n).2
      (fun t => KFCausalClockFloorFrozenClockLoss.dissipation_nonnegative ε hε h hne hb m g k (U n) t (hpos n).1 _)
  · rw [hint]
    have hi := KFCausalClockFloorFrozenClockLoss.dissipation_budget ε hε h hne hb m g k
      (U n) (L n) (hpos n).1 (hpos n).2 (aState a (U n) v)
    have he : J (aState a (U n) v)=E (physicalTime a) (physicalTime (U n)) (J v) :=
      (KFCausalClockFloorAveragedEvolution.evolution_embedding ε hε h hne hb m g k
        (physicalTime a) (physicalTime (U n)) v).symm
    simpa only [he,KFCausalClockFloorMovingFreeze.frozen,LinearIsometryEquiv.trans_apply] using hi

theorem exists_supercritical_windows (a : ℝ) (ha : 0 < a) (v : V) :
    ∃ U L : ℕ → ℝ, (∀ n, 0 < U n ∧ 0 < L n) ∧ Tendsto U atTop atTop ∧ Tendsto L atTop atTop ∧
      Tendsto (fun n => (L n)^2/U n) atTop atTop ∧
      Tendsto (fun n => L n/U n) atTop (𝓝 0) ∧
      TendstoUniformlyOn (fun n r => P a (U n) (r*L n) (J v)-Q a (U n) (r*L n) (J v))
        (fun _ => 0) atTop (Set.Icc 0 1) ∧
      TendstoUniformlyOn (fun n r => ‖D (Q a (U n) (r*L n) (J v))‖)
        (fun _ => rho (physicalTime a) (J v)) atTop (Set.Icc 0 1) ∧
      Tendsto (fun n => ∫ t in 0..L n, det (F (U n) t (aState a (U n) v))) atTop (𝓝 0) := by
  apply Exists.imp _ (KFCausalClockFloorSelectedFreeze.exists_windows ε hε h hne hb m g k a ha v)
  intro U hx
  apply Exists.imp _ hx
  intro L hp
  have hpos := hp.1
  have hU := hp.2.1
  have hLength := hp.2.2.1
  have hratio := hp.2.2.2.1
  have hsmall := hp.2.2.2.2.1
  have herr := hp.2.2.2.2.2
  refine ⟨hpos,hU,hLength,hratio,hsmall,herr,
    sequence_residual ε hε h hne hb m g k a v U L (fun n => ⟨(hpos n).1,(hpos n).2.le⟩) hU herr,?_⟩
  apply sequence_total_limit ε hε h hne hb m g k a v U L
    (fun n => ⟨(hpos n).1,(hpos n).2.le⟩) hU
  simpa only [one_mul] using herr.tendsto_at (show (1:ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one,le_rfl⟩)

#print axioms sequence_residual
#print axioms sequence_clock_drop
#print axioms sequence_total_limit
#print axioms exists_supercritical_windows
end
end UnifiedTheory.Audit.KFCausalClockFloorSelectedDissipation
