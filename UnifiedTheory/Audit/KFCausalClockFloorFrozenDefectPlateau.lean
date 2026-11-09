/- Any nonzero asymptotic clock defect persists under late frozen full
flows on growing fast-time windows. This is a necessary condition for
failure of recovery, not a proof that failure or recovery occurs. -/
import UnifiedTheory.Audit.KFCausalClockFloorMovingFreeze
import UnifiedTheory.Audit.KFCausalClockFloorResidualDefect

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFrozenDefectPlateau
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorFastTimeEnergy (physicalTime physicalTime_tendsto)
open KFCausalClockFloorDefectOperator (defectOperator defectOperator_norm_le)
open KFCausalClockFloorResidualDefect (residual residual_bounds norm_limit recovery_iff)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "D" => defectOperator ε hε
local notation "E" => KFCausalClockFloorAveragedEvolution.evolution ε hε h hne hb m g k
local notation "P" => KFCausalClockFloorMovingFreeze.actual ε hε h hne hb m g k
local notation "Q" => KFCausalClockFloorMovingFreeze.frozen ε hε h hne hb m g k
local notation "rho" => residual ε hε h hne hb m g k

theorem actual_window_residual (a : ℝ) (f : Hilbert) (ell : ℝ → ℝ)
    (hpos : ∀ᶠ U in atTop, 0 ≤ ell U) :
    TendstoUniformlyOn (fun U r => ‖D (P a U (r*ell U) f)‖)
      (fun _ => rho (physicalTime a) f) atTop (Set.Icc 0 1) := by
  have hs := (norm_limit ε hε h hne hb m g k (physicalTime a) f).comp physicalTime_tendsto
  rw [Metric.tendstoUniformlyOn_iff]
  intro eta heta
  filter_upwards [eventually_gt_atTop (0:ℝ),hpos,
    hs.eventually (gt_mem_nhds (show rho (physicalTime a) f < rho (physicalTime a) f+eta by linarith))]
    with U hU hp hsU
  intro r hr
  have ht : physicalTime U ≤ physicalTime (U+r*ell U) :=
    div_le_div_of_nonneg_right (Real.log_le_log hU (by nlinarith [hr.1])) (by norm_num)
  have hhi := KFCausalClockFloorDefectMonotonicity.evolution_defect_antitone
    ε hε h hne hb m g k (physicalTime a) f ht
  have hlo := (residual_bounds ε hε h hne hb m g k (physicalTime a)
    (physicalTime (U+r*ell U)) f).2
  change ‖D (E (physicalTime a) (physicalTime U) f)‖ < rho (physicalTime a) f+eta at hsU
  change dist (rho (physicalTime a) f) (‖D (E (physicalTime a) (physicalTime (U+r*ell U)) f)‖) < eta
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem defect_norm_difference (x y : Hilbert) : |‖D x‖-‖D y‖| ≤ ‖x-y‖ :=
  (abs_norm_sub_norm_le _ _).trans (by rw [← map_sub]; exact defectOperator_norm_le ε hε _)

theorem frozen_window_residual (a : ℝ) (ha : 0 < a) (f : Hilbert) (ell : ℝ → ℝ)
    (hpos : ∀ᶠ U in atTop, 0 ≤ ell U)
    (hsmall : Tendsto (fun U => ell U^2/U) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun U r => ‖D (Q a U (r*ell U) f)‖)
      (fun _ => rho (physicalTime a) f) atTop (Set.Icc 0 1) := by
  have hp := actual_window_residual ε hε h hne hb m g k a f ell hpos
  have he := KFCausalClockFloorMovingFreeze.window_error ε hε h hne hb m g k a ha f ell hpos hsmall
  rw [Metric.tendstoUniformlyOn_iff] at hp he ⊢
  intro eta heta
  filter_upwards [hp (eta/2) (by positivity),he (eta/2) (by positivity)] with U hP hE
  intro r hr
  have hdiff := defect_norm_difference ε hε (P a U (r*ell U) f) (Q a U (r*ell U) f)
  have hd := hE r hr
  rw [dist_zero_left] at hd
  have hn := (abs_le.mp hdiff)
  have ha' := hP r hr
  rw [Real.dist_eq] at ha' ⊢
  have hab := abs_lt.mp ha'
  exact abs_lt.mpr ⟨by linarith [hn.1],by linarith [hn.2]⟩

theorem frozen_window_drop (a : ℝ) (ha : 0 < a) (f : Hilbert) (ell : ℝ → ℝ)
    (hpos : ∀ᶠ U in atTop, 0 ≤ ell U)
    (hsmall : Tendsto (fun U => ell U^2/U) atTop (𝓝 0)) :
    TendstoUniformlyOn
      (fun U r => ‖D (E (physicalTime a) (physicalTime U) f)‖-‖D (Q a U (r*ell U) f)‖)
      (fun _ => 0) atTop (Set.Icc 0 1) := by
  have hs := actual_window_residual ε hε h hne hb m g k a f (fun _ => 0)
    (Eventually.of_forall (fun _ => le_rfl))
  simp only [KFCausalClockFloorMovingFreeze.actual,mul_zero,add_zero] at hs
  have hf := frozen_window_residual ε hε h hne hb m g k a ha f ell hpos hsmall
  have hd := hs.sub hf
  change TendstoUniformlyOn
    (fun U r => ‖D (E (physicalTime a) (physicalTime U) f)‖-‖D (Q a U (r*ell U) f)‖)
    (fun _ => rho (physicalTime a) f-rho (physicalTime a) f) atTop (Set.Icc 0 1) at hd
  simpa only [sub_self] using hd

theorem failure_plateau (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hfail : ¬ Tendsto (fun t => ‖D (E (physicalTime a) t f)‖) atTop (𝓝 0))
    (ell : ℝ → ℝ) (hpos : ∀ᶠ U in atTop, 0 ≤ ell U)
    (hsmall : Tendsto (fun U => ell U^2/U) atTop (𝓝 0)) :
    ∃ rho0 : ℝ, 0 < rho0 ∧
      Tendsto (fun U => ‖D (E (physicalTime a) (physicalTime U) f)‖) atTop (𝓝 rho0) ∧
      TendstoUniformlyOn (fun U r => ‖D (Q a U (r*ell U) f)‖)
        (fun _ => rho0) atTop (Set.Icc 0 1) := by
  refine ⟨rho (physicalTime a) f,?_,
    (norm_limit ε hε h hne hb m g k (physicalTime a) f).comp physicalTime_tendsto,
    frozen_window_residual ε hε h hne hb m g k a ha f ell hpos hsmall⟩
  exact lt_of_le_of_ne (residual_bounds ε hε h hne hb m g k (physicalTime a) 0 f).1
    (fun hz => hfail ((recovery_iff ε hε h hne hb m g k (physicalTime a) f).mpr hz.symm))

#print axioms actual_window_residual
#print axioms defect_norm_difference
#print axioms frozen_window_residual
#print axioms frozen_window_drop
#print axioms failure_plateau
end
end UnifiedTheory.Audit.KFCausalClockFloorFrozenDefectPlateau
