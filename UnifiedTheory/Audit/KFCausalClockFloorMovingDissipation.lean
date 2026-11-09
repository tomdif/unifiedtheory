/- Along reachable full-form states, the TOTAL positive ordered-output
clock dissipation of the late frozen flow tends to zero on every window
ell(U)^2/U -> 0. This does not identify the clock residual as zero. -/
import UnifiedTheory.Audit.KFCausalClockFloorFrozenClockLoss
import UnifiedTheory.Audit.KFCausalClockFloorDissipationRescaling
import UnifiedTheory.Audit.KFCausalClockFloorMovingFreeze
import UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumLimit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorMovingDissipation
noncomputable section
open Filter MeasureTheory
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput)
open KFCausalClockFloorFastTimeEnergy (physicalTime physicalTime_tendsto exp_physicalTime)
open KFCausalClockFloorFrozenClockLoss (expectation)

private theorem scaled_dissipation (U x y : ℝ) (hU : 0 < U) (he : x=U*y) :
    -x/(2*U)=-y/2 := by
  rw [he]
  field_simp

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "X" => expectation ε hε
local notation "D" => KFCausalClockFloorDefectOperator.defectOperator ε hε
local notation "E" => KFCausalClockFloorAveragedEvolution.evolution ε hε h hne hb m g k
local notation "F" => KFCausalClockFloorFrozenFastEvolution.evolution ε hε h hne hb m g k
local notation "P" => KFCausalClockFloorMovingFreeze.actual ε hε h hne hb m g k
local notation "Q" => KFCausalClockFloorMovingFreeze.frozen ε hε h hne hb m g k
local notation "aState" => KFCausalClockFloorFrozenComparison.actual ε hε h hne hb m g k
local notation "d" => KFCausalClockFloorFrozenClockLoss.dissipation ε hε h hne hb m g k
local notation "C" => KFCausalClockFloorQuantumVelocityOutput.classicalOutput ε hε
local notation "O0" => energyOutput ε hε h hne hb m g k 0

theorem actual_expectation_antitone (s : ℝ) (v : V) : Antitone (fun t => X (E s t (J v))) := by
  apply antitone_of_hasDerivAt_nonpos
    (fun t => KFCausalClockFloorExactEhrenfest.expectation_derivative ε hε h hne hb m g k s t v)
  intro t
  change KFCausalClockFloorExactEhrenfest.exactRate ε hε h hne hb m g k s t v ≤ 0
  have hc := KFCausalClockFloorDefectProductionCoercivity.averaged_coercivity ε hε h hne hb
    (KFCausalClockFloorExactEhrenfest.evolvingOutput ε hε h hne hb m g k s t v)
  have hn := KFCausalClockFloorDefectProductionCoercivity.averaged_classical_nonpositive ε hε
    (KFCausalClockFloorExactEhrenfest.evolvingOutput ε hε h hne hb m g k s t v)
  exact hc.trans (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hn)

theorem actual_expectation_limit (s : ℝ) (v : V) :
    ∃ b : ℝ, Tendsto (fun t => X (E s t (J v))) atTop (𝓝 b) :=
  ⟨⨅ t : ℝ, X (E s t (J v)),tendsto_atTop_ciInf (actual_expectation_antitone ε hε h hne hb m g k s v)
    ⟨0,by rintro _ ⟨t,rfl⟩; exact KFCausalClockFloorStrictQuantumLimit.expectation_nonnegative ε hε _⟩⟩

theorem actual_window_drop (a : ℝ) (v : V) (ell : ℝ → ℝ)
    (hpos : ∀ᶠ U in atTop, 0 ≤ ell U) :
    Tendsto (fun U => X (E (physicalTime a) (physicalTime U) (J v))-X (P a U (ell U) (J v)))
      atTop (𝓝 0) := by
  obtain ⟨b,hb'⟩ := actual_expectation_limit ε hε h hne hb m g k (physicalTime a) v
  have ht : Tendsto (fun U => U+ell U) atTop atTop :=
    tendsto_atTop_mono' atTop (hpos.mono (fun U hU => show U ≤ U+ell U from le_add_of_nonneg_right hU)) tendsto_id
  simpa only [sub_self] using (hb'.comp physicalTime_tendsto).sub (hb'.comp (physicalTime_tendsto.comp ht))

theorem frozen_expectation_error (a : ℝ) (ha : 0 < a) (v : V) (ell : ℝ → ℝ)
    (hpos : ∀ᶠ U in atTop, 0 ≤ ell U)
    (hsmall : Tendsto (fun U => ell U^2/U) atTop (𝓝 0)) :
    Tendsto (fun U => X (P a U (ell U) (J v))-X (Q a U (ell U) (J v))) atTop (𝓝 0) := by
  have he := (KFCausalClockFloorMovingFreeze.window_error ε hε h hne hb m g k a ha (J v) ell hpos hsmall).tendsto_at
    (show (1:ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one,le_rfl⟩)
  have hn : Tendsto (fun U => (2*‖J v‖)*‖P a U (ell U) (J v)-Q a U (ell U) (J v)‖) atTop (𝓝 0) := by
    simpa only [one_mul,norm_zero,mul_zero] using he.norm.const_mul (2*‖J v‖)
  apply squeeze_zero_norm (fun U => ?_) hn
  have hb' := KFCausalMassObservableDerivative.quadratic_difference_bound D
    (KFCausalClockFloorDefectOperator.defectOperator_norm_le ε hε) (P a U (ell U) (J v)) (Q a U (ell U) (J v))
  simpa only [expectation,Real.norm_eq_abs,(P a U (ell U)).norm_map,(Q a U (ell U)).norm_map,← two_mul] using hb'

theorem frozen_window_drop (a : ℝ) (ha : 0 < a) (v : V) (ell : ℝ → ℝ)
    (hpos : ∀ᶠ U in atTop, 0 ≤ ell U)
    (hsmall : Tendsto (fun U => ell U^2/U) atTop (𝓝 0)) :
    Tendsto (fun U => X (E (physicalTime a) (physicalTime U) (J v))-X (Q a U (ell U) (J v)))
      atTop (𝓝 0) := by
  have ht := (actual_window_drop ε hε h hne hb m g k a v ell hpos).add
    (frozen_expectation_error ε hε h hne hb m g k a ha v ell hpos hsmall)
  simpa only [sub_add_sub_cancel,add_zero] using ht

theorem total_dissipation_limit (a : ℝ) (ha : 0 < a) (v : V) (ell : ℝ → ℝ)
    (hpos : ∀ᶠ U in atTop, 0 ≤ ell U)
    (hsmall : Tendsto (fun U => ell U^2/U) atTop (𝓝 0)) :
    Tendsto (fun U => ∫ t in 0..ell U, d U t (aState a U v)) atTop (𝓝 0) := by
  have hl : Tendsto (fun U => 32*(X (E (physicalTime a) (physicalTime U) (J v))-X (Q a U (ell U) (J v))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (frozen_window_drop ε hε h hne hb m g k a ha v ell hpos hsmall).const_mul 32
  apply squeeze_zero' _ _ hl
  · filter_upwards [eventually_gt_atTop (0:ℝ),hpos] with U hU hp
    exact intervalIntegral.integral_nonneg_of_forall hp
      (fun t => KFCausalClockFloorFrozenClockLoss.dissipation_nonnegative ε hε h hne hb m g k U t hU _)
  · filter_upwards [eventually_gt_atTop (0:ℝ),hpos] with U hU hp
    have he := KFCausalClockFloorFrozenClockLoss.dissipation_budget ε hε h hne hb m g k U (ell U) hU hp (aState a U v)
    have hi : J (aState a U v)=E (physicalTime a) (physicalTime U) (J v) :=
      (KFCausalClockFloorAveragedEvolution.evolution_embedding ε hε h hne hb m g k (physicalTime a) (physicalTime U) v).symm
    simpa only [hi,KFCausalClockFloorMovingFreeze.frozen,LinearIsometryEquiv.trans_apply] using he

def detector (v : V) : ℝ := -(inner ℂ (O0 v) ((C).compLp (O0 v))).re/2
local notation "det" => detector ε hε h hne hb m g k

theorem dissipation_rescaling (U t : ℝ) (hU : 0 < U) (v : V) : d U t v=det (F U t v) := by
  have he := KFCausalClockFloorDissipationRescaling.averaged_real_pairing ε hε 0 (physicalTime U) (O0 (F U t v))
  have ht : Real.exp (2*(physicalTime U-0))=U := by
    simpa only [sub_zero] using exp_physicalTime U hU
  exact scaled_dissipation U _ _ hU
    (he.trans (congrArg (fun z => z*(inner ℂ (O0 (F U t v)) ((C).compLp (O0 (F U t v)))).re) ht))

theorem ordered_total_limit (a : ℝ) (ha : 0 < a) (v : V) (ell : ℝ → ℝ)
    (hpos : ∀ᶠ U in atTop, 0 ≤ ell U)
    (hsmall : Tendsto (fun U => ell U^2/U) atTop (𝓝 0)) :
    Tendsto (fun U => ∫ t in 0..ell U, det (F U t (aState a U v))) atTop (𝓝 0) := by
  apply (total_dissipation_limit ε hε h hne hb m g k a ha v ell hpos hsmall).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with U hU
  exact intervalIntegral.integral_congr (fun t _ => dissipation_rescaling ε hε h hne hb m g k U t hU _)

theorem quarter_ordered_total_limit (a : ℝ) (ha : 0 < a) (v : V) :
    Tendsto (fun U => ∫ t in 0..KFCausalGrowingTimeWindows.quarterWindow U, det (F U t (aState a U v))) atTop (𝓝 0) :=
  ordered_total_limit ε hε h hne hb m g k a ha v KFCausalGrowingTimeWindows.quarterWindow
    (Eventually.of_forall KFCausalGrowingTimeWindows.quarterWindow_nonneg)
    KFCausalGrowingTimeWindows.quarterWindow_square_ratio

#print axioms actual_expectation_antitone
#print axioms actual_expectation_limit
#print axioms actual_window_drop
#print axioms frozen_expectation_error
#print axioms frozen_window_drop
#print axioms total_dissipation_limit
#print axioms dissipation_rescaling
#print axioms ordered_total_limit
#print axioms quarter_ordered_total_limit
end
end UnifiedTheory.Audit.KFCausalClockFloorMovingDissipation
