/- Exponential time and its exact energy-loss identity for the full
physical evolution. Every differential statement is restricted to u>0. -/
import UnifiedTheory.Audit.KFCausalClockFloorRescaledEnergy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorFastTimeEnergy
noncomputable section
open Filter MeasureTheory
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorRescaledEnergy

def physicalTime (u : ℝ) : ℝ := Real.log u/2

theorem physicalTime_derivative (u : ℝ) (hu : 0 < u) :
    HasDerivAt physicalTime (1/(2*u)) u := by
  convert (Real.hasDerivAt_log hu.ne').div_const 2 using 1
  field_simp

theorem physicalTime_continuous : ContinuousOn physicalTime (Set.Ioi 0) :=
  (Real.continuousOn_log.mono (fun _ hu => ne_of_gt hu)).div_const 2

theorem physicalTime_tendsto : Tendsto physicalTime atTop atTop :=
  Real.tendsto_log_atTop.atTop_div_const (by norm_num)

theorem exp_physicalTime (u : ℝ) (hu : 0 < u) : Real.exp (2*physicalTime u) = u := by
  rw [physicalTime,show 2*(Real.log u/2) = Real.log u by ring,Real.exp_log hu]

theorem exp_neg_physicalTime (u : ℝ) (hu : 0 < u) : Real.exp (-2*physicalTime u) = u⁻¹ := by
  rw [show -2*physicalTime u = -(2*physicalTime u) by ring,Real.exp_neg,exp_physicalTime u hu]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "E" => scaledEnergy ε hε h hne hb m g k
local notation "S" => staticEnergy ε hε h hne hb m g k

def fastEnergy (s u : ℝ) (w : V) : ℝ := E s (physicalTime u) w
def fastLoss (s u : ℝ) (w : V) : ℝ := S s (physicalTime u) w/u^2

theorem fastEnergy_derivative (s u : ℝ) (hu : 0 < u) (w : V) :
    HasDerivAt (fun r => fastEnergy ε hε h hne hb m g k s r w)
      (-fastLoss ε hε h hne hb m g k s u w) u := by
  have hd := (scaled_derivative ε hε h hne hb m g k s (physicalTime u) w).comp u
    (physicalTime_derivative u hu)
  convert hd using 1
  rw [staticLoss,exp_neg_physicalTime u hu]
  unfold fastLoss
  field_simp

theorem fastLoss_continuous (s : ℝ) (w : V) :
    ContinuousOn (fun u => fastLoss ε hε h hne hb m g k s u w) (Set.Ioi 0) :=
  ((staticEnergy_continuous ε hε h hne hb m g k s w).comp_continuousOn
    physicalTime_continuous).div (continuousOn_id.pow 2) (fun _ hu => pow_ne_zero 2 (ne_of_gt hu))

theorem fastLoss_integral (s a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (w : V) :
    (∫ u in a..b, fastLoss ε hε h hne hb m g k s u w) =
      fastEnergy ε hε h hne hb m g k s a w-fastEnergy ε hε h hne hb m g k s b w := by
  have hc := (fastLoss_continuous ε hε h hne hb m g k s w).mono
    (show Set.Icc a b ⊆ Set.Ioi 0 from fun _ hu => ha.trans_le hu.1)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => fastEnergy_derivative ε hε h hne hb m g k s u
      (ha.trans_le ((Set.uIcc_of_le hab ▸ hu : u ∈ Set.Icc a b).1)) w)
    (hc.neg.intervalIntegrable_of_Icc hab)
  rw [intervalIntegral.integral_neg] at hi
  linarith only [hi]

theorem fastEnergy_limit (s : ℝ) (w : V) :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧ (∀ u, ℓ ≤ fastEnergy ε hε h hne hb m g k s u w) ∧
      Tendsto (fun u => fastEnergy ε hε h hne hb m g k s u w) atTop (𝓝 ℓ) := by
  obtain ⟨ℓ,hℓ,hl,ht⟩ := scaled_limit ε hε h hne hb m g k s w
  exact ⟨ℓ,hℓ,fun u => hl (physicalTime u),ht.comp physicalTime_tendsto⟩

theorem fastLoss_integrable (s a : ℝ) (ha : 0 < a) (w : V) :
    IntegrableOn (fun u => fastLoss ε hε h hne hb m g k s u w) (Set.Ioi a) := by
  obtain ⟨ℓ,_,_,ht⟩ := fastEnergy_limit ε hε h hne hb m g k s w
  have hi := integrableOn_Ioi_deriv_of_nonpos'
    (fun u hu => fastEnergy_derivative ε hε h hne hb m g k s u (ha.trans_le hu) w)
    (fun u _ => neg_nonpos.mpr (div_nonneg (sq_nonneg _) (sq_nonneg u))) ht
  have hn := hi.neg
  change Integrable (fun u => - -fastLoss ε hε h hne hb m g k s u w)
    (volume.restrict (Set.Ioi a)) at hn
  simpa only [neg_neg] using hn

theorem fastLoss_upper (s u : ℝ) (hu : 0 < u) (ht : s ≤ physicalTime u) (w : V) :
    fastLoss ε hε h hne hb m g k s u w ≤ E s s w/u := by
  have hs : S s (physicalTime u) w/u ≤ E s s w := by
    have hsplit := scaled_split ε hε h hne hb m g k s (physicalTime u) w
    rw [staticLoss,exp_neg_physicalTime u hu] at hsplit
    have hle := scaled_antitone ε hε h hne hb m g k s w ht
    change E s (physicalTime u) w ≤ E s s w at hle
    rw [hsplit] at hle
    have hn := sq_nonneg ‖KFCausalClockFloorAveragedRegularity.growingMap ε hε h hne hb m g k
      (KFCausalClockFloorAveragedFormFlow.formFlow ε hε h hne hb m g k s (physicalTime u) w)‖
    rw [div_eq_mul_inv,mul_comm]
    linarith only [hle,hn]
  simpa only [fastLoss,div_div,pow_two] using div_le_div_of_nonneg_right hs hu.le

theorem fastLoss_tendsto_zero (s : ℝ) (w : V) :
    Tendsto (fun u => fastLoss ε hε h hne hb m g k s u w) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun u => div_nonneg (sq_nonneg _) (sq_nonneg u))) _
    (tendsto_id.const_div_atTop (E s s w))
  filter_upwards [eventually_gt_atTop (0:ℝ),physicalTime_tendsto.eventually (eventually_ge_atTop s)] with u hu ht
  exact fastLoss_upper ε hε h hne hb m g k s u hu ht w

#print axioms physicalTime_derivative
#print axioms physicalTime_continuous
#print axioms physicalTime_tendsto
#print axioms exp_physicalTime
#print axioms exp_neg_physicalTime
#print axioms fastEnergy_derivative
#print axioms fastLoss_continuous
#print axioms fastLoss_integral
#print axioms fastEnergy_limit
#print axioms fastLoss_integrable
#print axioms fastLoss_upper
#print axioms fastLoss_tendsto_zero
end
end UnifiedTheory.Audit.KFCausalClockFloorFastTimeEnergy
