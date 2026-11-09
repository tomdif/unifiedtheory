/- Quantitative comparison of actual dynamics at nearby positive real
cutoffs. The bound tends to zero as their common scale grows, using the
proved form-energy estimate rather than assuming a residual bound. -/
import UnifiedTheory.Audit.KFCausalYosidaParameterDifference
import UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedCutoffComparison
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormWindowBound
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSmoothedTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation
open UnifiedTheory.Audit.KFCausalYosidaParameterDifference

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "J" => embedding ε hε hbar hh hbound mass2 quartic vacuum 0
local notation "Y" => averagedYosida ε hε hbar hh hbound mass2 quartic vacuum
local notation "R" => shiftedResolvent ε hε hbar hh hbound mass2 quartic vacuum
local notation "F" => dynamics ε hε hbar hh hbound mass2 quartic vacuum
local notation "W" => windowEnergy ε hε hbar hh hbound mass2 quartic vacuum

theorem yosida_parameter_bound (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (f : Hilbert) :
    ‖(Y b t-Y a t) f‖ ≤ 2*|a-b| *‖f-b • R b t f‖ := by
  have he := yosida_difference_bound
    (hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t) (R a t) (R b t) a b ha
    (averaged_resolves ε hε hbar hh hbound mass2 quartic vacuum a t ha)
    (averaged_resolves ε hε hbar hh hbound mass2 quartic vacuum b t hb)
    (hamiltonian_positive ε hε hbar hh hbound mass2 quartic vacuum t)
    (shiftedResolvent_left ε hε hbar hh hbound mass2 quartic vacuum a t ha) f
  simpa only [ContinuousLinearMap.sub_apply,norm_sub_rev] using he

theorem dynamics_nearby_cutoff_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (s t : ℝ) (hclose : |a-b| ≤ 1)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    ‖F a ha s t (J w)-F b hb s t (J w)‖ ≤
      (|1/hbar| *(2*Real.sqrt (W s (max |s| |t|) w/b)))*|t-s| := by
  apply dynamics_difference_bound ε hε hbar hh hbound mass2 quartic vacuum a b ha hb s t
    (2*Real.sqrt (W s (max |s| |t|) w/b)) (J w)
  intro z hz
  have hd := smoothed_window_defect ε hε hbar hh hbound mass2 quartic vacuum b hb s
    (max |s| |t|) z (abs_le_window_of_mem_uIcc s t z hz) w
  have hd' : ‖F b hb s z (J w)-b • R b z (F b hb s z (J w))‖^2 ≤ W s (max |s| |t|) w/b := by
    simpa only [smoothedState_resolvent] using hd
  have hn : ‖F b hb s z (J w)-b • R b z (F b hb s z (J w))‖ ≤
      Real.sqrt (W s (max |s| |t|) w/b) :=
    (Real.le_sqrt (norm_nonneg _) (div_nonneg
      (windowEnergy_nonneg ε hε hbar hh hbound mass2 quartic vacuum s (max |s| |t|) w) hb.le)).mpr hd'
  have hp := yosida_parameter_bound ε hε hbar hh hbound mass2 quartic vacuum a b z ha hb (F b hb s z (J w))
  have he := mul_le_mul (mul_le_mul_of_nonneg_left hclose (show 0 ≤ (2:ℝ) by norm_num))
    hn (norm_nonneg _) (show 0 ≤ (2:ℝ)*1 by norm_num)
  exact hp.trans (by simpa only [mul_one] using he)

#print axioms yosida_parameter_bound
#print axioms dynamics_nearby_cutoff_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedCutoffComparison
