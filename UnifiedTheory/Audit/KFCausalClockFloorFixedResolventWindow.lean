/- A single spectral threshold works throughout any compact time window.
The scaled full resolvents are uniformly bounded there and their time
derivatives are continuous. These are resolvent bounds, not flow bounds. -/
import UnifiedTheory.Audit.KFCausalClockFloorFixedResolventCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorFixedResolventWindow
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFixedResolventCurve

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "C" => connection ε hε h hne hh m g k
local notation "K" => baseBound ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k
local notation "R" => fullResolvent ε hε h hne hh m g k

theorem base_bound_continuous (a s : ℝ) (ha : 0 < a) : Continuous (K a s) := by
  have hs : Continuous (S a s) := continuous_iff_continuousAt.mpr
    (fun t => (transport_derivative ε hε h hne hh m g k a s t ha).continuousAt)
  have hu : Continuous (fun t => S a t s) := continuous_iff_continuousAt.mpr
    (fun t => (transport_reverse_derivative ε hε h hne hh m g k a s t).continuousAt)
  have hf : Continuous (F a) := continuous_iff_continuousAt.mpr
    (fun t => (referenceShift_derivative ε hε h hne hh m g k a t).continuousAt)
  have hd : Continuous (KFCausalShiftedForm.lowerConstant a) :=
    continuous_const.min (continuous_const.min (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  have hc := (hf.norm.div hd (fun t => ne_of_gt (KFCausalShiftedForm.lowerConstant_positive a t ha))).sqrt
  exact (hu.norm.mul hc).mul hs.norm

theorem threshold_continuous (a s : ℝ) (ha : 0 < a) : Continuous (q a s) := by
  have hc : Continuous (C a s) := continuous_iff_continuousAt.mpr
    (fun t => (connection_derivative ε hε h hne hh m g k a s t ha).continuousAt)
  exact hc.norm.mul (base_bound_continuous ε hε h hne hh m g k a s ha)

theorem admissible_open (a b s : ℝ) (ha : 0 < a) : IsOpen {t | q a s t < b} :=
  isOpen_lt (threshold_continuous ε hε h hne hh m g k a s ha) continuous_const

theorem uniform_window (a s l r : ℝ) (ha : 0 < a) :
    ∃ b₀ K₀ : ℝ, 0 < b₀ ∧ 0 ≤ K₀ ∧ ∀ b, b₀ ≤ b → ∀ t ∈ Icc l r,
      q a s t < b ∧ ∀ f : V, ‖b • R a b s t f‖ ≤ K₀*‖f‖ :=
  KFCausalEventualResolventApproximation.compact_uniform_scaling (fun b t => R a b s t)
    (K a s) (q a s) (base_bound_continuous ε hε h hne hh m g k a s ha)
    (threshold_continuous ε hε h hne hh m g k a s ha)
    (fun b t hb hbq => full_scaled_bound ε hε h hne hh m g k a b s t ha hb hbq) l r

theorem resolvent_output_bound (a b s t K₀ : ℝ)
    (hb : ∀ f : V, ‖b • R a b s t f‖ ≤ K₀*‖f‖) (f : V) :
    ‖b • R a b s t f-f‖ ≤ (K₀+1)*‖f‖ := by
  calc
    _ ≤ ‖b • R a b s t f‖+‖f‖ := norm_sub_le _ _
    _ ≤ K₀*‖f‖+‖f‖ := add_le_add (hb f) le_rfl
    _ = _ := by ring

theorem full_resolvent_continuousOn (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (R a b s) {t | q a s t < b} :=
  fun t ht => (full_resolvent_derivative ε hε h hne hh m g k a b s t ha hb ht).continuousAt.continuousWithinAt

#print axioms base_bound_continuous
#print axioms threshold_continuous
#print axioms admissible_open
#print axioms uniform_window
#print axioms resolvent_output_bound
#print axioms full_resolvent_continuousOn
end
end UnifiedTheory.Audit.KFCausalClockFloorFixedResolventWindow
