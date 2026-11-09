/- Remove both clock endpoints for actual field-weighted Gaussian pairs.
Both individual densities are integrable on the full configuration space;
the equality of their full clock integrals follows from the derived
boundary limit. Clock/transverse Fubini is justified by that integrability. -/
import UnifiedTheory.Audit.KFCausalGaussianResponseIntegrability
import UnifiedTheory.Audit.KFCausalGaussianBoundaryLimit
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalGaussianWholeClockResponse
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalGaussianResponseIntegrability
  (weakDensity reducedDensity weakDensity_integrable reducedDensity_integrable)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)

variable (ε a a' p p' α β α' β' h : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ)
  (l : Transverse →L[ℝ] ℝ) (n : Fin 3)
  (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (ha : 0 < a) (ha' : 0 < a') (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hα' : 0 < α') (hβ' : 0 < β') (hw' : 32*β' ≤ α')
local notation "W" => weakDensity ε (-h/2) a a' p p' α β α' β' b c C D l n
local notation "R" => reducedDensity ε (-h/2) a a' p p' α β α' β' b c C D l n

include hε hh hb ha ha' hα hβ hw hα' hβ' hw' in
theorem clock_integrable_ae : ∀ᵐ q : Transverse ∂volume,
    Integrable (fun s : ℝ => W (s,q)) volume ∧ Integrable (fun s : ℝ => R (s,q)) volume := by
  have hi := weakDensity_integrable ε a a' p p' α β α' β' b c C D l n h hε hh hb ha ha' hα hβ hw hα' hβ' hw'
  have hj := reducedDensity_integrable ε a a' p p' α β α' β' b c C D l n h hε hh hb ha ha' hα hβ hw hα' hβ' hw'
  exact hi.prod_left_ae.and hj.prod_left_ae

include hε hh hb ha ha' hα hβ hw hα' hβ' hw' in
theorem clock_integrals_eq_ae : ∀ᵐ q : Transverse ∂volume,
    (∫ s : ℝ, W (s,q)) = ∫ s : ℝ, R (s,q) := by
  filter_upwards [clock_integrable_ae ε a a' p p' α β α' β' h b c C D l n
    hε hh hb ha ha' hα hβ hw hα' hβ' hw'] with q hq
  have ht := (intervalIntegral_tendsto_integral hq.1 tendsto_neg_atTop_atBot tendsto_id).sub
    (intervalIntegral_tendsto_integral hq.2 tendsto_neg_atTop_atBot tendsto_id)
  have hz := (KFCausalGaussianBoundaryLimit.interval_difference_atTop ε (-h/2) α β α' β'
    b c C D q hε (shift_bound ε h hb) a a' p p' (by linarith)).const_mul ((l q:ℂ)^(2*n.val))
  simp only [mul_zero] at hz
  have hz' : Tendsto (fun T : ℝ => (∫ s in -T..T, W (s,q))-
      ∫ s in -T..T, R (s,q)) atTop (𝓝 0) := by
    simpa only [weakDensity,reducedDensity,mul_assoc,
      intervalIntegral.integral_const_mul,← mul_sub] using hz
  exact sub_eq_zero.mp (tendsto_nhds_unique ht hz')

include hε hh hb ha ha' hα hβ hw hα' hβ' hw' in
theorem configuration_integrals_eq : (∫ x : Configuration, W x) = ∫ x : Configuration, R x := by
  have hi := weakDensity_integrable ε a a' p p' α β α' β' b c C D l n h hε hh hb ha ha' hα hβ hw hα' hβ' hw'
  have hj := reducedDensity_integrable ε a a' p p' α β α' β' b c C D l n h hε hh hb ha ha' hα hβ hw hα' hβ' hw'
  exact (integral_prod_symm _ hi).trans
    ((integral_congr_ae (clock_integrals_eq_ae ε a a' p p' α β α' β' h b c C D l n
      hε hh hb ha ha' hα hβ hw hα' hβ' hw')).trans (integral_prod_symm _ hj).symm)

include hε hh hb ha ha' hα hβ hw hα' hβ' hw' in
theorem iterated_response_eq :
    (∫ s : ℝ, ∫ q : Transverse, W (s,q)) = (∫ q : Transverse, ∫ s : ℝ, R (s,q)) := by
  have hi := weakDensity_integrable ε a a' p p' α β α' β' b c C D l n h hε hh hb ha ha' hα hβ hw hα' hβ' hw'
  have hj := reducedDensity_integrable ε a a' p p' α β α' β' b c C D l n h hε hh hb ha ha' hα hβ hw hα' hβ' hw'
  rw [← integral_prod _ hi,← integral_prod_symm _ hj]
  exact configuration_integrals_eq ε a a' p p' α β α' β' h b c C D l n
    hε hh hb ha ha' hα hβ hw hα' hβ' hw'

#print axioms clock_integrable_ae
#print axioms clock_integrals_eq_ae
#print axioms configuration_integrals_eq
#print axioms iterated_response_eq
end
end UnifiedTheory.Audit.KFCausalGaussianWholeClockResponse
