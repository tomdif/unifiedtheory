/- Clock differentiation of the complete correlated joint energy. The
common envelope is derived for all blocks and all positive spacings. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredLeibniz
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredDensity
open KFCausalCorrelatedClusteredIntegrals
open KFCausalReciprocalGaussianCoordinates (area)

variable {m : ℕ} (f : Family m)

theorem density_integral_derivative (α β δ q : ℝ) (hδ : 0 < δ)
    (r : ℝ → ℂ) (hr : ContDiff ℝ 1 r) (hβ : 0 < β) (hq : 0 < q)
    (ha : ∀ t, q ≤ α*area (r t)) (hc : ∀ t, q ≤ α*area (r t)-8*β*(r t).im^2) (s : ℝ) :
    HasDerivAt (fun t => ∫ p, density f α β δ (r t) p ∂jointMeasure)
      (∫ p, response f α β δ (r s) (deriv r s) p ∂jointMeasure) s := by
  obtain ⟨D,hDi,_,hD⟩ := common_envelope f (Set.Icc (s-1) (s+1)) isCompact_Icc α β q
    r (deriv r) hr.continuous hr.continuous_deriv_one hβ hq (fun t _ => ha t) (fun t _ => hc t)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t p => density f α β δ (r t) p)
    (F' := fun t p => response f α β δ (r t) (deriv r t) p) (bound := D)
    (Icc_mem_nhds (by linarith : s-1<s) (by linarith : s<s+1))
    (Filter.Eventually.of_forall (fun t => (density_continuous f α β δ (r t)).aestronglyMeasurable))
    (integrability f α β δ hδ (r s) (deriv r s) hβ (hq.trans_le (ha s)) (hq.trans_le (hc s))).1
    (response_continuous f α β δ (r s) (deriv r s)).aestronglyMeasurable
    _ hDi _).2
  · filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
    exact fun t ht => ((hD t ht p hp).1 δ hδ).2
  · exact Filter.Eventually.of_forall (fun p t _ =>
      density_derivative f α β δ hδ r (deriv r t) t p ((hr.differentiable (by norm_num)) t).hasDerivAt)

theorem limitDensity_integral_derivative (α β q : ℝ)
    (r : ℝ → ℂ) (hr : ContDiff ℝ 1 r) (hβ : 0 < β) (hq : 0 < q)
    (ha : ∀ t, q ≤ α*area (r t)) (hc : ∀ t, q ≤ α*area (r t)-8*β*(r t).im^2) (s : ℝ) :
    HasDerivAt (fun t => ∫ p, limitDensity f α β (r t) p ∂jointMeasure)
      (∫ p, limitResponse f α β (r s) (deriv r s) p ∂jointMeasure) s := by
  obtain ⟨D,hDi,_,hD⟩ := common_envelope f (Set.Icc (s-1) (s+1)) isCompact_Icc α β q
    r (deriv r) hr.continuous hr.continuous_deriv_one hβ hq (fun t _ => ha t) (fun t _ => hc t)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t p => limitDensity f α β (r t) p)
    (F' := fun t p => limitResponse f α β (r t) (deriv r t) p) (bound := D)
    (Icc_mem_nhds (by linarith : s-1<s) (by linarith : s<s+1))
    (Filter.Eventually.of_forall (fun t => (limitDensity_continuous f α β (r t)).aestronglyMeasurable))
    (integrability f α β 1 (by norm_num) (r s) (deriv r s) hβ (hq.trans_le (ha s)) (hq.trans_le (hc s))).2.2.1
    (limitResponse_continuous f α β (r s) (deriv r s)).aestronglyMeasurable
    _ hDi _).2
  · filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
    exact fun t ht => (hD t ht p hp).2.2
  · exact Filter.Eventually.of_forall (fun p t _ =>
      limitDensity_derivative f α β r (deriv r t) t p ((hr.differentiable (by norm_num)) t).hasDerivAt)

#print axioms density_integral_derivative
#print axioms limitDensity_integral_derivative
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredLeibniz
