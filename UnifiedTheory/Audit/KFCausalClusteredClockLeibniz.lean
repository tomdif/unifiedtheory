/- Differentiation under the actual joint integral. A common integrable
clock-neighborhood envelope is derived rather than assumed. -/
import UnifiedTheory.Audit.KFCausalClusteredClockCompactEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalClusteredClockLeibniz
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalClusteredWidthProfiles (widths coefficients limitDensity)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalClusteredClockDensity (response limitResponse)
open KFCausalClusteredClockDerivativeLimit
open KFCausalReciprocalGaussianCoordinates (area)

theorem density_integrable (n : ℕ) (α β δ : ℝ) (hδ : 0 < δ) (r b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) :
    Integrable (positiveDensity (n+1) α β (widths n δ) r (coefficients n δ)
      (fun _ => exponentialProfile b 1 P)) jointMeasure := by
  apply (KFCausalClusteredWidthDensityIntegrability.limitDensity_integrable n α β r b P hβ hA hC).mono'
    (KFCausalClusteredWidthEnergyLimit.positiveDensity_continuous n α β δ r b P).aestronglyMeasurable
  filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
  rw [Real.norm_eq_abs,abs_of_nonneg (KFCausalReciprocalNeutralPositiveForm.positiveDensity_nonneg _ _ _ _ _ _ _ _)]
  exact KFCausalClusteredWidthProfiles.positiveDensity_le_limit n α β δ r _ hδ hA.le p hp

theorem limitDensity_continuous (n : ℕ) (α β : ℝ) (r b : ℂ) (P : Polynomial ℂ) :
    Continuous (limitDensity n α β r (exponentialProfile b 1 P)) := by
  unfold limitDensity KFCausalReciprocalNeutralLaplace.weight KFCausalReciprocalWedgeGeometry.chart
    exponentialProfile KFCausalReciprocalNeutralKernel.neutral KFCausalQuarticPlaneDomination.potential
  fun_prop

theorem density_integral_derivative (n : ℕ) (α β δ q : ℝ) (hδ : 0 < δ)
    (r : ℝ → ℂ) (hr : ContDiff ℝ 1 r) (b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hq : 0 < q) (ha : ∀ t, q ≤ α*area (r t))
    (hc : ∀ t, q ≤ α*area (r t)-8*β*(r t).im^2) (s : ℝ) :
    HasDerivAt (fun t => ∫ p, positiveDensity (n+1) α β (widths n δ) (r t)
      (coefficients n δ) (fun _ => exponentialProfile b 1 P) p ∂jointMeasure)
      (∫ p, response n α β δ (r s) (deriv r s) b P p ∂jointMeasure) s := by
  obtain ⟨D,hDi,_,hD⟩ := KFCausalClusteredClockCompactEnvelope.response_common_envelope
    (Set.Icc (s-1) (s+1)) isCompact_Icc n α β q r (deriv r) hr.continuous hr.continuous_deriv_one b P
    hβ hq (fun t _ => ha t) (fun t _ => hc t)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t p => positiveDensity (n+1) α β (widths n δ) (r t) (coefficients n δ)
      (fun _ => exponentialProfile b 1 P) p)
    (F' := fun t p => response n α β δ (r t) (deriv r t) b P p) (bound := D)
    (Icc_mem_nhds (by linarith : s-1<s) (by linarith : s<s+1))
    (Filter.Eventually.of_forall (fun t =>
      (KFCausalClusteredWidthEnergyLimit.positiveDensity_continuous n α β δ (r t) b P).aestronglyMeasurable))
    (density_integrable n α β δ hδ (r s) b P hβ (hq.trans_le (ha s)) (hq.trans_le (hc s)))
    (response_continuous n α β δ (r s) (deriv r s) b P).aestronglyMeasurable
    _ hDi _).2
  · filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
    exact fun t ht => (hD t ht p hp).1 δ hδ
  · exact Filter.Eventually.of_forall (fun p t _ =>
      KFCausalClusteredClockDensity.density_derivative n α β δ hδ r (deriv r t) b P t p
        ((hr.differentiable (by norm_num)) t).hasDerivAt)

theorem limitDensity_integral_derivative (n : ℕ) (α β q : ℝ)
    (r : ℝ → ℂ) (hr : ContDiff ℝ 1 r) (b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hq : 0 < q) (ha : ∀ t, q ≤ α*area (r t))
    (hc : ∀ t, q ≤ α*area (r t)-8*β*(r t).im^2) (s : ℝ) :
    HasDerivAt (fun t => ∫ p, limitDensity n α β (r t) (exponentialProfile b 1 P) p ∂jointMeasure)
      (∫ p, limitResponse n α β (r s) (deriv r s) b P p ∂jointMeasure) s := by
  obtain ⟨D,hDi,_,hD⟩ := KFCausalClusteredClockCompactEnvelope.response_common_envelope
    (Set.Icc (s-1) (s+1)) isCompact_Icc n α β q r (deriv r) hr.continuous hr.continuous_deriv_one b P
    hβ hq (fun t _ => ha t) (fun t _ => hc t)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t p => limitDensity n α β (r t) (exponentialProfile b 1 P) p)
    (F' := fun t p => limitResponse n α β (r t) (deriv r t) b P p) (bound := D)
    (Icc_mem_nhds (by linarith : s-1<s) (by linarith : s<s+1))
    (Filter.Eventually.of_forall (fun t => (limitDensity_continuous n α β (r t) b P).aestronglyMeasurable))
    (KFCausalClusteredWidthDensityIntegrability.limitDensity_integrable n α β (r s) b P hβ
      (hq.trans_le (ha s)) (hq.trans_le (hc s)))
    (limitResponse_continuous n α β (r s) (deriv r s) b P).aestronglyMeasurable
    _ hDi _).2
  · filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
    exact fun t ht => (hD t ht p hp).2
  · exact Filter.Eventually.of_forall (fun p t _ =>
      KFCausalClusteredClockDensity.limitDensity_derivative n α β r (deriv r t) b P t p
        ((hr.differentiable (by norm_num)) t).hasDerivAt)

#print axioms density_integrable
#print axioms limitDensity_continuous
#print axioms density_integral_derivative
#print axioms limitDensity_integral_derivative
end
end UnifiedTheory.Audit.KFCausalClusteredClockLeibniz
