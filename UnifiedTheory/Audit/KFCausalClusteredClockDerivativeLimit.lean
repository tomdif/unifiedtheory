/- The complete clock density derivative passes through the positive
width-spacing limit under the joint integral. This is an integral of the
pointwise clock derivative; moving the clock derivative outside that
integral is a separate remaining identification. -/
import UnifiedTheory.Audit.KFCausalClusteredClockEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalClusteredClockDerivativeLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalClusteredClockFactors
open KFCausalClusteredClockDensity
open KFCausalClusteredClockEnvelope
open KFCausalClusteredWidthProfiles (widths coefficients limitDensity)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalClockFloorRelativeShift (scale)

theorem response_continuous (n : ℕ) (α β δ : ℝ) (r v b : ℂ) (P : Polynomial ℂ) :
    Continuous (response n α β δ r v b P) := by
  unfold response component factor KFCausalClusteredClockFactors.slope B0 B1 E Ed Z Zd N Nd F Fd G Gd
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
    KFCausalClusteredWidthProfiles.quotient
  fun_prop

theorem limitResponse_continuous (n : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ) :
    Continuous (limitResponse n α β r v b P) := by
  unfold limitResponse limitComponent limitFactor limitSlope B0 B1 E Ed Z Zd N Nd F Fd G Gd
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
  fun_prop

theorem response_integrable (n : ℕ) (α β δ : ℝ) (hδ : 0 < δ) (r v b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) :
    Integrable (response n α β δ r v b P) jointMeasure := by
  apply (responseBound_integrable n α β r v b P hβ hA hC).mono'
    (response_continuous n α β δ r v b P).aestronglyMeasurable
  filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
  exact response_norm_le n α β δ hδ r v b P hA.le p hp

theorem limitResponse_integrable (n : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) :
    Integrable (limitResponse n α β r v b P) jointMeasure := by
  apply (responseBound_integrable n α β r v b P hβ hA hC).mono'
    (limitResponse_continuous n α β r v b P).aestronglyMeasurable
  filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
  apply le_of_tendsto (response_tendsto n α β r v b P p).norm
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact response_norm_le n α β δ hδ r v b P hA.le p hp

theorem response_integral_tendsto (n : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) :
    Tendsto (fun δ : ℝ => ∫ p, response n α β δ r v b P p ∂jointMeasure) (𝓝[>] 0)
      (𝓝 (∫ p, limitResponse n α β r v b P p ∂jointMeasure)) := by
  apply tendsto_integral_filter_of_dominated_convergence (responseBound n α β r v b P)
  · exact Filter.Eventually.of_forall (fun δ => (response_continuous n α β δ r v b P).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
    exact response_norm_le n α β δ hδ r v b P hA.le p hp
  · exact responseBound_integrable n α β r v b P hβ hA hC
  · exact Filter.Eventually.of_forall (response_tendsto n α β r v b P)

theorem curve_derivative_integral_tendsto (n : ℕ) (α β : ℝ) (r : ℝ → ℂ) (v b : ℂ)
    (P : Polynomial ℂ) (s : ℝ) (hr : HasDerivAt r v s)
    (hβ : 0 < β) (hA : 0 < α*area (r s)) (hC : 0 < α*area (r s)-8*β*(r s).im^2) :
    Tendsto (fun δ : ℝ => ∫ p, deriv (fun t => positiveDensity (n+1) α β (widths n δ) (r t)
        (coefficients n δ) (fun _ => exponentialProfile b 1 P) p) s ∂jointMeasure) (𝓝[>] 0)
      (𝓝 (∫ p, deriv (fun t => limitDensity n α β (r t) (exponentialProfile b 1 P) p) s ∂jointMeasure)) := by
  have hl : (fun p => deriv (fun t => limitDensity n α β (r t) (exponentialProfile b 1 P) p) s) =
      limitResponse n α β (r s) v b P := by
    funext p
    exact (limitDensity_derivative n α β r v b P s p hr).deriv
  rw [hl]
  apply Tendsto.congr' _ (response_integral_tendsto n α β (r s) v b P hβ hA hC)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  congr 1
  funext p
  exact (density_derivative n α β δ hδ r v b P s p hr).deriv.symm

theorem actual_clock_derivative_integral_tendsto (n : ℕ) (α β ε y s : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Tendsto (fun δ : ℝ => ∫ p, deriv (fun t => positiveDensity (n+1) α β (widths n δ) (scale ε y t)
        (coefficients n δ) (fun _ => exponentialProfile b 1 P) p) s ∂jointMeasure) (𝓝[>] 0)
      (𝓝 (∫ p, deriv (fun t => limitDensity n α β (scale ε y t) (exponentialProfile b 1 P) p) s ∂jointMeasure)) := by
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hw hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  exact curve_derivative_integral_tendsto n α β (scale ε y)
    (KFCausalNeutralPlaneClockGeometry.velocity ε (Real.exp s) (scale ε y s)) b P s
    (KFCausalNeutralPlaneClockGeometry.scale_velocity ε y s hε hy) hβ ha hc

#print axioms response_continuous
#print axioms limitResponse_continuous
#print axioms response_integrable
#print axioms limitResponse_integrable
#print axioms response_integral_tendsto
#print axioms curve_derivative_integral_tendsto
#print axioms actual_clock_derivative_integral_tendsto
end
end UnifiedTheory.Audit.KFCausalClusteredClockDerivativeLimit
