/- Fixed-order full-Joint energy and actual-response limits for genuine
simultaneous width/source differences. No bound uniform in the order is used. -/
import UnifiedTheory.Audit.KFCausalJointSourceConfluenceEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointSourceConfluenceLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalJointSourceConfluenceProfiles (widths sources coefficients)
open KFCausalJointSourceConfluenceFactors
open KFCausalJointSourceConfluenceEnvelope (responseBound)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalClockFloorRelativeShift (scale)

private theorem density_continuous (n : ℕ) (α β w0 δ : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) :
    Continuous (density n α β w0 δ r b ℓ P) := by
  unfold density factor Q KFCausalClusteredWidthProfiles.quotient
    KFCausalClusteredClockFactors.E KFCausalClusteredClockFactors.Z
    KFCausalClusteredClockFactors.N KFCausalClusteredClockFactors.G KFCausalClusteredClockFactors.F
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
  fun_prop

private theorem response_continuous (n : ℕ) (α β w0 δ : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) :
    Continuous (response n α β w0 δ r v b ℓ P) := by
  unfold response component factor KFCausalJointSourceConfluenceFactors.slope Q B1 Qd KFCausalClusteredWidthProfiles.quotient
    KFCausalClusteredClockFactors.B0 KFCausalClusteredClockFactors.E KFCausalClusteredClockFactors.Ed
    KFCausalClusteredClockFactors.Z KFCausalClusteredClockFactors.Zd
    KFCausalClusteredClockFactors.N KFCausalClusteredClockFactors.Nd
    KFCausalClusteredClockFactors.G KFCausalClusteredClockFactors.Gd
    KFCausalClusteredClockFactors.F KFCausalClusteredClockFactors.Fd
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
  fun_prop

private theorem spacing_eventually : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ ≤ 1 := by
  have hlt : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hlt] with δ hp hq
  exact ⟨hp,hq.le⟩

theorem limit_density_joint (n : ℕ) (α β w0 : ℝ) (hw0 : 1 ≤ w0)
    (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    limitDensity n α β w0 r b ℓ P p = KFCausalReciprocalNeutralLaplace.weight β r p*
      ‖Complex.exp (-(w0:ℂ)*KFCausalClusteredClockFactors.Z α r p+b*KFCausalClusteredClockFactors.N r p)*
        (KFCausalClusteredClockFactors.Z α r p-ℓ*KFCausalClusteredClockFactors.N r p)^n*
          P.eval (KFCausalClusteredClockFactors.N r p)‖^2 := by
  have ht := (((KFCausalJointSourceConfluenceProfiles.profileSum_tendsto n w0 hw0 b ℓ
    (KFCausalClusteredClockFactors.Z α r p) (KFCausalClusteredClockFactors.N r p) P).norm).pow 2).const_mul
      (KFCausalReciprocalNeutralLaplace.weight β r p)
  apply tendsto_nhds_unique (density_tendsto n α β w0 r b ℓ P p)
  apply Tendsto.congr' _ ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact density_joint n α β w0 δ hw0 hδ r b ℓ P p

theorem limit_density_derivative (n : ℕ) (α β w0 : ℝ)
    (r : ℝ → ℂ) (v b ℓ : ℂ) (P : Polynomial ℂ) (s : ℝ) (p : Joint)
    (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => limitDensity n α β w0 (r t) b ℓ P p)
      (limitResponse n α β w0 (r s) v b ℓ P p) s := by
  have hk (k : ℕ) := KFCausalNeutralQuarticBoundary.norm_square_derivative
    (fun t => limitFactor n k α β w0 (r t) b ℓ P p)
    (fun _ => limitSlope n k α β w0 (r s) v b ℓ P p) s
    (limitFactor_derivative n k α β w0 r v b ℓ P s p hr)
  exact ((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4)

theorem density_integral_tendsto (n : ℕ) (α β w0 : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ)
    (hw0 : 1 ≤ w0) (hβ : 0 < β) (hA : 0 < α*area r)
    (hC : 0 < α*area r-8*β*r.im^2) :
    Tendsto (fun δ : ℝ => ∫ p, density n α β w0 δ r b ℓ P p ∂jointMeasure)
      (𝓝[>] 0) (𝓝 (∫ p, limitDensity n α β w0 r b ℓ P p ∂jointMeasure)) := by
  obtain ⟨hAw,hCw⟩ := KFCausalJointFourierDilationQuartic.width_floors α r w0 β hw0 hA hC
  apply tendsto_integral_filter_of_dominated_convergence (responseBound n α β w0 r 0 b ℓ P)
  · exact Filter.Eventually.of_forall (fun δ => (density_continuous n α β w0 δ r b ℓ P).aestronglyMeasurable)
  · filter_upwards [spacing_eventually] with δ hδ
    filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
    exact KFCausalJointSourceConfluenceEnvelope.density_norm_le n α β w0 δ r 0 b ℓ P
      hδ.1 hδ.2 hA.le p hp
  · exact KFCausalJointSourceConfluenceEnvelope.responseBound_integrable n α β w0 r 0 b ℓ P hβ hAw hCw
  · exact Filter.Eventually.of_forall (density_tendsto n α β w0 r b ℓ P)

theorem response_integral_tendsto (n : ℕ) (α β w0 : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ)
    (hw0 : 1 ≤ w0) (hβ : 0 < β) (hA : 0 < α*area r)
    (hC : 0 < α*area r-8*β*r.im^2) :
    Tendsto (fun δ : ℝ => ∫ p, response n α β w0 δ r v b ℓ P p ∂jointMeasure)
      (𝓝[>] 0) (𝓝 (∫ p, limitResponse n α β w0 r v b ℓ P p ∂jointMeasure)) := by
  obtain ⟨hAw,hCw⟩ := KFCausalJointFourierDilationQuartic.width_floors α r w0 β hw0 hA hC
  apply tendsto_integral_filter_of_dominated_convergence (responseBound n α β w0 r v b ℓ P)
  · exact Filter.Eventually.of_forall (fun δ => (response_continuous n α β w0 δ r v b ℓ P).aestronglyMeasurable)
  · filter_upwards [spacing_eventually] with δ hδ
    filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
    exact KFCausalJointSourceConfluenceEnvelope.response_norm_le n α β w0 δ r v b ℓ P
      hδ.1 hδ.2 hA.le p hp
  · exact KFCausalJointSourceConfluenceEnvelope.responseBound_integrable n α β w0 r v b ℓ P hβ hAw hCw
  · exact Filter.Eventually.of_forall (response_tendsto n α β w0 r v b ℓ P)

theorem original_energy_tendsto (n : ℕ) (α β w0 : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ)
    (hw0 : 1 ≤ w0) (hβ : 0 < β) (hA : 0 < α*area r)
    (hC : 0 < α*area r-8*β*r.im^2) :
    Tendsto (fun δ : ℝ => ∫ p, positiveDensity (n+1) α β (widths n w0 δ) r
      (coefficients n w0 δ) (fun i => exponentialProfile (sources n δ b ℓ i) 1 P) p ∂jointMeasure)
      (𝓝[>] 0) (𝓝 (∫ p, limitDensity n α β w0 r b ℓ P p ∂jointMeasure)) := by
  apply Tendsto.congr' _ (density_integral_tendsto n α β w0 r b ℓ P hw0 hβ hA hC)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => (density_joint n α β w0 δ hw0 hδ r b ℓ P p).symm)

theorem original_response_tendsto (n : ℕ) (α β w0 : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ)
    (hw0 : 1 ≤ w0) (hβ : 0 < β) (hA : 0 < α*area r)
    (hC : 0 < α*area r-8*β*r.im^2) :
    Tendsto (fun δ : ℝ => ∫ p : Joint,
      KFCausalJointNeutralFourierOuterDensity.spatialQuarticResponse (n+1) α β (widths n w0 δ)
        (sources n δ b ℓ) (coefficients n w0 δ) (fun _ => P) r v
          p.1.1 (p.1.2 0) p.2 (p.1.2 1) ∂jointMeasure)
      (𝓝[>] 0) (𝓝 (∫ p, limitResponse n α β w0 r v b ℓ P p ∂jointMeasure)) := by
  apply Tendsto.congr' _ (response_integral_tendsto n α β w0 r v b ℓ P hw0 hβ hA hC)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => (spatial_response_eq n α β w0 δ hw0 hδ r v b ℓ P p).symm)

theorem actual_energy_tendsto (n : ℕ) (α β w0 ε y s : ℝ) (b ℓ : ℂ) (P : Polynomial ℂ)
    (hw0 : 1 ≤ w0) (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Tendsto (fun δ : ℝ => ∫ p, positiveDensity (n+1) α β (widths n w0 δ) (scale ε y s)
      (coefficients n w0 δ) (fun i => exponentialProfile (sources n δ b ℓ i) 1 P) p ∂jointMeasure)
      (𝓝[>] 0) (𝓝 (∫ p, limitDensity n α β w0 (scale ε y s) b ℓ P p ∂jointMeasure)) := by
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  exact original_energy_tendsto n α β w0 _ b ℓ P hw0 hβ ha hc

theorem actual_response_tendsto (n : ℕ) (α β w0 ε y s : ℝ) (b ℓ : ℂ) (P : Polynomial ℂ)
    (hw0 : 1 ≤ w0) (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Tendsto (fun δ : ℝ => ∫ p : Joint,
      KFCausalJointNeutralFourierOuterDensity.spatialQuarticResponse (n+1) α β (widths n w0 δ)
        (sources n δ b ℓ) (coefficients n w0 δ) (fun _ => P) (scale ε y s)
          (deriv (scale ε y) s) p.1.1 (p.1.2 0) p.2 (p.1.2 1) ∂jointMeasure)
      (𝓝[>] 0) (𝓝 (∫ p, limitResponse n α β w0 (scale ε y s)
        (deriv (scale ε y) s) b ℓ P p ∂jointMeasure)) := by
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  exact original_response_tendsto n α β w0 _ _ b ℓ P hw0 hβ ha hc

#print axioms density_integral_tendsto
#print axioms limit_density_joint
#print axioms limit_density_derivative
#print axioms response_integral_tendsto
#print axioms original_energy_tendsto
#print axioms original_response_tendsto
#print axioms actual_energy_tendsto
#print axioms actual_response_tendsto
end
end UnifiedTheory.Audit.KFCausalJointSourceConfluenceLimit
