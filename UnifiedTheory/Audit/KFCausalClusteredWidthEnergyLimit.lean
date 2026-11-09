/- The actual positive joint energy integral converges as admissible
charged widths coalesce. Domination is supplied by a proved integrable
charged polynomial density, not by an assumed response estimate. -/
import UnifiedTheory.Audit.KFCausalClusteredWidthDensityIntegrability
import UnifiedTheory.Audit.KFCausalReciprocalNeutralKernelDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalClusteredWidthEnergyLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalClusteredWidthProfiles (widths coefficients limitDensity)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity pairing)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalClockFloorRelativeShift (scale)

theorem ae_halfline : ∀ᵐ p : Joint ∂jointMeasure, 0 ≤ p.2 := by
  have hy : ∀ᵐ y : ℝ ∂volume.restrict (Set.Ioi 0), 0 ≤ y :=
    (ae_restrict_mem measurableSet_Ioi).mono (fun _ h => h.le)
  exact MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hy

theorem positiveDensity_continuous (n : ℕ) (α β δ : ℝ) (r b : ℂ) (P : Polynomial ℂ) :
    Continuous (positiveDensity (n+1) α β (widths n δ) r (coefficients n δ)
      (fun _ => exponentialProfile b 1 P)) := by
  unfold positiveDensity KFCausalReciprocalNeutralPositiveForm.profileSum
    KFCausalReciprocalWedgeLaplace.laplaceSum KFCausalReciprocalNeutralLaplace.weight
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
    exponentialProfile KFCausalQuarticPlaneDomination.potential
  fun_prop

theorem integral_tendsto (n : ℕ) (α β : ℝ) (r b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hA : 0 < α*KFCausalReciprocalGaussianCoordinates.area r)
    (hC : 0 < α*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2) :
    Tendsto (fun δ : ℝ => ∫ p, positiveDensity (n+1) α β (widths n δ) r
        (coefficients n δ) (fun _ => exponentialProfile b 1 P) p ∂jointMeasure)
      (𝓝[>] 0) (𝓝 (∫ p, limitDensity n α β r (exponentialProfile b 1 P) p ∂jointMeasure)) := by
  apply tendsto_integral_filter_of_dominated_convergence (limitDensity n α β r (exponentialProfile b 1 P))
  · exact Filter.Eventually.of_forall (fun δ => (positiveDensity_continuous n α β δ r b P).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_halfline] with p hp
    rw [Real.norm_eq_abs,abs_of_nonneg (KFCausalReciprocalNeutralPositiveForm.positiveDensity_nonneg _ _ _ _ _ _ _ _)]
    exact KFCausalClusteredWidthProfiles.positiveDensity_le_limit n α β δ r _ hδ hA.le p hp
  · exact KFCausalClusteredWidthDensityIntegrability.limitDensity_integrable n α β r b P hβ hA hC
  · exact Filter.Eventually.of_forall (KFCausalClusteredWidthProfiles.positiveDensity_tendsto n α β r _)

theorem actual_integral_tendsto (n : ℕ) (α β ε y s : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Tendsto (fun δ : ℝ => ∫ p, positiveDensity (n+1) α β (widths n δ) (scale ε y s)
        (coefficients n δ) (fun _ => exponentialProfile b 1 P) p ∂jointMeasure)
      (𝓝[>] 0) (𝓝 (∫ p, limitDensity n α β (scale ε y s) (exponentialProfile b 1 P) p ∂jointMeasure)) := by
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hw hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  exact integral_tendsto n α β _ b P hβ ha hc

theorem actual_pairing_integral (n : ℕ) (α β ε y s δ : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hδ : 0 < δ) :
    (pairing (n+1) α β (widths n δ) (scale ε y s) (coefficients n δ) (coefficients n δ)
      (fun _ => exponentialProfile b 1 P)).re = Real.pi/4*
      ∫ p, positiveDensity (n+1) α β (widths n δ) (scale ε y s) (coefficients n δ)
        (fun _ => exponentialProfile b 1 P) p ∂jointMeasure := by
  have hwi := KFCausalClusteredWidthProfiles.widths_admissible n δ hδ.le
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hw hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  have hpos (i j : Fin (n+1)) := KFCausalReciprocalCrossGeometry.widths_positive α β
    (widths n δ i) (widths n δ j) (scale ε y s) (hwi i) (hwi j) ha hc hβ
  rw [KFCausalReciprocalNeutralPositiveForm.pairing_integral (n+1) α β _ _ _ _
    (fun i j => (hpos i j).2.1)
    (fun i j => KFCausalReciprocalNeutralPlaneIntegrability.actual_plane_integrable α β ε y s _ _
      hα hβ hw hε hy (hwi i) (hwi j) b b P P)
    (fun i => by have := hwi i; linarith) (fun i j => (hpos i j).1),Complex.ofReal_re]

theorem actual_pairing_tendsto (n : ℕ) (α β ε y s : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Tendsto (fun δ : ℝ => (pairing (n+1) α β (widths n δ) (scale ε y s)
        (coefficients n δ) (coefficients n δ) (fun _ => exponentialProfile b 1 P)).re)
      (𝓝[>] 0) (𝓝 (Real.pi/4*∫ p, limitDensity n α β (scale ε y s)
        (exponentialProfile b 1 P) p ∂jointMeasure)) := by
  apply Tendsto.congr' _ ((actual_integral_tendsto n α β ε y s b P hα hβ hw hε hy).const_mul (Real.pi/4))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (actual_pairing_integral n α β ε y s δ b P hα hβ hw hε hy hδ).symm

theorem actual_totalEnergy_tendsto (n : ℕ) (α β ε y s : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Tendsto (fun δ : ℝ => KFCausalReciprocalNeutralClockDerivative.totalEnergy
        (n+1) ε y α β (widths n δ) (fun _ => b) (fun _ => P) (fun _ => coefficients n δ) s)
      (𝓝[>] 0) (𝓝 (Real.pi/4*∫ p, limitDensity n α β (scale ε y s)
        (exponentialProfile b 1 P) p ∂jointMeasure)) := by
  apply Tendsto.congr' _ (actual_pairing_tendsto n α β ε y s b P hα hβ hw hε hy)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [KFCausalReciprocalNeutralKernelDerivative.pairing_totalEnergy (n+1) ε y α β
    (widths n δ) (fun _ => b) (fun _ => P) (fun _ => coefficients n δ) hε hy hα hβ hw
    (KFCausalClusteredWidthProfiles.widths_admissible n δ hδ.le),Complex.ofReal_re]

#print axioms ae_halfline
#print axioms positiveDensity_continuous
#print axioms integral_tendsto
#print axioms actual_integral_tendsto
#print axioms actual_pairing_integral
#print axioms actual_pairing_tendsto
#print axioms actual_totalEnergy_tendsto
end
end UnifiedTheory.Audit.KFCausalClusteredWidthEnergyLimit
