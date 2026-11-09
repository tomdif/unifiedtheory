/- Full-Joint integrability of the genuine joint confluence limits,
derived from the fixed-order domination already proved for finite packets. -/
import UnifiedTheory.Audit.KFCausalJointSourceConfluenceLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointSourceConfluenceIntegrability
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalJointSourceConfluenceFactors
open KFCausalJointSourceConfluenceEnvelope (responseBound)

theorem density_continuous (n : ℕ) (α β w : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) :
    Continuous (limitDensity n α β w r b ℓ P) := by
  unfold limitDensity limitFactor Q
    KFCausalClusteredClockFactors.E KFCausalClusteredClockFactors.Z
    KFCausalClusteredClockFactors.N KFCausalClusteredClockFactors.G KFCausalClusteredClockFactors.F
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
  fun_prop

theorem response_continuous (n : ℕ) (α β w : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) :
    Continuous (limitResponse n α β w r v b ℓ P) := by
  unfold limitResponse limitComponent limitFactor limitSlope Q B1 Qd
    KFCausalClusteredClockFactors.B0 KFCausalClusteredClockFactors.E KFCausalClusteredClockFactors.Ed
    KFCausalClusteredClockFactors.Z KFCausalClusteredClockFactors.Zd
    KFCausalClusteredClockFactors.N KFCausalClusteredClockFactors.Nd
    KFCausalClusteredClockFactors.G KFCausalClusteredClockFactors.Gd
    KFCausalClusteredClockFactors.F KFCausalClusteredClockFactors.Fd
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
  fun_prop

private theorem spacing : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ ≤ 1 := by
  have hlt : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hlt] with δ hp hq
  exact ⟨hp,hq.le⟩

theorem density_bound (n : ℕ) (α β w : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ)
    (hA : 0 ≤ α*area r) (p : Joint) (hp : 0 ≤ p.2) :
    ‖limitDensity n α β w r b ℓ P p‖ ≤ responseBound n α β w r 0 b ℓ P p := by
  apply le_of_tendsto ((density_tendsto n α β w r b ℓ P p).norm)
  filter_upwards [spacing] with δ hδ
  exact KFCausalJointSourceConfluenceEnvelope.density_norm_le n α β w δ r 0 b ℓ P hδ.1 hδ.2 hA p hp

theorem response_bound (n : ℕ) (α β w : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ)
    (hA : 0 ≤ α*area r) (p : Joint) (hp : 0 ≤ p.2) :
    ‖limitResponse n α β w r v b ℓ P p‖ ≤ responseBound n α β w r v b ℓ P p := by
  apply le_of_tendsto ((response_tendsto n α β w r v b ℓ P p).norm)
  filter_upwards [spacing] with δ hδ
  exact KFCausalJointSourceConfluenceEnvelope.response_norm_le n α β w δ r v b ℓ P hδ.1 hδ.2 hA p hp

theorem density_integrable (n : ℕ) (α β w : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ)
    (hw : 1 ≤ w) (hβ : 0 < β) (hA : 0 < α*area r)
    (hC : 0 < α*area r-8*β*r.im^2) :
    Integrable (limitDensity n α β w r b ℓ P) jointMeasure := by
  obtain ⟨hAw,hCw⟩ := KFCausalJointFourierDilationQuartic.width_floors α r w β hw hA hC
  apply (KFCausalJointSourceConfluenceEnvelope.responseBound_integrable n α β w r 0 b ℓ P hβ hAw hCw).mono'
    (density_continuous n α β w r b ℓ P).aestronglyMeasurable
  filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
  exact density_bound n α β w r b ℓ P hA.le p hp

theorem response_integrable (n : ℕ) (α β w : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ)
    (hw : 1 ≤ w) (hβ : 0 < β) (hA : 0 < α*area r)
    (hC : 0 < α*area r-8*β*r.im^2) :
    Integrable (limitResponse n α β w r v b ℓ P) jointMeasure := by
  obtain ⟨hAw,hCw⟩ := KFCausalJointFourierDilationQuartic.width_floors α r w β hw hA hC
  apply (KFCausalJointSourceConfluenceEnvelope.responseBound_integrable n α β w r v b ℓ P hβ hAw hCw).mono'
    (response_continuous n α β w r v b ℓ P).aestronglyMeasurable
  filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
  exact response_bound n α β w r v b ℓ P hA.le p hp

theorem density_nonnegative (n : ℕ) (α β w : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    0 ≤ limitDensity n α β w r b ℓ P p := by unfold limitDensity; positivity

#print axioms density_continuous
#print axioms response_continuous
#print axioms density_bound
#print axioms response_bound
#print axioms density_integrable
#print axioms response_integrable
#print axioms density_nonnegative
end
end UnifiedTheory.Audit.KFCausalJointSourceConfluenceIntegrability
