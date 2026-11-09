/- Entire-clock domination with independent coefficients for each block.
The amplitude mass controls absolute size; cancellations remain in the
actual energy and response. No uniform relative estimate is assumed. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredGlobalEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockBounds
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredDensity
open KFCausalCorrelatedClusteredGlobalEnvelope
open KFCausalClockFloorRelativeShift (scale)

variable {m : ℕ} (f : Family m)

theorem all_coefficients_envelope (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ ε y s : ℝ, 0 < ε → |y| ≤ Real.pi*ε/3 → ∀ c : Fin m → ℂ, ∀ p, 0 ≤ p.2 →
        (∀ δ : ℝ, 0 < δ →
          ‖density (reweight f c) α β δ (scale ε y s) p‖ ≤ coefficientMass c*D p ∧
          ‖response (reweight f c) α β δ (scale ε y s) (deriv (scale ε y) s) p‖ ≤ coefficientMass c*D p) ∧
        ‖limitDensity (reweight f c) α β (scale ε y s) p‖ ≤ coefficientMass c*D p ∧
        ‖limitResponse (reweight f c) α β (scale ε y s) (deriv (scale ε y) s) p‖ ≤ coefficientMass c*D p := by
  obtain ⟨D,hDi,hD0,hD⟩ := global_envelope f α β hα hβ hw
  refine ⟨D,hDi,hD0,?_⟩
  intro ε y s hε hy c p hp
  have hA : 0 ≤ α*KFCausalReciprocalGaussianCoordinates.area (scale ε y s) :=
    (mul_pos hα (KFCausalNeutralPlaneClockGeometry.scale_square_re_positive ε y s hε hy)).le
  have hb := (fullBound_reweight f c α β (scale ε y s) (deriv (scale ε y) s) p).trans
    (mul_le_mul_of_nonneg_left (hD ε y s hε hy p hp) (coefficientMass_nonnegative c))
  have he (δ : ℝ) (hδ : 0 < δ) :=
    (KFCausalCorrelatedClusteredBounds.density_norm_le (reweight f c) α β δ hδ
      (scale ε y s) (deriv (scale ε y) s) hA p hp).trans hb
  have hr (δ : ℝ) (hδ : 0 < δ) :=
    (KFCausalCorrelatedClusteredBounds.response_norm_le (reweight f c) α β δ hδ
      (scale ε y s) (deriv (scale ε y) s) hA p hp).trans hb
  refine ⟨fun δ hδ => ⟨he δ hδ,hr δ hδ⟩,?_,?_⟩
  · apply le_of_tendsto (density_tendsto (reweight f c) α β (scale ε y s) p).norm
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact he δ hδ
  · apply le_of_tendsto (response_tendsto (reweight f c) α β (scale ε y s) (deriv (scale ε y) s) p).norm
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hr δ hδ

theorem coefficientMass_integrable (c : ℝ → Fin m → ℂ)
    (hc : ∀ i, MemLp (fun s => c s i) 2 volume) : Integrable (fun s => coefficientMass (c s)) := by
  exact integrable_finset_sum Finset.univ (fun i _ => (hc i).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))

theorem physical_coefficientMass_integrable (ε y : ℝ) (a p : Fin m → ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (ha : ∀ i, 0 < a i) :
    Integrable (fun s => coefficientMass (fun i =>
      KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε (a i) (p i) y s)) :=
  coefficientMass_integrable _ (fun i => KFCausalShiftedClockAmplitude.clockAmplitude_memLp
    ε (a i) (p i) y hε (ha i) hy)

#print axioms all_coefficients_envelope
#print axioms coefficientMass_integrable
#print axioms physical_coefficientMass_integrable
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockBounds
