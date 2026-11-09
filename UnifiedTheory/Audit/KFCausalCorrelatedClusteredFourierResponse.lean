/- The original full correlated clustered response is exactly the
ordered integral of the explicit quartic Fourier response. The spatial
response supplies all outer integrability hypotheses. -/
import UnifiedTheory.Audit.KFCausalJointNeutralFourierOuterDensity
import UnifiedTheory.Audit.KFCausalJointNeutralFourierOuterFubini
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredResponseLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierResponse
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredDensity (density response)
open KFCausalJointNeutralFourierOuterDensity (spatialQuarticResponse)
open KFCausalJointNeutralFourierMarginal (quarticResponse)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalReciprocalNeutralClockDerivative (totalResponse)

variable {m : ℕ} (f : Family m) (α β δ : ℝ) (hδ : 0 < δ)
include hδ

theorem response_spatial (r rd : ℂ) (u v x Y : ℝ) :
    response f α β δ r rd ((u,![v,x]),Y) =
      spatialQuarticResponse (count f) α β (widths f δ) (sources f) (coefficients f δ)
        (polynomials f) r rd u v Y x := by
  let curve : ℝ → ℂ := fun t => r+(t:ℂ)*rd
  have hr : HasDerivAt curve rd 0 := by
    simpa only [curve,id_eq,Complex.ofReal_one,one_mul] using
      ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const rd).const_add r
  have hA := KFCausalCorrelatedClusteredDensity.density_derivative f α β δ hδ
    curve rd 0 ((u,![v,x]),Y) hr
  have hB := KFCausalJointNeutralFourierOuterDensity.density_derivative (count f) α β
    (widths f δ) (sources f) (coefficients f δ) (polynomials f) curve rd 0 u v x Y hr
  simpa only [curve,Complex.ofReal_zero,zero_mul,add_zero] using hA.unique hB

variable (hβ : 0 < β)
include hδ hβ

theorem response_slice_integral (r rd : ℂ) (u v Y : ℝ) :
    (∫ x, response f α β δ r rd ((u,![v,x]),Y)) =
      ∫ k, quarticResponse (count f) α β (widths f δ) (sources f) (coefficients f δ)
        (polynomials f) r rd u v Y k := by
  simp_rw [response_spatial f α β δ hδ]
  exact KFCausalJointNeutralFourierOuterDensity.spatialQuarticResponse_integral
    (count f) α β (widths f δ) (sources f) (coefficients f δ) (polynomials f) hβ r rd u v Y

theorem response_integral (r rd : ℂ)
    (ha : 0 < α*KFCausalReciprocalGaussianCoordinates.area r)
    (hc : 0 < α*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2) :
    (∫ p, response f α β δ r rd p ∂jointMeasure) =
      ∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ, ∫ k : ℝ,
        quarticResponse (count f) α β (widths f δ) (sources f) (coefficients f δ)
          (polynomials f) r rd u v Y k := by
  have hi := (KFCausalCorrelatedClusteredIntegrals.integrability f α β δ hδ r rd hβ ha hc).2.1
  rw [KFCausalJointNeutralFourierIntegral.joint_integral_iterated _ hi]
  simp_rw [response_slice_integral f α β δ hδ hβ]

theorem outer_marginals_integrable (r rd : ℂ)
    (ha : 0 < α*KFCausalReciprocalGaussianCoordinates.area r)
    (hc : 0 < α*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2) :
    Integrable (fun Y : ℝ => ∫ u : ℝ, ∫ v : ℝ, ∫ k : ℝ,
      quarticResponse (count f) α β (widths f δ) (sources f) (coefficients f δ)
        (polynomials f) r rd u v Y k) (volume.restrict (Set.Ioi (0:ℝ))) ∧
    (∀ᵐ Y : ℝ ∂volume.restrict (Set.Ioi (0:ℝ)),
      Integrable (fun u : ℝ => ∫ v : ℝ, ∫ k : ℝ,
        quarticResponse (count f) α β (widths f δ) (sources f) (coefficients f δ)
          (polynomials f) r rd u v Y k)) ∧
    (∀ᵐ Y : ℝ ∂volume.restrict (Set.Ioi (0:ℝ)), ∀ᵐ u : ℝ,
      Integrable (fun v : ℝ => ∫ k : ℝ,
        quarticResponse (count f) α β (widths f δ) (sources f) (coefficients f δ)
          (polynomials f) r rd u v Y k)) := by
  have hi := (KFCausalCorrelatedClusteredIntegrals.integrability f α β δ hδ r rd hβ ha hc).2.1
  have ho := KFCausalJointNeutralFourierOuterFubini.joint_marginals_integrable _ hi
  simpa only [response_slice_integral f α β δ hδ hβ] using ho

variable (ε y : ℝ) (hα : 0 < α) (hw : 32*β ≤ α) (hε : 0 < ε)
  (hy : |y| ≤ Real.pi*ε/3)
include hα hw hε hy

theorem actual_totalResponse_integral (s : ℝ) :
    totalResponse (count f) ε y α β (widths f δ) (sources f) (polynomials f)
      (fun _ => coefficients f δ) s =
      Real.pi/4*(∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ, ∫ k : ℝ,
        quarticResponse (count f) α β (widths f δ) (sources f) (coefficients f δ)
          (polynomials f) (scale ε y s) (deriv (scale ε y) s) u v Y k) := by
  have hf := KFCausalClusteredResponseLimit.actual_width_floors α β ε y hα hβ hw hε hy s
  have hq := KFCausalChargedPairCompactGeometry.widthFloor_positive α hα
  rw [KFCausalCorrelatedClusteredResponseLimit.actual_totalResponse_integral f α β ε y
    hα hβ hw hε hy δ hδ s,
    response_integral f α β δ hδ hβ _ _ (hq.trans_le hf.1) (hq.trans_le hf.2)]

theorem actual_outer_marginals_integrable (s : ℝ) :
    Integrable (fun Y : ℝ => ∫ u : ℝ, ∫ v : ℝ, ∫ k : ℝ,
      quarticResponse (count f) α β (widths f δ) (sources f) (coefficients f δ)
        (polynomials f) (scale ε y s) (deriv (scale ε y) s) u v Y k)
        (volume.restrict (Set.Ioi (0:ℝ))) ∧
    (∀ᵐ Y : ℝ ∂volume.restrict (Set.Ioi (0:ℝ)),
      Integrable (fun u : ℝ => ∫ v : ℝ, ∫ k : ℝ,
        quarticResponse (count f) α β (widths f δ) (sources f) (coefficients f δ)
          (polynomials f) (scale ε y s) (deriv (scale ε y) s) u v Y k)) ∧
    (∀ᵐ Y : ℝ ∂volume.restrict (Set.Ioi (0:ℝ)), ∀ᵐ u : ℝ,
      Integrable (fun v : ℝ => ∫ k : ℝ,
        quarticResponse (count f) α β (widths f δ) (sources f) (coefficients f δ)
          (polynomials f) (scale ε y s) (deriv (scale ε y) s) u v Y k)) := by
  have hf := KFCausalClusteredResponseLimit.actual_width_floors α β ε y hα hβ hw hε hy s
  have hq := KFCausalChargedPairCompactGeometry.widthFloor_positive α hα
  exact outer_marginals_integrable f α β δ hδ hβ _ _ (hq.trans_le hf.1) (hq.trans_le hf.2)

#print axioms response_spatial
#print axioms response_slice_integral
#print axioms response_integral
#print axioms outer_marginals_integrable
#print axioms actual_totalResponse_integral
#print axioms actual_outer_marginals_integrable
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierResponse
