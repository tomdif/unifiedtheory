/- The exact dilation/cooling split for each original finite channel.
The actual spatial response has derived full Joint integrability;
no whole-integral derivative interchange is assumed. -/
import UnifiedTheory.Audit.KFCausalFiniteNeutralResponseIntegrability
import UnifiedTheory.Audit.KFCausalCorrelatedFourierCoolingResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFiniteChannelCoolingSplit
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalJointFourierDilationRepresentation (fieldDensity)
open KFCausalFiniteNeutralResponseIntegrability (value slope channelResponse)
open KFCausalJointNeutralFourierOuterDensity (spatialFieldResponse)
open KFCausalCorrelatedFourierCoolingResponse (fieldCooling)

variable (n : ℕ) (α β : ℝ) (w : Fin n→ℝ) (b c : Fin n→ℂ) (P : Fin n→Polynomial ℂ)

theorem density_eq (r : ℂ) (ell : ℝ) (j : ℕ) (p : Joint) :
    fieldDensity n α β w b c P r ell 0 j p=‖value n α β w b c P j r p‖^2 := by
  rw [KFCausalJointFourierDilationRepresentation.density_eq]
  simp only [KFCausalCorrelatedDilationDifferentiation.value,
    KFCausalCorrelatedDilationPolynomials.packet,KFCausalCorrelatedDilationPolynomials.prefactor,
    KFCausalCorrelatedDilationPolynomials.field,KFCausalCorrelatedDilationEnvelope.geometry,
    KFCausalCorrelatedDilationEnvelope.scale,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul,
    pow_zero,mul_one,value,KFCausalClusteredClockFactors.limitFactor,KFCausalClusteredClockFactors.F,mul_assoc]

theorem spatial_response_eq (r rd : ℂ) (j : ℕ) (p : Joint) :
    spatialFieldResponse n α β w b c P r rd p.1.1 (p.1.2 0) p.2 j (p.1.2 1)=
      channelResponse n α β w b c P j r rd p := by
  let curve : ℝ→ℂ := fun t=>r+(t:ℂ)*rd
  have hc : HasDerivAt curve rd 0 := by
    simpa only [curve,id_eq,Complex.ofReal_one,one_mul] using
      ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const rd).const_add r
  have hd := KFCausalNeutralFourierMovingJet.actual_square_derivative n β b P α w c curve rd
    0 p.1.1 (p.1.2 0) (p.1.2 1) p.2 j hc
  have he (t : ℝ) : ‖KFCausalNeutralFourierField.fieldLine n β b
      (KFCausalNeutralJointCurvatureForm.coefficients n w c
        (KFCausalReciprocalWedgeGeometry.chart α (curve t) (p.1.1^2+(p.1.2 0)^2) p.2)) P j
      (KFCausalChargedPairCoordinates.fieldSlope (curve t)*p.1.2 0)
      (2*(curve t).im*p.1.2 0) (p.1.2 1)‖^2=‖value n α β w b c P j (curve t) p‖^2 := by
    simpa only [KFCausalClusteredClockFactors.Z] using
      (KFCausalJointFourierDilationRepresentation.density_zero n α β w b c P (curve t) 0 j p).symm.trans
        (density_eq n α β w b c P (curve t) 0 j p)
  simp_rw [he] at hd
  have hd' := KFCausalNeutralQuarticBoundary.norm_square_derivative
    (fun t=>value n α β w b c P j (curve t) p)
    (fun t=>slope n α β w b c P j (curve t) rd p) 0
    (KFCausalFiniteNeutralResponseIntegrability.value_derivative n α β w b c P j curve rd 0 p hc)
  simpa only [curve,Complex.ofReal_zero,zero_mul,add_zero,channelResponse,spatialFieldResponse] using hd.unique hd'

variable (r rd : ℂ) (ell : ℝ) (hβ : 0<β)
    (hA : ∀i,0<(w i*α)*area r) (hC : ∀i,0<(w i*α)*area r-8*β*r.im^2)
    (hi : rd.im=ell*r.im)
include hβ hA hC hi

theorem cooling_integrable (j : ℕ) :
    Integrable (fieldCooling n α β w b c P r rd ell j) jointMeasure := by
  have hpoint (p : Joint) : fieldCooling n α β w b c P r rd ell j p=
      channelResponse n α β w b c P j r rd p-
        KFCausalJointFourierDilationResponse.response n α β w b c P r ell j p := by
    rw [←spatial_response_eq]
    exact (KFCausalJointFourierDilationJet.corrected_response n β b P α w c r rd ell
      p.1.1 (p.1.2 0) p.2 (p.1.2 1) j hi).symm
  have hr := KFCausalFiniteNeutralResponseIntegrability.channel_response_integrable
    n α β w b c P j r rd hβ hA hC
  have hd := KFCausalJointFourierDilationResponse.response_integrable n α β w b c P r ell hβ hA hC j
  exact (hr.sub hd).congr (Filter.Eventually.of_forall (fun p=>(hpoint p).symm))

theorem response_integral (j : ℕ) :
    (∫p:Joint,spatialFieldResponse n α β w b c P r rd p.1.1 (p.1.2 0) p.2 j (p.1.2 1) ∂jointMeasure)=
      -4*ell*(∫p,fieldDensity n α β w b c P r ell 0 j p ∂jointMeasure)+
        ∫p,fieldCooling n α β w b c P r rd ell j p ∂jointMeasure := by
  have hr := KFCausalFiniteNeutralResponseIntegrability.channel_response_integrable
    n α β w b c P j r rd hβ hA hC
  have hd := KFCausalJointFourierDilationResponse.response_integrable n α β w b c P r ell hβ hA hC j
  have he := integral_congr_ae (μ:=jointMeasure) (Filter.Eventually.of_forall (fun p : Joint =>
    KFCausalJointFourierDilationJet.corrected_response n β b P α w c r rd ell
      p.1.1 (p.1.2 0) p.2 (p.1.2 1) j hi))
  change (∫p:Joint,spatialFieldResponse n α β w b c P r rd p.1.1 (p.1.2 0) p.2 j (p.1.2 1)-
    KFCausalJointFourierDilationResponse.response n α β w b c P r ell j p ∂jointMeasure)=
      ∫p,fieldCooling n α β w b c P r rd ell j p ∂jointMeasure at he
  simp_rw [spatial_response_eq] at he ⊢
  rw [integral_sub hr hd,KFCausalJointFourierDilationResponse.response_integral n α β w b c P r ell hβ hA hC j] at he
  linarith only [he]

#print axioms density_eq
#print axioms spatial_response_eq
#print axioms cooling_integrable
#print axioms response_integral
end
end UnifiedTheory.Audit.KFCausalFiniteChannelCoolingSplit
