/- The original common-complex-source mass spatial response is
exactly the corrected coherent marginal plus its dilation Jacobian.
Every full Joint and reordered integral is absolutely integrable. -/
import UnifiedTheory.Audit.KFCausalCommonComplexMassResponseMarginal
import UnifiedTheory.Audit.KFCausalFiniteChannelCoolingSplit
import UnifiedTheory.Audit.KFCausalChargedMassScoreAttachment
import UnifiedTheory.Audit.KFCausalChargedMarginalReordering

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexMassJointResponse
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalCommonComplexQuarticJointAngular (source)
open KFCausalChargedMassScoreIBP (energyDensity fieldDensity coolingDensity)
open KFCausalJointFourierDilationRepresentation (fieldDensity)
open KFCausalCorrelatedFourierCoolingResponse (fieldCooling)
open KFCausalCommonRealGaussianEnergy (neutralMoment)
open KFCausalReciprocalWedgeGeometry (gamma)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalGaussianCoordinates (area)

variable (n : ℕ) (α β A D : ℝ) (w : Fin n→ℝ) (r rd : ℂ) (c : Fin n→ℂ) (ell : ℝ)

theorem original_energy_density (p : Joint) :
    KFCausalJointFourierDilationRepresentation.fieldDensity n α β w (fun _=>source A D) c
      (fun _=>1) r ell 0 1 p=KFCausalCommonComplexMassJointEnergy.energyDensity n α β A D w r c p := by
  rw [KFCausalJointFourierDilationRepresentation.density_zero,
    KFCausalJointFourierDilationRepresentation.fieldLine_factor]
  have hn (t : ℝ) : ‖(t:ℂ)^1‖^2=t^2 := by
    simp only [pow_one,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simp only [norm_mul,mul_pow]
  simp only [KFCausalClusteredClockFactors.N]
  rw [hn,KFCausalReciprocalNeutralHolomorphic.gaussian_norm β r (p.1.2 0) (p.1.2 1)]
  simp only [KFCausalCommonComplexMassJointEnergy.energyDensity,
    KFCausalCommonComplexQuarticJointAngular.channel,KFCausalCommonComplexQuarticJointAngular.jointBase,
    KFCausalClusteredClockFactors.Z,pow_zero,one_mul]
  ring

private theorem gamma_re : 2*(gamma α r).re=α*(r.re^2-r.im^2) := by
  simp [gamma,pow_two,Complex.mul_re,Complex.mul_im]
  ring

variable (hα : 0<α) (hβ : 0<β) (hr : |r.im|<r.re) (hw : ∀i,0<w i)
    (hd : ∀i,8*β*r.im^2<2*(gamma α r).re*w i) (hi : rd.im=ell*r.im)
include hα hβ hr hw hd

omit hα hr hw in
private theorem actual_floors : (∀i,0<(w i*α)*area r) ∧
    ∀i,0<(w i*α)*area r-8*β*r.im^2 := by
  have hm (i : Fin n) : 0<(w i*α)*area r-8*β*r.im^2 := by
    have h := hd i
    rw [gamma_re] at h
    unfold area
    nlinarith only [h]
  refine ⟨fun i=>?_,hm⟩
  have h := hm i
  have hp : 0≤8*β*r.im^2 := by positivity
  linarith only [h,hp]

include hi
theorem cooling_integral :
    (∫p:Joint,fieldCooling n α β w (fun _=>source A D) c (fun _=>1) r rd ell 1 p ∂jointMeasure)=
      neutralMoment β A 0*
        (-(rd.re-ell*r.re)*(∫v,coolingDensity (1/(4*β)) (8*β*r.im^2) (4*D*r.im)
          (A/(2*β)) (fieldSlope r) n α r w (fun i=>c i*(w i:ℂ)) v)+
        (-2*(rd.re-ell*r.re)-3*ell)*(∫v,KFCausalChargedMassScoreIBP.fieldDensity (1/(4*β))
          (8*β*r.im^2) (4*D*r.im) (A/(2*β)) (fieldSlope r) n α r w (fun i=>c i*(w i:ℂ)) v)) := by
  have hfloors := actual_floors n α β w r hβ hd
  let f := fieldCooling n α β w (fun _=>source A D) c (fun _=>1) r rd ell 1
  have hf := KFCausalFiniteChannelCoolingSplit.cooling_integrable n α β w (fun _=>source A D) c
    (fun _=>1) r rd ell hβ hfloors.1 hfloors.2 hi 1
  have ho := KFCausalChargedMarginalReordering.outer_integrable f hf
  rw [Measure.volume_eq_prod ℝ ℝ] at ho
  rw [KFCausalChargedMarginalReordering.integral_order _ hf,Measure.volume_eq_prod ℝ ℝ,
    integral_prod _ ho]
  change (∫v : ℝ,∫x : ℝ,∫z : ℝ×ℝ,fieldCooling n α β w (fun _=>source A D) c
    (fun _=>1) r rd ell 1 ((z.1,![v,x]),z.2) ∂planeMeasure)=_
  simp_rw [KFCausalCommonComplexMassResponseMarginal.cooling_neutral_integral n α β A D w r rd c ell hα hr hw hβ]
  have hL := KFCausalChargedMassScoreIBP.densities_integrable n α r (8*β*r.im^2) (4*D*r.im)
    w (fun i=>c i*(w i:ℂ)) hα hr hw hd (1/(4*β)) (A/(2*β)) (fieldSlope r)
  rw [integral_const_mul,integral_add (hL.2.2.2.const_mul _) (hL.2.1.const_mul _),
    integral_const_mul,integral_const_mul]

omit hi in
theorem energy_integral :
    (∫p:Joint,KFCausalCommonComplexMassJointEnergy.energyDensity n α β A D w r c p ∂jointMeasure)=
      neutralMoment β A 0*(∫v,energyDensity (1/(4*β)) (8*β*r.im^2) (4*D*r.im) (A/(2*β))
        (fieldSlope r) n α r w (fun i=>c i*(w i:ℂ)) v) := by
  have hp := KFCausalChargedCoolingFixedV.actual_gamma_re_positive α r hα hr
  have hj := KFCausalCommonComplexMassJointEnergy.energy_integral n α β A D w r c hβ hp hw hd
  have he := (KFCausalChargedMassScoreAttachment.energy_field_tilt n α r (8*β*r.im^2) (4*D*r.im)
    w (fun i=>c i*(w i:ℂ)) hα hr hw hd (1/(4*β)) (A/(2*β)) (fieldSlope r)).1
  exact hj.trans (congrArg (fun x : ℝ=>neutralMoment β A 0*x) he)

theorem response_integral :
    (∫p:Joint,KFCausalJointNeutralFourierOuterDensity.spatialFieldResponse n α β w
      (fun _=>source A D) c (fun _=>1) r rd p.1.1 (p.1.2 0) p.2 1 (p.1.2 1) ∂jointMeasure)=
      neutralMoment β A 0*
        (-4*ell*(∫v,energyDensity (1/(4*β)) (8*β*r.im^2) (4*D*r.im) (A/(2*β))
          (fieldSlope r) n α r w (fun i=>c i*(w i:ℂ)) v)-
        (rd.re-ell*r.re)*(∫v,coolingDensity (1/(4*β)) (8*β*r.im^2) (4*D*r.im)
          (A/(2*β)) (fieldSlope r) n α r w (fun i=>c i*(w i:ℂ)) v)+
        (-2*(rd.re-ell*r.re)-3*ell)*(∫v,KFCausalChargedMassScoreIBP.fieldDensity (1/(4*β))
          (8*β*r.im^2) (4*D*r.im) (A/(2*β)) (fieldSlope r) n α r w (fun i=>c i*(w i:ℂ)) v)) := by
  have hfloors := actual_floors n α β w r hβ hd
  rw [KFCausalFiniteChannelCoolingSplit.response_integral n α β w (fun _=>source A D) c
    (fun _=>1) r rd ell hβ hfloors.1 hfloors.2 hi 1]
  simp_rw [original_energy_density n α β A D w r c ell]
  rw [energy_integral n α β A D w r c hα hβ hr hw hd,
    cooling_integral n α β A D w r rd c ell hα hβ hr hw hd hi]
  ring

#print axioms original_energy_density
#print axioms cooling_integral
#print axioms energy_integral
#print axioms response_integral
end
end UnifiedTheory.Audit.KFCausalCommonComplexMassJointResponse
