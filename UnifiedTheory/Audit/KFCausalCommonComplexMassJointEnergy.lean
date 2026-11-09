/- Exact full Joint mass-channel energy and its neutral marginal.
The original coherent source sum and all finite cross terms are retained;
full integrability is supplied before reordering. -/
import UnifiedTheory.Audit.KFCausalCommonComplexQuarticJointAngular
import UnifiedTheory.Audit.KFCausalCommonComplexMassNeutralIntegral
import UnifiedTheory.Audit.KFCausalChargedMassAngularLoss

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCommonComplexMassJointEnergy
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalCommonComplexQuarticJointAngular (source jointBase channel jointBase_factor channel_integrable)
open KFCausalCommonRealGaussianEnergy (neutralWeight neutralMoment)
open KFCausalChargedEvenMomentImaginaryBound (gamma)
open KFCausalChargedPairCoordinates (fieldSlope)

variable (n : ℕ) (alpha beta A D : ℝ) (w : Fin n→ℝ) (r : ℂ) (c : Fin n→ℂ)

def energyDensity (z : Joint) : ℝ := channel n alpha beta A D w r c (fieldSlope r) 0 2 z

variable (hbeta : 0<beta) (hp : 0<(gamma alpha r).re) (hw : ∀i,0<w i)
  (hd : ∀i,8*beta*r.im^2<2*(gamma alpha r).re*w i)
include hbeta hp hw hd

theorem density_integrable : Integrable (energyDensity n alpha beta A D w r c) jointMeasure :=
  channel_integrable n alpha beta A D w r c hbeta hp hw hd (fieldSlope r) 0 2

omit hp hw hd in
theorem energy_marginal (z : Charged) :
    (∫x:ℝ,energyDensity n alpha beta A D w r c ((z.1.1,![z.1.2,x]),z.2))=
      neutralMoment beta A 0*KFCausalChargedMassAngularLoss.energyDensity (1/(4*beta))
        (8*beta*r.im^2) (4*D*r.im) (A/(2*beta)) (fieldSlope r) (gamma alpha r)
        w (fun i=>c i*(w i:ℂ)) z := by
  have he (x:ℝ) : energyDensity n alpha beta A D w r c ((z.1.1,![z.1.2,x]),z.2)=
      ((x+fieldSlope r*z.1.2)^2*neutralWeight beta A x)*
        KFCausalChargedMassAngularLoss.base (gamma alpha r)
          (8*beta*r.im^2) (4*D*r.im) w (fun i=>c i*(w i:ℂ)) z := by
    simp only [energyDensity,channel,jointBase_factor,Matrix.cons_val_zero,
      Matrix.cons_val_one,pow_zero,one_mul,KFCausalChargedMassAngularLoss.base,
      KFCausalChargedQuarticAngularLoss.base]
    ring
  simp_rw [he]
  rw [integral_mul_const,KFCausalCommonComplexMassNeutralIntegral.quadratic_integral beta A _ hbeta]
  unfold KFCausalChargedMassAngularLoss.energyDensity
  ring

theorem energy_integral :
    (∫z,energyDensity n alpha beta A D w r c z ∂jointMeasure)=
      neutralMoment beta A 0*KFCausalChargedMassAngularLoss.energy (1/(4*beta))
        (8*beta*r.im^2) (4*D*r.im) (A/(2*beta)) (fieldSlope r) (gamma alpha r) w (fun i=>c i*(w i:ℂ)) := by
  have hi := density_integrable n alpha beta A D w r c hbeta hp hw hd
  rw [KFCausalJointChargedNeutralReordering.integral_order _ hi]
  simp only [energy_marginal n alpha beta A D w r c hbeta,integral_const_mul,
    KFCausalChargedMassAngularLoss.energy]

#print axioms density_integrable
#print axioms energy_marginal
#print axioms energy_integral
end
end UnifiedTheory.Audit.KFCausalCommonComplexMassJointEnergy
