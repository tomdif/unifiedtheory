/- The one-dimensional weighted score is attached to the literal
coherent charged integral by a measure-preserving coordinate reordering.
All Fubini integrability is supplied by the original Gaussian margin. -/
import UnifiedTheory.Audit.KFCausalChargedMassScoreIBP
import UnifiedTheory.Audit.KFCausalChargedQuarticScoreAttachment
import UnifiedTheory.Audit.KFCausalChargedMassAngularLoss

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedMassScoreAttachment
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalChargedCoolingMarginalScore (marginal)
open KFCausalReciprocalWedgeGeometry (gamma)
open KFCausalAngularMassGaussianSmoothing (weight weightSlope)

variable (n : ℕ) (α : ℝ) (r : ℂ) (d q : ℝ) (w : Fin n→ℝ) (c : Fin n→ℂ)
    (hα : 0<α) (hr : |r.im|<r.re) (hw : ∀i,0<w i)
    (hd : ∀i,d<2*(gamma α r).re*w i)
include hα hr hw hd

private def weightPolynomial (sigma mu L : ℝ) : Polynomial ℝ :=
  (Polynomial.C mu+Polynomial.C L*Polynomial.X)^2+Polynomial.C sigma
private def fieldPolynomial (_sigma mu L : ℝ) : Polynomial ℝ :=
  Polynomial.X*(Polynomial.C 2*(Polynomial.C mu+Polynomial.C L*Polynomial.X))
private def tiltPolynomial (sigma d q mu L : ℝ) : Polynomial ℝ :=
  (Polynomial.C (2*d)*Polynomial.X^2-Polynomial.C q*Polynomial.X)*weightPolynomial sigma mu L

omit hα hr hw hd in
private theorem weight_eval (sigma mu L v : ℝ) :
    (weightPolynomial sigma mu L).eval v=weight sigma (mu+L*v) := by
  simp [weightPolynomial,weight]
omit hα hr hw hd in
private theorem field_eval (sigma mu L v : ℝ) :
    (fieldPolynomial sigma mu L).eval v=v*weightSlope sigma (mu+L*v) := by
  simp [fieldPolynomial,weightSlope]
omit hα hr hw hd in
private theorem tilt_eval (sigma d q mu L v : ℝ) :
    (tiltPolynomial sigma d q mu L).eval v=(2*d*v^2-q*v)*weight sigma (mu+L*v) := by
  simp [tiltPolynomial,weight_eval]

theorem energy_field_tilt (sigma mu L : ℝ) :
    KFCausalChargedMassAngularLoss.energy sigma d q mu L (gamma α r) w c=
      (∫v,KFCausalChargedMassScoreIBP.energyDensity sigma d q mu L n α r w c v) ∧
    KFCausalChargedMassAngularLoss.fieldSlope sigma d q mu L (gamma α r) w c=
      (∫v,KFCausalChargedMassScoreIBP.fieldDensity sigma d q mu L n α r w c v) ∧
    KFCausalChargedMassAngularLoss.tilt sigma d q mu L (gamma α r) w c=
      (∫v,KFCausalChargedMassScoreIBP.tiltDensity sigma d q mu L n α r w c v) := by
  have he := KFCausalChargedQuarticScoreAttachment.polynomial_marginal n α r d q w c hα hr hw hd (weightPolynomial sigma mu L)
  have hf := KFCausalChargedQuarticScoreAttachment.polynomial_marginal n α r d q w c hα hr hw hd (fieldPolynomial sigma mu L)
  have ht := KFCausalChargedQuarticScoreAttachment.polynomial_marginal n α r d q w c hα hr hw hd (tiltPolynomial sigma d q mu L)
  refine ⟨?_,?_,?_⟩
  · simpa only [weight_eval,KFCausalChargedMassAngularLoss.energy,
      KFCausalChargedMassAngularLoss.energyDensity,KFCausalChargedMassAngularLoss.base,KFCausalChargedQuarticAngularLoss.base,KFCausalChargedMassScoreIBP.energyDensity] using he
  · simpa only [field_eval,KFCausalChargedMassAngularLoss.fieldSlope,
      KFCausalChargedMassAngularLoss.fieldDensity,KFCausalChargedMassAngularLoss.base,KFCausalChargedQuarticAngularLoss.base,KFCausalChargedMassScoreIBP.fieldDensity] using hf
  · simpa only [tilt_eval,KFCausalChargedMassAngularLoss.tilt,
      KFCausalChargedMassAngularLoss.tiltDensity,KFCausalChargedMassAngularLoss.energyDensity,KFCausalChargedMassAngularLoss.base,KFCausalChargedQuarticAngularLoss.base,
      KFCausalChargedMassScoreIBP.tiltDensity,KFCausalChargedMassScoreIBP.energyDensity,mul_assoc] using ht

theorem charged_score (sigma mu L : ℝ) (hsigma : 0≤sigma) :
    (KFCausalChargedCoolingBoundaryScore.scoreRate r+1/r.re)*
      KFCausalChargedMassAngularLoss.energy sigma d q mu L (gamma α r) w c+
    (KFCausalChargedCoolingBoundaryScore.scoreRate r/2)*L*
      KFCausalChargedMassAngularLoss.fieldSlope sigma d q mu L (gamma α r) w c+
    (KFCausalChargedCoolingBoundaryScore.scoreRate r/2)*
      KFCausalChargedMassAngularLoss.tilt sigma d q mu L (gamma α r) w c ≤
        ∫ v,KFCausalChargedMassScoreIBP.coolingDensity sigma d q mu L n α r w c v := by
  have he := energy_field_tilt n α r d q w c hα hr hw hd sigma mu L
  rw [he.1,he.2.1,he.2.2]
  exact KFCausalChargedMassScoreIBP.mass_score n α r d q w c hα hr hw hd sigma mu L hsigma

#print axioms energy_field_tilt
#print axioms charged_score
end
end UnifiedTheory.Audit.KFCausalChargedMassScoreAttachment
