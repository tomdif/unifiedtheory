/- The one-dimensional weighted score is attached to the literal
coherent charged integral by a measure-preserving coordinate reordering.
All Fubini integrability is supplied by the original Gaussian margin. -/
import UnifiedTheory.Audit.KFCausalChargedQuarticScoreIBP
import UnifiedTheory.Audit.KFCausalChargedQuarticAngularLoss

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedQuarticScoreAttachment
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalChargedCoolingMarginalScore (marginal)
open KFCausalReciprocalWedgeGeometry (gamma)
open KFCausalAngularQuarticGaussianSmoothing (weight weightSlope)

local instance : SFinite planeMeasure := by unfold planeMeasure; infer_instance

private def reorder : Charged ≃ᵐ ℝ×(ℝ×ℝ) :=
  (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl ℝ)).trans MeasurableEquiv.prodAssoc
private theorem reorder_preserving :
    MeasurePreserving reorder chargedMeasure (volume.prod planeMeasure) :=
  (measurePreserving_prodAssoc volume volume (volume.restrict (Set.Ioi 0))).comp
    (MeasurePreserving.prod Measure.measurePreserving_swap (MeasurePreserving.id _))

variable (n : ℕ) (α : ℝ) (r : ℂ) (d q : ℝ) (w : Fin n→ℝ) (c : Fin n→ℂ)
    (hα : 0<α) (hr : |r.im|<r.re) (hw : ∀i,0<w i)
    (hd : ∀i,d<2*(gamma α r).re*w i)
include hα hr hw hd

theorem polynomial_marginal (P : Polynomial ℝ) :
    (∫ x : Charged,P.eval x.1.2*KFCausalChargedQuarticAngularLoss.base
      (gamma α r) d q w c x ∂chargedMeasure)=
      ∫ v : ℝ,P.eval v*Real.exp (d*v^2-q*v)*marginal n α r w c v := by
  let f (x : ℝ×(ℝ×ℝ)) := P.eval x.1*Real.exp (d*x.1^2-q*x.1)*
    ‖KFCausalChargedCoolingPhysicalMarginal.packetSum n (gamma α r) w c x.2.1 x.1 x.2.2‖^2
  have hf : Integrable f (volume.prod planeMeasure) := by
    apply (reorder_preserving.integrable_comp_emb reorder.measurableEmbedding).mp
    have hi := KFCausalChargedQuarticAngularLoss.polynomial_integrable
      P (gamma α r) d q w c (KFCausalChargedCoolingFixedV.actual_gamma_re_positive α r hα hr) hw hd
    convert hi using 1
    funext x
    change P.eval x.1.2*Real.exp (d*x.1.2^2-q*x.1.2)*
      ‖KFCausalChargedEvenMomentFamily.packet 0 (gamma α r) w c x‖^2=
      P.eval x.1.2*(Real.exp (d*x.1.2^2-q*x.1.2)*
        ‖KFCausalChargedEvenMomentFamily.packet 0 (gamma α r) w c x‖^2)
    ring
  have he := reorder_preserving.integral_comp reorder.measurableEmbedding f
  have he' :
      (∫ x : Charged,P.eval x.1.2*KFCausalChargedQuarticAngularLoss.base
        (gamma α r) d q w c x ∂chargedMeasure)=∫ x,f x ∂volume.prod planeMeasure := by
    convert he using 1
    apply integral_congr_ae
    filter_upwards [] with x
    change P.eval x.1.2*(Real.exp (d*x.1.2^2-q*x.1.2)*
        ‖KFCausalChargedEvenMomentFamily.packet 0 (gamma α r) w c x‖^2)=
      P.eval x.1.2*Real.exp (d*x.1.2^2-q*x.1.2)*
        ‖KFCausalChargedEvenMomentFamily.packet 0 (gamma α r) w c x‖^2
    ring
  rw [he',integral_prod f hf]
  apply integral_congr_ae
  filter_upwards [] with v
  exact integral_const_mul (P.eval v*Real.exp (d*v^2-q*v)) _

private def weightPolynomial (sigma mu L : ℝ) : Polynomial ℝ :=
  (Polynomial.C mu+Polynomial.C L*Polynomial.X)^4+
    Polynomial.C (6*sigma)*(Polynomial.C mu+Polynomial.C L*Polynomial.X)^2+
    Polynomial.C (3*sigma^2)
private def fieldPolynomial (sigma mu L : ℝ) : Polynomial ℝ :=
  Polynomial.X*(Polynomial.C 4*(Polynomial.C mu+Polynomial.C L*Polynomial.X)^3+
    Polynomial.C (12*sigma)*(Polynomial.C mu+Polynomial.C L*Polynomial.X))
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
    KFCausalChargedQuarticAngularLoss.energy sigma d q mu L (gamma α r) w c=
      (∫v,KFCausalChargedQuarticScoreIBP.energyDensity sigma d q mu L n α r w c v) ∧
    KFCausalChargedQuarticAngularLoss.fieldSlope sigma d q mu L (gamma α r) w c=
      (∫v,KFCausalChargedQuarticScoreIBP.fieldDensity sigma d q mu L n α r w c v) ∧
    KFCausalChargedQuarticAngularLoss.tilt sigma d q mu L (gamma α r) w c=
      (∫v,KFCausalChargedQuarticScoreIBP.tiltDensity sigma d q mu L n α r w c v) := by
  have he := polynomial_marginal n α r d q w c hα hr hw hd (weightPolynomial sigma mu L)
  have hf := polynomial_marginal n α r d q w c hα hr hw hd (fieldPolynomial sigma mu L)
  have ht := polynomial_marginal n α r d q w c hα hr hw hd (tiltPolynomial sigma d q mu L)
  refine ⟨?_,?_,?_⟩
  · simpa only [weight_eval,KFCausalChargedQuarticAngularLoss.energy,
      KFCausalChargedQuarticAngularLoss.energyDensity,KFCausalChargedQuarticScoreIBP.energyDensity] using he
  · simpa only [field_eval,KFCausalChargedQuarticAngularLoss.fieldSlope,
      KFCausalChargedQuarticAngularLoss.fieldDensity,KFCausalChargedQuarticScoreIBP.fieldDensity] using hf
  · simpa only [tilt_eval,KFCausalChargedQuarticAngularLoss.tilt,
      KFCausalChargedQuarticAngularLoss.tiltDensity,KFCausalChargedQuarticAngularLoss.energyDensity,
      KFCausalChargedQuarticScoreIBP.tiltDensity,KFCausalChargedQuarticScoreIBP.energyDensity,mul_assoc] using ht

theorem charged_score (sigma mu L : ℝ) (hsigma : 0≤sigma) :
    (KFCausalChargedCoolingBoundaryScore.scoreRate r+1/r.re)*
      KFCausalChargedQuarticAngularLoss.energy sigma d q mu L (gamma α r) w c+
    (KFCausalChargedCoolingBoundaryScore.scoreRate r/2)*L*
      KFCausalChargedQuarticAngularLoss.fieldSlope sigma d q mu L (gamma α r) w c+
    (KFCausalChargedCoolingBoundaryScore.scoreRate r/2)*
      KFCausalChargedQuarticAngularLoss.tilt sigma d q mu L (gamma α r) w c ≤
        ∫ v,KFCausalChargedQuarticScoreIBP.coolingDensity sigma d q mu L n α r w c v := by
  have he := energy_field_tilt n α r d q w c hα hr hw hd sigma mu L
  rw [he.1,he.2.1,he.2.2]
  exact KFCausalChargedQuarticScoreIBP.quartic_score n α r d q w c hα hr hw hd sigma mu L hsigma

#print axioms polynomial_marginal
#print axioms energy_field_tilt
#print axioms charged_score
end
end UnifiedTheory.Audit.KFCausalChargedQuarticScoreAttachment
