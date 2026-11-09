/- Actual weighted integration by parts for the coherent charged score.
All functions and derivatives are integrable by their Gaussian margins.
The resulting quartic score bound retains the linked field and tilt
terms; neither a boundary condition nor a response bound is assumed. -/
import UnifiedTheory.Audit.KFCausalChargedQuarticScoreIntegrability
import UnifiedTheory.Audit.KFCausalAngularQuarticGaussianSmoothing
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedQuarticScoreIBP
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalWedgeGeometry (gamma)
open KFCausalChargedCoolingMarginalScore (marginal)
open KFCausalChargedCoolingBoundaryScore (scoreRate)
open KFCausalAngularQuarticGaussianSmoothing (weight weightSlope)

private def scorePolynomial (P : Polynomial ℝ) (d q : ℝ) : Polynomial ℝ :=
  P.derivative+(Polynomial.C (2*d)*Polynomial.X-Polynomial.C q)*P

variable (n : ℕ) (α : ℝ) (r : ℂ) (d q : ℝ) (w : Fin n→ℝ) (c : Fin n→ℂ)
    (hα : 0<α) (hr : |r.im|<r.re) (hw : ∀i,0<w i)
    (hd : ∀i,d<2*(gamma α r).re*w i)
include hα hr hw hd

theorem polynomial_ibp (P : Polynomial ℝ) :
    (∫ v : ℝ, P.eval v*Real.exp (d*v^2-q*v)*deriv (marginal n α r w c) v)=
      -∫ v : ℝ, (P.derivative.eval v+(2*d*v-q)*P.eval v)*
        Real.exp (d*v^2-q*v)*marginal n α r w c v := by
  have hi := KFCausalChargedQuarticScoreIntegrability.polynomial_integrable
    n α r d q w c hα hr hw hd P
  have hj := (KFCausalChargedQuarticScoreIntegrability.polynomial_integrable
    n α r d q w c hα hr hw hd (scorePolynomial P d q)).1
  have hu (v : ℝ) : HasDerivAt (fun x : ℝ => P.eval x*Real.exp (d*x^2-q*x))
      ((P.derivative.eval v+(2*d*v-q)*P.eval v)*Real.exp (d*v^2-q*v)) v := by
    have h := (P.hasDerivAt v).mul
      ((((hasDerivAt_id v).pow 2).const_mul d).sub ((hasDerivAt_id v).const_mul q)).exp
    convert h using 1
    simp only [id_eq,Pi.pow_apply,Pi.sub_apply,Nat.cast_ofNat,mul_one]
    ring
  have hv (v : ℝ) :=
    KFCausalChargedCoolingMarginalScore.marginal_radial_derivative n α r w c v hα hr hw
  have hv' (v : ℝ) : HasDerivAt (marginal n α r w c) (deriv (marginal n α r w c) v) v :=
    (hv v).differentiableAt.hasDerivAt
  have hj' : Integrable (fun v : ℝ =>
      ((P.derivative.eval v+(2*d*v-q)*P.eval v)*Real.exp (d*v^2-q*v))*marginal n α r w c v) := by
    simpa only [scorePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_X] using hj
  exact integral_mul_deriv_eq_deriv_mul_of_integrable hu hv' hi.2.1 hj' hi.1

def energyDensity (sigma d q mu L : ℝ) (n : ℕ) (α : ℝ) (r : ℂ)
    (w : Fin n→ℝ) (c : Fin n→ℂ) (v : ℝ) : ℝ :=
  weight sigma (mu+L*v)*Real.exp (d*v^2-q*v)*marginal n α r w c v
def fieldDensity (sigma d q mu L : ℝ) (n : ℕ) (α : ℝ) (r : ℂ)
    (w : Fin n→ℝ) (c : Fin n→ℂ) (v : ℝ) : ℝ :=
  (v*weightSlope sigma (mu+L*v))*Real.exp (d*v^2-q*v)*marginal n α r w c v
def tiltDensity (sigma d q mu L : ℝ) (n : ℕ) (α : ℝ) (r : ℂ)
    (w : Fin n→ℝ) (c : Fin n→ℂ) (v : ℝ) : ℝ :=
  (2*d*v^2-q*v)*energyDensity sigma d q mu L n α r w c v
def coolingDensity (sigma d q mu L : ℝ) (n : ℕ) (α : ℝ) (r : ℂ)
    (w : Fin n→ℝ) (c : Fin n→ℂ) (v : ℝ) : ℝ :=
  weight sigma (mu+L*v)*Real.exp (d*v^2-q*v)*
    (-deriv (fun t : ℝ => marginal n α (r+(t:ℂ)) w c v) 0)

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
private theorem weightPolynomial_eval (sigma mu L v : ℝ) :
    (weightPolynomial sigma mu L).eval v=weight sigma (mu+L*v) := by
  simp [weightPolynomial,weight]
omit hα hr hw hd in
private theorem fieldPolynomial_eval (sigma mu L v : ℝ) :
    (fieldPolynomial sigma mu L).eval v=v*weightSlope sigma (mu+L*v) := by
  simp [fieldPolynomial,weightSlope]
omit hα hr hw hd in
private theorem tiltPolynomial_eval (sigma d q mu L v : ℝ) :
    (tiltPolynomial sigma d q mu L).eval v=(2*d*v^2-q*v)*weight sigma (mu+L*v) := by
  simp [tiltPolynomial,weightPolynomial_eval]

theorem densities_integrable (sigma mu L : ℝ) :
    Integrable (energyDensity sigma d q mu L n α r w c) ∧
    Integrable (fieldDensity sigma d q mu L n α r w c) ∧
    Integrable (tiltDensity sigma d q mu L n α r w c) ∧
    Integrable (coolingDensity sigma d q mu L n α r w c) := by
  have he := KFCausalChargedQuarticScoreIntegrability.polynomial_integrable
    n α r d q w c hα hr hw hd (weightPolynomial sigma mu L)
  have hf := (KFCausalChargedQuarticScoreIntegrability.polynomial_integrable
    n α r d q w c hα hr hw hd (fieldPolynomial sigma mu L)).1
  have ht := (KFCausalChargedQuarticScoreIntegrability.polynomial_integrable
    n α r d q w c hα hr hw hd (tiltPolynomial sigma d q mu L)).1
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [weightPolynomial_eval,energyDensity] using he.1
  · simpa only [fieldPolynomial_eval,fieldDensity] using hf
  · apply ht.congr
    filter_upwards [] with v
    rw [tiltPolynomial_eval]
    dsimp only [tiltDensity,energyDensity]
    ring
  · simpa only [weightPolynomial_eval,coolingDensity] using he.2.2

theorem quartic_ibp (sigma mu L : ℝ) :
    (∫ v : ℝ, (v*weight sigma (mu+L*v))*Real.exp (d*v^2-q*v)*
      deriv (marginal n α r w c) v)=
      -(∫ v,energyDensity sigma d q mu L n α r w c v)-
        L*(∫ v,fieldDensity sigma d q mu L n α r w c v)-
        ∫ v,tiltDensity sigma d q mu L n α r w c v := by
  let P := Polynomial.X*weightPolynomial sigma mu L
  have hi := polynomial_ibp n α r d q w c hα hr hw hd P
  have he (v : ℝ) : P.eval v=v*weight sigma (mu+L*v) := by
    simp only [P,Polynomial.eval_mul,Polynomial.eval_X,weightPolynomial_eval]
  have hder (v : ℝ) : P.derivative.eval v=
      weight sigma (mu+L*v)+L*(v*weightSlope sigma (mu+L*v)) := by
    simp [P,weightPolynomial,Polynomial.derivative_pow,weight,weightSlope]
    ring
  simp_rw [he,hder] at hi
  have hh (v : ℝ) :
      (weight sigma (mu+L*v)+L*(v*weightSlope sigma (mu+L*v))+
        (2*d*v-q)*(v*weight sigma (mu+L*v)))*Real.exp (d*v^2-q*v)*marginal n α r w c v=
      energyDensity sigma d q mu L n α r w c v+
        L*fieldDensity sigma d q mu L n α r w c v+
        tiltDensity sigma d q mu L n α r w c v := by
    dsimp only [tiltDensity,energyDensity,fieldDensity]
    ring
  simp_rw [hh] at hi
  have hs := densities_integrable n α r d q w c hα hr hw hd sigma mu L
  have hadd := integral_add (hs.1.add (hs.2.1.const_mul L)) hs.2.2.1
  simp only [Pi.add_apply] at hadd
  rw [hadd,integral_add hs.1 (hs.2.1.const_mul L),integral_const_mul] at hi
  linarith only [hi]

theorem quartic_score (sigma mu L : ℝ) (hsigma : 0≤sigma) :
    (scoreRate r+1/r.re)*(∫ v,energyDensity sigma d q mu L n α r w c v)+
      (scoreRate r/2)*L*(∫ v,fieldDensity sigma d q mu L n α r w c v)+
      (scoreRate r/2)*(∫ v,tiltDensity sigma d q mu L n α r w c v) ≤
        ∫ v,coolingDensity sigma d q mu L n α r w c v := by
  have hi := densities_integrable n α r d q w c hα hr hw hd sigma mu L
  have hj := (KFCausalChargedQuarticScoreIntegrability.polynomial_integrable
    n α r d q w c hα hr hw hd (Polynomial.X*weightPolynomial sigma mu L)).2.1
  simp only [Polynomial.eval_mul,Polynomial.eval_X,weightPolynomial_eval] at hj
  have hp (v : ℝ) := KFCausalChargedCoolingMarginalScore.actual_marginal_score n α r w c v hα hr hw
  have hmono := integral_mono
    ((hi.1.const_mul (scoreRate r/2+1/r.re)).sub (hj.const_mul (scoreRate r/2))) hi.2.2.2
    (fun v => show (scoreRate r/2+1/r.re)*energyDensity sigma d q mu L n α r w c v-
      (scoreRate r/2)*((v*weight sigma (mu+L*v))*Real.exp (d*v^2-q*v)*deriv (marginal n α r w c) v) ≤
        coolingDensity sigma d q mu L n α r w c v from by
      have hW : 0≤weight sigma (mu+L*v)*Real.exp (d*v^2-q*v) := by
        unfold weight
        positivity
      have hh := mul_le_mul_of_nonneg_left (hp v) hW
      dsimp only [energyDensity,coolingDensity]
      nlinarith only [hh])
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (hi.1.const_mul (scoreRate r/2+1/r.re)) (hj.const_mul (scoreRate r/2)),
    integral_const_mul,integral_const_mul,quartic_ibp n α r d q w c hα hr hw hd sigma mu L] at hmono
  nlinarith only [hmono]

#print axioms polynomial_ibp
#print axioms densities_integrable
#print axioms quartic_ibp
#print axioms quartic_score
end
end UnifiedTheory.Audit.KFCausalChargedQuarticScoreIBP
