/- The actual coherent charged packet inherits the quartic circle loss.
All polynomially weighted densities are integrable under the original
strict Gaussian width margin. The polar/Fubini passage keeps every width
cross term and uses no supplied integrability or angular inequality. -/
import UnifiedTheory.Audit.KFCausalAngularQuarticQuadraticTilt
import UnifiedTheory.Audit.KFCausalChargedCoshGaussianMomentSeries
import UnifiedTheory.Audit.KFCausalPlanePolarComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedQuarticAngularLoss
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalChargedEvenMomentFamily (packet)
open KFCausalAngularQuarticGaussianSmoothing (weight weightSlope)

variable {ι : Type*} [Fintype ι]

def base (p : ℂ) (d q : ℝ) (w : ι→ℝ) (c : ι→ℂ) (x : Charged) : ℝ :=
  Real.exp (d*x.1.2^2-q*x.1.2)*‖packet 0 p w c x‖^2
def energyDensity (sigma d q mu L : ℝ) (p : ℂ) (w : ι→ℝ) (c : ι→ℂ) (x : Charged) : ℝ :=
  weight sigma (mu+L*x.1.2)*base p d q w c x
def fieldDensity (sigma d q mu L : ℝ) (p : ℂ) (w : ι→ℝ) (c : ι→ℂ) (x : Charged) : ℝ :=
  (x.1.2*weightSlope sigma (mu+L*x.1.2))*base p d q w c x
def tiltDensity (sigma d q mu L : ℝ) (p : ℂ) (w : ι→ℝ) (c : ι→ℂ) (x : Charged) : ℝ :=
  (2*d*x.1.2^2-q*x.1.2)*energyDensity sigma d q mu L p w c x

def energy (sigma d q mu L : ℝ) (p : ℂ) (w : ι→ℝ) (c : ι→ℂ) : ℝ :=
  ∫ x, energyDensity sigma d q mu L p w c x ∂chargedMeasure
def fieldSlope (sigma d q mu L : ℝ) (p : ℂ) (w : ι→ℝ) (c : ι→ℂ) : ℝ :=
  ∫ x, fieldDensity sigma d q mu L p w c x ∂chargedMeasure
def tilt (sigma d q mu L : ℝ) (p : ℂ) (w : ι→ℝ) (c : ι→ℂ) : ℝ :=
  ∫ x, tiltDensity sigma d q mu L p w c x ∂chargedMeasure

theorem monomial_integrable (n : ℕ) (p : ℂ) (d q : ℝ) (w : ι→ℝ) (c : ι→ℂ)
    (hp : 0<p.re) (hw : ∀i,0<w i) (hd : ∀i,d<2*p.re*w i) :
    Integrable (fun x : Charged => x.1.2^n*base p d q w c x) chargedMeasure := by
  have hi (j : ℕ) := KFCausalChargedCoshGaussianMomentSeries.exponential_square_integrable
    j p d (-q) w c hp hw hd
  have hc : Continuous (fun x : Charged => x.1.2^n*base p d q w c x) := by
    unfold base packet KFCausalChargedFourierPolynomialGram.atom
    fun_prop
  apply ((hi 0).add (hi n)).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  have hn := KFCausalChargedGaussianMomentSeries.packet_norm_add 0 n p w c x
  simp only [zero_add] at hn
  have hv : |x.1.2^n|≤1+(x.1.2^n)^2 := by
    nlinarith [sq_nonneg (|x.1.2^n|-1),sq_abs (x.1.2^n)]
  have hpow : x.1.2^(2*n)=(x.1.2^n)^2 := by rw [mul_comm 2 n,pow_mul]
  simp only [Pi.add_apply]
  rw [hn,← pow_mul,hpow]
  simp only [base,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (Real.exp_pos _).le,abs_of_nonneg (sq_nonneg ‖packet 0 p w c x‖)]
  have hh := mul_le_mul_of_nonneg_right hv
    (mul_nonneg (Real.exp_pos (d*x.1.2^2-q*x.1.2)).le (sq_nonneg ‖packet 0 p w c x‖))
  convert hh using 1
  simp only [neg_mul,sub_eq_add_neg]
  ring

theorem polynomial_integrable (P : Polynomial ℝ) (p : ℂ) (d q : ℝ)
    (w : ι→ℝ) (c : ι→ℂ) (hp : 0<p.re) (hw : ∀i,0<w i) (hd : ∀i,d<2*p.re*w i) :
    Integrable (fun x : Charged => P.eval x.1.2*base p d q w c x) chargedMeasure := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add,add_mul] using hP.add hQ
  | monomial n a => simpa only [Polynomial.eval_monomial,mul_assoc] using
      (monomial_integrable n p d q w c hp hw hd).const_mul a

private def weightPolynomial (sigma mu L : ℝ) : Polynomial ℝ :=
  (Polynomial.C mu+Polynomial.C L*Polynomial.X)^4+
    Polynomial.C (6*sigma)*(Polynomial.C mu+Polynomial.C L*Polynomial.X)^2+
    Polynomial.C (3*sigma^2)
private def fieldPolynomial (sigma mu L : ℝ) : Polynomial ℝ :=
  Polynomial.X*(Polynomial.C 4*(Polynomial.C mu+Polynomial.C L*Polynomial.X)^3+
    Polynomial.C (12*sigma)*(Polynomial.C mu+Polynomial.C L*Polynomial.X))

private theorem weightPolynomial_eval (sigma mu L v : ℝ) :
    (weightPolynomial sigma mu L).eval v=weight sigma (mu+L*v) := by
  simp [weightPolynomial,weight]
private theorem fieldPolynomial_eval (sigma mu L v : ℝ) :
    (fieldPolynomial sigma mu L).eval v=v*weightSlope sigma (mu+L*v) := by
  simp [fieldPolynomial,weightSlope]

theorem densities_integrable (sigma d q mu L : ℝ) (p : ℂ) (w : ι→ℝ) (c : ι→ℂ)
    (hp : 0<p.re) (hw : ∀i,0<w i) (hd : ∀i,d<2*p.re*w i) :
    Integrable (energyDensity sigma d q mu L p w c) chargedMeasure ∧
    Integrable (fieldDensity sigma d q mu L p w c) chargedMeasure ∧
    Integrable (tiltDensity sigma d q mu L p w c) chargedMeasure := by
  refine ⟨?_,?_,?_⟩
  · simpa only [weightPolynomial_eval,energyDensity] using
      polynomial_integrable (weightPolynomial sigma mu L) p d q w c hp hw hd
  · simpa only [fieldPolynomial_eval,fieldDensity] using
      polynomial_integrable (fieldPolynomial sigma mu L) p d q w c hp hw hd
  · have hi := polynomial_integrable
      ((Polynomial.C (2*d)*Polynomial.X^2-Polynomial.C q*Polynomial.X)*
        weightPolynomial sigma mu L) p d q w c hp hw hd
    apply hi.congr
    filter_upwards [] with x
    simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_pow,
      Polynomial.eval_C,Polynomial.eval_X,weightPolynomial_eval,tiltDensity,energyDensity]
    ring

private theorem sine_cosine_integral (f : ℝ→ℝ) :
    (∫ theta in -Real.pi..Real.pi, f (Real.sin theta))=
      ∫ theta in 0..(2*Real.pi), f (Real.cos theta) := by
  have hp : Function.Periodic (fun theta => f (Real.cos theta)) (2*Real.pi) :=
    fun theta => by simp only [Real.cos_add_two_pi]
  have hs := hp.intervalIntegral_add_eq (-Real.pi-Real.pi/2) 0
  have hb : -Real.pi-Real.pi/2+2*Real.pi=Real.pi-Real.pi/2 := by ring
  rw [hb,zero_add] at hs
  rw [← hs,← intervalIntegral.integral_comp_sub_right (f := fun theta => f (Real.cos theta))
    (a := -Real.pi) (b := Real.pi) (Real.pi/2)]
  simp only [Real.cos_sub_pi_div_two]

private theorem packet_circle (p : ℂ) (w : ι→ℝ) (c : ι→ℂ) (R Y theta : ℝ) :
    packet 0 p w c ((R*Real.cos theta,R*Real.sin theta),Y)=
      ∑i,c i*Complex.exp (-(w i:ℂ)*(p*((R^2:ℝ):ℂ)+conj p*(Y:ℂ))) := by
  rw [KFCausalChargedEvenMomentFamily.packet_expansion]
  simp only [pow_zero,one_mul]
  have he : ((R*Real.cos theta:ℝ):ℂ)^2+((R*Real.sin theta:ℝ):ℂ)^2=((R^2:ℝ):ℂ) := by
    rw [← Complex.ofReal_pow,← Complex.ofReal_pow,← Complex.ofReal_add]
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq theta]
  rw [he]

private theorem angular_nonnegative (C sigma d q mu L : ℝ) (p : ℂ)
    (w : ι→ℝ) (c : ι→ℂ) (hsigma : 0≤sigma) (hd : 0≤d)
    (hC : ∀ s dd qq mm ll : ℝ,0≤s→0≤dd→0≤
      KFCausalAngularQuarticQuadraticTilt.defect s dd qq mm ll+
        C*KFCausalAngularQuarticQuadraticTilt.energy s dd qq mm ll)
    (R Y : ℝ) :
    0≤∫ theta in -Real.pi..Real.pi,
      2*tiltDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y)-
        L*fieldDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y)+
        C*energyDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y) := by
  let A := ‖∑i,c i*Complex.exp (-(w i:ℂ)*(p*((R^2:ℝ):ℂ)+conj p*(Y:ℂ)))‖^2
  let f : ℝ→ℝ := fun v => 2*(2*(d*R^2)*v^2-(q*R)*v)*
      Real.exp ((d*R^2)*v^2-(q*R)*v)*weight sigma (mu+(L*R)*v)-
      (L*R)*(Real.exp ((d*R^2)*v^2-(q*R)*v)*v*weightSlope sigma (mu+(L*R)*v))+
      C*(Real.exp ((d*R^2)*v^2-(q*R)*v)*weight sigma (mu+(L*R)*v))
  have he : (∫ theta in -Real.pi..Real.pi,
      2*tiltDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y)-
        L*fieldDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y)+
        C*energyDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y))=
      A*∫ theta in 0..(2*Real.pi),f (Real.cos theta) := by
    rw [← sine_cosine_integral f,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro theta _
    simp only [tiltDensity,energyDensity,fieldDensity,base,packet_circle]
    dsimp [A,f]
    rw [show d*(R*Real.sin theta)^2-q*(R*Real.sin theta)=
      d*R^2*(Real.sin theta)^2-q*R*Real.sin theta by ring]
    rw [show mu+L*(R*Real.sin theta)=mu+(L*R)*Real.sin theta by ring]
    ring
  rw [he]
  have h0 : IntervalIntegrable (fun theta => Real.exp ((d*R^2)*(Real.cos theta)^2-
      (q*R)*Real.cos theta)*weight sigma (mu+(L*R)*Real.cos theta)) volume 0 (2*Real.pi) :=
    (by unfold weight; fun_prop : Continuous _).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun theta => Real.exp ((d*R^2)*(Real.cos theta)^2-
      (q*R)*Real.cos theta)*Real.cos theta*weightSlope sigma (mu+(L*R)*Real.cos theta)) volume 0 (2*Real.pi) :=
    (by unfold weightSlope; fun_prop : Continuous _).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun theta => (2*(d*R^2)*(Real.cos theta)^2-
      (q*R)*Real.cos theta)*Real.exp ((d*R^2)*(Real.cos theta)^2-
      (q*R)*Real.cos theta)*weight sigma (mu+(L*R)*Real.cos theta)) volume 0 (2*Real.pi) :=
    (by unfold weight; fun_prop : Continuous _).intervalIntegrable _ _
  have he2 : (∫ theta in 0..(2*Real.pi),f (Real.cos theta))=
      KFCausalAngularQuarticQuadraticTilt.defect sigma (d*R^2) (q*R) mu (L*R)+
      C*KFCausalAngularQuarticQuadraticTilt.energy sigma (d*R^2) (q*R) mu (L*R) := by
    dsimp [f,KFCausalAngularQuarticQuadraticTilt.defect,KFCausalAngularQuarticQuadraticTilt.tilt,
      KFCausalAngularQuarticQuadraticTilt.fieldSlope,KFCausalAngularQuarticQuadraticTilt.energy]
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (h2.const_mul 2) (h1.const_mul (L*R)),
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((h2.const_mul 2).sub (h1.const_mul (L*R))) (h0.const_mul C)]
    apply intervalIntegral.integral_congr
    intro theta _
    ring
  rw [he2]
  exact mul_nonneg (sq_nonneg _) (hC sigma (d*R^2) (q*R) mu (L*R) hsigma (mul_nonneg hd (sq_nonneg R)))

theorem global_loss : ∃ C : ℝ,0≤C ∧ ∀ (sigma d q mu L : ℝ) (p : ℂ)
    (w : ι→ℝ) (c : ι→ℂ),0≤sigma→0≤d→0<p.re→(∀i,0<w i)→(∀i,d<2*p.re*w i)→
    0≤2*tilt sigma d q mu L p w c-L*fieldSlope sigma d q mu L p w c+
      C*energy sigma d q mu L p w c := by
  obtain ⟨C,hC,hbound⟩ := KFCausalAngularQuarticQuadraticTilt.global_quadratic_loss
  refine ⟨C,hC,?_⟩
  intro sigma d q mu L p w c hsigma hd0 hp hw hd
  obtain ⟨he,hf,ht⟩ := densities_integrable sigma d q mu L p w c hp hw hd
  let F : Charged→ℝ := fun x => 2*tiltDensity sigma d q mu L p w c x-
      L*fieldDensity sigma d q mu L p w c x+C*energyDensity sigma d q mu L p w c x
  have hF : Integrable F chargedMeasure := ((ht.const_mul 2).sub (hf.const_mul L)).add (he.const_mul C)
  have hFc : Continuous F := by
    unfold F tiltDensity energyDensity fieldDensity base weight weightSlope packet
      KFCausalChargedFourierPolynomialGram.atom
    fun_prop
  have hpos : 0≤∫x,F x ∂chargedMeasure := by
    unfold chargedMeasure at hF ⊢
    rw [integral_prod_symm _ hF]
    apply integral_nonneg_of_ae
    filter_upwards [hF.prod_left_ae] with Y hY
    rw [← Measure.volume_eq_prod ℝ ℝ] at hY ⊢
    have hc : Continuous (fun x : ℝ×ℝ => F (x,Y)) := hFc.comp (by fun_prop)
    have hh := KFCausalPlanePolarComparison.integral_le_of_angular (fun _ : ℝ×ℝ => 0)
      (fun x => F (x,Y)) continuous_const hc (integrable_zero _ _ _) hY
      (fun R _ => by simpa only [intervalIntegral.integral_zero] using
        angular_nonnegative C sigma d q mu L p w c hsigma hd0 hbound R Y)
    simpa only [integral_zero] using hh
  unfold F at hpos
  have hsum := integral_add ((ht.const_mul 2).sub (hf.const_mul L)) (he.const_mul C)
  have hsub := integral_sub (ht.const_mul 2) (hf.const_mul L)
  simp only [Pi.sub_apply] at hsum hsub
  rw [hsum,hsub] at hpos
  simpa only [integral_const_mul,energy,fieldSlope,tilt] using hpos

#print axioms monomial_integrable
#print axioms polynomial_integrable
#print axioms densities_integrable
#print axioms global_loss
end
end UnifiedTheory.Audit.KFCausalChargedQuarticAngularLoss
