/- The genuine entire-circle Hardy estimate passes to the full coherent
charged integral. The positive radius term is weakened to the actual v²
moment before Fubini, so its integrability follows from the original
Gaussian margin. No free width jets or boundary-domain relaxation occurs. -/
import UnifiedTheory.Audit.KFCausalAngularQuarticHardy
import UnifiedTheory.Audit.KFCausalChargedQuarticScoreAttachment

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedQuarticHardy
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalChargedEvenMomentFamily (packet)
open KFCausalChargedQuarticAngularLoss (base energyDensity tiltDensity energy tilt)
open KFCausalAngularQuarticGaussianSmoothing (weight)
open KFCausalReciprocalWedgeGeometry (gamma)

variable {ι : Type*} [Fintype ι]

private theorem sine_cosine_integral (f : ℝ→ℝ) :
    (∫ theta in -Real.pi..Real.pi,f (Real.sin theta))=
      ∫ theta in 0..(2*Real.pi),f (Real.cos theta) := by
  have hp : Function.Periodic (fun theta => f (Real.cos theta)) (2*Real.pi) :=
    fun theta => by simp only [Real.cos_add_two_pi]
  have hs := hp.intervalIntegral_add_eq (-Real.pi-Real.pi/2) 0
  have hb : -Real.pi-Real.pi/2+2*Real.pi=Real.pi-Real.pi/2 := by ring
  rw [hb,zero_add] at hs
  rw [←hs,←intervalIntegral.integral_comp_sub_right (f := fun theta => f (Real.cos theta))
    (a := -Real.pi) (b := Real.pi) (Real.pi/2)]
  simp only [Real.cos_sub_pi_div_two]

private theorem packet_circle (p : ℂ) (w : ι→ℝ) (c : ι→ℂ) (R Y theta : ℝ) :
    packet 0 p w c ((R*Real.cos theta,R*Real.sin theta),Y)=
      ∑i,c i*Complex.exp (-(w i:ℂ)*(p*((R^2:ℝ):ℂ)+conj p*(Y:ℂ))) := by
  rw [KFCausalChargedEvenMomentFamily.packet_expansion]
  simp only [pow_zero,one_mul]
  have he : ((R*Real.cos theta:ℝ):ℂ)^2+((R*Real.sin theta:ℝ):ℂ)^2=((R^2:ℝ):ℂ) := by
    rw [←Complex.ofReal_pow,←Complex.ofReal_pow,←Complex.ofReal_add]
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq theta]
  rw [he]

private theorem angular_radius_lower (sigma d q mu L : ℝ) (p : ℂ)
    (w : ι→ℝ) (c : ι→ℂ) (hsigma : 0≤sigma) (R Y : ℝ) :
    0≤∫ theta in -Real.pi..Real.pi,
      tiltDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y)-
        (d*R^2-4)*energyDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y) := by
  let A := ‖∑i,c i*Complex.exp (-(w i:ℂ)*(p*((R^2:ℝ):ℂ)+conj p*(Y:ℂ)))‖^2
  let f : ℝ→ℝ := fun v => ((2*(d*R^2)*v^2-(q*R)*v)-(d*R^2-4))*
    Real.exp ((d*R^2)*v^2-(q*R)*v)*weight sigma (mu+(L*R)*v)
  have he : (∫ theta in -Real.pi..Real.pi,
      tiltDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y)-
        (d*R^2-4)*energyDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y))=
      A*∫ theta in 0..(2*Real.pi),f (Real.cos theta) := by
    rw [←sine_cosine_integral f,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro theta _
    simp only [tiltDensity,energyDensity,base,packet_circle]
    dsimp only [A,f]
    rw [show d*(R*Real.sin theta)^2-q*(R*Real.sin theta)=
      d*R^2*(Real.sin theta)^2-q*R*Real.sin theta by ring,
      show mu+L*(R*Real.sin theta)=mu+(L*R)*Real.sin theta by ring]
    ring
  have hE : IntervalIntegrable (fun theta => Real.exp ((d*R^2)*(Real.cos theta)^2-
      (q*R)*Real.cos theta)*weight sigma (mu+(L*R)*Real.cos theta)) volume 0 (2*Real.pi) :=
    (by unfold weight; fun_prop : Continuous _).intervalIntegrable _ _
  have hT : IntervalIntegrable (fun theta => (2*(d*R^2)*(Real.cos theta)^2-
      (q*R)*Real.cos theta)*Real.exp ((d*R^2)*(Real.cos theta)^2-
      (q*R)*Real.cos theta)*weight sigma (mu+(L*R)*Real.cos theta)) volume 0 (2*Real.pi) :=
    (by unfold weight; fun_prop : Continuous _).intervalIntegrable _ _
  have hf : (∫ theta in 0..(2*Real.pi),f (Real.cos theta))=
      KFCausalAngularQuarticQuadraticTilt.tilt sigma (d*R^2) (q*R) mu (L*R)-
        (d*R^2-4)*KFCausalAngularQuarticQuadraticTilt.energy sigma (d*R^2) (q*R) mu (L*R) := by
    unfold KFCausalAngularQuarticQuadraticTilt.tilt KFCausalAngularQuarticQuadraticTilt.energy
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_sub hT (hE.const_mul (d*R^2-4))]
    apply intervalIntegral.integral_congr
    intro theta _
    dsimp only [f]
    ring
  rw [he,hf]
  exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr
    (KFCausalAngularQuarticHardy.smoothed_bound sigma (d*R^2) (q*R) mu (L*R) hsigma))

private theorem angular_coordinate_lower (sigma d q mu L : ℝ) (p : ℂ)
    (w : ι→ℝ) (c : ι→ℂ) (hsigma : 0≤sigma) (hd : 0≤d) (R Y : ℝ) :
    0≤∫ theta in -Real.pi..Real.pi,
      tiltDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y)-
        d*((R*Real.sin theta)^2*energyDensity sigma d q mu L p w c
          ((R*Real.cos theta,R*Real.sin theta),Y))+
        4*energyDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y) := by
  have hcont : Continuous (fun theta => energyDensity sigma d q mu L p w c
      ((R*Real.cos theta,R*Real.sin theta),Y)) := by
    unfold energyDensity base weight packet KFCausalChargedFourierPolynomialGram.atom
    fun_prop
  have htcont : Continuous (fun theta => tiltDensity sigma d q mu L p w c
      ((R*Real.cos theta,R*Real.sin theta),Y)) := by
    unfold tiltDensity
    exact (by fun_prop : Continuous (fun theta =>
      2*d*(R*Real.sin theta)^2-q*(R*Real.sin theta))).mul hcont
  have hleft : IntervalIntegrable (fun theta =>
      tiltDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y)-
        (d*R^2-4)*energyDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y))
      volume (-Real.pi) Real.pi :=
    (htcont.sub (continuous_const.mul hcont)).intervalIntegrable _ _
  have hright : IntervalIntegrable (fun theta =>
      tiltDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y)-
        d*((R*Real.sin theta)^2*energyDensity sigma d q mu L p w c
          ((R*Real.cos theta,R*Real.sin theta),Y))+
        4*energyDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y))
      volume (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  apply (angular_radius_lower sigma d q mu L p w c hsigma R Y).trans
  apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hleft hright
  intro theta _
  have hE : 0≤energyDensity sigma d q mu L p w c ((R*Real.cos theta,R*Real.sin theta),Y) := by
    unfold energyDensity base weight
    positivity
  have hR : (R*Real.sin theta)^2≤R^2 := by
    nlinarith [mul_nonneg (sq_nonneg R) (sub_nonneg.mpr (Real.sin_sq_le_one theta))]
  nlinarith [mul_nonneg (mul_nonneg hd (sub_nonneg.mpr hR)) hE]

private def weightPolynomial (sigma mu L : ℝ) : Polynomial ℝ :=
  (Polynomial.C mu+Polynomial.C L*Polynomial.X)^4+
    Polynomial.C (6*sigma)*(Polynomial.C mu+Polynomial.C L*Polynomial.X)^2+
    Polynomial.C (3*sigma^2)
private theorem weight_eval (sigma mu L v : ℝ) :
    (weightPolynomial sigma mu L).eval v=weight sigma (mu+L*v) := by
  simp [weightPolynomial,weight]

theorem second_moment_integrable (sigma d q mu L : ℝ) (p : ℂ) (w : ι→ℝ) (c : ι→ℂ)
    (hp : 0<p.re) (hw : ∀i,0<w i) (hd : ∀i,d<2*p.re*w i) :
    Integrable (fun x : Charged => x.1.2^2*energyDensity sigma d q mu L p w c x) chargedMeasure := by
  have hi := KFCausalChargedQuarticAngularLoss.polynomial_integrable
    (Polynomial.X^2*weightPolynomial sigma mu L) p d q w c hp hw hd
  simpa only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,weight_eval,
    energyDensity,mul_assoc] using hi

theorem charged_bound (sigma d q mu L : ℝ) (p : ℂ) (w : ι→ℝ) (c : ι→ℂ)
    (hsigma : 0≤sigma) (hd0 : 0≤d) (hp : 0<p.re) (hw : ∀i,0<w i) (hd : ∀i,d<2*p.re*w i) :
    d*(∫x : Charged,x.1.2^2*energyDensity sigma d q mu L p w c x ∂chargedMeasure)-
      4*energy sigma d q mu L p w c ≤ tilt sigma d q mu L p w c := by
  obtain ⟨he,_,ht⟩ := KFCausalChargedQuarticAngularLoss.densities_integrable sigma d q mu L p w c hp hw hd
  have hv := second_moment_integrable sigma d q mu L p w c hp hw hd
  let F : Charged→ℝ := fun x => tiltDensity sigma d q mu L p w c x-
    d*(x.1.2^2*energyDensity sigma d q mu L p w c x)+4*energyDensity sigma d q mu L p w c x
  have hF : Integrable F chargedMeasure := (ht.sub (hv.const_mul d)).add (he.const_mul 4)
  have hFc : Continuous F := by
    unfold F tiltDensity energyDensity base weight packet KFCausalChargedFourierPolynomialGram.atom
    fun_prop
  have hpos : 0≤∫x,F x ∂chargedMeasure := by
    unfold chargedMeasure at hF ⊢
    rw [integral_prod_symm _ hF]
    apply integral_nonneg_of_ae
    filter_upwards [hF.prod_left_ae] with Y hY
    rw [←Measure.volume_eq_prod ℝ ℝ] at hY ⊢
    have hc : Continuous (fun x : ℝ×ℝ => F (x,Y)) := hFc.comp (by fun_prop)
    have hh := KFCausalPlanePolarComparison.integral_le_of_angular (fun _ : ℝ×ℝ => 0)
      (fun x => F (x,Y)) continuous_const hc (integrable_zero _ _ _) hY
      (fun R _ => by simpa only [intervalIntegral.integral_zero] using
        angular_coordinate_lower sigma d q mu L p w c hsigma hd0 R Y)
    simpa only [integral_zero] using hh
  unfold F at hpos
  have hadd := integral_add (ht.sub (hv.const_mul d)) (he.const_mul 4)
  simp only [Pi.sub_apply] at hadd
  rw [hadd,integral_sub ht (hv.const_mul d)] at hpos
  simp only [integral_const_mul] at hpos
  change _-4*energy sigma d q mu L p w c≤tilt sigma d q mu L p w c
  dsimp only [energy,tilt]
  linarith only [hpos]

theorem second_moment_marginal (n : ℕ) (α : ℝ) (r : ℂ) (sigma d q mu L : ℝ)
    (w : Fin n→ℝ) (c : Fin n→ℂ) (hα : 0<α) (hr : |r.im|<r.re)
    (hw : ∀i,0<w i) (hd : ∀i,d<2*(gamma α r).re*w i) :
    (∫x : Charged,x.1.2^2*energyDensity sigma d q mu L (gamma α r) w c x ∂chargedMeasure)=
      ∫v : ℝ,v^2*KFCausalChargedQuarticScoreIBP.energyDensity sigma d q mu L n α r w c v := by
  have hi := KFCausalChargedQuarticScoreAttachment.polynomial_marginal n α r d q w c hα hr hw hd
    (Polynomial.X^2*weightPolynomial sigma mu L)
  simpa only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,weight_eval,
    energyDensity,KFCausalChargedQuarticScoreIBP.energyDensity,mul_assoc] using hi

theorem marginal_bound (n : ℕ) (α : ℝ) (r : ℂ) (sigma d q mu L : ℝ)
    (w : Fin n→ℝ) (c : Fin n→ℂ) (hsigma : 0≤sigma) (hd0 : 0≤d)
    (hα : 0<α) (hr : |r.im|<r.re) (hw : ∀i,0<w i) (hd : ∀i,d<2*(gamma α r).re*w i) :
    d*(∫v : ℝ,v^2*KFCausalChargedQuarticScoreIBP.energyDensity sigma d q mu L n α r w c v)-
      4*(∫v,KFCausalChargedQuarticScoreIBP.energyDensity sigma d q mu L n α r w c v)≤
        ∫v,KFCausalChargedQuarticScoreIBP.tiltDensity sigma d q mu L n α r w c v := by
  have h := charged_bound sigma d q mu L (gamma α r) w c hsigma hd0
    (KFCausalChargedCoolingFixedV.actual_gamma_re_positive α r hα hr) hw hd
  have he := KFCausalChargedQuarticScoreAttachment.energy_field_tilt n α r d q w c hα hr hw hd sigma mu L
  rw [second_moment_marginal n α r sigma d q mu L w c hα hr hw hd,he.1,he.2.2] at h
  exact h

#print axioms second_moment_integrable
#print axioms charged_bound
#print axioms second_moment_marginal
#print axioms marginal_bound
end
end UnifiedTheory.Audit.KFCausalChargedQuarticHardy
