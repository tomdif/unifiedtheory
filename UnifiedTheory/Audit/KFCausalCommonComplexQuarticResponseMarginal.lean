/- Literal corrected quartic response for a common complex neutral
source. The charged derivative is the actual derivative of its coherent
half-plane marginal. Neutral integration keeps its exact Gaussian mass,
mean, variance, and both source components. -/
import UnifiedTheory.Audit.KFCausalPhysicalCoolingMarginal
import UnifiedTheory.Audit.KFCausalCommonComplexQuarticJointAngular
import UnifiedTheory.Audit.KFCausalChargedQuarticScoreIBP

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexQuarticResponseMarginal
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalChargedCoolingPhysicalMarginal
open KFCausalChargedCoolingResponseMarginal
open KFCausalChargedCoolingMarginalScore (marginal)
open KFCausalReciprocalWedgeGeometry (gamma)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalCorrelatedFourierCoolingResponse (fieldCooling)
open KFCausalCommonComplexQuarticJointAngular (source)
open KFCausalCommonRealGaussianEnergy (neutralWeight neutralMoment)
open KFCausalNeutralLinePackets (entire)

private theorem response_weight (F G : ℂ) (t ad : ℝ) :
    2*(conj ((t:ℂ)^2*F)*((t:ℂ)^2*G+2*(ad:ℂ)*(t:ℂ)*F)).re=
      t^4*(2*(conj F*G).re)+4*ad*t^3*‖F‖^2 := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  norm_num [pow_two,Complex.mul_re,Complex.mul_im]
  ring

theorem quartic_cooling_density (n : ℕ) (α β : ℝ) (w : Fin n→ℝ) (b c : Fin n→ℂ)
    (P : Fin n→Polynomial ℂ) (r rd : ℂ) (ell u v Y x : ℝ) :
    fieldCooling n α β w b c P r rd ell 2 ((u,![v,x]),Y)=
      (rd.re-ell*r.re)*(x+fieldSlope r*v)^4*
        packetResponse n (gamma α r) ((α:ℂ)*r) w (neutralCoefficients n β w b c P r v x) u v Y+
      4*(-2*(rd.re-ell*r.re)-3*ell)*v*(x+fieldSlope r*v)^3*
        ‖packetSum n (gamma α r) w (neutralCoefficients n β w b c P r v x) u v Y‖^2 := by
  unfold fieldCooling KFCausalNeutralFourierResponseSplit.response
    KFCausalNeutralFourierResponseSplit.slope KFCausalNeutralFourierField.fieldLine
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,KFCausalClusteredClockFactors.Z,
    line_packet,KFCausalPhysicalCoolingMarginal.line_charged_slope,Complex.ofReal_zero,
    mul_zero,zero_mul,add_zero,Nat.cast_ofNat,Nat.reduceSub,pow_one]
  have he := response_weight
    (packetSum n (gamma α r) w (neutralCoefficients n β w b c P r v x) u v Y)
    (((rd.re-ell*r.re:ℝ):ℂ)*packetSlope n (gamma α r) ((α:ℂ)*r) w
      (neutralCoefficients n β w b c P r v x) u v Y)
    (x+fieldSlope r*v) ((-2*(rd.re-ell*r.re)-3*ell)*v)
  convert he using 1
  · congr 2
    push_cast
    ring
  · unfold packetResponse
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,add_zero]
    ring

theorem response_integral_derivative (n : ℕ) (α : ℝ) (r : ℂ) (w : Fin n→ℝ) (c : Fin n→ℂ)
    (v : ℝ) (hα : 0<α) (hr : |r.im|<r.re) (hw : ∀i,0<w i) :
    (∫z : ℝ×ℝ,packetResponse n (gamma α r) ((α:ℂ)*r) w c z.1 v z.2 ∂planeMeasure)=
      deriv (fun t : ℝ=>marginal n α (r+(t:ℂ)) w c v) 0 := by
  rw [(KFCausalChargedCoolingMarginalScore.marginal_real_derivative n α r w c v hα hr hw).deriv,
    packet_response_integral n (gamma α r) ((α:ℂ)*r) w c
      (KFCausalChargedCoolingFixedV.actual_gamma_re_positive α r hα hr) hw v]
  unfold KFCausalChargedCoolingMarginalDerivative.coolingForm gamma
  simp only [map_div₀,map_mul,map_pow,Complex.conj_ofReal,Complex.conj_ofNat]

theorem neutral_norm (β A D : ℝ) (r : ℂ) (v x : ℝ) :
    ‖entire β (source A D) 1 ((x:ℂ)+(2*r.im*v:ℝ)*Complex.I)‖^2=
      neutralWeight β A x*Real.exp ((8*β*r.im^2)*v^2-(4*D*r.im)*v) := by
  simp only [entire,Polynomial.eval_one,mul_one,Complex.norm_exp,←Real.exp_nat_mul]
  rw [neutralWeight,←Real.exp_add]
  congr 1
  simp [source,Complex.mul_re,Complex.mul_im,pow_two]
  ring

private theorem packet_scalar (n : ℕ) (p : ℂ) (w : Fin n→ℝ) (c : Fin n→ℂ)
    (a : ℂ) (u v Y : ℝ) :
    packetSum n p w (fun i=>c i*a) u v Y=a*packetSum n p w c u v Y := by
  simp only [packetSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
private theorem response_scalar (n : ℕ) (p q : ℂ) (w : Fin n→ℝ) (c : Fin n→ℂ)
    (a : ℂ) (u v Y : ℝ) :
    packetResponse n p q w (fun i=>c i*a) u v Y=‖a‖^2*packetResponse n p q w c u v Y := by
  have hs : packetSlope n p q w (fun i=>c i*a) u v Y=a*packetSlope n p q w c u v Y := by
    simp only [packetSlope,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold packetResponse
  rw [packet_scalar,hs,map_mul,Complex.sq_norm]
  have he : conj a*conj (packetSum n p w c u v Y)*(a*packetSlope n p q w c u v Y)=
      (Complex.normSq a:ℂ)*(conj (packetSum n p w c u v Y)*packetSlope n p q w c u v Y) := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [he,Complex.re_ofReal_mul]
  ring

variable (n : ℕ) (α β A D : ℝ) (w : Fin n→ℝ) (r rd : ℂ) (c : Fin n→ℂ) (ell : ℝ)

theorem common_cooling_density (u v Y x : ℝ) :
    fieldCooling n α β w (fun _=>source A D) c (fun _=>1) r rd ell 2 ((u,![v,x]),Y)=
      neutralWeight β A x*Real.exp ((8*β*r.im^2)*v^2-(4*D*r.im)*v)*
        ((rd.re-ell*r.re)*(x+fieldSlope r*v)^4*
          packetResponse n (gamma α r) ((α:ℂ)*r) w (fun i=>c i*(w i:ℂ)) u v Y+
        4*(-2*(rd.re-ell*r.re)-3*ell)*v*(x+fieldSlope r*v)^3*
          ‖packetSum n (gamma α r) w (fun i=>c i*(w i:ℂ)) u v Y‖^2) := by
  rw [quartic_cooling_density]
  have he : neutralCoefficients n β w (fun _=>source A D) c (fun _=>1) r v x=
      fun i=>(c i*(w i:ℂ))*entire β (source A D) 1 ((x:ℂ)+(2*r.im*v:ℝ)*Complex.I) := rfl
  rw [he,response_scalar,packet_scalar,norm_mul,mul_pow,neutral_norm]
  ring

variable (hα : 0<α) (hr : |r.im|<r.re) (hw : ∀i,0<w i)
include hα hr hw

theorem cooling_marginal_integrable (v x : ℝ) :
    Integrable (fun z : ℝ×ℝ=>fieldCooling n α β w (fun _=>source A D) c (fun _=>1)
      r rd ell 2 ((z.1,![v,x]),z.2)) planeMeasure := by
  simp_rw [common_cooling_density]
  have hp := KFCausalChargedCoolingFixedV.actual_gamma_re_positive α r hα hr
  exact (((packet_response_integrable n (gamma α r) ((α:ℂ)*r) w _ hp hw v).const_mul _).add
    ((packet_square_integrable n (gamma α r) w _ hp hw v).const_mul _)).const_mul _

theorem cooling_marginal (v x : ℝ) :
    (∫z : ℝ×ℝ,fieldCooling n α β w (fun _=>source A D) c (fun _=>1)
      r rd ell 2 ((z.1,![v,x]),z.2) ∂planeMeasure)=
      neutralWeight β A x*Real.exp ((8*β*r.im^2)*v^2-(4*D*r.im)*v)*
        ((rd.re-ell*r.re)*(x+fieldSlope r*v)^4*
          deriv (fun t : ℝ=>marginal n α (r+(t:ℂ)) w (fun i=>c i*(w i:ℂ)) v) 0+
        4*(-2*(rd.re-ell*r.re)-3*ell)*v*(x+fieldSlope r*v)^3*
          marginal n α r w (fun i=>c i*(w i:ℂ)) v) := by
  simp_rw [common_cooling_density]
  have hp := KFCausalChargedCoolingFixedV.actual_gamma_re_positive α r hα hr
  rw [integral_const_mul,integral_add
    ((packet_response_integrable n (gamma α r) ((α:ℂ)*r) w _ hp hw v).const_mul _)
    ((packet_square_integrable n (gamma α r) w _ hp hw v).const_mul _),
    integral_const_mul,integral_const_mul,response_integral_derivative n α r w _ v hα hr hw]
  rfl

theorem cooling_neutral_integral (hβ : 0<β) (v : ℝ) :
    (∫x : ℝ,∫z : ℝ×ℝ,fieldCooling n α β w (fun _=>source A D) c (fun _=>1)
      r rd ell 2 ((z.1,![v,x]),z.2) ∂planeMeasure)=
      neutralMoment β A 0*
        (-(rd.re-ell*r.re)*KFCausalChargedQuarticScoreIBP.coolingDensity (1/(4*β))
          (8*β*r.im^2) (4*D*r.im) (A/(2*β)) (fieldSlope r) n α r w (fun i=>c i*(w i:ℂ)) v+
        (-2*(rd.re-ell*r.re)-3*ell)*KFCausalChargedQuarticScoreIBP.fieldDensity (1/(4*β))
          (8*β*r.im^2) (4*D*r.im) (A/(2*β)) (fieldSlope r) n α r w (fun i=>c i*(w i:ℂ)) v) := by
  simp_rw [cooling_marginal n α β A D w r rd c ell hα hr hw]
  let e := Real.exp ((8*β*r.im^2)*v^2-(4*D*r.im)*v)
  let f := marginal n α r w (fun i=>c i*(w i:ℂ)) v
  let fa := deriv (fun t : ℝ=>marginal n α (r+(t:ℂ)) w (fun i=>c i*(w i:ℂ)) v) 0
  have he (x : ℝ) : neutralWeight β A x*e*((rd.re-ell*r.re)*(x+fieldSlope r*v)^4*fa+
      4*(-2*(rd.re-ell*r.re)-3*ell)*v*(x+fieldSlope r*v)^3*f)=
      (e*(rd.re-ell*r.re)*fa)*((x+fieldSlope r*v)^4*neutralWeight β A x)+
      (e*(-2*(rd.re-ell*r.re)-3*ell)*v*f)*(4*(x+fieldSlope r*v)^3*neutralWeight β A x) := by ring
  change (∫x,neutralWeight β A x*e*((rd.re-ell*r.re)*(x+fieldSlope r*v)^4*fa+
      4*(-2*(rd.re-ell*r.re)-3*ell)*v*(x+fieldSlope r*v)^3*f))=_
  simp_rw [he]
  have h4 := KFCausalCommonComplexQuarticNeutralIntegral.quartic_integrable β A (fieldSlope r*v) hβ
  have h3 : Integrable (fun x : ℝ=>4*(x+fieldSlope r*v)^3*neutralWeight β A x) := by
    have hi := KFCausalCommonComplexQuarticNeutralIntegral.polynomial_integrable β A hβ
      (Polynomial.C 4*(Polynomial.X+Polynomial.C (fieldSlope r*v))^3)
    simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X] using hi
  rw [integral_add (h4.const_mul _) (h3.const_mul _),integral_const_mul,integral_const_mul,
    KFCausalCommonComplexQuarticNeutralIntegral.quartic_integral β A _ hβ,
    KFCausalCommonComplexQuarticNeutralIntegral.cubic_integral β A _ hβ]
  dsimp only [e,f,fa,KFCausalChargedQuarticScoreIBP.coolingDensity,KFCausalChargedQuarticScoreIBP.fieldDensity]
  ring

#print axioms quartic_cooling_density
#print axioms response_integral_derivative
#print axioms neutral_norm
#print axioms common_cooling_density
#print axioms cooling_marginal_integrable
#print axioms cooling_marginal
#print axioms cooling_neutral_integral
end
end UnifiedTheory.Audit.KFCausalCommonComplexQuarticResponseMarginal
