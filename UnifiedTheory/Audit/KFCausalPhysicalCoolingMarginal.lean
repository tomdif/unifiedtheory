/- Exact half-plane marginal of the original corrected quartic clock
response, including arbitrary finite neutral sources and polynomials. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingResponseMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalPhysicalCoolingMarginal
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalChargedCoolingPhysicalMarginal
open KFCausalChargedCoolingResponseMarginal
open KFCausalChargedCoolingMarginalDerivative (marginalSlope coolingForm)
open KFCausalChargedCoolingDerivative (form)
open KFCausalReciprocalWedgeGeometry (gamma chart)
open KFCausalQuarticPlaneDomination (potential potentialSlope)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalCorrelatedFourierCoolingResponse (cooling fieldCooling)
open KFCausalNeutralFourierMovingJet (chargedSlope)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalNeutralFourierShift (line)

theorem line_charged_slope (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (r : ℂ) (δ u v Y x : ℝ) :
    line n β b (chargedSlope n α w c r (δ:ℂ) u v Y) P (2*r.im*v) x =
      (δ:ℂ)*packetSlope n (gamma α r) ((α:ℂ)*r) w
        (neutralCoefficients n β w b c P r v x) u v Y := by
  unfold line KFCausalGaussianContourShift.horizontal KFCausalNeutralLineDomain.family packetSlope
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold chargedSlope coefficients neutralCoefficients atomSlope KFCausalClusteredClockFactors.Zd
  rw [atom_chart]
  simp only [Matrix.cons_val_zero,map_mul,Complex.conj_ofReal]
  push_cast
  ring

private theorem quartic_response_weight (F G : ℂ) (t ad : ℝ) :
    2*(conj F*G).re+
      2*(conj ((t:ℂ)*F)*((t:ℂ)*G+(ad:ℂ)*F)).re/2+
      2*(conj ((t:ℂ)^2*F)*((t:ℂ)^2*G+2*(ad:ℂ)*(t:ℂ)*F)).re/4 =
      potential t*(2*(conj F*G).re)+ad*potentialSlope t*‖F‖^2 := by
  rw [Complex.sq_norm]
  simp only [potential,potentialSlope,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,
    Complex.ofReal_im]
  norm_num [pow_two,Complex.mul_re,Complex.mul_im]
  ring

theorem cooling_density (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (r rd : ℂ) (ell u v Y x : ℝ) :
    cooling n α β w b c P r rd ell ((u,![v,x]),Y) =
      (rd.re-ell*r.re)*potential (x+fieldSlope r*v)*
        packetResponse n (gamma α r) ((α:ℂ)*r) w
          (neutralCoefficients n β w b c P r v x) u v Y+
      (-2*(rd.re-ell*r.re)-3*ell)*v*potentialSlope (x+fieldSlope r*v)*
        ‖packetSum n (gamma α r) w (neutralCoefficients n β w b c P r v x) u v Y‖^2 := by
  unfold cooling fieldCooling KFCausalNeutralFourierResponseSplit.response
    KFCausalNeutralFourierResponseSplit.slope KFCausalNeutralFourierField.fieldLine
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,KFCausalClusteredClockFactors.Z]
  simp only [line_packet,line_charged_slope,Complex.ofReal_zero,mul_zero,zero_mul,add_zero,
    Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,Nat.reduceSub,pow_zero,pow_one,one_mul]
  have he := quartic_response_weight
    (packetSum n (gamma α r) w (neutralCoefficients n β w b c P r v x) u v Y)
    ((rd.re-ell*r.re:ℝ)*packetSlope n (gamma α r) ((α:ℂ)*r) w
      (neutralCoefficients n β w b c P r v x) u v Y)
    (x+fieldSlope r*v) ((-2*(rd.re-ell*r.re)-3*ell)*v)
  convert he using 1
  · congr 2
    congr 2
    congr 1
    push_cast
    ring
  · unfold packetResponse
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,add_zero]
    ring

theorem cooling_marginal_integrable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (r rd : ℂ) (ell : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i) (v x : ℝ) :
    Integrable (fun q : ℝ × ℝ => cooling n α β w b c P r rd ell ((q.1,![v,x]),q.2)) planeMeasure := by
  simp_rw [cooling_density]
  have hp := KFCausalChargedCoolingFixedV.actual_gamma_re_positive α r hα hr
  exact ((packet_response_integrable n (gamma α r) ((α:ℂ)*r) w _ hp hw v).const_mul _).add
    ((packet_square_integrable n (gamma α r) w _ hp hw v).const_mul _)

theorem cooling_marginal_integral (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (r rd : ℂ) (ell : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i) (v x : ℝ) :
    (∫ q : ℝ × ℝ, cooling n α β w b c P r rd ell ((q.1,![v,x]),q.2) ∂planeMeasure) =
      marginalSlope n α r w (neutralCoefficients n β w b c P r v x)
        (rd.re-ell*r.re) (fieldSlope r) (-2*(rd.re-ell*r.re)-3*ell) v x := by
  simp_rw [cooling_density]
  have hp := KFCausalChargedCoolingFixedV.actual_gamma_re_positive α r hα hr
  have hR := (packet_response_integrable n (gamma α r) ((α:ℂ)*r) w
    (neutralCoefficients n β w b c P r v x) hp hw v).const_mul
      ((rd.re-ell*r.re)*potential (x+fieldSlope r*v))
  have hE := (packet_square_integrable n (gamma α r) w
    (neutralCoefficients n β w b c P r v x) hp hw v).const_mul
      ((-2*(rd.re-ell*r.re)-3*ell)*v*potentialSlope (x+fieldSlope r*v))
  rw [integral_add hR hE,integral_const_mul,integral_const_mul,
    packet_response_integral n (gamma α r) ((α:ℂ)*r) w _ hp hw v,
    packet_square_integral n (gamma α r) w _ hp hw v]
  unfold marginalSlope coolingForm gamma
  simp only [map_div₀,map_mul,map_pow,Complex.conj_ofReal,Complex.conj_ofNat]
  ring

#print axioms line_charged_slope
#print axioms cooling_density
#print axioms cooling_marginal_integrable
#print axioms cooling_marginal_integral
end
end UnifiedTheory.Audit.KFCausalPhysicalCoolingMarginal
