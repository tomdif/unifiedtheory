/- Exact correction by charged-coordinate dilation. The neutral
imaginary translation cancels when r'.im = lambda*r.im; the remaining
real field correction includes the constant 3 in fieldSlope. This file
is a pointwise and neutral-integrated identity, not a charged divergence
identity or a dissipative inequality. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierMovingIntegral
import UnifiedTheory.Audit.KFCausalJointClockCoolingCoercivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalJointFourierDilationJet
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalNeutralFourierField (fieldLine)
open KFCausalNeutralFourierShift (line)
open KFCausalNeutralLineDomain (family)
open KFCausalNeutralFourierResponseSplit (response)
open KFCausalNeutralFourierMovingJet (chargedSlope)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalWedgeGeometry (chart gamma)
open KFCausalClusteredClockFactors (Zd)

variable (n : ℕ) (β : ℝ) (b : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

theorem fieldLine_sub (c d : Fin n → ℂ) (j : ℕ) (a y x : ℝ) :
    fieldLine n β b (fun i => c i-d i) P j a y x =
      fieldLine n β b c P j a y x-fieldLine n β b d P j a y x := by
  unfold fieldLine line KFCausalGaussianContourShift.horizontal family
  simp only [sub_mul,Finset.sum_sub_distrib,mul_sub]

theorem response_sub (c d e : Fin n → ℂ) (j : ℕ) (a y ad yd ae ye x : ℝ) :
    response n β b c d P j a y ad yd x-response n β b c e P j a y ae ye x =
      response n β b c (fun i => d i-e i) P j a y (ad-ae) (yd-ye) x := by
  unfold response KFCausalNeutralFourierResponseSplit.slope
  rw [fieldLine_sub]
  push_cast
  rw [show fieldLine n β b d P j a y x-fieldLine n β b e P j a y x+
      (j:ℂ)*((ad:ℂ)-(ae:ℂ))*fieldLine n β b c P (j-1) a y x+
      (Complex.I*((yd:ℂ)-(ye:ℂ)))*fieldLine n β b c (fun i => KFCausalNeutralLinePackets.step β (b i) (P i)) j a y x =
      (fieldLine n β b d P j a y x+(j:ℂ)*(ad:ℂ)*fieldLine n β b c P (j-1) a y x+
        (Complex.I*(yd:ℂ))*fieldLine n β b c (fun i => KFCausalNeutralLinePackets.step β (b i) (P i)) j a y x)-
      (fieldLine n β b e P j a y x+(j:ℂ)*(ae:ℂ)*fieldLine n β b c P (j-1) a y x+
        (Complex.I*(ye:ℂ))*fieldLine n β b c (fun i => KFCausalNeutralLinePackets.step β (b i) (P i)) j a y x) by ring]
  rw [mul_sub,Complex.sub_re]
  ring

omit n β b P in
theorem corrected_velocity_real (r rd : ℂ) (ell : ℝ) (hi : rd.im=ell*r.im) :
    rd-(ell:ℂ)*r = ((rd.re-ell*r.re:ℝ):ℂ) := by
  apply Complex.ext <;> simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  linarith

omit n β b P in
theorem corrected_chart (α : ℝ) (r rd : ℂ) (ell u v Y : ℝ) :
    Zd α r rd ((u,![v,0]),Y)-(2*ell:ℝ)*chart α r (u^2+v^2) Y =
      Zd α r (rd-(ell:ℂ)*r) ((u,![v,0]),Y) := by
  unfold Zd chart gamma
  simp only [Matrix.cons_val_zero,map_sub,map_mul,map_div₀,map_pow,Complex.conj_ofReal,map_ofNat]
  push_cast
  ring

omit n β b P in
theorem corrected_field (r rd : ℂ) (ell v : ℝ) :
    -2*rd.re*v-ell*(fieldSlope r*v) = (-2*(rd.re-ell*r.re)-3*ell)*v := by
  unfold fieldSlope
  ring

omit β b P in
def dilationCoefficients (α : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (r : ℂ) (ell u v Y : ℝ) (i : Fin n) : ℂ :=
  -(w i:ℂ)*((2*ell:ℝ):ℂ)*chart α r (u^2+v^2) Y*
    coefficients n w c (chart α r (u^2+v^2) Y) i

omit β b P in
theorem corrected_coefficients (α : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (r rd : ℂ) (ell u v Y : ℝ) :
    (fun i => chargedSlope n α w c r rd u v Y i-dilationCoefficients n α w c r ell u v Y i) =
      chargedSlope n α w c r (rd-(ell:ℂ)*r) u v Y := by
  funext i
  unfold chargedSlope dilationCoefficients
  rw [← corrected_chart]
  ring

theorem corrected_response (α : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (r rd : ℂ) (ell u v Y x : ℝ) (j : ℕ) (hi : rd.im=ell*r.im) :
    response n β b (coefficients n w c (chart α r (u^2+v^2) Y))
      (chargedSlope n α w c r rd u v Y) P j (fieldSlope r*v) (2*r.im*v) (-2*rd.re*v) (2*rd.im*v) x-
    response n β b (coefficients n w c (chart α r (u^2+v^2) Y))
      (dilationCoefficients n α w c r ell u v Y) P j (fieldSlope r*v) (2*r.im*v)
        (ell*(fieldSlope r*v)) (ell*(2*r.im*v)) x =
    response n β b (coefficients n w c (chart α r (u^2+v^2) Y))
      (chargedSlope n α w c r ((rd.re-ell*r.re:ℝ):ℂ) u v Y) P j (fieldSlope r*v) (2*r.im*v)
        ((-2*(rd.re-ell*r.re)-3*ell)*v) 0 x := by
  rw [response_sub,corrected_coefficients,corrected_velocity_real r rd ell hi,corrected_field]
  have he : 2*rd.im*v-ell*(2*r.im*v)=0 := by rw [hi]; ring
  rw [he]

theorem corrected_integral (hβ : 0 < β) (α : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (r rd : ℂ) (ell u v Y : ℝ) (j : ℕ) (hi : rd.im=ell*r.im) :
    (∫ x, response n β b (coefficients n w c (chart α r (u^2+v^2) Y))
      (chargedSlope n α w c r rd u v Y) P j (fieldSlope r*v) (2*r.im*v) (-2*rd.re*v) (2*rd.im*v) x)-
    (∫ x, response n β b (coefficients n w c (chart α r (u^2+v^2) Y))
      (dilationCoefficients n α w c r ell u v Y) P j (fieldSlope r*v) (2*r.im*v)
        (ell*(fieldSlope r*v)) (ell*(2*r.im*v)) x) =
    2*(∫ k, KFCausalNeutralFourierPairing.weightedCross n β b
      (coefficients n w c (chart α r (u^2+v^2) Y))
      (chargedSlope n α w c r ((rd.re-ell*r.re:ℝ):ℂ) u v Y) P P j j (fieldSlope r*v) (2*r.im*v) k).re+
    2*(j:ℝ)*((-2*(rd.re-ell*r.re)-3*ell)*v)*(∫ k, KFCausalNeutralFourierPairing.weightedCross n β b
      (coefficients n w c (chart α r (u^2+v^2) Y))
      (coefficients n w c (chart α r (u^2+v^2) Y)) P P j (j-1) (fieldSlope r*v) (2*r.im*v) k).re := by
  rw [← integral_sub (KFCausalNeutralFourierResponseSplit.response_integrable n β b _ _ P hβ j _ _ _ _)
    (KFCausalNeutralFourierResponseSplit.response_integrable n β b _ _ P hβ j _ _ _ _)]
  simp_rw [corrected_response n β b P α w c r rd ell u v Y _ j hi]
  rw [KFCausalNeutralFourierResponseSplit.response_integral_split n β b _ _ P hβ]
  ring

omit n β b P in
theorem actual_imaginary_cancellation (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    (deriv (KFCausalClockFloorRelativeShift.scale ε y) s).im =
      KFCausalJointClockCoolingCoercivity.imaginaryRate
        (KFCausalNeutralPlaneNormalizedGeometry.fraction ε s) (KFCausalClockFloorRelativeShift.scale ε y s)*
        (KFCausalClockFloorRelativeShift.scale ε y s).im := by
  rw [(KFCausalNeutralPlaneNormalizedGeometry.actual_normalized_velocity ε y s hε hy).deriv]
  exact KFCausalJointClockCoolingCoercivity.imaginary_velocity _ _

#print axioms fieldLine_sub
#print axioms response_sub
#print axioms corrected_velocity_real
#print axioms corrected_chart
#print axioms corrected_field
#print axioms corrected_coefficients
#print axioms corrected_response
#print axioms corrected_integral
#print axioms actual_imaginary_cancellation
end
end UnifiedTheory.Audit.KFCausalJointFourierDilationJet
