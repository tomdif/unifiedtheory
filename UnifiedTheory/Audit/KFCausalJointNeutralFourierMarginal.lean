/- The exact moving neutral quartic marginal has an explicit Fourier
response. Its charged coefficients move with the physical chart. The
remaining outer charged integrations are not differentiated here. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierMovingIntegral
import UnifiedTheory.Audit.KFCausalJointNeutralFourierIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalJointNeutralFourierMarginal
noncomputable section
open MeasureTheory
open KFCausalNeutralFourierEnergy (frequencyMoment frequencyDensity)
open KFCausalNeutralFourierResponseSplit (frequencyResponse)
open KFCausalNeutralFourierMovingJet (chargedSlope)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalJointNeutralFourierIntegral (frequencySlice)
open KFCausalClockFloorRelativeShift (scale)

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

def fieldResponse (r rd : ℂ) (u v Y : ℝ) (j : ℕ) (k : ℝ) : ℝ :=
  frequencyResponse n β b (coefficients n w c (chart α r (u^2+v^2) Y))
    (chargedSlope n α w c r rd u v Y) P j (fieldSlope r*v) (2*r.im*v) (-2*rd.re*v) (2*rd.im*v) k

def quarticResponse (r rd : ℂ) (u v Y k : ℝ) : ℝ :=
  fieldResponse n α β w b c P r rd u v Y 0 k+
    fieldResponse n α β w b c P r rd u v Y 1 k/2+
    fieldResponse n α β w b c P r rd u v Y 2 k/4

variable (hβ : 0 < β)
include hβ

theorem fieldResponse_integrable (r rd : ℂ) (u v Y : ℝ) (j : ℕ) :
    Integrable (fieldResponse n α β w b c P r rd u v Y j) :=
  KFCausalNeutralFourierResponseSplit.frequencyResponse_integrable n β b _ _ P hβ j _ _ _ _

theorem quarticResponse_integrable (r rd : ℂ) (u v Y : ℝ) :
    Integrable (quarticResponse n α β w b c P r rd u v Y) :=
  ((fieldResponse_integrable n α β w b c P hβ r rd u v Y 0).add
    ((fieldResponse_integrable n α β w b c P hβ r rd u v Y 1).div_const 2)).add
    ((fieldResponse_integrable n α β w b c P hβ r rd u v Y 2).div_const 4)

theorem energy_split (r : ℂ) (u v Y : ℝ) :
    (∫ k, frequencySlice n β w b c P r (chart α r (u^2+v^2) Y) v k) =
      (∫ k, frequencyMoment n β b (coefficients n w c (chart α r (u^2+v^2) Y)) P 0 (fieldSlope r*v) (2*r.im*v) k)+
      (∫ k, frequencyMoment n β b (coefficients n w c (chart α r (u^2+v^2) Y)) P 1 (fieldSlope r*v) (2*r.im*v) k)/2+
      (∫ k, frequencyMoment n β b (coefficients n w c (chart α r (u^2+v^2) Y)) P 2 (fieldSlope r*v) (2*r.im*v) k)/4 := by
  have hi := KFCausalNeutralFourierEnergy.frequencyMoment_integrable n β b
    (coefficients n w c (chart α r (u^2+v^2) Y)) P hβ
  unfold frequencySlice frequencyDensity
  have hs := integral_add ((hi 0 (fieldSlope r*v) (2*r.im*v)).add ((hi 1 (fieldSlope r*v) (2*r.im*v)).div_const 2)) ((hi 2 (fieldSlope r*v) (2*r.im*v)).div_const 4)
  simp only [Pi.add_apply] at hs
  rw [hs,integral_add (hi 0 (fieldSlope r*v) (2*r.im*v)) ((hi 1 (fieldSlope r*v) (2*r.im*v)).div_const 2),integral_div,integral_div]

theorem response_split (r rd : ℂ) (u v Y : ℝ) :
    (∫ k, quarticResponse n α β w b c P r rd u v Y k) =
      (∫ k, fieldResponse n α β w b c P r rd u v Y 0 k)+
      (∫ k, fieldResponse n α β w b c P r rd u v Y 1 k)/2+
      (∫ k, fieldResponse n α β w b c P r rd u v Y 2 k)/4 := by
  have hi := fieldResponse_integrable n α β w b c P hβ r rd u v Y
  unfold quarticResponse
  have hs := integral_add ((hi 0).add ((hi 1).div_const 2)) ((hi 2).div_const 4)
  simp only [Pi.add_apply] at hs
  rw [hs,integral_add (hi 0) ((hi 1).div_const 2),integral_div,integral_div]

theorem marginal_derivative (r rd : ℝ → ℂ) (hr : Continuous r) (hrd : Continuous rd)
    (hr' : ∀ t, HasDerivAt r (rd t) t) (s u v Y : ℝ) :
    HasDerivAt (fun t => ∫ k, frequencySlice n β w b c P (r t) (chart α (r t) (u^2+v^2) Y) v k)
      (∫ k, quarticResponse n α β w b c P (r s) (rd s) u v Y k) s := by
  have hd := KFCausalNeutralFourierMovingIntegral.actual_frequency_energy_derivative n β hβ b P
    α w c r rd hr hrd hr' s u v Y
  have he := ((hd 0).add ((hd 1).div_const 2)).add ((hd 2).div_const 4)
  convert he using 1
  · funext t
    exact energy_split n α β w b c P hβ (r t) u v Y
  · exact response_split n α β w b c P hβ (r s) (rd s) u v Y

theorem actual_clock_marginal_derivative (ε y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (s u v Y : ℝ) :
    HasDerivAt (fun t => ∫ k, frequencySlice n β w b c P (scale ε y t)
      (chart α (scale ε y t) (u^2+v^2) Y) v k)
      (∫ k, quarticResponse n α β w b c P (scale ε y s) (deriv (scale ε y) s) u v Y k) s := by
  have hr := KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy
  have hd := contDiff_one_iff_deriv.mp hr
  exact marginal_derivative n α β w b c P hβ (scale ε y) (deriv (scale ε y))
    hr.continuous hd.2 (fun t => (hd.1 t).hasDerivAt) s u v Y

#print axioms fieldResponse_integrable
#print axioms quarticResponse_integrable
#print axioms energy_split
#print axioms response_split
#print axioms marginal_derivative
#print axioms actual_clock_marginal_derivative
end
end UnifiedTheory.Audit.KFCausalJointNeutralFourierMarginal
