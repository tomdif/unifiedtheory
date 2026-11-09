/- Pointwise identification of the full physical quartic density and
its clock response with moving neutral fields. All charged jets remain
inside the summed fields. -/
import UnifiedTheory.Audit.KFCausalJointNeutralFourierMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalJointNeutralFourierOuterDensity
noncomputable section
open MeasureTheory
open KFCausalNeutralFourierField (fieldLine)
open KFCausalNeutralFourierMovingJet (chargedSlope)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalJointNeutralFourierMarginal (fieldResponse quarticResponse)

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

def spatialFieldResponse (r rd : ℂ) (u v Y : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  KFCausalNeutralFourierResponseSplit.response n β b
    (coefficients n w c (chart α r (u^2+v^2) Y))
    (chargedSlope n α w c r rd u v Y) P j
    (fieldSlope r*v) (2*r.im*v) (-2*rd.re*v) (2*rd.im*v) x

def spatialQuarticResponse (r rd : ℂ) (u v Y x : ℝ) : ℝ :=
  spatialFieldResponse n α β w b c P r rd u v Y 0 x+
    spatialFieldResponse n α β w b c P r rd u v Y 1 x/2+
    spatialFieldResponse n α β w b c P r rd u v Y 2 x/4

theorem density_quartic (r : ℂ) (u v x Y : ℝ) :
    positiveDensity n α β w r c (fun i => exponentialProfile (b i) 1 (P i)) ((u,![v,x]),Y) =
      ‖fieldLine n β b (coefficients n w c (chart α r (u^2+v^2) Y)) P 0 (fieldSlope r*v) (2*r.im*v) x‖^2+
      ‖fieldLine n β b (coefficients n w c (chart α r (u^2+v^2) Y)) P 1 (fieldSlope r*v) (2*r.im*v) x‖^2/2+
      ‖fieldLine n β b (coefficients n w c (chart α r (u^2+v^2) Y)) P 2 (fieldSlope r*v) (2*r.im*v) x‖^2/4 := by
  rw [KFCausalJointNeutralFourierIntegral.density_slice,
    KFCausalJointNeutralFourierIntegral.jointSlice_line,
    KFCausalNeutralFourierEnergy.quartic_density]

theorem density_derivative (r : ℝ → ℂ) (rd : ℂ) (s u v x Y : ℝ)
    (hr : HasDerivAt r rd s) :
    HasDerivAt (fun t => positiveDensity n α β w (r t) c
      (fun i => exponentialProfile (b i) 1 (P i)) ((u,![v,x]),Y))
      (spatialQuarticResponse n α β w b c P (r s) rd u v Y x) s := by
  have hd := KFCausalNeutralFourierMovingJet.actual_square_derivative n β b P α w c r rd s u v x Y
  convert ((hd 0 hr).add ((hd 1 hr).div_const 2)).add ((hd 2 hr).div_const 4) using 1
  funext t
  exact density_quartic n α β w b c P (r t) u v x Y

variable (hβ : 0 < β)
include hβ

theorem spatialFieldResponse_integrable (r rd : ℂ) (u v Y : ℝ) (j : ℕ) :
    Integrable (spatialFieldResponse n α β w b c P r rd u v Y j) :=
  KFCausalNeutralFourierResponseSplit.response_integrable n β b _ _ P hβ j _ _ _ _

theorem spatialQuarticResponse_integrable (r rd : ℂ) (u v Y : ℝ) :
    Integrable (spatialQuarticResponse n α β w b c P r rd u v Y) :=
  ((spatialFieldResponse_integrable n α β w b c P hβ r rd u v Y 0).add
    ((spatialFieldResponse_integrable n α β w b c P hβ r rd u v Y 1).div_const 2)).add
    ((spatialFieldResponse_integrable n α β w b c P hβ r rd u v Y 2).div_const 4)

theorem spatialFieldResponse_integral (r rd : ℂ) (u v Y : ℝ) (j : ℕ) :
    (∫ x, spatialFieldResponse n α β w b c P r rd u v Y j x) =
      ∫ k, fieldResponse n α β w b c P r rd u v Y j k :=
  KFCausalNeutralFourierResponseSplit.response_frequency_integral n β b _ _ P hβ j _ _ _ _

theorem spatialQuarticResponse_integral (r rd : ℂ) (u v Y : ℝ) :
    (∫ x, spatialQuarticResponse n α β w b c P r rd u v Y x) =
      ∫ k, quarticResponse n α β w b c P r rd u v Y k := by
  have hi := spatialFieldResponse_integrable n α β w b c P hβ r rd u v Y
  unfold spatialQuarticResponse
  have hs := integral_add ((hi 0).add ((hi 1).div_const 2)) ((hi 2).div_const 4)
  simp only [Pi.add_apply] at hs
  rw [hs,integral_add (hi 0) ((hi 1).div_const 2),integral_div,integral_div]
  simp only [spatialFieldResponse_integral n α β w b c P hβ]
  exact (KFCausalJointNeutralFourierMarginal.response_split n α β w b c P hβ r rd u v Y).symm

#print axioms density_quartic
#print axioms density_derivative
#print axioms spatialFieldResponse_integrable
#print axioms spatialQuarticResponse_integrable
#print axioms spatialFieldResponse_integral
#print axioms spatialQuarticResponse_integral
end
end UnifiedTheory.Audit.KFCausalJointNeutralFourierOuterDensity
