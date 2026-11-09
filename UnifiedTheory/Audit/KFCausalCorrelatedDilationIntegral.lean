/- The actual finite-family density obeys the charged dilation Jacobian
law. Its full-integral derivative and pointwise jet are proved separately.
Equality with the integral of that jet still requires differentiation under
the full charged integral. -/
import UnifiedTheory.Audit.KFCausalJointFourierDilationMeasure
import UnifiedTheory.Audit.KFCausalJointFourierDilationPath

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedDilationIntegral
noncomputable section
open MeasureTheory
open KFCausalNeutralFourierField (fieldLine)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalJointFourierDilationPath (dilationChart)
open KFCausalJointFourierDilationMeasure (integral scaled)

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (r : ℂ)

def density (j : ℕ) (Y u v x : ℝ) : ℝ :=
  ‖fieldLine n β b (coefficients n w c (chart α r (u^2+v^2) Y)) P j
    (fieldSlope r*v) (2*r.im*v) x‖^2

def linearDensity (ell : ℝ) (j : ℕ) (t Y u v x : ℝ) : ℝ :=
  ‖fieldLine n β b (coefficients n w c (dilationChart α r ell u v Y t)) P j
    ((1+t*ell)*(fieldSlope r*v)) ((1+t*ell)*(2*r.im*v)) x‖^2

theorem linearDensity_eq (ell : ℝ) (j : ℕ) (t : ℝ) :
    linearDensity n α β w b c P r ell j t =
      scaled (density n α β w b c P r j) (1+t*ell) (1+2*t*ell) := by
  funext Y u v x
  unfold linearDensity scaled density
  rw [KFCausalJointFourierDilationPath.chart_coordinates]
  congr 3 <;> ring

theorem pointwise_derivative (ell Y u v x : ℝ) (j : ℕ) :
    HasDerivAt (fun t => linearDensity n α β w b c P r ell j t Y u v x)
      (KFCausalNeutralFourierResponseSplit.response n β b
        (coefficients n w c (chart α r (u^2+v^2) Y))
        (KFCausalJointFourierDilationJet.dilationCoefficients n α w c r ell u v Y) P j
        (fieldSlope r*v) (2*r.im*v) (ell*(fieldSlope r*v)) (ell*(2*r.im*v)) x) 0 :=
  KFCausalJointFourierDilationPath.square_derivative n α β w b c P r ell u v Y x j

theorem field_integral_derivative (ell : ℝ) (j : ℕ) :
    HasDerivAt (fun t => integral (linearDensity n α β w b c P r ell j t))
      (-4*ell*integral (density n α β w b c P r j)) 0 := by
  simp_rw [linearDensity_eq]
  exact KFCausalJointFourierDilationMeasure.linear_derivative _ ell

def quarticDensity (Y u v x : ℝ) : ℝ :=
  density n α β w b c P r 0 Y u v x+
    density n α β w b c P r 1 Y u v x/2+density n α β w b c P r 2 Y u v x/4

theorem quartic_density_identity (Y u v x : ℝ) :
    quarticDensity n α β w b c P r Y u v x =
      KFCausalReciprocalNeutralPositiveForm.positiveDensity n α β w r c
        (fun i => KFCausalNeutralExponentialProfiles.exponentialProfile (b i) 1 (P i))
          ((u,![v,x]),Y) := by
  rw [KFCausalJointNeutralFourierIntegral.density_slice,
    KFCausalJointNeutralFourierIntegral.jointSlice_line]
  exact (KFCausalNeutralFourierEnergy.quartic_density n β b
    (coefficients n w c (chart α r (u^2+v^2) Y)) P (fieldSlope r*v) (2*r.im*v) x).symm

theorem quartic_integral_derivative (ell : ℝ) :
    HasDerivAt (fun t => integral (scaled (quarticDensity n α β w b c P r) (1+t*ell) (1+2*t*ell)))
      (-4*ell*integral (quarticDensity n α β w b c P r)) 0 :=
  KFCausalJointFourierDilationMeasure.linear_derivative _ ell

omit r in
theorem actual_integral (ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i) :
    integral (quarticDensity n α β w b c P (KFCausalClockFloorRelativeShift.scale ε y s)) =
      ∫ p, KFCausalReciprocalNeutralPositiveForm.positiveDensity n α β w
        (KFCausalClockFloorRelativeShift.scale ε y s) c
        (fun i => KFCausalNeutralExponentialProfiles.exponentialProfile (b i) 1 (P i)) p
          ∂KFCausalReciprocalNeutralLaplace.jointMeasure := by
  rw [KFCausalJointNeutralFourierIntegral.joint_integral_iterated _
    (KFCausalReciprocalNeutralActualPositive.positive_integrable n α β ε y s w b c P hα hβ hwidth hε hy hw)]
  unfold KFCausalJointFourierDilationMeasure.integral
  simp_rw [quartic_density_identity]

omit r in
theorem actual_integral_derivative (ε y s ell : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i) :
    HasDerivAt (fun t => integral (scaled
      (quarticDensity n α β w b c P (KFCausalClockFloorRelativeShift.scale ε y s))
        (1+t*ell) (1+2*t*ell)))
      (-4*ell*(∫ p, KFCausalReciprocalNeutralPositiveForm.positiveDensity n α β w
        (KFCausalClockFloorRelativeShift.scale ε y s) c
        (fun i => KFCausalNeutralExponentialProfiles.exponentialProfile (b i) 1 (P i)) p
          ∂KFCausalReciprocalNeutralLaplace.jointMeasure)) 0 := by
  rw [← actual_integral n α β w b c P ε y s hα hβ hwidth hε hy hw]
  exact quartic_integral_derivative n α β w b c P _ ell

#print axioms linearDensity_eq
#print axioms pointwise_derivative
#print axioms field_integral_derivative
#print axioms quartic_density_identity
#print axioms quartic_integral_derivative
#print axioms actual_integral
#print axioms actual_integral_derivative
end
end UnifiedTheory.Audit.KFCausalCorrelatedDilationIntegral
