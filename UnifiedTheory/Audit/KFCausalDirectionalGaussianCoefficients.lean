/- Directional powers are exact source-circle coefficients in physical
L2. The source direction is arbitrary and all normalization factors are
retained. -/
import UnifiedTheory.Audit.KFCausalDirectionalGaussianStates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalDirectionalGaussianCoefficients
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalSourceCircleCoefficients
open KFCausalClockFloorCoherentBounds (sourceSize)
open KFCausalClockFloorCoherentSources (linearSource)
open KFCausalClockFloorCoherentMoments (sourcedPacket)
open KFCausalClockFloorCoherentDerivative (physicalProfile clockMultiplier)
open KFCausalClockFloorCoherentOrbitContinuity (physicalProfile_curve_continuous)
open KFCausalClockFloorSourcedClockMomentum (profileState profileState_coe)
open KFCausalDirectionalGaussianStates (linearForm linearForm_continuous profile profile_memLp)

def sourceCurve (d : Transverse) (θ : ℝ) : Fin 5 → ℂ :=
  fun i => circle θ*(d i:ℂ)

def sourceBound (d : Transverse) : ℝ := ∑ i, ‖(d i:ℂ)‖^2

theorem sourceCurve_continuous (d : Transverse) : Continuous (sourceCurve d) := by
  apply continuous_pi
  intro i
  exact circle_continuous.mul continuous_const

theorem sourceCurve_bound (d : Transverse) (θ : ℝ) :
    sourceSize (sourceCurve d θ) ≤ sourceBound d := by
  simp only [sourceSize,sourceCurve,sourceBound,norm_mul,circle_norm,one_mul,le_refl]

theorem linearSource_curve (d q : Transverse) (θ : ℝ) :
    linearSource (sourceCurve d θ) q = (linearForm d q:ℂ)*circle θ := by
  simp only [linearSource,sourceCurve,linearForm,Complex.ofReal_sum,Complex.ofReal_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem circleProfile (p α β : ℝ) (g : ℝ → ℂ) (d : Transverse)
    (n : ℕ) (θ : ℝ) (x : Configuration) :
    physicalProfile (weight n θ) p α β (sourceCurve d θ) g x =
      (weight n θ*Complex.exp ((linearForm d x.2:ℂ)*circle θ))*
        physicalProfile 1 p α β 0 g x := by
  have hz : linearSource 0 x.2 = 0 := by simp [linearSource]
  simp only [physicalProfile,clockMultiplier,sourcedPacket,linearSource_curve,
    hz,Complex.exp_zero,one_mul]
  ring

def coefficientState (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : ℂ) (p : ℝ) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (d : Transverse) (n : ℕ) : Hilbert :=
  (C*normalization n) •
    ∫ θ, profileState α β hα hβ hw (weight n θ) p (sourceCurve d θ) g hg ∂angleMeasure

theorem coefficientState_coe (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : ℂ) (p : ℝ) (g : ℝ → ℂ) (hg : MemLp g 2 volume) (hgc : Continuous g)
    (d : Transverse) (n : ℕ) :
    coefficientState α β hα hβ hw C p g hg d n =ᵐ[volume] profile C p α β g d n := by
  let U : ℝ → Hilbert := fun θ =>
    (C*normalization n) • profileState α β hα hβ hw (weight n θ) p (sourceCurve d θ) g hg
  let F : ℝ → Configuration → ℂ := fun θ x =>
    (C*normalization n)*(weight n θ*Complex.exp ((linearForm d x.2:ℂ)*circle θ))*
      physicalProfile 1 p α β 0 g x
  have hu : Continuous U := continuous_const.smul
    (physicalProfile_curve_continuous α β (sourceBound d) hα hβ hw
      (weight n) (fun _ => p) (sourceCurve d) g hg
      (weight_continuous n) continuous_const (sourceCurve_continuous d)
      (fun θ => (weight_norm n θ).le) (sourceCurve_bound d))
  have hf : Continuous (fun z : ℝ × Configuration => F z.1 z.2) := by
    have hc := circle_continuous
    have hn := weight_continuous n
    unfold F physicalProfile clockMultiplier sourcedPacket linearSource linearForm
      KFCausalClockFloorCoherentStrip.clockPhase KFCausalClockFloorShearBounds.physicalGaussian
    fun_prop
  have hr (θ : ℝ) : U θ =ᵐ[volume] F θ := by
    filter_upwards [Lp.coeFn_smul (C*normalization n)
      (profileState α β hα hβ hw (weight n θ) p (sourceCurve d θ) g hg),
      profileState_coe α β hα hβ hw (weight n θ) p (sourceCurve d θ) g hg] with x hx hy
    change ((C*normalization n) • profileState α β hα hβ hw
      (weight n θ) p (sourceCurve d θ) g hg) x = _
    rw [hx,Pi.smul_apply,hy,smul_eq_mul,circleProfile]
    exact (mul_assoc _ _ _).symm
  have hm (x : Configuration) : (∫ θ, F θ x ∂angleMeasure) = profile C p α β g d n x := by
    dsimp only [F]
    rw [integral_mul_const,integral_const_mul]
    have he := exponential_coefficient n (linearForm d x.2:ℂ)
    calc
      _ = C*(normalization n*(∫ θ, weight n θ*
          Complex.exp ((linearForm d x.2:ℂ)*circle θ) ∂angleMeasure))*
          physicalProfile 1 p α β 0 g x := by ring
      _ = _ := by
        rw [he]
        unfold profile physicalProfile clockMultiplier
        ring
  have he := KFCausalL2IntegralRepresentative.integral_coe U F
    (profile C p α β g d n) hu hf hr (profile_memLp C p α β hα hβ g hg d n) hm
  have hi : (∫ θ, U θ ∂angleMeasure) =
      coefficientState α β hα hβ hw C p g hg d n := by
    exact integral_smul _ _
  exact hi ▸ he

#print axioms sourceCurve_continuous
#print axioms sourceCurve_bound
#print axioms linearSource_curve
#print axioms circleProfile
#print axioms coefficientState_coe
end
end UnifiedTheory.Audit.KFCausalDirectionalGaussianCoefficients
