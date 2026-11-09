/- A uniform bound for the pure exponential tilt in the actual complete
three-channel Fourier density on every charged circle. Charged motion
and the real field correction are not included in this subestimate. -/
import UnifiedTheory.Audit.KFCausalQuadraticAngularTilt
import UnifiedTheory.Audit.KFCausalJointFourierMatrixIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalJointFourierAngularTilt
noncomputable section
open MeasureTheory
open KFCausalQuadraticAngularTilt (quad)
open KFCausalNeutralFourierQuadraticJet (jetEnergy)
open KFCausalJointFourierQuadraticJet (chargedJet complexShear jetSlice)
open KFCausalReciprocalWedgeGeometry (chart)

def angleDensity (κ : ℝ) (q A B C : ℂ) (θ : ℝ) : ℝ :=
  Real.exp (-κ*Real.sin θ)*jetEnergy (q*(Real.sin θ:ℂ)) A B C

private def channel (κ : ℝ) (A B C : ℂ) (θ : ℝ) : ℝ :=
  Real.exp (-κ*Real.sin θ)*‖quad A B C θ‖^2

private theorem channel_continuous (κ : ℝ) (A B C : ℂ) :
    Continuous (channel κ A B C) := by
  unfold channel quad
  fun_prop

private theorem density_channels (κ : ℝ) (q A B C : ℂ) (θ : ℝ) :
    angleDensity κ q A B C θ = channel κ A 0 0 θ+
      channel κ B (q*A) 0 θ/2+channel κ C (2*q*B) (q^2*A) θ/4 := by
  have h0 : quad A 0 0 θ = A := by simp [quad]
  have h1 : quad B (q*A) 0 θ = B+q*(Real.sin θ:ℂ)*A := by unfold quad; ring
  have h2 : quad C (2*q*B) (q^2*A) θ =
      C+2*(q*(Real.sin θ:ℂ))*B+(q*(Real.sin θ:ℂ))^2*A := by unfold quad; ring
  unfold angleDensity channel jetEnergy
  rw [h0,h1,h2]
  ring

theorem jet_tilt_lower (κ : ℝ) (q A B C : ℂ) :
    -2400*(∫ θ in -Real.pi..Real.pi, angleDensity κ q A B C θ) ≤
      ∫ θ in -Real.pi..Real.pi, (-κ*Real.sin θ)*angleDensity κ q A B C θ := by
  have hi (A B C : ℂ) : IntervalIntegrable (channel κ A B C) volume (-Real.pi) Real.pi :=
    (channel_continuous κ A B C).intervalIntegrable (-Real.pi) Real.pi
  have ht (A B C : ℂ) : IntervalIntegrable
      (fun θ => (-κ*Real.sin θ)*channel κ A B C θ) volume (-Real.pi) Real.pi :=
    ((continuous_const.mul Real.continuous_sin).mul
      (channel_continuous κ A B C)).intervalIntegrable _ _
  have h0 := KFCausalQuadraticAngularTilt.quadratic_tilt_lower κ A 0 0
  have h1 := KFCausalQuadraticAngularTilt.quadratic_tilt_lower κ B (q*A) 0
  have h2 := KFCausalQuadraticAngularTilt.quadratic_tilt_lower κ C (2*q*B) (q^2*A)
  change -2400*(∫ θ in -Real.pi..Real.pi, channel κ A 0 0 θ) ≤
    ∫ θ in -Real.pi..Real.pi, (-κ*Real.sin θ)*channel κ A 0 0 θ at h0
  change -2400*(∫ θ in -Real.pi..Real.pi, channel κ B (q*A) 0 θ) ≤
    ∫ θ in -Real.pi..Real.pi, (-κ*Real.sin θ)*channel κ B (q*A) 0 θ at h1
  change -2400*(∫ θ in -Real.pi..Real.pi, channel κ C (2*q*B) (q^2*A) θ) ≤
    ∫ θ in -Real.pi..Real.pi, (-κ*Real.sin θ)*channel κ C (2*q*B) (q^2*A) θ at h2
  simp_rw [density_channels]
  have he (θ : ℝ) : (-κ*Real.sin θ)*(channel κ A 0 0 θ+
      channel κ B (q*A) 0 θ/2+channel κ C (2*q*B) (q^2*A) θ/4) =
      (-κ*Real.sin θ)*channel κ A 0 0 θ+
        ((-κ*Real.sin θ)*channel κ B (q*A) 0 θ)/2+
        ((-κ*Real.sin θ)*channel κ C (2*q*B) (q^2*A) θ)/4 := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_add ((hi A 0 0).add ((hi B (q*A) 0).div_const 2))
      ((hi C (2*q*B) (q^2*A)).div_const 4),
    intervalIntegral.integral_add (hi A 0 0) ((hi B (q*A) 0).div_const 2),
    intervalIntegral.integral_add ((ht A 0 0).add ((ht B (q*A) 0).div_const 2))
      ((ht C (2*q*B) (q^2*A)).div_const 4),
    intervalIntegral.integral_add (ht A 0 0) ((ht B (q*A) 0).div_const 2)]
  simp only [intervalIntegral.integral_div]
  linarith

variable (n : ℕ) (β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ)

theorem slice_angle_identity (r z : ℂ) (R k θ : ℝ) :
    jetSlice n β w b c P r z (R*Real.sin θ) k =
      angleDensity (8*Real.pi*k*r.im*R) (complexShear r*(R:ℂ))
        (chargedJet n β w b c P 0 z k) (chargedJet n β w b c P 1 z k)
        (chargedJet n β w b c P 2 z k) θ := by
  unfold jetSlice angleDensity
  congr 2
  · ring
  · push_cast
    ring

theorem slice_tilt_lower (r z : ℂ) (R k : ℝ) :
    -2400*(∫ θ in -Real.pi..Real.pi, jetSlice n β w b c P r z (R*Real.sin θ) k) ≤
      ∫ θ in -Real.pi..Real.pi,
        (-8*Real.pi*k*r.im*(R*Real.sin θ))*jetSlice n β w b c P r z (R*Real.sin θ) k := by
  simp_rw [slice_angle_identity]
  have he (θ : ℝ) : -8*Real.pi*k*r.im*(R*Real.sin θ) =
      -(8*Real.pi*k*r.im*R)*Real.sin θ := by ring
  simp_rw [he]
  exact jet_tilt_lower _ _ _ _ _

theorem original_angular_tilt_lower (α : ℝ) (r : ℂ) (R Y k : ℝ) :
    -2400*(∫ θ in -Real.pi..Real.pi,
      KFCausalJointFourierMatrixIntegral.density n β w b c P α r
        (((R*Real.cos θ,R*Real.sin θ),Y),k)) ≤
      ∫ θ in -Real.pi..Real.pi, (-8*Real.pi*k*r.im*(R*Real.sin θ))*
        KFCausalJointFourierMatrixIntegral.density n β w b c P α r
          (((R*Real.cos θ,R*Real.sin θ),Y),k) := by
  have he (θ : ℝ) : (R*Real.cos θ)^2+(R*Real.sin θ)^2 = R^2 := by
    linear_combination R^2*(Real.sin_sq_add_cos_sq θ)
  simp only [KFCausalJointFourierMatrixIntegral.density,he]
  exact slice_tilt_lower n β w b c P r (chart α r (R^2) Y) R k

#print axioms jet_tilt_lower
#print axioms slice_angle_identity
#print axioms slice_tilt_lower
#print axioms original_angular_tilt_lower
end
end UnifiedTheory.Audit.KFCausalJointFourierAngularTilt
