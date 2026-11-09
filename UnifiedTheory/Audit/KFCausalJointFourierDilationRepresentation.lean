/- The actual dilation packets and neutral Fourier fields have equal
squared densities. The common neutral Gaussian phase is removed only
inside the norm, retaining interference between all finite summands. -/
import UnifiedTheory.Audit.KFCausalCorrelatedDilationDifferentiation
import UnifiedTheory.Audit.KFCausalJointFourierDilationPath

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3400000

namespace UnifiedTheory.Audit.KFCausalJointFourierDilationRepresentation
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint)
open KFCausalClusteredClockFactors (Z N G E)
open KFCausalCorrelatedDilationEnvelope (scale geometry)
open KFCausalCorrelatedDilationPolynomials (field packet prefactor)
open KFCausalCorrelatedDilationDifferentiation (value)
open KFCausalNeutralFourierField (fieldLine)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalReciprocalNeutralPositiveForm (profileSum)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalChargedPairCoordinates (fieldSlope)

theorem charged_width (α w : ℝ) (r : ℂ) (p : Joint) :
    Z (w*α) r p = (w:ℂ)*Z α r p := by
  unfold Z KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalWedgeGeometry.gamma
  simp only [map_mul,map_div₀,map_pow,Complex.conj_ofReal,map_ofNat]
  push_cast
  ring

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (r : ℂ)

theorem value_factor (ell t : ℝ) (j : ℕ) (p : Joint) :
    value n (fun _ => 0) j (fun i => w i*α) β ell r b
      (fun i => c i*(w i:ℂ)) P t p =
      (field ell r t p:ℂ)^j*Complex.exp (G β (geometry ell r t) p:ℂ)*
        profileSum n w c (fun i => exponentialProfile (b i) 1 (P i))
          (Z α (geometry ell r t) p) (N (geometry ell r t) p) := by
  unfold value packet prefactor E profileSum KFCausalReciprocalWedgeLaplace.laplaceSum
  simp only [pow_zero,mul_one,charged_width,Complex.exp_add,exponentialProfile,one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show -(w i:ℂ)*Z α (geometry ell r t) p = -((w i:ℂ)*Z α (geometry ell r t) p) by ring]
  ring

theorem fieldLine_factor (a : ℝ) (j : ℕ) (p : Joint) :
    fieldLine n β b (coefficients n w c (Z α r p)) P j a
      (2*r.im*p.1.2 0) (p.1.2 1) =
      ((p.1.2 1+a:ℝ):ℂ)^j*Complex.exp (-(β:ℂ)*(N r p)^2)*
        profileSum n w c (fun i => exponentialProfile (b i) 1 (P i)) (Z α r p) (N r p) := by
  have he : ((p.1.2 1:ℝ):ℂ)+((2*r.im*p.1.2 0:ℝ):ℂ)*Complex.I = N r p := by
    unfold N KFCausalReciprocalNeutralKernel.neutral
    push_cast
    ring
  unfold fieldLine KFCausalNeutralFourierShift.line KFCausalGaussianContourShift.horizontal
  rw [he,← KFCausalNeutralJointCurvatureForm.joint_profile_family,
    KFCausalReciprocalNeutralHolomorphic.profileSum_weighted]
  ring

def fieldDensity (ell t : ℝ) (j : ℕ) (p : Joint) : ℝ :=
  ‖fieldLine n β b (coefficients n w c (Z α (geometry ell r t) p)) P j
    (scale ell t*(fieldSlope r*p.1.2 0))
    (2*(geometry ell r t).im*p.1.2 0) (p.1.2 1)‖^2

theorem density_eq (ell t : ℝ) (j : ℕ) (p : Joint) :
    fieldDensity n α β w b c P r ell t j p =
      ‖value n (fun _ => 0) j (fun i => w i*α) β ell r b
        (fun i => c i*(w i:ℂ)) P t p‖^2 := by
  unfold fieldDensity
  rw [fieldLine_factor,value_factor]
  simp only [norm_mul,mul_pow]
  have hg : ‖Complex.exp (G β (geometry ell r t) p:ℂ)‖^2 =
      Real.exp (-2*β*(p.1.2 1)^2+8*β*(geometry ell r t).im^2*(p.1.2 0)^2) := by
    rw [Complex.norm_exp,← Real.exp_nat_mul]
    congr 1
    simp only [Complex.ofReal_re,G]
    ring
  have hn : ‖Complex.exp (-(β:ℂ)*(N (geometry ell r t) p)^2)‖^2 =
      Real.exp (-2*β*(p.1.2 1)^2+8*β*(geometry ell r t).im^2*(p.1.2 0)^2) :=
    KFCausalReciprocalNeutralHolomorphic.gaussian_norm β (geometry ell r t) (p.1.2 0) (p.1.2 1)
  rw [hg,hn]
  unfold field
  congr 4
  push_cast
  ring

theorem geometry_zero (ell : ℝ) : geometry ell r 0 = r := by
  simp [geometry,scale]

theorem density_zero (ell : ℝ) (j : ℕ) (p : Joint) :
    fieldDensity n α β w b c P r ell 0 j p =
      ‖fieldLine n β b (coefficients n w c (Z α r p)) P j
        (fieldSlope r*p.1.2 0) (2*r.im*p.1.2 0) (p.1.2 1)‖^2 := by
  simp only [fieldDensity,geometry_zero,scale,mul_zero,Real.exp_zero,one_mul]

#print axioms charged_width
#print axioms value_factor
#print axioms fieldLine_factor
#print axioms density_eq
#print axioms geometry_zero
#print axioms density_zero
end
end UnifiedTheory.Audit.KFCausalJointFourierDilationRepresentation
