/- A quantitative transverse Gaussian quotient for two ordered complex
shears, including the actual inverse-clock increments. The real input
and the unitary coordinate rotations are explicit hypotheses. Applying
this estimate to an operator graph still requires the physical Fourier
representative and its coordinate identification. -/
import UnifiedTheory.Audit.KFCausalComplexShearPerturbation
import UnifiedTheory.Audit.KFCausalTwoShearClockQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalTwoShearTransverseQuotient
noncomputable section
open KFCausalComplexShearPerturbation
open KFCausalComplexQuadraticPerturbation
open KFCausalComplexClockInverse

theorem mass_eq_norm_sq (x : Space) : mass (fun i => x i)=‖x‖^2 := by
  exact (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 5 => ℂ) x).symm

theorem ordered_mass (U V : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (hσ : |σ| ≤ 1/4)
    (z t : ℂ) (hzt : ‖z‖+‖t‖ ≤ 1/5) (x : Space) :
    mass (fun i => rotatedFlow U σ z (rotatedFlow V σ t x) i-x i) ≤
      (3/17:ℝ)^2*mass (fun i => x i) := by
  have hm := ordered_difference U V σ hσ z t hzt x
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (3/17:ℝ)*‖x‖)).mpr hm
  rw [mul_pow] at hs
  simpa only [mass,PiLp.norm_sq_eq_of_L2,PiLp.sub_apply] using hs

theorem baseline_mass (V : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (hσ : |σ| ≤ 1/4)
    (t : ℂ) (ht : ‖t‖ ≤ 1/5) (x : Space) :
    mass (fun i => rotatedFlow V σ t x i) ≤ (20/17:ℝ)^2*mass (fun i => x i) := by
  rw [mass_eq_norm_sq,mass_eq_norm_sq,← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (baseline_norm V σ hσ t ht x)

def transverse (U V : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (w : Fin 5 → ℝ)
    (z t : ℂ) (x : Space) : ℂ :=
  Complex.exp (-quadratic (fun i => rotatedFlow U σ z (rotatedFlow V σ t x) i)+
    weightedQuadratic w (fun i => rotatedFlow V σ t x i))

theorem transverse_bound (U V : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (hσ : |σ| ≤ 1/4)
    (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1/4)
    (z t : ℂ) (hzt : ‖z‖+‖t‖ ≤ 1/5) (x : Space) (hx : ∀ i, (x i).im=0) :
    ‖transverse U V σ w z t x‖ ≤ Real.exp (-(78/289:ℝ)*‖x‖^2) := by
  have ht : ‖t‖ ≤ 1/5 := by linarith [norm_nonneg z]
  simpa only [transverse,mass_eq_norm_sq] using
    gaussian_difference_bound w (fun i => x i)
      (fun i => rotatedFlow U σ z (rotatedFlow V σ t x) i)
      (fun i => rotatedFlow V σ t x i) hx hw
      (ordered_mass U V σ hσ z t hzt x) (baseline_mass V σ hσ t ht x)

def clockTransverse (ε h : ℝ) (U V : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ)
    (w : Fin 5 → ℝ) (q : ℂ) (x : Space) : ℂ :=
  transverse U V σ w
    (complexInverse ε (KFCausalTwoShearClockQuotient.shift h q)-complexInverse ε q)
    (complexInverse ε q-complexInverse ε (q.re:ℂ)) x

theorem clock_transverse_bound (ε h : ℝ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (U V : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (hσ : |σ| ≤ 1/4)
    (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1/4)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Space) (hx : ∀ i, (x i).im=0) :
    ‖clockTransverse ε h U V σ w q x‖ ≤ Real.exp (-(78/289:ℝ)*‖x‖^2) :=
  transverse_bound U V σ hσ w hw _ _
    (KFCausalTwoShearClockQuotient.two_increment_bound ε h hε hh q hq) x hx

theorem clock_times_transverse_bound (ε h : ℝ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (a : ℝ) (ha : 0 ≤ a) (U V : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (hσ : |σ| ≤ 1/4)
    (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1/4)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Space) (hx : ∀ i, (x i).im=0) :
    ‖KFCausalTwoShearClockQuotient.quotient ε h a q * clockTransverse ε h U V σ w q x‖ ≤
      (ε⁻¹*Real.exp (|h|/ε)*Real.exp (-(a/2)*q.re^2+4*a*h^2))*
        Real.exp (-(78/289:ℝ)*‖x‖^2) := by
  rw [norm_mul]
  exact mul_le_mul
    (KFCausalTwoShearClockQuotient.quotient_gaussian_bound ε h hε hh a ha q hq)
    (clock_transverse_bound ε h hε hh U V σ hσ w hw q hq x hx)
    (norm_nonneg _) (by positivity)

#print axioms mass_eq_norm_sq
#print axioms ordered_mass
#print axioms baseline_mass
#print axioms transverse_bound
#print axioms clock_transverse_bound
#print axioms clock_times_transverse_bound
end
end UnifiedTheory.Audit.KFCausalTwoShearTransverseQuotient
