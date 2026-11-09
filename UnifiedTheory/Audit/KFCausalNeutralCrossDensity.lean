/- Transverse density representatives for neutral cross kernels and
their derivatives. These identify the reduced kernel with the earlier
whole-configuration physical response density. -/
import UnifiedTheory.Audit.KFCausalNeutralFiniteResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralCrossDensity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPolynomialOrbitEnvelope (factor factorDerivative)
open UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles
open UnifiedTheory.Audit.KFCausalNeutralCrossKernel
open UnifiedTheory.Audit.KFCausalClockResponseTransport (clock coefficient pair)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)

def value (ε y α β : ℝ) (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ)
    (s : ℝ) (q : Transverse) : ℂ :=
  star (factor ε y α β (neutralSource b) C P pointField n q s)*
    factor ε y α β (neutralSource c) D Q pointField n q s
def derivative (ε y α β : ℝ) (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ)
    (s : ℝ) (q : Transverse) : ℂ :=
  star (factorDerivative ε y α β (neutralSource b) C P pointField n q s)*
      factor ε y α β (neutralSource c) D Q pointField n q s+
    star (factor ε y α β (neutralSource b) C P pointField n q s)*
      factorDerivative ε y α β (neutralSource c) D Q pointField n q s
def reducedValue (ε y α β : ℝ) (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ)
    (s : ℝ) (q : Transverse) : ℂ :=
  (coefficient ε y s:ℂ)*value ε y α β b c C D P Q n s q-
    derivative ε y α β b c C D P Q n s q/(clock ε s:ℂ)
def reducedKernel (ε y α β : ℝ) (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  (coefficient ε y s:ℂ)*crossKernel ε y α β b c C D P Q n s-
    crossDerivative ε y α β b c C D P Q n s/(clock ε s:ℂ)

theorem derivative_coefficient (ε y α β : ℝ) (b c C D : ℂ) (P Q : Polynomial ℂ)
    (n : ℕ) (s : ℝ) (q : Transverse) :
    derivative ε y α β b c C D P Q n s q =
      (star C*D)*derivative ε y α β b c 1 1 P Q n s q := by
  simp only [derivative,factor,factorDerivative,KFCausalPolynomialKernelResponse.transverse,
    KFCausalPolynomialKernelResponse.transverseDerivative,KFCausalGaussianKernelResponse.transverse,
    one_mul,star_mul,star_add]
  ring

theorem value_integrable (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ) :
    Integrable (value ε y α β b c C D P Q n s) volume := by
  simpa only [value,exponentialProfile_factor] using
    cross_integrable α β ε y s hα hβ hw hε hy b c C D P Q n

theorem derivative_integrable (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ) :
    Integrable (derivative ε y α β b c C D P Q n s) volume := by
  have hi := KFCausalPolynomialLocalKernel.derivative_integrable ε y α β
    (fun _ => neutralSource b) (fun _ => neutralSource c) (fun _ => 1) (fun _ => 1)
    P Q pointField n hε hy continuous_const continuous_const continuous_const continuous_const
    (neutralSource b) (neutralSource c) hα hβ hw (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => by simp) (fun _ => by simp) s
  have hu : Integrable (derivative ε y α β b c 1 1 P Q n s) volume := by
    simpa [KFCausalPolynomialLocalKernel.derivative,derivative] using hi.integral_prod_right
  convert hu.const_mul (star C*D) using 1
  exact funext (derivative_coefficient ε y α β b c C D P Q n s)

theorem value_integral (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ) :
    (∫ q, value ε y α β b c C D P Q n s q) = crossKernel ε y α β b c C D P Q n s := by
  simpa only [value,exponentialProfile_factor] using
    (crossKernel_gram α β ε y s hα hβ hw hε hy b c C D P Q n).symm

theorem derivative_integral (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ) :
    (∫ q, derivative ε y α β b c C D P Q n s q) =
      crossDerivative ε y α β b c C D P Q n s := by
  have hi := KFCausalPolynomialLocalKernel.derivative_integrable ε y α β
    (fun _ => neutralSource b) (fun _ => neutralSource c) (fun _ => 1) (fun _ => 1)
    P Q pointField n hε hy continuous_const continuous_const continuous_const continuous_const
    (neutralSource b) (neutralSource c) hα hβ hw (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => by simp) (fun _ => by simp) s
  simp_rw [derivative_coefficient ε y α β b c C D P Q n s]
  rw [integral_const_mul]
  unfold crossDerivative KFCausalPolynomialLocalKernel.integralDerivative KFCausalPolynomialLocalKernel.measure
  rw [integral_prod_symm _ hi]
  simp [KFCausalPolynomialLocalKernel.derivative,derivative]

theorem reducedValue_integrable (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ) :
    Integrable (reducedValue ε y α β b c C D P Q n s) volume :=
  ((value_integrable α β ε y s hα hβ hw hε hy b c C D P Q n).const_mul _).sub
    ((derivative_integrable α β ε y s hα hβ hw hε hy b c C D P Q n).div_const _)

theorem reducedValue_integral (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ) :
    (∫ q, reducedValue ε y α β b c C D P Q n s q) =
      reducedKernel ε y α β b c C D P Q n s := by
  unfold reducedValue
  rw [integral_sub ((value_integrable α β ε y s hα hβ hw hε hy b c C D P Q n).const_mul _)
    ((derivative_integrable α β ε y s hα hβ hw hε hy b c C D P Q n).div_const _),
    integral_const_mul,integral_div,value_integral α β ε y s hα hβ hw hε hy,
    derivative_integral α β ε y s hα hβ hw hε hy]
  rfl

theorem value_formula (ε y α β : ℝ) (b c C D : ℂ) (P Q : Polynomial ℂ)
    (n : ℕ) (s : ℝ) (q : Transverse) :
    value ε y α β b c C D P Q n s q =
      (pointField q:ℂ)^(2*n)*KFCausalPolynomialKernelResponse.kernel ε y α β α β
        (neutralSource b) (neutralSource c) C D P Q q s := by
  simp only [value,factor,KFCausalPolynomialKernelResponse.kernel,
    star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
  rw [show 2*n=n+n by omega,pow_add]
  ring

theorem derivative_formula (ε y α β : ℝ) (b c C D : ℂ) (P Q : Polynomial ℂ)
    (n : ℕ) (s : ℝ) (q : Transverse) :
    derivative ε y α β b c C D P Q n s q =
      (pointField q:ℂ)^(2*n)*KFCausalPolynomialKernelResponse.kernelDerivative ε y α β α β
        (neutralSource b) (neutralSource c) C D P Q q s := by
  simp only [derivative,factor,factorDerivative,KFCausalPolynomialKernelResponse.kernelDerivative,
    star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
  rw [show 2*n=n+n by omega,pow_add]
  ring

theorem physical_reducedDensity (ε a h : ℝ) (b c C D : ℂ) (P Q : Polynomial ℂ)
    (n : Fin 3) (s : ℝ) (q : Transverse) :
    KFCausalPolynomialResponseIntegrability.reducedDensity ε a a h 0 0
      (neutralSource b) (neutralSource c) C D P Q pointField n (s,q) =
      pair ε a a 0 0 (-h/2) s*
        reducedValue ε (-h/2) (groundWidth h) (neutralWidth h) b c C D P Q n s q := by
  unfold reducedValue
  rw [value_formula,derivative_formula]
  unfold KFCausalPolynomialResponseIntegrability.reducedDensity KFCausalClockResponseTransport.reduced
  ring

#print axioms derivative_coefficient
#print axioms value_integrable
#print axioms derivative_integrable
#print axioms value_integral
#print axioms derivative_integral
#print axioms reducedValue_integrable
#print axioms reducedValue_integral
#print axioms value_formula
#print axioms derivative_formula
#print axioms physical_reducedDensity
end
end UnifiedTheory.Audit.KFCausalNeutralCrossDensity
