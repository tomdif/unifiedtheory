/- The full charged dilation response has integral minus four times the
dilation rate times the energy. All differentiation and integrability
hypotheses are discharged for the finite exponential-polynomial family;
the identity follows from changes of variables, without boundary flux
assumptions at zero or infinity. -/
import UnifiedTheory.Audit.KFCausalCorrelatedDilationDifferentiation
import UnifiedTheory.Audit.KFCausalJointFourierDilationMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedDilationDivergence
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate Topology
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalCorrelatedDilationEnvelope (scale geometry)
open KFCausalCorrelatedDilationPolynomials (field prefactor packet)
open KFCausalCorrelatedDilationDifferentiation (value response)
open KFCausalClusteredClockFactors (Z N G E)

def point (ell t : ℝ) (p : Joint) : Joint :=
  ((scale ell t*p.1.1,![scale ell t*p.1.2 0,p.1.2 1]),Real.exp (2*ell*t)*p.2)

theorem exp_double (ell t : ℝ) : Real.exp (2*ell*t) = scale ell t^2 := by
  unfold scale
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

theorem charged_scaling (α ell t : ℝ) (r : ℂ) (p : Joint) :
    Z α (geometry ell r t) p = Z α r (point ell t p) := by
  unfold Z KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalWedgeGeometry.gamma geometry point
  rw [exp_double]
  simp only [Matrix.cons_val_zero,map_mul,map_div₀,map_pow,Complex.conj_ofReal,map_ofNat]
  push_cast
  ring

theorem neutral_scaling (ell t : ℝ) (r : ℂ) (p : Joint) :
    N (geometry ell r t) p = N r (point ell t p) := by
  unfold N KFCausalReciprocalNeutralKernel.neutral geometry point
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,add_zero]
  push_cast
  ring

theorem gaussian_scaling (β ell t : ℝ) (r : ℂ) (p : Joint) :
    G β (geometry ell r t) p = G β r (point ell t p) := by
  unfold G geometry point
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,add_zero]
  ring

theorem exponent_scaling (α β ell t : ℝ) (r b : ℂ) (p : Joint) :
    E α β (geometry ell r t) b p = E α β r b (point ell t p) := by
  unfold E
  rw [charged_scaling,neutral_scaling,gaussian_scaling]

theorem packet_zero (n j : ℕ) (α β ell : ℝ) (r b : ℂ) (P : Polynomial ℂ) (p : Joint) :
    packet n j α β ell r b P 0 p =
      Complex.exp (E α β r b p)*
        ((p.1.2 1+KFCausalChargedPairCoordinates.fieldSlope r*p.1.2 0:ℝ):ℂ)^j*
        Z α r p^n*P.eval (N r p) := by
  simp only [packet,prefactor,geometry,scale,field,mul_zero,Real.exp_zero,
    Complex.ofReal_one,one_mul]
  ring

theorem packet_scaling (n j : ℕ) (α β ell t : ℝ) (r b : ℂ) (P : Polynomial ℂ) (p : Joint) :
    packet n j α β ell r b P t p = packet n j α β ell r b P 0 (point ell t p) := by
  rw [packet_zero]
  unfold packet prefactor
  rw [exponent_scaling,charged_scaling,neutral_scaling]
  unfold field point
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring

variable (m : ℕ) (degree : Fin m → ℕ) (j : ℕ) (α : Fin m → ℝ) (β ell : ℝ)
  (r : ℂ) (b c : Fin m → ℂ) (P : Fin m → Polynomial ℂ)

theorem value_scaling (t : ℝ) (p : Joint) :
    value m degree j α β ell r b c P t p =
      value m degree j α β ell r b c P 0 (point ell t p) := by
  unfold value
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z : ℂ => c i*z) (packet_scaling (degree i) j (α i) β ell t r (b i) (P i) p)

variable (hβ : 0 < β) (hA : ∀ i, 0 < α i*area r) (hC : ∀ i, 0 < α i*area r-8*β*r.im^2)
include hβ hA hC

theorem response_integrable (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Integrable (response m degree j α β ell r b c P t) jointMeasure := by
  obtain ⟨D,hDi,_,hD⟩ :=
    KFCausalCorrelatedDilationDifferentiation.finite_envelope m degree j α β ell r b c P hβ hA hC
  apply hDi.mono'
    (KFCausalCorrelatedDilationDifferentiation.response_continuous m degree j α β ell r b c P t).aestronglyMeasurable
  filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
  exact (KFCausalCorrelatedClusteredBounds.cross_bound _ _).trans (hD t ht p hp)

theorem integral_scaling (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    (∫ p, ‖value m degree j α β ell r b c P t p‖^2 ∂jointMeasure) =
      Real.exp (-4*ell*t)*(∫ p, ‖value m degree j α β ell r b c P 0 p‖^2 ∂jointMeasure) := by
  have hi := KFCausalCorrelatedDilationDifferentiation.density_integrable m degree j α β ell r b c P hβ hA hC
  rw [KFCausalJointNeutralFourierIntegral.joint_integral_iterated _ (hi t ht),
    KFCausalJointNeutralFourierIntegral.joint_integral_iterated _ (hi 0 (by constructor <;> norm_num))]
  change KFCausalJointFourierDilationMeasure.integral
    (fun Y u v x => ‖value m degree j α β ell r b c P t ((u,![v,x]),Y)‖^2) = _
  have he : (fun Y u v x => ‖value m degree j α β ell r b c P t ((u,![v,x]),Y)‖^2) =
      KFCausalJointFourierDilationMeasure.scaled
        (fun Y u v x => ‖value m degree j α β ell r b c P 0 ((u,![v,x]),Y)‖^2)
        (Real.exp (ell*t)) (Real.exp (2*ell*t)) := by
    funext Y u v x
    rw [value_scaling]
    rfl
  rw [he,KFCausalJointFourierDilationMeasure.exponential_scaling]
  rfl

theorem jacobian_derivative :
    HasDerivAt (fun t => ∫ p, ‖value m degree j α β ell r b c P t p‖^2 ∂jointMeasure)
      (-4*ell*(∫ p, ‖value m degree j α β ell r b c P 0 p‖^2 ∂jointMeasure)) 0 := by
  have hd : HasDerivAt
      (fun t : ℝ => Real.exp (-4*ell*t)*(∫ p, ‖value m degree j α β ell r b c P 0 p‖^2 ∂jointMeasure))
      (-4*ell*(∫ p, ‖value m degree j α β ell r b c P 0 p‖^2 ∂jointMeasure)) 0 := by
    convert ((((hasDerivAt_id (0:ℝ)).const_mul (-4*ell)).exp).mul_const
      (∫ p, ‖value m degree j α β ell r b c P 0 p‖^2 ∂jointMeasure)) using 1
    simp
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1)] with t ht
  exact integral_scaling m degree j α β ell r b c P hβ hA hC t ht

theorem response_integral :
    (∫ p, response m degree j α β ell r b c P 0 p ∂jointMeasure) =
      -4*ell*(∫ p, ‖value m degree j α β ell r b c P 0 p‖^2 ∂jointMeasure) :=
  (KFCausalCorrelatedDilationDifferentiation.integral_derivative m degree j α β ell r b c P hβ hA hC).unique
    (jacobian_derivative m degree j α β ell r b c P hβ hA hC)

#print axioms exp_double
#print axioms charged_scaling
#print axioms neutral_scaling
#print axioms gaussian_scaling
#print axioms exponent_scaling
#print axioms packet_zero
#print axioms packet_scaling
#print axioms value_scaling
#print axioms response_integrable
#print axioms integral_scaling
#print axioms jacobian_derivative
#print axioms response_integral
end
end UnifiedTheory.Audit.KFCausalCorrelatedDilationDivergence
