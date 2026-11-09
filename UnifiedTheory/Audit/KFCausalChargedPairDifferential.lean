/- Exact transverse derivative of the paired Gaussian, with derived L2
bounds for the polynomial derivative and an arbitrary L2 clock factor. -/
import UnifiedTheory.Audit.KFCausalDirectionalGaussianStates
import UnifiedTheory.Audit.KFCausalChargedPairDomain
import UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalChargedPairDifferential
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorShearBounds (physicalGaussian)
open KFCausalChargedPairCoordinates (pairPolynomial)
open KFCausalPhysicalGaussianDerivative
  (physicalGaussian_differentiable physicalGaussian_hasLineDerivAt configuration_product_memLp)
open KFCausalTransverseTrialDerivative (derivative)

def weightedLinear (α β : ℝ) (v q : Transverse) : ℝ :=
  α*(v 0*q 0+v 1*q 1+v 2*q 2+v 3*q 3)+β*v 4*q 4

def pairDerivative (v q : Transverse) : ℝ :=
  v 0*q 1+v 1*q 0-v 2*q 3-v 3*q 2

def derivativePolynomial (α β : ℝ) (v q : Transverse) : ℝ :=
  pairDerivative v q-2*weightedLinear α β v q*pairPolynomial q

def pairPoly : MvPolynomial (Fin 5) ℝ :=
  MvPolynomial.X 0*MvPolynomial.X 1-MvPolynomial.X 2*MvPolynomial.X 3

def derivativePoly (α β : ℝ) (v : Transverse) : MvPolynomial (Fin 5) ℝ :=
  (MvPolynomial.C (v 0)*MvPolynomial.X 1+MvPolynomial.C (v 1)*MvPolynomial.X 0-
    MvPolynomial.C (v 2)*MvPolynomial.X 3-MvPolynomial.C (v 3)*MvPolynomial.X 2)-
  MvPolynomial.C 2*(MvPolynomial.C α*
    (MvPolynomial.C (v 0)*MvPolynomial.X 0+MvPolynomial.C (v 1)*MvPolynomial.X 1+
      MvPolynomial.C (v 2)*MvPolynomial.X 2+MvPolynomial.C (v 3)*MvPolynomial.X 3)+
    MvPolynomial.C β*MvPolynomial.C (v 4)*MvPolynomial.X 4)*pairPoly

theorem pairPoly_eval (q : Transverse) : MvPolynomial.eval q pairPoly = pairPolynomial q := by
  simp [pairPoly,pairPolynomial]

theorem derivativePoly_eval (α β : ℝ) (v q : Transverse) :
    MvPolynomial.eval q (derivativePoly α β v) = derivativePolynomial α β v q := by
  simp [derivativePoly,derivativePolynomial,pairDerivative,weightedLinear,pairPoly_eval]

theorem pair_hasLineDerivAt (v q : Transverse) :
    HasLineDerivAt ℝ pairPolynomial (pairDerivative v q) q v := by
  have hl (i : Fin 5) : HasDerivAt (fun t : ℝ => q i+t*v i) (v i) 0 := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (q i)
  change HasDerivAt (fun t : ℝ => pairPolynomial (q+t • v)) (pairDerivative v q) 0
  convert ((hl 0).mul (hl 1)).sub ((hl 2).mul (hl 3)) using 1
  simp only [pairDerivative,zero_mul,add_zero]
  ring

theorem gaussian_gradient (α β : ℝ) (v q : Transverse) :
    KFCausalPhysicalGaussianDerivative.gradient α β v q =
      (-2*weightedLinear α β v q:ℝ)*physicalGaussian α β q := by
  simp only [KFCausalPhysicalGaussianDerivative.gradient,KFCausalPhysicalGaussianMoments.widths,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,
    weightedLinear]
  push_cast
  ring

def profile (α β : ℝ) (g : ℝ → ℂ) (x : Configuration) : ℂ :=
  g x.1*((pairPolynomial x.2:ℂ)*physicalGaussian α β x.2)

theorem profile_transverse_differentiable (α β : ℝ) (g : ℝ → ℂ) (s : ℝ) :
    Differentiable ℝ (fun q : Transverse => profile α β g (s,q)) := by
  have hP : Differentiable ℝ (fun q : Transverse => (pairPolynomial q:ℂ)) := by
    have hr : Differentiable ℝ pairPolynomial := by unfold pairPolynomial; fun_prop
    exact Complex.ofRealCLM.differentiable.comp hr
  exact (hP.mul (physicalGaussian_differentiable α β)).const_mul (g s)

theorem profile_derivative (α β : ℝ) (g : ℝ → ℂ) (v : Transverse) (x : Configuration) :
    derivative v (profile α β g) x =
      g x.1*((derivativePolynomial α β v x.2:ℂ)*physicalGaussian α β x.2) := by
  have hP := pair_hasLineDerivAt v x.2
  have hG := physicalGaussian_hasLineDerivAt α β v x.2
  change HasDerivAt (fun t : ℝ => pairPolynomial (x.2+t • v)) (pairDerivative v x.2) 0 at hP
  change HasDerivAt (fun t : ℝ => physicalGaussian α β (x.2+t • v))
    (KFCausalPhysicalGaussianDerivative.gradient α β v x.2) 0 at hG
  have hd := ((hP.ofReal_comp.mul hG).const_mul (g x.1)).deriv
  change derivative v (profile α β g) x = _ at hd
  rw [hd,gaussian_gradient]
  simp only [zero_smul,add_zero,derivativePolynomial,Complex.ofReal_sub,Complex.ofReal_mul,
    Complex.ofReal_ofNat,Complex.ofReal_neg]
  ring

theorem profile_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) : MemLp (profile α β g) 2 volume := by
  refine configuration_product_memLp g
    (fun q => (pairPolynomial q:ℂ)*physicalGaussian α β q) hg ?_
  simpa only [pairPoly_eval] using
    KFCausalDirectionalGaussianStates.realPolynomial_memLp α β hα hβ pairPoly

theorem derivative_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) (v : Transverse) :
    MemLp (derivative v (profile α β g)) 2 volume := by
  rw [funext (profile_derivative α β g v)]
  refine configuration_product_memLp g
    (fun q => (derivativePolynomial α β v q:ℂ)*physicalGaussian α β q) hg ?_
  simpa only [derivativePoly_eval] using
    KFCausalDirectionalGaussianStates.realPolynomial_memLp α β hα hβ (derivativePoly α β v)

#print axioms pairPoly_eval
#print axioms derivativePoly_eval
#print axioms pair_hasLineDerivAt
#print axioms gaussian_gradient
#print axioms profile_transverse_differentiable
#print axioms profile_derivative
#print axioms profile_memLp
#print axioms derivative_memLp
end
end UnifiedTheory.Audit.KFCausalChargedPairDifferential
