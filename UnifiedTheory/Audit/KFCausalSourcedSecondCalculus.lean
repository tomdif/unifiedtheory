/- The actual second transverse derivative of a coherent-source packet,
including the complex source contribution and the derivative of its
linear Gaussian coefficient. -/
import UnifiedTheory.Audit.KFCausalGaussianSecondMomentum
import UnifiedTheory.Audit.KFCausalSourcedDirectionalMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalSourcedSecondCalculus
noncomputable section
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalDirectionalGaussianStates (linearForm)
open KFCausalGaussianSecondMomentum (direction linearForm_hasLineDerivAt)
open KFCausalClockFloorCoherentSources (linearSource)
open KFCausalClockFloorCoherentMoments (sourcedPacket)
open KFCausalClockFloorCoherentDerivative
open KFCausalTransverseTrialDerivative (derivative)

def coefficient (α β : ℝ) (b : Fin 5 → ℂ) (v q : Transverse) : ℂ :=
  linearSource b v+(linearForm (direction α β v) q:ℂ)

theorem gradient_formula (α β : ℝ) (b : Fin 5 → ℂ) (v q : Transverse) :
    gradient α β b v q = coefficient α β b v q*sourcedPacket α β b q := by
  simp only [gradient,coefficient,linearForm,direction,Complex.ofReal_sum,Complex.ofReal_mul,
    Finset.sum_mul,add_mul]

theorem packet_line_derivative (α β : ℝ) (b : Fin 5 → ℂ) (v q : Transverse) :
    HasLineDerivAt ℝ (sourcedPacket α β b)
      (coefficient α β b v q*sourcedPacket α β b q) q v := by
  rw [← gradient_formula]
  exact sourcedPacket_hasLineDerivAt α β b v q

theorem coefficient_line_derivative (α β : ℝ) (b : Fin 5 → ℂ) (v q : Transverse) :
    HasLineDerivAt ℝ (coefficient α β b v) (linearForm (direction α β v) v:ℂ) q v :=
  (linearForm_hasLineDerivAt (direction α β v) q v).const_add (linearSource b v)

theorem first_formula (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ) (v : Transverse) :
    derivative v (physicalProfile C p α β b g) = fun x =>
      coefficient α β b v x.2*physicalProfile C p α β b g x := by
  funext x
  rw [physicalProfile_derivative,gradient_formula]
  unfold physicalProfile
  ring

def secondProfile (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ)
    (v : Transverse) (x : Configuration) : ℂ :=
  (coefficient α β b v x.2^2+(linearForm (direction α β v) v:ℂ))*physicalProfile C p α β b g x

theorem second_derivative (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ) (v : Transverse) :
    derivative v (derivative v (physicalProfile C p α β b g)) = secondProfile C p α β b g v := by
  rw [first_formula]
  funext x
  have hd := (coefficient_line_derivative α β b v x.2).mul
    ((packet_line_derivative α β b v x.2).const_mul (clockMultiplier C p g x.1))
  convert hd.deriv using 1
  unfold secondProfile physicalProfile
  simp only [zero_smul,add_zero]
  ring

theorem first_differentiable (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ)
    (v : Transverse) (s : ℝ) :
    Differentiable ℝ (fun q : Transverse => derivative v (physicalProfile C p α β b g) (s,q)) := by
  rw [first_formula]
  have hd : Differentiable ℝ (coefficient α β b v) := by
    have hr : Differentiable ℝ (linearForm (direction α β v)) := by
      unfold linearForm
      fun_prop
    exact (Complex.ofRealCLM.differentiable.comp hr).const_add (linearSource b v)
  exact hd.mul (physicalProfile_transverse_differentiable C p α β b g s)

theorem second_expansion (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ)
    (v : Transverse) (x : Configuration) :
    secondProfile C p α β b g v x =
      KFCausalSourcedDirectionalMoments.profile C p α β b g (direction α β v) 2 x+
      (2*linearSource b v)*KFCausalSourcedDirectionalMoments.profile C p α β b g (direction α β v) 1 x+
      (linearSource b v^2+(linearForm (direction α β v) v:ℂ))*
        KFCausalSourcedDirectionalMoments.profile C p α β b g (direction α β v) 0 x := by
  unfold secondProfile coefficient KFCausalSourcedDirectionalMoments.profile
  ring

#print axioms gradient_formula
#print axioms packet_line_derivative
#print axioms coefficient_line_derivative
#print axioms first_formula
#print axioms second_derivative
#print axioms first_differentiable
#print axioms second_expansion
end
end UnifiedTheory.Audit.KFCausalSourcedSecondCalculus
