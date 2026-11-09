/- A pair of bounded momentum functions tracks a test and its momentum
derivative. Flattening a bounded time curve preserves uniform convergence. -/
import UnifiedTheory.Audit.KFCausalLocalizedBernsteinC1
import UnifiedTheory.Audit.KFCausalTensorTestClosure
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalMomentumPairTests
noncomputable section
open BoundedContinuousFunction SchwartzMap

abbrev MomentumPair := (ℝ →ᵇ ℂ) × (ℝ →ᵇ ℂ)

def spatialPair (f : 𝓢(ℝ,ℂ)) : MomentumPair :=
  (f.toBoundedContinuousFunction,(derivCLM ℂ ℂ f).toBoundedContinuousFunction)

def uncurry (F : ℝ →ᵇ (ℝ →ᵇ ℂ)) : (ℝ × ℝ) →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => F z.1 z.2)
    (by fun_prop) ‖F‖ (fun z => ((F z.1).norm_coe_le_norm z.2).trans (F.norm_coe_le_norm z.1))

theorem uncurry_apply (F : ℝ →ᵇ (ℝ →ᵇ ℂ)) (t p : ℝ) : uncurry F (t,p) = F t p := rfl

theorem uncurry_norm_le (F : ℝ →ᵇ (ℝ →ᵇ ℂ)) : ‖uncurry F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  exact fun z => ((F z.1).norm_coe_le_norm z.2).trans (F.norm_coe_le_norm z.1)

def uncurryCLM : (ℝ →ᵇ (ℝ →ᵇ ℂ)) →L[ℝ] ((ℝ × ℝ) →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := uncurry
      map_add' := fun _ _ => by ext z; rfl
      map_smul' := fun _ _ => by ext z; rfl }
    1 (fun F => by simpa only [one_mul] using uncurry_norm_le F)

def flattenFirst : (ℝ →ᵇ MomentumPair) →L[ℝ] ((ℝ × ℝ) →ᵇ ℂ) :=
  uncurryCLM.comp ((ContinuousLinearMap.fst ℝ (ℝ →ᵇ ℂ) (ℝ →ᵇ ℂ)).compLeftContinuousBounded ℝ)

def flattenSecond : (ℝ →ᵇ MomentumPair) →L[ℝ] ((ℝ × ℝ) →ᵇ ℂ) :=
  uncurryCLM.comp ((ContinuousLinearMap.snd ℝ (ℝ →ᵇ ℂ) (ℝ →ᵇ ℂ)).compLeftContinuousBounded ℝ)

theorem flattenFirst_apply (F : ℝ →ᵇ MomentumPair) (t p : ℝ) :
    flattenFirst F (t,p) = (F t).1 p := rfl

theorem flattenSecond_apply (F : ℝ →ᵇ MomentumPair) (t p : ℝ) :
    flattenSecond F (t,p) = (F t).2 p := rfl

def complexify (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℂ := Complex.ofRealCLM.compLeftContinuousBounded ℝ f

theorem complexify_apply (f : ℝ →ᵇ ℝ) (t : ℝ) : complexify f t = (f t : ℂ) := rfl

theorem complexify_derivative (f g : ℝ →ᵇ ℝ) (h : ∀ t, HasDerivAt f (g t) t) (t : ℝ) :
    HasDerivAt (complexify f) (complexify g t) t := (h t).ofReal_comp

#print axioms uncurry_apply
#print axioms uncurry_norm_le
#print axioms flattenFirst_apply
#print axioms flattenSecond_apply
#print axioms complexify_apply
#print axioms complexify_derivative
end
end UnifiedTheory.Audit.KFCausalMomentumPairTests
