/- Affine changes of time preserve derivative-controlled tensor approximation. -/
import UnifiedTheory.Audit.KFCausalTensorTestClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalTensorAffineTime
noncomputable section
open Set Filter BoundedContinuousFunction
open scoped Topology
open UnifiedTheory.Audit.KFCausalTensorTestClosure
open UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation (tensor_apply)

def timeMap (c d : ℝ) : C(ℝ,ℝ) := ⟨fun t => c*t+d,by fun_prop⟩
def spacetimeMap (c d : ℝ) : C(ℝ × ℝ,ℝ × ℝ) :=
  ⟨fun z => (c*z.1+d,z.2),by fun_prop⟩

def pullback (c d : ℝ) : ((ℝ × ℝ) →ᵇ ℂ) →L[ℂ] ((ℝ × ℝ) →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun q => q.compContinuous (spacetimeMap c d)
      map_add' := fun _ _ => by ext z; rfl
      map_smul' := fun _ _ => by ext z; rfl }
    1 (fun q => by simpa only [one_mul] using q.norm_compContinuous_le (spacetimeMap c d))

theorem pullback_apply (c d : ℝ) (q : (ℝ × ℝ) →ᵇ ℂ) (t p : ℝ) :
    pullback c d q (t,p) = q (c*t+d,p) := rfl

def transform (c d : ℝ) (χ : TensorTest) : TensorTest where
  size := χ.size
  time i := (χ.time i).compContinuous (timeMap c d)
  timeDeriv i := (c : ℂ) • (χ.timeDeriv i).compContinuous (timeMap c d)
  momentum := χ.momentum
  hasDeriv i t := by
    have ht : HasDerivAt (fun u : ℝ => c*u+d) c t := by
      simpa only [mul_one] using ((hasDerivAt_id t).const_mul c).add_const d
    simpa only [Function.comp_def,Complex.real_smul] using (χ.hasDeriv i (c*t+d)).scomp t ht

theorem transform_value (c d : ℝ) (χ : TensorTest) :
    (transform c d χ).value = pullback c d χ.value := by
  ext ⟨t,p⟩
  simp only [TensorTest.value,tensor_apply,pullback_apply]
  rfl

theorem transform_dt (c d : ℝ) (χ : TensorTest) :
    (transform c d χ).dt = (c : ℂ) • pullback c d χ.dt := by
  ext ⟨t,p⟩
  simp only [BoundedContinuousFunction.smul_apply,pullback_apply,TensorTest.dt,tensor_apply]
  change (∑ i, ((c : ℂ)*χ.timeDeriv i (c*t+d))*χ.momentum i p) =
    (c : ℂ)*(∑ i, χ.timeDeriv i (c*t+d)*χ.momentum i p)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_assoc _ _ _

theorem transform_dp (c d : ℝ) (χ : TensorTest) :
    (transform c d χ).dp = pullback c d χ.dp := by
  ext ⟨t,p⟩
  simp only [TensorTest.dp,tensor_apply,pullback_apply]
  rfl

theorem approximable_pullback (c d : ℝ) (q r s : (ℝ × ℝ) →ᵇ ℂ)
    (h : Approximable q r s) :
    Approximable (pullback c d q) ((c : ℂ) • pullback c d r) (pullback c d s) := by
  obtain ⟨χ,hq,hr,hs⟩ := h
  refine ⟨fun n => transform c d (χ n),?_,?_,?_⟩
  · simp only [transform_value]
    exact ((pullback c d).continuous.tendsto q).comp hq
  · simp only [transform_dt]
    exact (((pullback c d).continuous.tendsto r).comp hr).const_smul (c : ℂ)
  · simp only [transform_dp]
    exact ((pullback c d).continuous.tendsto s).comp hs

#print axioms pullback_apply
#print axioms transform
#print axioms transform_value
#print axioms transform_dt
#print axioms transform_dp
#print axioms approximable_pullback
end
end UnifiedTheory.Audit.KFCausalTensorAffineTime
