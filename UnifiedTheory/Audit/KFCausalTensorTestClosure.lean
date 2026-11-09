/- Simultaneous uniform limits of finite tensor tests and both derivatives
retain the actual partial derivatives and the weak equation. Density in all
smooth compactly supported spacetime tests is not assumed here. -/
import UnifiedTheory.Audit.KFCausalSpacetimeUniformTests
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalTensorTestClosure
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction SchwartzMap
open scoped Topology
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce (Force)
open UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation
open UnifiedTheory.Audit.KFCausalSpacetimeUniformTests

structure TensorTest where
  size : ℕ
  time : Fin size → ℝ →ᵇ ℂ
  timeDeriv : Fin size → ℝ →ᵇ ℂ
  momentum : Fin size → 𝓢(ℝ,ℂ)
  hasDeriv : ∀ i t, HasDerivAt (time i) (timeDeriv i t) t

def TensorTest.value (χ : TensorTest) : (ℝ × ℝ) →ᵇ ℂ := tensor χ.time χ.momentum
def TensorTest.dt (χ : TensorTest) : (ℝ × ℝ) →ᵇ ℂ := tensor χ.timeDeriv χ.momentum
def TensorTest.dp (χ : TensorTest) : (ℝ × ℝ) →ᵇ ℂ :=
  tensor χ.time (fun i => derivCLM ℂ ℂ (χ.momentum i))

theorem TensorTest.has_time_derivative (χ : TensorTest) (t p : ℝ) :
    HasDerivAt (fun u => χ.value (u,p)) (χ.dt (t,p)) t :=
  tensor_time_derivative χ.time χ.timeDeriv χ.momentum χ.hasDeriv t p

theorem TensorTest.has_momentum_derivative (χ : TensorTest) (t p : ℝ) :
    HasDerivAt (fun x => χ.value (t,x)) (χ.dp (t,p)) p :=
  tensor_momentum_derivative χ.time χ.momentum t p

def Approximable (φ φt φp : (ℝ × ℝ) →ᵇ ℂ) : Prop :=
  ∃ χ : ℕ → TensorTest,
    Tendsto (fun n => (χ n).value) atTop (𝓝 φ) ∧
    Tendsto (fun n => (χ n).dt) atTop (𝓝 φt) ∧
    Tendsto (fun n => (χ n).dp) atTop (𝓝 φp)

theorem tensor_approximable (χ : TensorTest) : Approximable χ.value χ.dt χ.dp :=
  ⟨fun _ => χ,tendsto_const_nhds,tendsto_const_nhds,tendsto_const_nhds⟩

theorem limit_time_derivative (φ φt φp : (ℝ × ℝ) →ᵇ ℂ)
    (hφ : Approximable φ φt φp) (t p : ℝ) :
    HasDerivAt (fun u => φ (u,p)) (φt (t,p)) t := by
  obtain ⟨χ,hv,ht,_⟩ := hφ
  exact hasDerivAt_of_tendstoUniformly
    ((BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp ht).comp (fun u : ℝ => (u,p)))
    (Eventually.of_forall (fun n u => (χ n).has_time_derivative u p))
    (fun u => (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hv).tendsto_at (u,p)) t

theorem limit_momentum_derivative (φ φt φp : (ℝ × ℝ) →ᵇ ℂ)
    (hφ : Approximable φ φt φp) (t p : ℝ) :
    HasDerivAt (fun x => φ (t,x)) (φp (t,p)) p := by
  obtain ⟨χ,hv,_,hp⟩ := hφ
  exact hasDerivAt_of_tendstoUniformly
    ((BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hp).comp (fun x : ℝ => (t,x)))
    (Eventually.of_forall (fun n x => (χ n).has_momentum_derivative t x))
    (fun x => (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hv).tendsto_at (t,x)) p

theorem limit_time_integrable (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (hweak : TensorWeakEquation ν J) (a b : ℝ) (hab : a ≤ b)
    (φ φt φp : (ℝ × ℝ) →ᵇ ℂ) (hφ : Approximable φ φt φp) :
    Integrable (expectation ν φt) (volume.restrict (Icc a b)) := by
  obtain ⟨χ,_,ht,_⟩ := hφ
  exact expectation_limit_integrable ν a b (fun n => (χ n).dt) φt ht
    (fun n => (hweak a b hab (χ n).size (χ n).time (χ n).timeDeriv
      (χ n).momentum (χ n).hasDeriv).1)

theorem limit_balance (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (hweak : TensorWeakEquation ν J) (a b : ℝ) (hab : a ≤ b)
    (φ φt φp : (ℝ × ℝ) →ᵇ ℂ) (hφ : Approximable φ φt φp) :
    (∫ t in Icc a b, expectation ν φt t)+(J.window a b).evaluate φp =
      expectation ν φ b-expectation ν φ a := by
  obtain ⟨χ,hv,ht,hp⟩ := hφ
  have hi : ∀ n, Integrable (expectation ν (χ n).dt) (volume.restrict (Icc a b)) :=
    fun n => (hweak a b hab (χ n).size (χ n).time (χ n).timeDeriv
      (χ n).momentum (χ n).hasDeriv).1
  have hl := (expectation_integral_tendsto ν a b (fun n => (χ n).dt) φt ht hi).add
    (force_tendsto (J.window a b) (fun n => (χ n).dp) φp hp)
  have hr := (expectation_tendsto ν (fun n => (χ n).value) φ hv b).sub
    (expectation_tendsto ν (fun n => (χ n).value) φ hv a)
  have he : (fun n => (∫ t in Icc a b, expectation ν (χ n).dt t)+
      (J.window a b).evaluate (χ n).dp) =
        (fun n => expectation ν (χ n).value b-expectation ν (χ n).value a) := by
    funext n
    exact (hweak a b hab (χ n).size (χ n).time (χ n).timeDeriv
      (χ n).momentum (χ n).hasDeriv).2
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

theorem limit_zero_boundary (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (hweak : TensorWeakEquation ν J) (a b : ℝ) (hab : a ≤ b)
    (φ φt φp : (ℝ × ℝ) →ᵇ ℂ) (hφ : Approximable φ φt φp)
    (ha : ∀ p, φ (a,p) = 0) (hb : ∀ p, φ (b,p) = 0) :
    (∫ t in Icc a b, expectation ν φt t)+(J.window a b).evaluate φp = 0 := by
  simpa only [expectation,ha,hb,integral_zero,sub_zero] using
    limit_balance ν J hweak a b hab φ φt φp hφ

def UniformWeakEquation (ν : ℝ → ProbabilityMeasure ℝ) (J : Force) : Prop :=
  ∀ (a b : ℝ), a ≤ b → ∀ (φ φt φp : (ℝ × ℝ) →ᵇ ℂ), Approximable φ φt φp →
    Integrable (expectation ν φt) (volume.restrict (Icc a b)) ∧
    (∫ t in Icc a b, expectation ν φt t)+(J.window a b).evaluate φp =
      expectation ν φ b-expectation ν φ a

theorem uniform_weak_equation (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (hweak : TensorWeakEquation ν J) : UniformWeakEquation ν J := by
  intro a b hab φ φt φp hφ
  exact ⟨limit_time_integrable ν J hweak a b hab φ φt φp hφ,
    limit_balance ν J hweak a b hab φ φt φp hφ⟩

#print axioms TensorTest.has_time_derivative
#print axioms TensorTest.has_momentum_derivative
#print axioms tensor_approximable
#print axioms limit_time_derivative
#print axioms limit_momentum_derivative
#print axioms limit_time_integrable
#print axioms limit_balance
#print axioms limit_zero_boundary
#print axioms uniform_weak_equation
end
end UnifiedTheory.Audit.KFCausalTensorTestClosure
