/- Finite sums of separated smooth time and Schwartz momentum tests satisfy
the neutral weak equation. This does not assert density in all spacetime tests. -/
import UnifiedTheory.Audit.KFCausalSpacetimeTimeTestBalance
import UnifiedTheory.Audit.KFCausalNeutralGlobalSpacetimeDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction SchwartzMap
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce
open UnifiedTheory.Audit.KFCausalSpacetimeTriangularIntegral
open UnifiedTheory.Audit.KFCausalSpacetimeTimeTestBalance
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair (Pair)

def tensor {n : ℕ} (η : Fin n → ℝ →ᵇ ℂ) (f : Fin n → 𝓢(ℝ,ℂ)) : (ℝ × ℝ) →ᵇ ℂ :=
  ∑ i, timeWeight (η i) (momentumTest (f i).toBoundedContinuousFunction)

theorem tensor_apply {n : ℕ} (η : Fin n → ℝ →ᵇ ℂ) (f : Fin n → 𝓢(ℝ,ℂ)) (t p : ℝ) :
    tensor η f (t,p) = ∑ i, η i t*f i p := by
  simp only [tensor,BoundedContinuousFunction.sum_apply]
  rfl

theorem tensor_time_derivative {n : ℕ} (η η' : Fin n → ℝ →ᵇ ℂ)
    (f : Fin n → 𝓢(ℝ,ℂ)) (hη : ∀ i t, HasDerivAt (η i) (η' i t) t) (t p : ℝ) :
    HasDerivAt (fun u => tensor η f (u,p)) (tensor η' f (t,p)) t := by
  simp only [tensor_apply]
  exact HasDerivAt.fun_sum (fun i _ => (hη i t).mul_const (f i p))

theorem tensor_momentum_derivative {n : ℕ} (η : Fin n → ℝ →ᵇ ℂ)
    (f : Fin n → 𝓢(ℝ,ℂ)) (t p : ℝ) :
    HasDerivAt (fun x => tensor η f (t,x))
      (tensor η (fun i => derivCLM ℂ ℂ (f i)) (t,p)) p := by
  simp only [tensor_apply,derivCLM_apply]
  exact HasDerivAt.fun_sum (fun i _ => ((f i).hasDerivAt p).const_mul (η i t))

theorem tensor_slice_integral {n : ℕ} (η : Fin n → ℝ →ᵇ ℂ) (f : Fin n → 𝓢(ℝ,ℂ))
    (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    (∫ p, tensor η f (t,p) ∂μ) = ∑ i, η i t*(∫ p, f i p ∂μ) := by
  simp only [tensor_apply]
  have hi : ∀ i : Fin n, Integrable (fun p => η i t*f i p) μ :=
    fun i => ((f i).toBoundedContinuousFunction.integrable μ).const_mul (η i t)
  rw [integral_finset_sum _ (fun i _ => hi i)]
  simp only [integral_const_mul]

theorem evaluate_sum (F : Pair) {n : ℕ} (q : Fin n → (ℝ × ℝ) →ᵇ ℂ) :
    F.evaluate (∑ i, q i) = ∑ i, F.evaluate (q i) := by
  simp only [Pair.evaluate,BoundedContinuousFunction.sum_apply]
  rw [integral_finset_sum _ (fun i _ => (q i).integrable F.positive),
    integral_finset_sum _ (fun i _ => (q i).integrable F.negative),
    ← Finset.sum_sub_distrib,Finset.sum_div]

def IntervalBalance (ν : ℝ → ProbabilityMeasure ℝ) (J : Force) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∀ f : 𝓢(ℝ,ℂ),
    (∫ p, f p ∂(ν b : Measure ℝ))-(∫ p, f p ∂(ν a : Measure ℝ)) =
      (J.interval a b).evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction

theorem tensor_time_integrable (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (hbalance : IntervalBalance ν J) (a b : ℝ) {n : ℕ}
    (η' : Fin n → ℝ →ᵇ ℂ) (f : Fin n → 𝓢(ℝ,ℂ)) :
    Integrable (fun t => ∫ p, tensor η' f (t,p) ∂(ν t : Measure ℝ))
      (volume.restrict (Icc a b)) := by
  have hi : ∀ i : Fin n, Integrable
      (fun t => η' i t*(∫ p, f i p ∂(ν t : Measure ℝ))) (volume.restrict (Icc a b)) := by
    intro i
    exact weighted_balance_integrable J a b (fun t => ∫ p, f i p ∂(ν t : Measure ℝ))
      (derivCLM ℂ ℂ (f i)).toBoundedContinuousFunction
      (fun t ht => hbalance a t ht.1 (f i)) (η' i)
  simpa only [tensor_slice_integral] using integrable_finset_sum Finset.univ (fun i _ => hi i)

theorem tensor_test_balance (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (hbalance : IntervalBalance ν J) (a b : ℝ) (hab : a ≤ b) {n : ℕ}
    (η η' : Fin n → ℝ →ᵇ ℂ) (f : Fin n → 𝓢(ℝ,ℂ))
    (hη : ∀ i t, HasDerivAt (η i) (η' i t) t) :
    (∫ t in Icc a b, ∫ p, tensor η' f (t,p) ∂(ν t : Measure ℝ)) +
      (J.window a b).evaluate (tensor η (fun i => derivCLM ℂ ℂ (f i))) =
        (∫ p, tensor η f (b,p) ∂(ν b : Measure ℝ))-
          (∫ p, tensor η f (a,p) ∂(ν a : Measure ℝ)) := by
  have hi : ∀ i : Fin n, Integrable
      (fun t => η' i t*(∫ p, f i p ∂(ν t : Measure ℝ))) (volume.restrict (Icc a b)) := by
    intro i
    exact weighted_balance_integrable J a b (fun t => ∫ p, f i p ∂(ν t : Measure ℝ))
      (derivCLM ℂ ℂ (f i)).toBoundedContinuousFunction
      (fun t ht => hbalance a t ht.1 (f i)) (η' i)
  simp only [tensor_slice_integral]
  rw [integral_finset_sum _ (fun i _ => hi i),tensor,evaluate_sum,
    ← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact time_test_balance J a b hab (fun t => ∫ p, f i p ∂(ν t : Measure ℝ))
    (derivCLM ℂ ℂ (f i)).toBoundedContinuousFunction
    (fun t ht => hbalance a t ht.1 (f i)) (η i) (η' i) (hη i)

theorem tensor_test_zero_boundary (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (hbalance : IntervalBalance ν J) (a b : ℝ) (hab : a ≤ b) {n : ℕ}
    (η η' : Fin n → ℝ →ᵇ ℂ) (f : Fin n → 𝓢(ℝ,ℂ))
    (hη : ∀ i t, HasDerivAt (η i) (η' i t) t)
    (ha : ∀ i, η i a = 0) (hb : ∀ i, η i b = 0) :
    (∫ t in Icc a b, ∫ p, tensor η' f (t,p) ∂(ν t : Measure ℝ)) +
      (J.window a b).evaluate (tensor η (fun i => derivCLM ℂ ℂ (f i))) = 0 := by
  simpa only [tensor_slice_integral,ha,hb,zero_mul,Finset.sum_const_zero,sub_zero] using
    tensor_test_balance ν J hbalance a b hab η η' f hη

def TensorWeakEquation (ν : ℝ → ProbabilityMeasure ℝ) (J : Force) : Prop :=
  ∀ (a b : ℝ), a ≤ b → ∀ (n : ℕ) (η η' : Fin n → ℝ →ᵇ ℂ) (f : Fin n → 𝓢(ℝ,ℂ)),
    (∀ i t, HasDerivAt (η i) (η' i t) t) →
    Integrable (fun t => ∫ p, tensor η' f (t,p) ∂(ν t : Measure ℝ))
      (volume.restrict (Icc a b)) ∧
    (∫ t in Icc a b, ∫ p, tensor η' f (t,p) ∂(ν t : Measure ℝ)) +
      (J.window a b).evaluate (tensor η (fun i => derivCLM ℂ ℂ (f i))) =
        (∫ p, tensor η f (b,p) ∂(ν b : Measure ℝ))-
          (∫ p, tensor η f (a,p) ∂(ν a : Measure ℝ))

theorem tensor_weak_equation (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (hbalance : IntervalBalance ν J) : TensorWeakEquation ν J := by
  intro a b hab n η η' f hη
  exact ⟨tensor_time_integrable ν J hbalance a b η' f,
    tensor_test_balance ν J hbalance a b hab η η' f hη⟩

#print axioms tensor_apply
#print axioms tensor_time_derivative
#print axioms tensor_momentum_derivative
#print axioms tensor_slice_integral
#print axioms evaluate_sum
#print axioms tensor_time_integrable
#print axioms tensor_test_balance
#print axioms tensor_test_zero_boundary
#print axioms tensor_weak_equation
end
end UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation
