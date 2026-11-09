/- Summable norm budgets construct infinite tensor-series tests with uniform
control of the value and both derivatives. These tests satisfy weak dynamics. -/
import UnifiedTheory.Audit.KFCausalTensorTestClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalTensorSeriesTests
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction SchwartzMap
open scoped Topology
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce (Force momentumTest)
open UnifiedTheory.Audit.KFCausalSpacetimeTriangularIntegral (timeWeight)
open UnifiedTheory.Audit.KFCausalSpacetimeUniformTests (expectation)
open UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation (TensorWeakEquation tensor)
open UnifiedTheory.Audit.KFCausalTensorTestClosure

def term (η : ℝ →ᵇ ℂ) (f : 𝓢(ℝ,ℂ)) : (ℝ × ℝ) →ᵇ ℂ :=
  timeWeight η (momentumTest f.toBoundedContinuousFunction)

theorem term_norm_le (η : ℝ →ᵇ ℂ) (f : 𝓢(ℝ,ℂ)) :
    ‖term η f‖ ≤ ‖η‖*‖f.toBoundedContinuousFunction‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro z
  change ‖η z.1*f z.2‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (η.norm_coe_le_norm z.1)
    (f.toBoundedContinuousFunction.norm_coe_le_norm z.2) (norm_nonneg _) (norm_nonneg _)

theorem terms_summable (η : ℕ → ℝ →ᵇ ℂ) (f : ℕ → 𝓢(ℝ,ℂ))
    (h : Summable (fun n => ‖η n‖*‖(f n).toBoundedContinuousFunction‖)) :
    Summable (fun n => term (η n) (f n)) :=
  h.of_norm_bounded (fun n => term_norm_le (η n) (f n))

def partialTest (η η' : ℕ → ℝ →ᵇ ℂ) (f : ℕ → 𝓢(ℝ,ℂ))
    (hη : ∀ n t, HasDerivAt (η n) (η' n t) t) (N : ℕ) : TensorTest where
  size := N
  time := fun i => η i.val
  timeDeriv := fun i => η' i.val
  momentum := fun i => f i.val
  hasDeriv := fun i => hη i.val

theorem partial_value (η η' : ℕ → ℝ →ᵇ ℂ) (f : ℕ → 𝓢(ℝ,ℂ))
    (hη : ∀ n t, HasDerivAt (η n) (η' n t) t) (N : ℕ) :
    (partialTest η η' f hη N).value = ∑ n ∈ Finset.range N, term (η n) (f n) := by
  exact Fin.sum_univ_eq_sum_range (fun n => term (η n) (f n)) N

theorem partial_dt (η η' : ℕ → ℝ →ᵇ ℂ) (f : ℕ → 𝓢(ℝ,ℂ))
    (hη : ∀ n t, HasDerivAt (η n) (η' n t) t) (N : ℕ) :
    (partialTest η η' f hη N).dt = ∑ n ∈ Finset.range N, term (η' n) (f n) := by
  exact Fin.sum_univ_eq_sum_range (fun n => term (η' n) (f n)) N

theorem partial_dp (η η' : ℕ → ℝ →ᵇ ℂ) (f : ℕ → 𝓢(ℝ,ℂ))
    (hη : ∀ n t, HasDerivAt (η n) (η' n t) t) (N : ℕ) :
    (partialTest η η' f hη N).dp =
      ∑ n ∈ Finset.range N, term (η n) (derivCLM ℂ ℂ (f n)) := by
  exact Fin.sum_univ_eq_sum_range (fun n => term (η n) (derivCLM ℂ ℂ (f n))) N

theorem series_approximable (η η' : ℕ → ℝ →ᵇ ℂ) (f : ℕ → 𝓢(ℝ,ℂ))
    (hη : ∀ n t, HasDerivAt (η n) (η' n t) t)
    (hv : Summable (fun n => ‖η n‖*‖(f n).toBoundedContinuousFunction‖))
    (ht : Summable (fun n => ‖η' n‖*‖(f n).toBoundedContinuousFunction‖))
    (hp : Summable (fun n => ‖η n‖*‖(derivCLM ℂ ℂ (f n)).toBoundedContinuousFunction‖)) :
    Approximable (∑' n, term (η n) (f n)) (∑' n, term (η' n) (f n))
      (∑' n, term (η n) (derivCLM ℂ ℂ (f n))) := by
  refine ⟨partialTest η η' f hη,?_,?_,?_⟩
  · simpa only [partial_value] using (terms_summable η f hv).hasSum.tendsto_sum_nat
  · simpa only [partial_dt] using (terms_summable η' f ht).hasSum.tendsto_sum_nat
  · simpa only [partial_dp] using
      (terms_summable η (fun n => derivCLM ℂ ℂ (f n)) hp).hasSum.tendsto_sum_nat

theorem series_derivatives (η η' : ℕ → ℝ →ᵇ ℂ) (f : ℕ → 𝓢(ℝ,ℂ))
    (hη : ∀ n t, HasDerivAt (η n) (η' n t) t)
    (hv : Summable (fun n => ‖η n‖*‖(f n).toBoundedContinuousFunction‖))
    (ht : Summable (fun n => ‖η' n‖*‖(f n).toBoundedContinuousFunction‖))
    (hp : Summable (fun n => ‖η n‖*‖(derivCLM ℂ ℂ (f n)).toBoundedContinuousFunction‖))
    (t p : ℝ) :
    HasDerivAt (fun u => (∑' n, term (η n) (f n)) (u,p))
      ((∑' n, term (η' n) (f n)) (t,p)) t ∧
    HasDerivAt (fun x => (∑' n, term (η n) (f n)) (t,x))
      ((∑' n, term (η n) (derivCLM ℂ ℂ (f n))) (t,p)) p := by
  have ha := series_approximable η η' f hη hv ht hp
  exact ⟨limit_time_derivative _ _ _ ha t p,limit_momentum_derivative _ _ _ ha t p⟩

theorem series_weak_equation (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (hweak : TensorWeakEquation ν J) (a b : ℝ) (hab : a ≤ b)
    (η η' : ℕ → ℝ →ᵇ ℂ) (f : ℕ → 𝓢(ℝ,ℂ))
    (hη : ∀ n t, HasDerivAt (η n) (η' n t) t)
    (hv : Summable (fun n => ‖η n‖*‖(f n).toBoundedContinuousFunction‖))
    (ht : Summable (fun n => ‖η' n‖*‖(f n).toBoundedContinuousFunction‖))
    (hp : Summable (fun n => ‖η n‖*‖(derivCLM ℂ ℂ (f n)).toBoundedContinuousFunction‖)) :
    Integrable (expectation ν (∑' n, term (η' n) (f n))) (volume.restrict (Icc a b)) ∧
    (∫ t in Icc a b, expectation ν (∑' n, term (η' n) (f n)) t)+
      (J.window a b).evaluate (∑' n, term (η n) (derivCLM ℂ ℂ (f n))) =
        expectation ν (∑' n, term (η n) (f n)) b-
          expectation ν (∑' n, term (η n) (f n)) a :=
  uniform_weak_equation ν J hweak a b hab _ _ _ (series_approximable η η' f hη hv ht hp)

#print axioms term_norm_le
#print axioms terms_summable
#print axioms partial_value
#print axioms partial_dt
#print axioms partial_dp
#print axioms series_approximable
#print axioms series_derivatives
#print axioms series_weak_equation
end
end UnifiedTheory.Audit.KFCausalTensorSeriesTests
