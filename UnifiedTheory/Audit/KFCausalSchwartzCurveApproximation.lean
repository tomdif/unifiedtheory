/- Construct tensor approximants for a compactly time-localized Schwartz
curve whose value/momentum-derivative pair has a continuous norm derivative.
The analytic curve hypotheses are not physical evolution assumptions. -/
import UnifiedTheory.Audit.KFCausalMomentumPairTests

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSchwartzCurveApproximation
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction SchwartzMap
open scoped Topology unitInterval
open UnifiedTheory.Audit.KFCausalBernsteinC1Approximation
open UnifiedTheory.Audit.KFCausalCompactTimeLocalization
open UnifiedTheory.Audit.KFCausalLocalizedBernsteinC1
open UnifiedTheory.Audit.KFCausalMomentumPairTests
open UnifiedTheory.Audit.KFCausalTensorTestClosure
open UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce (Force)
open UnifiedTheory.Audit.KFCausalSpacetimeUniformTests (expectation)

def samples (n : ℕ) (F G : ℝ → 𝓢(ℝ,ℂ)) : Fin (n+2) → 𝓢(ℝ,ℂ) :=
  Fin.cases (F 0) (fun k => G (bernstein.z k))

def tensorApprox (χ : Cutoff) (F G : ℝ → 𝓢(ℝ,ℂ)) (n : ℕ) : TensorTest where
  size := n+2
  time := fun i => complexify (coefficient χ n i)
  timeDeriv := fun i => complexify (coefficientDeriv χ n i)
  momentum := samples n F G
  hasDeriv := fun i => complexify_derivative _ _ (coefficient_derivative χ n i)

theorem samples_pair (n : ℕ) (F G : ℝ → 𝓢(ℝ,ℂ))
    (hG : Continuous (fun t => spatialPair (G t))) (i : Fin (n+2)) :
    nodes n (spatialPair (F 0)) (unitCurve (fun t => spatialPair (G t)) hG) i =
      spatialPair (samples n F G i) := by
  exact Fin.cases rfl (fun _ => rfl) i

theorem tensorApprox_value (χ : Cutoff) (F G : ℝ → 𝓢(ℝ,ℂ))
    (hG : Continuous (fun t => spatialPair (G t))) (n : ℕ) :
    (tensorApprox χ F G n).value =
      flattenFirst (approximate χ n (spatialPair (F 0))
        (unitCurve (fun t => spatialPair (G t)) hG)) := by
  ext ⟨t,p⟩
  rw [flattenFirst_apply,approximate_eq_sum]
  simp only [Prod.fst_sum,Prod.smul_fst,BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.smul_apply,Complex.real_smul]
  simp_rw [samples_pair n F G hG]
  exact tensor_apply _ _ t p

theorem tensorApprox_dt (χ : Cutoff) (F G : ℝ → 𝓢(ℝ,ℂ))
    (hG : Continuous (fun t => spatialPair (G t))) (n : ℕ) :
    (tensorApprox χ F G n).dt =
      flattenFirst (approximateDeriv χ n (spatialPair (F 0))
        (unitCurve (fun t => spatialPair (G t)) hG)) := by
  ext ⟨t,p⟩
  rw [flattenFirst_apply,approximateDeriv_eq_sum]
  simp only [Prod.fst_sum,Prod.smul_fst,BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.smul_apply,Complex.real_smul]
  simp_rw [samples_pair n F G hG]
  exact tensor_apply _ _ t p

theorem tensorApprox_dp (χ : Cutoff) (F G : ℝ → 𝓢(ℝ,ℂ))
    (hG : Continuous (fun t => spatialPair (G t))) (n : ℕ) :
    (tensorApprox χ F G n).dp =
      flattenSecond (approximate χ n (spatialPair (F 0))
        (unitCurve (fun t => spatialPair (G t)) hG)) := by
  ext ⟨t,p⟩
  rw [flattenSecond_apply,approximate_eq_sum]
  simp only [Prod.snd_sum,Prod.smul_snd,BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.smul_apply,Complex.real_smul]
  simp_rw [samples_pair n F G hG]
  exact tensor_apply _ _ t p

theorem schwartz_curve_approximable (χ : Cutoff) (F G : ℝ → 𝓢(ℝ,ℂ))
    (hG : Continuous (fun t => spatialPair (G t)))
    (hF : ∀ t, HasDerivAt (fun u => spatialPair (F u)) (spatialPair (G t)) t) :
    Approximable
      (flattenFirst (weighted χ.value χ.support (fun t => spatialPair (F t))
        (curve_continuous _ _ hF)))
      (flattenFirst (localizedDerivative χ (fun t => spatialPair (F t))
        (fun t => spatialPair (G t)) (curve_continuous _ _ hF) hG))
      (flattenSecond (weighted χ.value χ.support (fun t => spatialPair (F t))
        (curve_continuous _ _ hF))) := by
  refine ⟨tensorApprox χ F G,?_,?_,?_⟩
  · simp only [tensorApprox_value χ F G hG]
    exact flattenFirst.continuous.tendsto _ |>.comp
      (approximate_converges χ (fun t => spatialPair (F t))
        (fun t => spatialPair (G t)) hG hF)
  · simp only [tensorApprox_dt χ F G hG]
    exact flattenFirst.continuous.tendsto _ |>.comp
      (approximateDeriv_converges χ (fun t => spatialPair (F t))
        (fun t => spatialPair (G t)) hG hF)
  · simp only [tensorApprox_dp χ F G hG]
    exact flattenSecond.continuous.tendsto _ |>.comp
      (approximate_converges χ (fun t => spatialPair (F t))
        (fun t => spatialPair (G t)) hG hF)

theorem schwartz_curve_weak_equation (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (hweak : UniformWeakEquation ν J) (a b : ℝ) (hab : a ≤ b)
    (χ : Cutoff) (F G : ℝ → 𝓢(ℝ,ℂ))
    (hG : Continuous (fun t => spatialPair (G t)))
    (hF : ∀ t, HasDerivAt (fun u => spatialPair (F u)) (spatialPair (G t)) t) :
    let φ := flattenFirst (weighted χ.value χ.support (fun t => spatialPair (F t))
      (curve_continuous _ _ hF))
    let φt := flattenFirst (localizedDerivative χ (fun t => spatialPair (F t))
      (fun t => spatialPair (G t)) (curve_continuous _ _ hF) hG)
    let φp := flattenSecond (weighted χ.value χ.support (fun t => spatialPair (F t))
      (curve_continuous _ _ hF))
    Integrable (expectation ν φt) (volume.restrict (Icc a b)) ∧
      (∫ t in Icc a b, expectation ν φt t)+(J.window a b).evaluate φp =
        expectation ν φ b-expectation ν φ a :=
  hweak a b hab _ _ _ (schwartz_curve_approximable χ F G hG hF)

#print axioms samples_pair
#print axioms tensorApprox_value
#print axioms tensorApprox_dt
#print axioms tensorApprox_dp
#print axioms schwartz_curve_approximable
#print axioms schwartz_curve_weak_equation
end
end UnifiedTheory.Audit.KFCausalSchwartzCurveApproximation
