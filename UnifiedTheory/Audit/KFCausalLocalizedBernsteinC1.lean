/- Explicit finite scalar coefficients give global C1 approximation after
compact time localization, for curves in any real Banach space. -/
import UnifiedTheory.Audit.KFCausalCompactTimeLocalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalLocalizedBernsteinC1
noncomputable section
open Set Filter BoundedContinuousFunction
open scoped Topology unitInterval
open UnifiedTheory.Audit.KFCausalBernsteinPrimitive
open UnifiedTheory.Audit.KFCausalBernsteinC1Approximation
open UnifiedTheory.Audit.KFCausalCompactTimeLocalization

def coefficient (χ : Cutoff) (n : ℕ) : Fin (n+2) → ℝ →ᵇ ℝ :=
  Fin.cases χ.value (fun k =>
    weighted χ.value χ.support (primitive n k) (primitive_continuous n k))

def coefficientDeriv (χ : Cutoff) (n : ℕ) : Fin (n+2) → ℝ →ᵇ ℝ :=
  Fin.cases χ.derivative (fun k =>
    localizedDerivative χ (primitive n k) (basis n k)
      (primitive_continuous n k) (basis_continuous n k))

theorem coefficient_derivative (χ : Cutoff) (n : ℕ) (i : Fin (n+2)) (t : ℝ) :
    HasDerivAt (coefficient χ n i) (coefficientDeriv χ n i t) t := by
  refine Fin.cases (χ.hasDeriv t) (fun k => ?_) i
  exact weighted_derivative χ (primitive n k) (basis n k)
    (primitive_continuous n k) (basis_continuous n k) (primitive_derivative n k) t

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def nodes (n : ℕ) (v : E) (g : C(I,E)) : Fin (n+2) → E :=
  Fin.cases v (fun k => g (bernstein.z k))

def approximate (χ : Cutoff) (n : ℕ) (v : E) (g : C(I,E)) : ℝ →ᵇ E :=
  weighted χ.value χ.support (valueApprox n v g) (valueApprox_continuous n v g)

def approximateDeriv (χ : Cutoff) (n : ℕ) (v : E) (g : C(I,E)) : ℝ →ᵇ E :=
  localizedDerivative χ (valueApprox n v g) (derivativeApprox n g)
    (valueApprox_continuous n v g) (derivativeApprox_continuous n g)

theorem approximate_derivative (χ : Cutoff) (n : ℕ) (v : E) (g : C(I,E)) (t : ℝ) :
    HasDerivAt (approximate χ n v g) (approximateDeriv χ n v g t) t :=
  weighted_derivative χ (valueApprox n v g) (derivativeApprox n g)
    (valueApprox_continuous n v g) (derivativeApprox_continuous n g)
    (valueApprox_derivative n v g) t

theorem approximate_eq_sum (χ : Cutoff) (n : ℕ) (v : E) (g : C(I,E)) (t : ℝ) :
    approximate χ n v g t = ∑ i : Fin (n+2), coefficient χ n i t • nodes n v g i := by
  simp only [approximate,weighted_apply,valueApprox,coefficient,nodes,Fin.sum_univ_succ,
    Fin.cases_zero,Fin.cases_succ,smul_add,Finset.smul_sum,smul_smul,smul_eq_mul]

theorem approximateDeriv_eq_sum (χ : Cutoff) (n : ℕ) (v : E) (g : C(I,E)) (t : ℝ) :
    approximateDeriv χ n v g t =
      ∑ i : Fin (n+2), coefficientDeriv χ n i t • nodes n v g i := by
  have hd := approximate_derivative χ n v g t
  have hs := HasDerivAt.fun_sum (u := Finset.univ)
    (fun (i : Fin (n+2)) _ => (coefficient_derivative χ n i t).smul_const (nodes n v g i))
  have he : (⇑(approximate χ n v g)) =
      (fun u => ∑ i : Fin (n+2), coefficient χ n i u • nodes n v g i) :=
    funext (approximate_eq_sum χ n v g)
  rw [he] at hd
  exact hd.unique hs

theorem derivative_unitCurve (n : ℕ) (g : C(I,E)) :
    unitCurve (derivativeApprox n g) (derivativeApprox_continuous n g) =
      bernsteinApproximation n g := by
  ext t
  exact derivativeApprox_on_unit n g t

variable [CompleteSpace E]

theorem approximate_converges (χ : Cutoff) (F F' : ℝ → E) (hF' : Continuous F')
    (hF : ∀ t, HasDerivAt F (F' t) t) :
    Tendsto (fun n => approximate χ n (F 0) (unitCurve F' hF')) atTop
      (𝓝 (weighted χ.value χ.support F (curve_continuous F F' hF))) :=
  weighted_tendsto χ.value χ.support
    (fun n => valueApprox n (F 0) (unitCurve F' hF')) F
    (fun n => valueApprox_continuous n (F 0) (unitCurve F' hF'))
    (curve_continuous F F' hF) (primitive_converges F F' hF' hF)

theorem approximateDeriv_converges (χ : Cutoff) (F F' : ℝ → E) (hF' : Continuous F')
    (hF : ∀ t, HasDerivAt F (F' t) t) :
    Tendsto (fun n => approximateDeriv χ n (F 0) (unitCurve F' hF')) atTop
      (𝓝 (localizedDerivative χ F F' (curve_continuous F F' hF) hF')) := by
  apply localizedDerivative_tendsto χ
    (fun n => valueApprox n (F 0) (unitCurve F' hF'))
    (fun n => derivativeApprox n (unitCurve F' hF')) F F'
    (fun n => valueApprox_continuous n (F 0) (unitCurve F' hF'))
    (fun n => derivativeApprox_continuous n (unitCurve F' hF'))
    (curve_continuous F F' hF) hF'
    (primitive_converges F F' hF' hF)
  simpa only [derivative_unitCurve] using derivative_converges F' hF'

theorem localized_c1_approximation (χ : Cutoff) (F F' : ℝ → E) (hF' : Continuous F')
    (hF : ∀ t, HasDerivAt F (F' t) t) :
    (∀ n t, HasDerivAt (approximate χ n (F 0) (unitCurve F' hF'))
      (approximateDeriv χ n (F 0) (unitCurve F' hF') t) t) ∧
    Tendsto (fun n => approximate χ n (F 0) (unitCurve F' hF')) atTop
      (𝓝 (weighted χ.value χ.support F (curve_continuous F F' hF))) ∧
    Tendsto (fun n => approximateDeriv χ n (F 0) (unitCurve F' hF')) atTop
      (𝓝 (localizedDerivative χ F F' (curve_continuous F F' hF) hF')) :=
  ⟨fun n t => approximate_derivative χ n (F 0) (unitCurve F' hF') t,
    approximate_converges χ F F' hF' hF,approximateDeriv_converges χ F F' hF' hF⟩

#print axioms coefficient_derivative
#print axioms approximate_derivative
#print axioms approximate_eq_sum
#print axioms approximateDeriv_eq_sum
#print axioms derivative_unitCurve
#print axioms approximate_converges
#print axioms approximateDeriv_converges
#print axioms localized_c1_approximation
end
end UnifiedTheory.Audit.KFCausalLocalizedBernsteinC1
