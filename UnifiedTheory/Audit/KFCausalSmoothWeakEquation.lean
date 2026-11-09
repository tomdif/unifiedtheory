/- Full smooth compact spacetime-test weak dynamics follows from the proved
tensor density. Both probability boundary terms are retained on every interval. -/
import UnifiedTheory.Audit.KFCausalSmoothTestDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSmoothWeakEquation
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalSmoothSpacetimeTests (Test)
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce (Force)
open UnifiedTheory.Audit.KFCausalSpacetimeUniformTests (expectation)
open UnifiedTheory.Audit.KFCausalTensorTestClosure
open UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation (TensorWeakEquation)
open UnifiedTheory.Audit.KFCausalSmoothTestDensity

def SmoothWeakEquation (ν : ℝ → ProbabilityMeasure ℝ) (J : Force) : Prop :=
  ∀ (a b : ℝ), a ≤ b → ∀ φ : Test,
    Integrable (expectation ν φ.dt.toBCF) (volume.restrict (Icc a b)) ∧
    (∫ t in Icc a b, expectation ν φ.dt.toBCF t)+(J.window a b).evaluate φ.dp.toBCF =
      expectation ν φ.toBCF b-expectation ν φ.toBCF a

theorem of_uniform (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (h : UniformWeakEquation ν J) : SmoothWeakEquation ν J := by
  intro a b hab φ
  exact h a b hab φ.toBCF φ.dt.toBCF φ.dp.toBCF (smooth_test_approximable φ)

theorem of_tensor (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (h : TensorWeakEquation ν J) : SmoothWeakEquation ν J :=
  of_uniform ν J (uniform_weak_equation ν J h)

theorem zero_boundary (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (h : SmoothWeakEquation ν J) (a b : ℝ) (hab : a ≤ b) (φ : Test)
    (ha : ∀ p, φ.value (a,p) = 0) (hb : ∀ p, φ.value (b,p) = 0) :
    (∫ t in Icc a b, expectation ν φ.dt.toBCF t)+(J.window a b).evaluate φ.dp.toBCF = 0 := by
  have hbalance := (h a b hab φ).2
  have hea : expectation ν φ.toBCF a = 0 := by
    change (∫ p, φ.value (a,p) ∂(ν a : Measure ℝ)) = 0
    simp only [ha,integral_zero]
  have heb : expectation ν φ.toBCF b = 0 := by
    change (∫ p, φ.value (b,p) ∂(ν b : Measure ℝ)) = 0
    simp only [hb,integral_zero]
  simpa only [hea,heb,sub_self] using hbalance

theorem compact_test_balance (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (h : SmoothWeakEquation ν J) (a b : ℝ) (hab : a ≤ b) (φ : Test)
    (hs : ∀ z, φ.value z ≠ 0 → z.1 ∈ Ioo a b) :
    (∫ t in Icc a b, expectation ν φ.dt.toBCF t)+(J.window a b).evaluate φ.dp.toBCF = 0 := by
  apply zero_boundary ν J h a b hab φ
  · intro p
    by_contra hn
    exact (lt_irrefl a) (hs (a,p) hn).1
  · intro p
    by_contra hn
    exact (lt_irrefl b) (hs (b,p) hn).2

theorem exists_compact_test_window (ν : ℝ → ProbabilityMeasure ℝ) (J : Force)
    (h : SmoothWeakEquation ν J) (φ : Test) :
    ∃ R : ℝ, 0 < R ∧ ∀ a b : ℝ, a ≤ -R → R ≤ b →
      Integrable (expectation ν φ.dt.toBCF) (volume.restrict (Icc a b)) ∧
      (∫ t in Icc a b, expectation ν φ.dt.toBCF t)+(J.window a b).evaluate φ.dp.toBCF = 0 := by
  obtain ⟨R,hR,hbound⟩ := test_time_bound φ
  refine ⟨R+1,by linarith,?_⟩
  intro a b ha hb
  have hab : a ≤ b := by linarith
  refine ⟨(h a b hab φ).1,compact_test_balance ν J h a b hab φ ?_⟩
  intro z hz
  have hh := abs_le.mp (hbound z hz)
  constructor <;> linarith [hh.1,hh.2]

#print axioms of_uniform
#print axioms of_tensor
#print axioms zero_boundary
#print axioms compact_test_balance
#print axioms exists_compact_test_window
end
end UnifiedTheory.Audit.KFCausalSmoothWeakEquation
