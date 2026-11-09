/- A concrete smooth two-sided compact profile with a nonzero quadratic jet.
All support, derivative, and uniform-bound data are constructed here. -/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalBDG4DCompactProfile
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

def bump : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩
def profile (x : ℝ) : ℝ := bump x*(1+x^2)
def first : ℝ → ℝ := deriv profile
def second : ℝ → ℝ := deriv first

theorem smooth : ContDiff ℝ ∞ profile := bump.contDiff.mul (contDiff_const.add (contDiff_id.pow 2))

theorem first_smooth : ContDiff ℝ ∞ first := (contDiff_infty_iff_deriv.mp smooth).2

theorem second_continuous : Continuous second := (contDiff_infty_iff_deriv.mp first_smooth).2.continuous

theorem profile_derivative (x : ℝ) : HasDerivAt profile (first x) x :=
  (smooth.differentiable (by simp) x).hasDerivAt

theorem first_derivative (x : ℝ) : HasDerivAt first (second x) x :=
  (first_smooth.differentiable (by simp) x).hasDerivAt

private theorem compact : HasCompactSupport profile := bump.hasCompactSupport.mul_right

private theorem profile_support : tsupport profile ⊆ closedBall (0:ℝ) 2 := by
  calc tsupport profile ⊆ tsupport (bump : ℝ → ℝ) := tsupport_mul_subset_left
       _ = closedBall (0:ℝ) 2 := bump.tsupport_eq

private theorem first_support : tsupport first ⊆ closedBall (0:ℝ) 2 :=
  (closure_minimal support_deriv_subset (isClosed_tsupport profile)).trans profile_support

private theorem second_support : tsupport second ⊆ closedBall (0:ℝ) 2 :=
  (closure_minimal support_deriv_subset (isClosed_tsupport first)).trans first_support

theorem outside_support (x : ℝ) (hx : 3 ≤ |x|) :
    profile x=0 ∧ first x=0 ∧ second x=0 := by
  have hn : x ∉ closedBall (0:ℝ) 2 := by
    simp only [mem_closedBall,Real.dist_eq,sub_zero]
    linarith
  exact ⟨image_eq_zero_of_notMem_tsupport (fun h => hn (profile_support h)),
    image_eq_zero_of_notMem_tsupport (fun h => hn (first_support h)),
    image_eq_zero_of_notMem_tsupport (fun h => hn (second_support h))⟩

theorem exists_uniform_bound : ∃ B : ℝ, 0 ≤ B ∧
    (∀ x, |profile x| ≤ B) ∧ (∀ x, |first x| ≤ B) ∧ (∀ x, |second x| ≤ B) := by
  obtain ⟨B0,h0⟩ := compact.exists_bound_of_continuous smooth.continuous
  obtain ⟨B1,h1⟩ := compact.deriv.exists_bound_of_continuous first_smooth.continuous
  obtain ⟨B2,h2⟩ := compact.deriv.deriv.exists_bound_of_continuous second_continuous
  refine ⟨max 0 (max B0 (max B1 B2)),le_max_left _ _,?_,?_,?_⟩
  · intro x
    exact (show |profile x| ≤ B0 by simpa only [Real.norm_eq_abs] using h0 x).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · intro x
    exact (show |first x| ≤ B1 by simpa only [Real.norm_eq_abs,first] using h1 x).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  · intro x
    exact (show |second x| ≤ B2 by simpa only [Real.norm_eq_abs,first,second] using h2 x).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

def bound : ℝ := Classical.choose exists_uniform_bound

theorem uniform_bound : 0 ≤ bound ∧
    (∀ x, |profile x| ≤ bound) ∧ (∀ x, |first x| ≤ bound) ∧ (∀ x, |second x| ≤ bound) :=
  Classical.choose_spec exists_uniform_bound

theorem local_profile : profile =ᶠ[𝓝 (0:ℝ)] (fun x => 1+x^2) := by
  filter_upwards [bump.eventuallyEq_one] with x hx
  simp only [profile,hx,Pi.one_apply,one_mul]

theorem origin_jet : profile 0=1 ∧ first 0=0 ∧ second 0=2 := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => 1+t^2) (2*x) x := by
    convert ((hasDerivAt_id x).pow 2).const_add 1 using 1
    norm_num
  have hd' : deriv (fun t : ℝ => 1+t^2) = fun x => 2*x := funext (fun x => (hd x).deriv)
  refine ⟨?_,?_,?_⟩
  · simpa using local_profile.eq_of_nhds
  · change deriv profile 0=0
    rw [local_profile.deriv_eq,hd']
    ring
  · change deriv (deriv profile) 0=2
    rw [local_profile.deriv.deriv_eq,hd']
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul 2).deriv

#print axioms smooth
#print axioms first_smooth
#print axioms second_continuous
#print axioms profile_derivative
#print axioms first_derivative
#print axioms outside_support
#print axioms exists_uniform_bound
#print axioms uniform_bound
#print axioms local_profile
#print axioms origin_jet
end
end UnifiedTheory.Audit.KFCausalBDG4DCompactProfile
