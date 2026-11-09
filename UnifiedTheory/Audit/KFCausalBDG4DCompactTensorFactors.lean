import UnifiedTheory.Audit.KFCausalBDG4DCompactProfile

/- Actual smooth compact one-variable factors for quadratic BDG profiles and
their Euler derivatives. The record contains regularity/support data, not a
limit or a prescribed coefficient. All factors used below are constructed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalBDG4DCompactTensorFactors
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

structure Factor where
  value : ℝ → ℝ
  smooth : ContDiff ℝ ∞ value
  support : tsupport value ⊆ closedBall (0 : ℝ) 2

namespace Factor
def first (f : Factor) : ℝ → ℝ := deriv f.value
def second (f : Factor) : ℝ → ℝ := deriv f.first

theorem first_smooth (f : Factor) : ContDiff ℝ ∞ f.first :=
  (contDiff_infty_iff_deriv.mp f.smooth).2

theorem second_smooth (f : Factor) : ContDiff ℝ ∞ f.second :=
  (contDiff_infty_iff_deriv.mp f.first_smooth).2

theorem value_derivative (f : Factor) (x : ℝ) : HasDerivAt f.value (f.first x) x :=
  (f.smooth.differentiable (by simp) x).hasDerivAt

theorem first_derivative (f : Factor) (x : ℝ) : HasDerivAt f.first (f.second x) x :=
  (f.first_smooth.differentiable (by simp) x).hasDerivAt

theorem compact (f : Factor) : HasCompactSupport f.value :=
  (isCompact_closedBall (0 : ℝ) 2).of_isClosed_subset (isClosed_tsupport _) f.support

private theorem first_support (f : Factor) : tsupport f.first ⊆ closedBall (0 : ℝ) 2 :=
  (closure_minimal support_deriv_subset (isClosed_tsupport f.value)).trans f.support

private theorem second_support (f : Factor) : tsupport f.second ⊆ closedBall (0 : ℝ) 2 :=
  (closure_minimal support_deriv_subset (isClosed_tsupport f.first)).trans f.first_support

theorem outside_support (f : Factor) (x : ℝ) (hx : 3 ≤ |x|) :
    f.value x=0 ∧ f.first x=0 ∧ f.second x=0 := by
  have hn : x ∉ closedBall (0 : ℝ) 2 := by
    simp only [mem_closedBall,Real.dist_eq,sub_zero]
    linarith
  exact ⟨image_eq_zero_of_notMem_tsupport (fun h => hn (f.support h)),
    image_eq_zero_of_notMem_tsupport (fun h => hn (f.first_support h)),
    image_eq_zero_of_notMem_tsupport (fun h => hn (f.second_support h))⟩

theorem exists_bound (f : Factor) : ∃ C : ℝ, 0 ≤ C ∧
    (∀ x, |f.value x| ≤ C) ∧ (∀ x, |f.first x| ≤ C) ∧ (∀ x, |f.second x| ≤ C) := by
  obtain ⟨C0,h0⟩ := f.compact.exists_bound_of_continuous f.smooth.continuous
  obtain ⟨C1,h1⟩ := f.compact.deriv.exists_bound_of_continuous f.first_smooth.continuous
  obtain ⟨C2,h2⟩ := f.compact.deriv.deriv.exists_bound_of_continuous f.second_smooth.continuous
  refine ⟨max 0 (max C0 (max C1 C2)),le_max_left _ _,?_,?_,?_⟩
  · intro x
    exact (show |f.value x| ≤ C0 by simpa only [Real.norm_eq_abs] using h0 x).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · intro x
    exact (show |f.first x| ≤ C1 by simpa only [Real.norm_eq_abs,first] using h1 x).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  · intro x
    exact (show |f.second x| ≤ C2 by simpa only [Real.norm_eq_abs,first,second] using h2 x).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

def bound (f : Factor) : ℝ := Classical.choose f.exists_bound

theorem uniform_bound (f : Factor) : 0 ≤ f.bound ∧
    (∀ x, |f.value x| ≤ f.bound) ∧ (∀ x, |f.first x| ≤ f.bound) ∧
      (∀ x, |f.second x| ≤ f.bound) := Classical.choose_spec f.exists_bound

end Factor

def polynomial (n : ℕ) : Factor where
  value x := x^n*KFCausalBDG4DCompactProfile.profile x
  smooth := (contDiff_id.pow n).mul KFCausalBDG4DCompactProfile.smooth
  support := by
    calc tsupport (fun x : ℝ => x^n*KFCausalBDG4DCompactProfile.profile x)
        ⊆ tsupport KFCausalBDG4DCompactProfile.profile := tsupport_mul_subset_right
      _ ⊆ tsupport (KFCausalBDG4DCompactProfile.bump : ℝ → ℝ) := tsupport_mul_subset_left
      _ = closedBall (0 : ℝ) 2 := KFCausalBDG4DCompactProfile.bump.tsupport_eq

def euler (f : Factor) : Factor where
  value x := x*f.first x
  smooth := contDiff_id.mul f.first_smooth
  support := (show tsupport (fun x : ℝ => x*f.first x) ⊆ tsupport f.first from
    tsupport_mul_subset_right).trans f.first_support

private theorem polynomial_local (n : ℕ) :
    (polynomial n).value =ᶠ[𝓝 (0 : ℝ)] (fun x => x^n*(1+x^2)) := by
  filter_upwards [KFCausalBDG4DCompactProfile.local_profile] with x hx
  simp only [polynomial,hx]

theorem polynomial_zero_jet :
    (polynomial 0).value 0=1 ∧ (polynomial 0).first 0=0 ∧ (polynomial 0).second 0=2 := by
  have he : (polynomial 0).value=KFCausalBDG4DCompactProfile.profile := by funext x; simp [polynomial]
  simpa only [Factor.first,Factor.second,he,KFCausalBDG4DCompactProfile.first,
    KFCausalBDG4DCompactProfile.second] using KFCausalBDG4DCompactProfile.origin_jet

theorem polynomial_one_jet :
    (polynomial 1).value 0=0 ∧ (polynomial 1).first 0=1 ∧ (polynomial 1).second 0=0 := by
  have he : deriv (fun x : ℝ => x^1*(1+x^2)) = fun x => 1+3*x^2 := by
    funext x
    apply HasDerivAt.deriv
    convert (hasDerivAt_id x).mul (((hasDerivAt_id x).pow 2).const_add 1) using 1
    · funext y; simp only [Pi.mul_apply,Pi.pow_apply,id_eq,pow_one]
    · simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one]; ring
  refine ⟨?_,?_,?_⟩
  · simp [polynomial]
  · change deriv (polynomial 1).value 0=1
    rw [(polynomial_local 1).deriv_eq,he]
    norm_num
  · change deriv (deriv (polynomial 1).value) 0=0
    rw [(polynomial_local 1).deriv.deriv_eq,he]
    convert ((((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 3).const_add 1).deriv using 1
    norm_num

theorem polynomial_two_jet :
    (polynomial 2).value 0=0 ∧ (polynomial 2).first 0=0 ∧ (polynomial 2).second 0=2 := by
  have he : deriv (fun x : ℝ => x^2*(1+x^2)) = fun x => 2*x+4*x^3 := by
    funext x
    apply HasDerivAt.deriv
    convert ((hasDerivAt_id x).pow 2).mul (((hasDerivAt_id x).pow 2).const_add 1) using 1
    simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one]; ring
  refine ⟨?_,?_,?_⟩
  · simp [polynomial]
  · change deriv (polynomial 2).value 0=0
    rw [(polynomial_local 2).deriv_eq,he]
    norm_num
  · change deriv (deriv (polynomial 2).value) 0=2
    rw [(polynomial_local 2).deriv.deriv_eq,he]
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul 2).add
      (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul 4)).deriv

theorem euler_origin_jet (f : Factor) :
    (euler f).value 0=0 ∧ (euler f).first 0=f.first 0 ∧
      (euler f).second 0=2*f.second 0 := by
  have he : (euler f).first = fun x => f.first x+x*f.second x := by
    funext x
    simpa only [Factor.first,euler,Pi.mul_apply,id_eq,one_mul] using
      ((hasDerivAt_id x).mul (f.first_derivative x)).deriv
  refine ⟨by simp [euler],?_,?_⟩
  · rw [he]; simp
  · change deriv (euler f).first 0=2*f.second 0
    rw [he]
    have hd := f.second_smooth.differentiable (by simp) (0 : ℝ)
    convert ((f.first_derivative 0).add ((hasDerivAt_id (0 : ℝ)).mul hd.hasDerivAt)).deriv using 1
    simp
    ring

#print axioms Factor.first_smooth
#print axioms Factor.second_smooth
#print axioms Factor.value_derivative
#print axioms Factor.first_derivative
#print axioms Factor.compact
#print axioms Factor.outside_support
#print axioms Factor.exists_bound
#print axioms Factor.uniform_bound
#print axioms polynomial_zero_jet
#print axioms polynomial_one_jet
#print axioms polynomial_two_jet
#print axioms euler_origin_jet
end
end UnifiedTheory.Audit.KFCausalBDG4DCompactTensorFactors
