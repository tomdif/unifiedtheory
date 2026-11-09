/- Actual all-time unitary dynamics for each bounded Yosida Hamiltonian
of the regularized homogeneous model. The unbounded approximation limit
of these evolutions is not asserted. -/
import UnifiedTheory.Audit.KFCausalRegularizedYosida
import UnifiedTheory.Audit.KFCausalHilbertEvolutionStability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedYosidaDynamics
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedYosida
open UnifiedTheory.Audit.KFCausalHilbertEvolution
open UnifiedTheory.Audit.KFCausalHilbertStateEvolution
open UnifiedTheory.Audit.KFCausalHilbertEvolutionStability

def generator (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  (-Complex.I*((1/hbar:ℝ):ℂ)) • homogeneousYosida ε hε hbar coupling a t

theorem generator_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a) :
    Continuous (generator ε hε hbar coupling a) :=
  (homogeneousYosida_continuous ε hε hbar coupling a ha).const_smul _

theorem generator_skew (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) :
    star (generator ε hε hbar coupling a t) = -generator ε hε hbar coupling a t := by
  have hh := homogeneousYosida_selfAdjoint ε hε hbar coupling a t ha
  unfold generator
  rw [star_smul,hh]
  simp

def dynamics (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a) (s t : ℝ) :
    Hilbert →L[ℂ] Hilbert :=
  evolution (generator ε hε hbar coupling a) (generator_continuous ε hε hbar coupling a ha)
    (fun t => generator_skew ε hε hbar coupling a t ha) s t

theorem dynamics_initial (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a) (s : ℝ) :
    dynamics ε hε hbar coupling a ha s s = 1 :=
  evolution_initial _ _ _ s

theorem dynamics_derivative (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a) (s t : ℝ) :
    HasDerivAt (dynamics ε hε hbar coupling a ha s)
      (generator ε hε hbar coupling a t * dynamics ε hε hbar coupling a ha s t) t :=
  evolution_derivative _ _ _ s t

theorem dynamics_initial_time_derivative (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ)
    (ha : 0 < a) (s t : ℝ) :
    HasDerivAt (fun r => dynamics ε hε hbar coupling a ha r t)
      (-dynamics ε hε hbar coupling a ha s t * generator ε hε hbar coupling a s) s :=
  evolution_initial_time_derivative _ _ _ s t

theorem dynamics_opNorm_le_one (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ)
    (ha : 0 < a) (s t : ℝ) : ‖dynamics ε hε hbar coupling a ha s t‖ ≤ 1 :=
  evolution_opNorm_le_one _ _ _ s t

theorem dynamics_compose (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a) (r s t : ℝ) :
    dynamics ε hε hbar coupling a ha s t * dynamics ε hε hbar coupling a ha r s =
      dynamics ε hε hbar coupling a ha r t := evolution_compose _ _ _ r s t

theorem dynamics_reverse (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a) (s t : ℝ) :
    star (dynamics ε hε hbar coupling a ha s t) = dynamics ε hε hbar coupling a ha t s :=
  evolution_reverse _ _ _ s t

theorem dynamics_unitary (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a) (s t : ℝ) :
    star (dynamics ε hε hbar coupling a ha s t) * dynamics ε hε hbar coupling a ha s t = 1 ∧
      dynamics ε hε hbar coupling a ha s t * star (dynamics ε hε hbar coupling a ha s t) = 1 :=
  evolution_unitary _ _ _ s t

theorem dynamics_joint_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a) :
    Continuous (fun p : ℝ × ℝ => dynamics ε hε hbar coupling a ha p.1 p.2) :=
  evolution_joint_continuous _ _ _

theorem dynamics_norm (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) : ‖dynamics ε hε hbar coupling a ha s t f‖ = ‖f‖ :=
  evolution_norm _ _ _ s t f

theorem dynamics_surjective (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a) (s t : ℝ) :
    Function.Surjective (dynamics ε hε hbar coupling a ha s t) :=
  evolution_surjective _ _ _ s t

theorem dynamics_state_derivative (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) :
    HasDerivAt (fun z => dynamics ε hε hbar coupling a ha s z f)
      (generator ε hε hbar coupling a t (dynamics ε hε hbar coupling a ha s t f)) t :=
  evolution_state_derivative _ _ _ s t f

theorem dynamics_state_unique (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s : ℝ) (f : Hilbert) (v : ℝ → Hilbert) (hinit : v s=f)
    (hv : ∀ t, HasDerivAt v (generator ε hε hbar coupling a t (v t)) t) :
    v = fun t => dynamics ε hε hbar coupling a ha s t f :=
  evolution_state_unique _ _ _ s f v hinit hv

theorem existsUnique_dynamics_state (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s : ℝ) (f : Hilbert) :
    ∃! v : ℝ → Hilbert, v s=f ∧ ∀ t, HasDerivAt v (generator ε hε hbar coupling a t (v t)) t :=
  existsUnique_state_solution _ (generator_continuous ε hε hbar coupling a ha)
    (fun t => generator_skew ε hε hbar coupling a t ha) s f

theorem generator_schrodinger (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ)
    (hhbar : hbar ≠ 0) (f : Hilbert) :
    (Complex.I*(hbar:ℂ)) • generator ε hε hbar coupling a t f =
      homogeneousYosida ε hε hbar coupling a t f := by
  have hc : (Complex.I*(hbar:ℂ))*(-Complex.I*((1/hbar:ℝ):ℂ)) = 1 := by
    calc
      _ = -(Complex.I*Complex.I)*((hbar:ℂ)*((1/hbar:ℝ):ℂ)) := by ring
      _ = 1 := by rw [Complex.I_mul_I,← Complex.ofReal_mul]; simp [hhbar]
  rw [generator,ContinuousLinearMap.smul_apply,smul_smul,hc,one_smul]

theorem dynamics_schrodinger (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (hhbar : hbar ≠ 0) (s t : ℝ) (f : Hilbert) :
    ∃ v' : Hilbert, HasDerivAt (fun z => dynamics ε hε hbar coupling a ha s z f) v' t ∧
      (Complex.I*(hbar:ℂ)) • v' =
        homogeneousYosida ε hε hbar coupling a t (dynamics ε hε hbar coupling a ha s t f) :=
  ⟨_,dynamics_state_derivative ε hε hbar coupling a ha s t f,
    generator_schrodinger ε hε hbar coupling a t hhbar _⟩

/-- Conditional comparison: the Hamiltonian residual bound remains an
explicit input. No decay of that bound with cutoff is asserted. -/
theorem dynamics_difference_bound (ε : ℝ) (hε : 0 < ε) (hbar coupling a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (s t C : ℝ) (f : Hilbert)
    (hsource : ∀ z ∈ Set.uIcc s t,
      ‖(homogeneousYosida ε hε hbar coupling b z-homogeneousYosida ε hε hbar coupling a z)
        (dynamics ε hε hbar coupling b hb s z f)‖ ≤ C) :
    ‖dynamics ε hε hbar coupling a ha s t f-dynamics ε hε hbar coupling b hb s t f‖ ≤
      (|1 / hbar| * C)*|t-s| := by
  apply evolution_difference_bound _ _ _ _ _ _ s t (|1 / hbar| * C) f
  intro z hz
  have he : generator ε hε hbar coupling b z-generator ε hε hbar coupling a z =
      (-Complex.I*((1/hbar:ℝ):ℂ)) •
        (homogeneousYosida ε hε hbar coupling b z-homogeneousYosida ε hε hbar coupling a z) := by
    rw [generator,generator,smul_sub]
  rw [he,ContinuousLinearMap.smul_apply,norm_smul]
  simp only [norm_mul,norm_neg,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul]
  exact mul_le_mul_of_nonneg_left (hsource z hz) (abs_nonneg _)

#print axioms generator_skew
#print axioms dynamics_initial
#print axioms dynamics_derivative
#print axioms dynamics_initial_time_derivative
#print axioms dynamics_opNorm_le_one
#print axioms dynamics_compose
#print axioms dynamics_reverse
#print axioms dynamics_unitary
#print axioms dynamics_joint_continuous
#print axioms dynamics_norm
#print axioms dynamics_surjective
#print axioms dynamics_state_derivative
#print axioms dynamics_state_unique
#print axioms existsUnique_dynamics_state
#print axioms dynamics_schrodinger
#print axioms dynamics_difference_bound

end
end UnifiedTheory.Audit.KFCausalRegularizedYosidaDynamics
