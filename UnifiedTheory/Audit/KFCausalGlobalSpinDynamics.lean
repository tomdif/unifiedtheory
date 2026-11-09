/- The specified finite spin model has a unique global Schrodinger
propagator, constructed without an ODE-existence premise. Its exact
time-dependent evolution is unitary and preserves the reconstructed
constraint on the zero-charge sector. This is a finite-model theorem. -/
import UnifiedTheory.Audit.KFCausalGlobalPropagator
import UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGlobalSpinDynamics
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.Audit.KFCausalFiniteOccupationLadders
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalConcreteClockConstraint
open UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian
open UnifiedTheory.Audit.KFCausalGlobalPropagator

local instance stateNonempty (R : ℕ) : Nonempty (State R) :=
  ⟨⟨fun _ => 0,by simp [total]⟩⟩

theorem hamiltonian_continuous (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ) :
    Continuous (hamiltonian R r hbar mass2 quartic vacuum) := by
  unfold hamiltonian dephase seedHamiltonian
  fun_prop

def generator (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ) :
    Matrix (State R) (State R) ℂ :=
  (-Complex.I*((1/hbar : ℝ) : ℂ)) • hamiltonian R r hbar mass2 quartic vacuum t

theorem generator_continuous (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ) :
    Continuous (generator R r hbar mass2 quartic vacuum) :=
  (hamiltonian_continuous R r hbar mass2 quartic vacuum).const_smul _

theorem generator_skew (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) :
    (generator R r hbar mass2 quartic vacuum t)ᴴ=
      -generator R r hbar mass2 quartic vacuum t := by
  have hH := (hamiltonian_positive R r hbar mass2 quartic vacuum t hm hq hvac).isHermitian
  simp [generator,Matrix.conjTranspose_smul,hH.eq]

def dynamics (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) :
    ℝ → Matrix (State R) (State R) ℂ :=
  globalFlow (generator R r hbar mass2 quartic vacuum)
    (generator_continuous R r hbar mass2 quartic vacuum)
    (fun t => generator_skew R r hbar mass2 quartic vacuum t hm hq hvac)

theorem dynamics_initial (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) :
    dynamics R r hbar mass2 quartic vacuum hm hq hvac 0=1 :=
  globalFlow_initial _ _ _

theorem dynamics_derivative (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) (t : ℝ) :
    HasDerivAt (dynamics R r hbar mass2 quartic vacuum hm hq hvac)
      ((-Complex.I*((1/hbar : ℝ) : ℂ)) •
        (hamiltonian R r hbar mass2 quartic vacuum t*
          dynamics R r hbar mass2 quartic vacuum hm hq hvac t)) t := by
  simpa only [generator,smul_mul_assoc] using
    globalFlow_derivative (generator R r hbar mass2 quartic vacuum)
      (generator_continuous R r hbar mass2 quartic vacuum)
      (fun s => generator_skew R r hbar mass2 quartic vacuum s hm hq hvac) t

theorem dynamics_unitary (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) (t : ℝ) :
    (dynamics R r hbar mass2 quartic vacuum hm hq hvac t)ᴴ*
        dynamics R r hbar mass2 quartic vacuum hm hq hvac t=1 ∧
    dynamics R r hbar mass2 quartic vacuum hm hq hvac t*
        (dynamics R r hbar mass2 quartic vacuum hm hq hvac t)ᴴ=1 :=
  globalFlow_unitary _ _ _ t

theorem dynamics_constraint (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) (t : ℝ)
    (v : State R → ℂ) (hv : (sector charge 0).mulVec v=v) :
    (constraint R r hbar).mulVec
      ((dynamics R r hbar mass2 quartic vacuum hm hq hvac t).mulVec v)=0 :=
  specified_dynamics_constraint R r hbar mass2 quartic vacuum hm hq hvac
    (dynamics R r hbar mass2 quartic vacuum hm hq hvac)
    (dynamics_derivative R r hbar mass2 quartic vacuum hm hq hvac)
    0 t (dynamics_initial R r hbar mass2 quartic vacuum hm hq hvac) v hv

/-- The same construction supports an arbitrary initial time. -/
def propagator (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) (s t : ℝ) :
    Matrix (State R) (State R) ℂ :=
  evolution (generator R r hbar mass2 quartic vacuum)
    (generator_continuous R r hbar mass2 quartic vacuum)
    (fun z => generator_skew R r hbar mass2 quartic vacuum z hm hq hvac) s t

theorem propagator_derivative (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) (s t : ℝ) :
    HasDerivAt (propagator R r hbar mass2 quartic vacuum hm hq hvac s)
      ((-Complex.I*((1/hbar : ℝ) : ℂ)) •
        (hamiltonian R r hbar mass2 quartic vacuum t*
          propagator R r hbar mass2 quartic vacuum hm hq hvac s t)) t := by
  simpa only [generator,smul_mul_assoc] using
    evolution_derivative (generator R r hbar mass2 quartic vacuum)
      (generator_continuous R r hbar mass2 quartic vacuum)
      (fun z => generator_skew R r hbar mass2 quartic vacuum z hm hq hvac) s t

theorem propagator_constraint (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) (s t : ℝ)
    (v : State R → ℂ) (hv : (sector charge 0).mulVec v=v) :
    (constraint R r hbar).mulVec
      ((propagator R r hbar mass2 quartic vacuum hm hq hvac s t).mulVec v)=0 :=
  specified_dynamics_constraint R r hbar mass2 quartic vacuum hm hq hvac
    (propagator R r hbar mass2 quartic vacuum hm hq hvac s)
    (propagator_derivative R r hbar mass2 quartic vacuum hm hq hvac s)
    s t (evolution_initial _ _ _ s) v hv

/-- Existence and uniqueness are proved for the actual time-dependent
Hamiltonian; the physical sector is preserved at every real time.
Positive hbar is an explicit physical parameter restriction. -/
theorem existsUnique_physical_dynamics (R : ℕ) (r : ℕ → ℝ)
    (hbar mass2 quartic vacuum : ℝ) (_hh : 0 < hbar)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) :
    ∃! U : ℝ → Matrix (State R) (State R) ℂ,
      U 0=1 ∧
      (∀ t, HasDerivAt U ((-Complex.I*((1/hbar : ℝ) : ℂ)) •
        (hamiltonian R r hbar mass2 quartic vacuum t*U t)) t) ∧
      (∀ t, (U t)ᴴ*U t=1 ∧ U t*(U t)ᴴ=1) ∧
      (∀ t v, (sector charge 0).mulVec v=v →
        (constraint R r hbar).mulVec ((U t).mulVec v)=0) := by
  refine ⟨dynamics R r hbar mass2 quartic vacuum hm hq hvac,
    ⟨dynamics_initial R r hbar mass2 quartic vacuum hm hq hvac,
      dynamics_derivative R r hbar mass2 quartic vacuum hm hq hvac,
      dynamics_unitary R r hbar mass2 quartic vacuum hm hq hvac,
      dynamics_constraint R r hbar mass2 quartic vacuum hm hq hvac⟩,?_⟩
  intro V hV
  apply global_solution_unique (generator R r hbar mass2 quartic vacuum)
    V (dynamics R r hbar mass2 quartic vacuum hm hq hvac)
    (fun t => generator_skew R r hbar mass2 quartic vacuum t hm hq hvac)
  · intro t; simpa only [generator,smul_mul_assoc] using hV.2.1 t
  · intro t
    simpa only [generator,smul_mul_assoc] using
      dynamics_derivative R r hbar mass2 quartic vacuum hm hq hvac t
  · rw [hV.1,dynamics_initial]

#print axioms hamiltonian_continuous
#print axioms generator_skew
#print axioms dynamics_derivative
#print axioms dynamics_unitary
#print axioms dynamics_constraint
#print axioms propagator_derivative
#print axioms propagator_constraint
#print axioms existsUnique_physical_dynamics

end
end UnifiedTheory.Audit.KFCausalGlobalSpinDynamics
