/- Full six-mode dynamics with the regularized homogeneous longitudinal
term. Positivity, the reconstructed spatial constraint, unique global
unitarity and capacity-independent clock bounds are derived. No continuum
limit or physical identification is asserted. -/
import UnifiedTheory.Audit.KFCausalRegularizedClockDatum
import UnifiedTheory.Audit.KFCausalUniformInverseClock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedSpinDynamics
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.Audit.KFCausalFiniteOccupationLadders
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalQuantumArealCandidate
open UnifiedTheory.Audit.KFCausalConcreteClockConstraint
open UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian (fieldQx fieldPhix fieldPhi)
open UnifiedTheory.Audit.KFCausalExponentialClockDynamics
open UnifiedTheory.Audit.KFCausalQuantumEnergyControl
open UnifiedTheory.Audit.KFCausalExponentialEnergyBound
open UnifiedTheory.Audit.KFCausalGravityPairCoercivity
open UnifiedTheory.Audit.KFCausalInverseClockEnergy
open UnifiedTheory.Audit.KFCausalUniformInverseClock
open UnifiedTheory.Audit.KFCausalRegularizedClockDatum
open UnifiedTheory.Audit.KFCausalContinuousConstraintFlow
open UnifiedTheory.Audit.KFCausalGlobalPropagator

def regularizedGrowing (R : ℕ) (r : ℕ → ℝ) (hbar ε mass2 quartic vacuum : ℝ) :
    Matrix (State R) (State R) ℂ :=
  (1/2 : ℝ) • gram (fieldQx R r hbar*halfExp (-clockS R r hbar))+
  (1/2 : ℝ) • gram (fieldPhix R r hbar*halfExp (-clockS R r hbar))+
  potentialHamiltonian (halfExp (-clockS R r hbar))
    (halfExp (regularizedLongitudinal R r hbar ε)) (fieldPhi R r hbar) mass2 quartic vacuum

def regularizedSeed (R : ℕ) (r : ℕ → ℝ) (hbar ε mass2 quartic vacuum t : ℝ) :
    Matrix (State R) (State R) ℂ :=
  exponentialKinetic R r hbar+Real.exp (2*t) • regularizedGrowing R r hbar ε mass2 quartic vacuum

def regularizedHamiltonian (R : ℕ) (r : ℕ → ℝ) (hbar ε mass2 quartic vacuum t : ℝ) :
    Matrix (State R) (State R) ℂ := dephase charge (regularizedSeed R r hbar ε mass2 quartic vacuum t)

def regularizedGrowingPart (R : ℕ) (r : ℕ → ℝ) (hbar ε mass2 quartic vacuum : ℝ) :
    Matrix (State R) (State R) ℂ := dephase charge (regularizedGrowing R r hbar ε mass2 quartic vacuum)

theorem regularizedGrowing_positive (R : ℕ) (r : ℕ → ℝ) (hbar ε mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (regularizedGrowing R r hbar ε mass2 quartic vacuum).PosSemidef :=
  (((gram_positive _).smul (by norm_num : (0 : ℝ)≤1/2)).add
    ((gram_positive _).smul (by norm_num : (0 : ℝ)≤1/2))).add
    (potentialHamiltonian_positive _ _ _ _ _ _ hm hq hv)

theorem regularizedGrowingPart_positive (R : ℕ) (r : ℕ → ℝ) (hbar ε mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (regularizedGrowingPart R r hbar ε mass2 quartic vacuum).PosSemidef :=
  dephase_positive charge _ (regularizedGrowing_positive R r hbar ε mass2 quartic vacuum hm hq hv)

theorem regularizedHamiltonian_split (R : ℕ) (r : ℕ → ℝ) (hbar ε mass2 quartic vacuum t : ℝ) :
    regularizedHamiltonian R r hbar ε mass2 quartic vacuum t=
      hamiltonian (staticPart R r hbar) (regularizedGrowingPart R r hbar ε mass2 quartic vacuum) t := by
  simp only [regularizedHamiltonian,regularizedSeed,dephase_add,dephase_real_smul,
    staticPart,regularizedGrowingPart,hamiltonian]

theorem regularizedHamiltonian_positive (R : ℕ) (r : ℕ → ℝ) (hbar ε mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (regularizedHamiltonian R r hbar ε mass2 quartic vacuum t).PosSemidef := by
  rw [regularizedHamiltonian_split]
  exact hamiltonian_positive _ _ (staticPart_positive R r hbar)
    (regularizedGrowingPart_positive R r hbar ε mass2 quartic vacuum hm hq hv) t

theorem regularizedHamiltonian_continuous (R : ℕ) (r : ℕ → ℝ) (hbar ε mass2 quartic vacuum : ℝ) :
    Continuous (regularizedHamiltonian R r hbar ε mass2 quartic vacuum) := by
  unfold regularizedHamiltonian dephase regularizedSeed
  fun_prop

theorem regularizedHamiltonian_zero (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ) :
    regularizedHamiltonian R r hbar 0 mass2 quartic vacuum t=
      exponentialHamiltonian R r hbar mass2 quartic vacuum t := by
  simp only [regularizedHamiltonian,regularizedSeed,regularizedGrowing,regularizedLongitudinal_zero,
    exponentialHamiltonian,exponentialSeed,exponentialGrowing]

/-- The new positive potential dominates the common potential-free model.
This transfers the earlier clock/parity bounds without comparing two
noncommuting exponential potentials. -/
theorem regularized_minus_free_positive (R : ℕ) (r : ℕ → ℝ) (hbar ε mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (regularizedHamiltonian R r hbar ε mass2 quartic vacuum t-
      exponentialHamiltonian R r hbar 0 0 0 t).PosSemidef := by
  have hp := (dephase_positive charge _
    (potentialHamiltonian_positive (halfExp (-clockS R r hbar))
      (halfExp (regularizedLongitudinal R r hbar ε)) (fieldPhi R r hbar)
      mass2 quartic vacuum hm hq hv)).smul (Real.exp_pos (2*t)).le
  convert hp using 1
  simp only [regularizedHamiltonian,regularizedSeed,regularizedGrowing,
    exponentialHamiltonian,exponentialSeed,exponentialGrowing,potentialHamiltonian,
    zero_div,zero_smul,add_zero,dephase_add,dephase_real_smul]
  module

theorem regularized_clock_lower (R : ℕ) (r : ℕ → ℝ) (hbar ε mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (regularizedHamiltonian R r hbar ε mass2 quartic vacuum t-
      (1/2 : ℝ) • exponentialClock R r hbar).PosSemidef := by
  convert (regularized_minus_free_positive R r hbar ε mass2 quartic vacuum t hm hq hv).add
    (hamiltonian_minus_clock_positive R r hbar 0 0 0 t le_rfl le_rfl le_rfl) using 1
  abel

theorem regularized_inverse_clock_lower (R : ℕ) (hbar ε mass2 quartic vacuum t : ℝ)
    (hh : 0 ≤ hbar) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (regularizedHamiltonian R (fun _ => 1) hbar ε mass2 quartic vacuum t-
      (min 1 (Real.exp (2*t))*min 1 hbar/2 : ℝ) • inverseClock R hbar).PosSemidef := by
  convert (regularized_minus_free_positive R (fun _ => 1) hbar ε mass2 quartic vacuum t hm hq hv).add
    (all_time_inverse_clock_lower R hbar 0 0 0 t hh le_rfl le_rfl le_rfl) using 1
  abel

theorem regularized_energy_growth (R : ℕ) (r : ℕ → ℝ) (hbar ε mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (U : ℝ → Matrix (State R) (State R) ℂ)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*((1/hbar : ℝ) : ℂ)) •
      (regularizedHamiltonian R r hbar ε mass2 quartic vacuum t*U t)) t)
    (v : State R → ℂ) (s t : ℝ) (hst : s ≤ t) :
    expectation (U s*ᵥv) (regularizedHamiltonian R r hbar ε mass2 quartic vacuum s) ≤
      expectation (U t*ᵥv) (regularizedHamiltonian R r hbar ε mass2 quartic vacuum t) ∧
    expectation (U t*ᵥv) (regularizedHamiltonian R r hbar ε mass2 quartic vacuum t) ≤
      Real.exp (2*(t-s))*expectation (U s*ᵥv)
        (regularizedHamiltonian R r hbar ε mass2 quartic vacuum s) := by
  have hd (z : ℝ) := hU z
  simp only [regularizedHamiltonian_split] at hd
  have he := energy_growth_bound (staticPart R r hbar)
    (regularizedGrowingPart R r hbar ε mass2 quartic vacuum)
    (staticPart_positive R r hbar)
    (regularizedGrowingPart_positive R r hbar ε mass2 quartic vacuum hm hq hv) U (1/hbar) hd v s t hst
  simpa only [energy,← regularizedHamiltonian_split,expectation_conjugate] using he

local instance stateNonempty (R : ℕ) : Nonempty (State R) :=
  ⟨⟨fun _ => 0,by simp [total]⟩⟩

/-- Global existence, uniqueness, unitarity, constraint preservation and
energy control for the specified full regularized finite Hamiltonian. -/
theorem existsUnique_regularized_dynamics (R : ℕ) (r : ℕ → ℝ)
    (hbar ε mass2 quartic vacuum : ℝ) (_hh : 0 < hbar) (hε : 0 ≤ ε)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) :
    ∃! U : ℝ → Matrix (State R) (State R) ℂ,
      U 0=1 ∧
      (∀ t, HasDerivAt U ((-Complex.I*((1/hbar : ℝ) : ℂ)) •
        (regularizedHamiltonian R r hbar ε mass2 quartic vacuum t*U t)) t) ∧
      (∀ t, (U t)ᴴ*U t=1 ∧ U t*(U t)ᴴ=1) ∧
      (∀ t v, (sector charge 0).mulVec v=v →
        (regularizedConstraint R r hbar ε).mulVec ((U t).mulVec v)=0) ∧
      (∀ v s t, s ≤ t →
        expectation (U s*ᵥv) (regularizedHamiltonian R r hbar ε mass2 quartic vacuum s) ≤
          expectation (U t*ᵥv) (regularizedHamiltonian R r hbar ε mass2 quartic vacuum t) ∧
        expectation (U t*ᵥv) (regularizedHamiltonian R r hbar ε mass2 quartic vacuum t) ≤
          Real.exp (2*(t-s))*expectation (U s*ᵥv)
            (regularizedHamiltonian R r hbar ε mass2 quartic vacuum s)) := by
  let H := regularizedHamiltonian R r hbar ε mass2 quartic vacuum
  let A := fun t => (-Complex.I*((1/hbar : ℝ) : ℂ)) • H t
  have hH (t : ℝ) : (H t).IsHermitian :=
    (regularizedHamiltonian_positive R r hbar ε mass2 quartic vacuum t hm hq hvac).isHermitian
  have hA : Continuous A := (regularizedHamiltonian_continuous R r hbar ε mass2 quartic vacuum).const_smul _
  have hs (t : ℝ) : (A t)ᴴ= -A t := by simp [A,Matrix.conjTranspose_smul,(hH t).eq]
  obtain ⟨U,⟨hinit,hU⟩,hunique⟩ := existsUnique_global_propagator A hA hs
  have hd (t : ℝ) : HasDerivAt U ((-Complex.I*((1/hbar : ℝ) : ℂ)) • (H t*U t)) t := by
    simpa only [A,smul_mul_assoc] using hU t
  refine ⟨U,⟨hinit,hd,?_,?_,?_⟩,?_⟩
  · intro t
    exact propagator_unitary H hH (1/hbar) U hd 0 t hinit
  · intro t v hv
    exact constraint_continuous charge _ (regularizedConstraint_sector R r hbar ε hε)
      (regularizedSeed R r hbar ε mass2 quartic vacuum) hH (1/hbar) U hd 0 t hinit v hv
  · exact regularized_energy_growth R r hbar ε mass2 quartic vacuum hm hq hvac U hd
  · intro V hV
    apply hunique V
    refine ⟨hV.1,?_⟩
    intro t
    simpa only [A,H,smul_mul_assoc] using hV.2.1 t

#print axioms regularizedGrowing_positive
#print axioms regularizedGrowingPart_positive
#print axioms regularizedHamiltonian_split
#print axioms regularizedHamiltonian_positive
#print axioms regularizedHamiltonian_continuous
#print axioms regularizedHamiltonian_zero
#print axioms regularized_minus_free_positive
#print axioms regularized_clock_lower
#print axioms regularized_inverse_clock_lower
#print axioms regularized_energy_growth
#print axioms existsUnique_regularized_dynamics

end
end UnifiedTheory.Audit.KFCausalRegularizedSpinDynamics
