/- Full finite polynomial Hamiltonian for the specified Fourier reduction.
This fixes the executable model's ordering and derives positivity and
continuous constraint preservation. Global propagator existence, the
microscopic selection law and a continuum limit remain separate. -/
import UnifiedTheory.Audit.KFCausalConcreteClockConstraint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian
noncomputable section
open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalGradedSpinSource
open UnifiedTheory.Audit.KFCausalQuantumArealCandidate
open UnifiedTheory.Audit.KFCausalConcreteClockConstraint
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity

variable {n : Type*} [Fintype n]
local notation "M" => Matrix n n ℂ

theorem current_scale (z : ℂ) (P D : M) : current (z • P) (z • D)=z^2 • current P D := by
  simp only [current,smul_mul_assoc,mul_smul_comm,smul_smul,← smul_add]
  congr 1
  ring

def fieldP (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  (Real.sqrt (hbar/2) : ℂ) • momentumPair (ladder r 1) (ladder r 2)
def fieldQx (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  (Real.sqrt (hbar/2) : ℂ) • gradientPair (ladder r 1) (ladder r 2)
def fieldPi (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  (Real.sqrt (hbar/2) : ℂ) •
    (momentumPair (ladder r 3) (ladder r 4)-Complex.I • skew (ladder r 5))
def fieldPhix (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  (Real.sqrt (hbar/2) : ℂ) • gradientPair (ladder r 3) (ladder r 4)
def fieldPhi (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  (Real.sqrt (hbar/2) : ℂ) •
    (ladder r 5+(ladder r 5)ᴴ+ladder r 3+(ladder r 3)ᴴ+ladder r 4+(ladder r 4)ᴴ)

/-- The previously normalized source is exactly the symmetrized product
of these physical point fields, for nonnegative hbar. -/
theorem source_eq_point_current (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) (hh : 0 ≤ hbar) :
    source R r hbar=current (fieldP R r hbar) (fieldQx R r hbar)+
      current (fieldPi R r hbar) (fieldPhix R r hbar) := by
  have hs : (Real.sqrt (hbar/2) : ℂ)^2=(hbar/2 : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  simp only [fieldP,fieldQx,fieldPi,fieldPhix,current_scale,hs,← smul_add]
  rfl

def inverseHalf (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  halfPolynomial (-clockS R r hbar)
def volumeHalf (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  halfPolynomial (longitudinal R r hbar)

def kinetic (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  staticHamiltonian (halfPolynomial (clockS R r hbar)) (inverseHalf R r hbar)
    (fieldP R r hbar) (fieldPi R r hbar)

def growing (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ) :
    Matrix (State R) (State R) ℂ :=
  (1/2 : ℝ) • gram (fieldQx R r hbar*inverseHalf R r hbar)+
  (1/2 : ℝ) • gram (fieldPhix R r hbar*inverseHalf R r hbar)+
  potentialHamiltonian (inverseHalf R r hbar) (volumeHalf R r hbar)
    (fieldPhi R r hbar) mass2 quartic vacuum

def seedHamiltonian (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ) :
    Matrix (State R) (State R) ℂ :=
  kinetic R r hbar+Real.exp (2*t) • growing R r hbar mass2 quartic vacuum

def hamiltonian (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ) :
    Matrix (State R) (State R) ℂ :=
  dephase charge (seedHamiltonian R r hbar mass2 quartic vacuum t)

theorem seed_positive (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (seedHamiltonian R r hbar mass2 quartic vacuum t).PosSemidef := by
  have hg : (growing R r hbar mass2 quartic vacuum).PosSemidef :=
    (((gram_positive _).smul (by norm_num : (0 : ℝ)≤1/2)).add
      ((gram_positive _).smul (by norm_num : (0 : ℝ)≤1/2))).add
      (potentialHamiltonian_positive _ _ _ _ _ _ hm hq hv)
  exact (staticHamiltonian_positive _ _ _ _).add (hg.smul (Real.exp_pos _).le)

theorem hamiltonian_positive (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (hamiltonian R r hbar mass2 quartic vacuum t).PosSemidef :=
  dephase_positive charge _ (seed_positive R r hbar mass2 quartic vacuum t hm hq hv)

/-- The fully specified finite exponential step needs no ODE-existence
premise and no external clock or source construction hypotheses. -/
theorem specified_step_constraint (R : ℕ) (r : ℕ → ℝ)
    (hbar mass2 quartic vacuum t dt : ℝ) (v : State R → ℂ)
    (hv : (sector charge 0).mulVec v=v) :
    (constraint R r hbar).mulVec
      ((NormedSpace.exp ((-Complex.I*((dt/hbar : ℝ) : ℂ)) •
        hamiltonian R r hbar mass2 quartic vacuum t)).mulVec v)=0 := by
  have hp := zero_sector_step charge (seedHamiltonian R r hbar mass2 quartic vacuum t)
    (-Complex.I*((dt/hbar : ℝ) : ℂ)) v hv
  unfold hamiltonian
  rw [← hp,Matrix.mulVec_mulVec,concrete_constraint_sector,Matrix.zero_mulVec]

/-- Fully specified finite Hamiltonian and reconstructed constraint.
The initial charge-zero state and a global differentiable propagator
solving this Hamiltonian's Schrodinger equation remain explicit inputs. -/
theorem specified_dynamics_constraint (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum)
    (U : ℝ → Matrix (State R) (State R) ℂ)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*((1/hbar : ℝ) : ℂ)) •
      (hamiltonian R r hbar mass2 quartic vacuum t*U t)) t)
    (t₀ t : ℝ) (hinit : U t₀=1) (v : State R → ℂ)
    (hv : (sector charge 0).mulVec v=v) : (constraint R r hbar).mulVec ((U t).mulVec v)=0 :=
  concrete_continuous_constraint R r hbar (seedHamiltonian R r hbar mass2 quartic vacuum)
    (fun s => (hamiltonian_positive R r hbar mass2 quartic vacuum s hm hq hvac).isHermitian)
    (1/hbar) U hU t₀ t hinit v hv

#print axioms current_scale
#print axioms source_eq_point_current
#print axioms seed_positive
#print axioms hamiltonian_positive
#print axioms specified_step_constraint
#print axioms specified_dynamics_constraint

end
end UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian
