/- The abstract energy estimate instantiated on the specified exponential
spin Hamiltonian, with a constructed global propagator and no supplied
energy-source, operator-commutation or evolution-existence premise. -/
import UnifiedTheory.Audit.KFCausalQuantumEnergyControl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalExponentialEnergyBound
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalQuantumArealCandidate
open UnifiedTheory.Audit.KFCausalGradedSpinSource
open UnifiedTheory.Audit.KFCausalConcreteClockConstraint
open UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian (fieldP fieldPi)
open UnifiedTheory.Audit.KFCausalExponentialClockDynamics
open UnifiedTheory.Audit.KFCausalQuantumEnergyControl

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

theorem dephase_add (q : n → ℤ) (A B : M) : dephase q (A+B)=dephase q A+dephase q B := by
  simp only [dephase,mul_add,add_mul,Finset.sum_add_distrib]

theorem dephase_real_smul (q : n → ℤ) (r : ℝ) (A : M) : dephase q (r • A)=r • dephase q A := by
  simp only [dephase,mul_smul_comm,smul_mul_assoc,Finset.smul_sum]

def staticPart (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  dephase charge (exponentialKinetic R r hbar)
def growingPart (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ) :
    Matrix (State R) (State R) ℂ :=
  dephase charge (exponentialGrowing R r hbar mass2 quartic vacuum)

theorem staticPart_positive (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    (staticPart R r hbar).PosSemidef := dephase_positive charge _ (staticHamiltonian_positive _ _ _ _)

theorem growingPart_positive (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (growingPart R r hbar mass2 quartic vacuum).PosSemidef := by
  apply dephase_positive
  exact (((gram_positive _).smul (by norm_num : (0 : ℝ)≤1/2)).add
    ((gram_positive _).smul (by norm_num : (0 : ℝ)≤1/2))).add
    (potentialHamiltonian_positive _ _ _ _ _ _ hm hq hv)

theorem exponential_hamiltonian_split (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ) :
    exponentialHamiltonian R r hbar mass2 quartic vacuum t=
      hamiltonian (staticPart R r hbar) (growingPart R r hbar mass2 quartic vacuum) t := by
  simp only [exponentialHamiltonian,exponentialSeed,dephase_add,dephase_real_smul,
    hamiltonian,staticPart,growingPart]

theorem dephase_exponentialClock (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    dephase charge (exponentialClock R r hbar)=exponentialClock R r hbar := by
  rw [dephase_eq_meanPart]
  exact mean_zero_charge charge _ (charge_gram charge _
    (halfExp_neutral charge _ (clockS_neutral R r hbar)))

theorem staticPart_minus_clock_positive (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    (staticPart R r hbar-(1/2 : ℝ) • exponentialClock R r hbar).PosSemidef := by
  have hp := dephase_positive charge
    ((1/2 : ℝ) • gram (fieldP R r hbar*halfExp (-clockS R r hbar))+
      (1/2 : ℝ) • gram (fieldPi R r hbar*halfExp (-clockS R r hbar)))
    (((gram_positive _).smul (by norm_num : (0 : ℝ)≤1/2)).add
      ((gram_positive _).smul (by norm_num : (0 : ℝ)≤1/2)))
  have hc : dephase charge (gram (halfExp (clockS R r hbar)))=exponentialClock R r hbar :=
    dephase_exponentialClock R r hbar
  convert hp using 1
  simp only [staticPart,exponentialKinetic,staticHamiltonian,dephase_add,dephase_real_smul,hc]
  abel

theorem hamiltonian_minus_clock_positive (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (exponentialHamiltonian R r hbar mass2 quartic vacuum t-
      (1/2 : ℝ) • exponentialClock R r hbar).PosSemidef := by
  have hp := (staticPart_minus_clock_positive R r hbar).add
    ((growingPart_positive R r hbar mass2 quartic vacuum hm hq hv).smul (Real.exp_pos (2*t)).le)
  convert hp using 1
  rw [exponential_hamiltonian_split,hamiltonian]
  abel

theorem clock_expectation_le_energy (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (v : State R → ℂ) :
    expectation v (exponentialClock R r hbar) ≤
      2*expectation v (exponentialHamiltonian R r hbar mass2 quartic vacuum t) := by
  have hp := expectation_nonneg v _
    (hamiltonian_minus_clock_positive R r hbar mass2 quartic vacuum t hm hq hv)
  have hs := (expectationMap v).map_sub
    (exponentialHamiltonian R r hbar mass2 quartic vacuum t) ((1/2 : ℝ) • exponentialClock R r hbar)
  simp only [expectationMap_apply,expectation_smul] at hs
  rw [hs] at hp
  linarith

theorem exponential_energy_growth (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (U : ℝ → Matrix (State R) (State R) ℂ)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*((1/hbar : ℝ) : ℂ)) •
      (exponentialHamiltonian R r hbar mass2 quartic vacuum t*U t)) t)
    (v : State R → ℂ) (s t : ℝ) (hst : s ≤ t) :
    expectation (U s*ᵥv) (exponentialHamiltonian R r hbar mass2 quartic vacuum s) ≤
      expectation (U t*ᵥv) (exponentialHamiltonian R r hbar mass2 quartic vacuum t) ∧
    expectation (U t*ᵥv) (exponentialHamiltonian R r hbar mass2 quartic vacuum t) ≤
      Real.exp (2*(t-s))*expectation (U s*ᵥv)
        (exponentialHamiltonian R r hbar mass2 quartic vacuum s) := by
  have hd (z : ℝ) := hU z
  simp only [exponential_hamiltonian_split] at hd
  have he := energy_growth_bound (staticPart R r hbar) (growingPart R r hbar mass2 quartic vacuum)
    (staticPart_positive R r hbar) (growingPart_positive R r hbar mass2 quartic vacuum hm hq hv)
    U (1/hbar) hd v s t hst
  simpa only [energy,← exponential_hamiltonian_split,expectation_conjugate] using he

theorem evolved_clock_bound (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (U : ℝ → Matrix (State R) (State R) ℂ)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*((1/hbar : ℝ) : ℂ)) •
      (exponentialHamiltonian R r hbar mass2 quartic vacuum t*U t)) t)
    (v : State R → ℂ) (s t : ℝ) (hst : s ≤ t) :
    expectation (U t*ᵥv) (exponentialClock R r hbar) ≤
      2*Real.exp (2*(t-s))*expectation (U s*ᵥv)
        (exponentialHamiltonian R r hbar mass2 quartic vacuum s) := by
  have hc := clock_expectation_le_energy R r hbar mass2 quartic vacuum t hm hq hv (U t*ᵥv)
  have he := (exponential_energy_growth R r hbar mass2 quartic vacuum hm hq hv U hU v s t hst).2
  nlinarith

/-- For every finite capacity a solution exists which simultaneously
preserves the physical constraint, is unitary, and obeys the same energy
growth factor exp(2(t-s)). No initial-state normalization is required. -/
theorem exists_energy_controlled_evolution (R : ℕ) (r : ℕ → ℝ)
    (hbar mass2 quartic vacuum : ℝ) (hh : 0 < hbar)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    ∃ U : ℝ → Matrix (State R) (State R) ℂ,
      U 0=1 ∧
      (∀ t, HasDerivAt U ((-Complex.I*((1/hbar : ℝ) : ℂ)) •
        (exponentialHamiltonian R r hbar mass2 quartic vacuum t*U t)) t) ∧
      (∀ t, (U t)ᴴ*U t=1 ∧ U t*(U t)ᴴ=1) ∧
      (∀ t v, (sector charge 0).mulVec v=v →
        (exponentialConstraint R r hbar).mulVec ((U t).mulVec v)=0) ∧
      (∀ v s t, s ≤ t →
        expectation (U s*ᵥv) (exponentialHamiltonian R r hbar mass2 quartic vacuum s) ≤
          expectation (U t*ᵥv) (exponentialHamiltonian R r hbar mass2 quartic vacuum t) ∧
        expectation (U t*ᵥv) (exponentialHamiltonian R r hbar mass2 quartic vacuum t) ≤
          Real.exp (2*(t-s))*expectation (U s*ᵥv)
            (exponentialHamiltonian R r hbar mass2 quartic vacuum s)) := by
  obtain ⟨U,hU,_⟩ := existsUnique_exponential_dynamics R r hbar mass2 quartic vacuum hh hm hq hv
  exact ⟨U,hU.1,hU.2.1,hU.2.2.1,hU.2.2.2,
    exponential_energy_growth R r hbar mass2 quartic vacuum hm hq hv U hU.2.1⟩

#print axioms dephase_add
#print axioms dephase_real_smul
#print axioms staticPart_positive
#print axioms growingPart_positive
#print axioms exponential_hamiltonian_split
#print axioms dephase_exponentialClock
#print axioms staticPart_minus_clock_positive
#print axioms hamiltonian_minus_clock_positive
#print axioms clock_expectation_le_energy
#print axioms exponential_energy_growth
#print axioms evolved_clock_bound
#print axioms exists_energy_controlled_evolution

end
end UnifiedTheory.Audit.KFCausalExponentialEnergyBound
