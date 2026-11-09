/- Capacity-independent inverse-clock control from the exact occupation
parity. The coefficient depends on hbar and vanishes in the classical
hbar->0 limit; this is not a global classical clock-domain theorem. -/
import UnifiedTheory.Audit.KFCausalInverseClockEnergy
import UnifiedTheory.Audit.KFCausalOccupationParity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalUniformInverseClock
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalQuantumArealCandidate
open UnifiedTheory.Audit.KFCausalConcreteClockConstraint
open UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian (fieldP fieldQx)
open UnifiedTheory.Audit.KFCausalExponentialClockDynamics
open UnifiedTheory.Audit.KFCausalQuantumEnergyControl
open UnifiedTheory.Audit.KFCausalExponentialEnergyBound
open UnifiedTheory.Audit.KFCausalGravityPairCoercivity
open UnifiedTheory.Audit.KFCausalInverseClockEnergy
open UnifiedTheory.Audit.KFCausalOccupationParity

theorem parity_neg_clockS (R : ℕ) (hbar : ℝ) :
    occupationParity R*(-clockS R (fun _ => 1) hbar)=
      -(-clockS R (fun _ => 1) hbar)*occupationParity R := by
  simp only [mul_neg,neg_neg,parity_clockS,neg_mul]

theorem concrete_clock_minus_parity_positive (R : ℕ) (hbar : ℝ) :
    (exponentialClock R (fun _ => 1) hbar-occupationParity R).PosSemidef :=
  clock_minus_parity_positive _ _ (clockS_hermitian R (fun _ => 1) hbar)
    (parity_square R) (parity_clockS R (fun _ => 1) hbar) (one_minus_parity_positive R)

theorem inverse_minus_parity_positive (R : ℕ) (hbar : ℝ) :
    (inverseClock R hbar-occupationParity R).PosSemidef :=
  clock_minus_parity_positive _ _ (clockS_hermitian R (fun _ => 1) hbar).neg
    (parity_square R) (parity_neg_clockS R hbar) (one_minus_parity_positive R)

theorem gravity_pair_minus_parity_positive (R : ℕ) (hbar : ℝ) (hh : 0 ≤ hbar) :
    ((1/2 : ℝ) • dephase charge
      (gram (fieldP R (fun _ => 1) hbar*clockInverseHalf R hbar)+
       gram (fieldQx R (fun _ => 1) hbar*clockInverseHalf R hbar))-
      (hbar/2 : ℝ) • (inverseClock R hbar-occupationParity R)).PosSemidef := by
  have hp := ((loops_minus_parity_positive R).conjTranspose_mul_mul_same
    (clockInverseHalf R hbar)).smul (by positivity : 0 ≤ hbar/2)
  have hd : (clockInverseHalf R hbar)ᴴ=clockInverseHalf R hbar :=
    (halfExp_hermitian _ (clockS_hermitian R (fun _ => 1) hbar).neg).eq
  have he : clockInverseHalf R hbar*occupationParity R*clockInverseHalf R hbar=occupationParity R :=
    halfExp_parity _ _ (parity_square R) (parity_neg_clockS R hbar)
  convert hp using 1
  rw [dephase_gram_pair_product charge _ _ _ (clockInverseHalf_neutral R hbar),
    dephase_gravity_pair R (fun _ => 1) hbar hh]
  simp only [inverseClock,gram,mul_smul_comm,smul_mul_assoc,mul_sub,sub_mul,mul_one,hd,he]
  module

/-- The coefficient is uniform in capacity and all states. There is no
boundary expectation or moment hypothesis. -/
theorem uniform_inverse_clock_lower (R : ℕ) (hbar mass2 quartic vacuum t : ℝ)
    (hh : 0 ≤ hbar) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (ht : 0 ≤ t) :
    (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum t-
      (min 1 hbar/2 : ℝ) • inverseClock R hbar).PosSemidef := by
  have hα : 0 ≤ min 1 hbar := le_min (by norm_num) hh
  have h1 : 0 ≤ 1-min 1 hbar := sub_nonneg.mpr (min_le_left _ _)
  have h2 : 0 ≤ hbar-min 1 hbar := sub_nonneg.mpr (min_le_right _ _)
  have hp := hamiltonian_minus_gravity_pair_positive R (fun _ => 1)
    hbar mass2 quartic vacuum t hm hq hv ht
  have hg := gravity_pair_minus_parity_positive R hbar hh
  have hc := (concrete_clock_minus_parity_positive R hbar).smul
    (by positivity : 0 ≤ min 1 hbar/2)
  have hC := (exponentialClock_positive R (fun _ => 1) hbar).posSemidef.smul
    (by positivity : 0 ≤ (1-min 1 hbar)/2)
  have hi := (inverse_minus_parity_positive R hbar).smul
    (by positivity : 0 ≤ (hbar-min 1 hbar)/2)
  convert ((((hp.add hg).add hc).add hC).add hi) using 1
  simp only [clockInverseHalf]
  module

theorem uniform_inverse_clock_expectation (R : ℕ) (hbar mass2 quartic vacuum t : ℝ)
    (hh : 0 < hbar) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (ht : 0 ≤ t) (v : State R → ℂ) :
    expectation v (inverseClock R hbar) ≤
      2*expectation v (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum t)/min 1 hbar := by
  have hp := expectation_nonneg v _
    (uniform_inverse_clock_lower R hbar mass2 quartic vacuum t hh.le hm hq hv ht)
  simp only [expectation_sub,expectation_smul] at hp
  apply (le_div_iff₀ (lt_min (by norm_num) hh)).mpr
  nlinarith

theorem uniform_evolved_inverse_clock_bound (R : ℕ) (hbar mass2 quartic vacuum : ℝ)
    (hh : 0 < hbar) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (U : ℝ → Matrix (State R) (State R) ℂ)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*((1/hbar : ℝ) : ℂ)) •
      (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum t*U t)) t)
    (v : State R → ℂ) (s t : ℝ) (hst : s ≤ t) (ht : 0 ≤ t) :
    expectation (U t*ᵥv) (inverseClock R hbar) ≤
      2*Real.exp (2*(t-s))*expectation (U s*ᵥv)
        (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum s)/min 1 hbar := by
  have hi := uniform_inverse_clock_expectation R hbar mass2 quartic vacuum t hh hm hq hv ht (U t*ᵥv)
  have he := (exponential_energy_growth R (fun _ => 1) hbar mass2 quartic vacuum
    hm hq hv U hU v s t hst).2
  apply hi.trans
  apply div_le_div_of_nonneg_right _ (le_min (by norm_num) hh.le)
  nlinarith

/-- Positive K,V give a comparison with H(0) in both time directions. -/
theorem hamiltonian_time_floor (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (exponentialHamiltonian R r hbar mass2 quartic vacuum t-
      min 1 (Real.exp (2*t)) • exponentialHamiltonian R r hbar mass2 quartic vacuum 0).PosSemidef := by
  have h1 : 0 ≤ 1-min 1 (Real.exp (2*t)) := sub_nonneg.mpr (min_le_left _ _)
  have h2 : 0 ≤ Real.exp (2*t)-min 1 (Real.exp (2*t)) := sub_nonneg.mpr (min_le_right _ _)
  have hp := ((staticPart_positive R r hbar).smul h1).add
    ((growingPart_positive R r hbar mass2 quartic vacuum hm hq hv).smul h2)
  convert hp using 1
  simp only [exponential_hamiltonian_split,hamiltonian,mul_zero,Real.exp_zero,one_smul]
  module

/-- The estimate holds at every real time with an explicit positive
factor. The factor is uniform in capacity on bounded time intervals. -/
theorem all_time_inverse_clock_lower (R : ℕ) (hbar mass2 quartic vacuum t : ℝ)
    (hh : 0 ≤ hbar) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum t-
      (min 1 (Real.exp (2*t))*min 1 hbar/2 : ℝ) • inverseClock R hbar).PosSemidef := by
  have hp := hamiltonian_time_floor R (fun _ => 1) hbar mass2 quartic vacuum t hm hq hv
  have hb : 0 ≤ min 1 (Real.exp (2*t)) := le_min (by norm_num) (Real.exp_pos _).le
  have hi := (uniform_inverse_clock_lower R hbar mass2 quartic vacuum 0 hh hm hq hv le_rfl).smul hb
  convert hp.add hi using 1
  module

theorem all_time_inverse_clock_expectation (R : ℕ) (hbar mass2 quartic vacuum t : ℝ)
    (hh : 0 < hbar) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (v : State R → ℂ) :
    expectation v (inverseClock R hbar) ≤
      2*expectation v (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum t)/
        (min 1 (Real.exp (2*t))*min 1 hbar) := by
  have hp := expectation_nonneg v _ (all_time_inverse_clock_lower R hbar mass2 quartic vacuum t hh.le hm hq hv)
  simp only [expectation_sub,expectation_smul] at hp
  have hd : 0 < min 1 (Real.exp (2*t))*min 1 hbar :=
    mul_pos (lt_min (by norm_num) (Real.exp_pos _)) (lt_min (by norm_num) hh)
  apply (le_div_iff₀ hd).mpr
  nlinarith

/-- The global flow already constructed in Lean now carries an inverse-
clock bound without any state-tail, occupation-moment or boundary input. -/
theorem exists_clock_controlled_evolution (R : ℕ) (hbar mass2 quartic vacuum : ℝ)
    (hh : 0 < hbar) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    ∃ U : ℝ → Matrix (State R) (State R) ℂ,
      U 0=1 ∧
      (∀ t, HasDerivAt U ((-Complex.I*((1/hbar : ℝ) : ℂ)) •
        (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum t*U t)) t) ∧
      (∀ t, (U t)ᴴ*U t=1 ∧ U t*(U t)ᴴ=1) ∧
      (∀ t v, (sector charge 0).mulVec v=v →
        (exponentialConstraint R (fun _ => 1) hbar).mulVec ((U t).mulVec v)=0) ∧
      (∀ v s t, s ≤ t →
        expectation (U t*ᵥv) (inverseClock R hbar) ≤
          2*Real.exp (2*(t-s))*expectation (U s*ᵥv)
            (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum s)/
              (min 1 (Real.exp (2*t))*min 1 hbar)) := by
  obtain ⟨U,hU,_⟩ := existsUnique_exponential_dynamics R (fun _ => 1)
    hbar mass2 quartic vacuum hh hm hq hv
  refine ⟨U,hU.1,hU.2.1,hU.2.2.1,hU.2.2.2,?_⟩
  intro v s t hst
  have hi := all_time_inverse_clock_expectation R hbar mass2 quartic vacuum t hh hm hq hv (U t*ᵥv)
  have he := (exponential_energy_growth R (fun _ => 1) hbar mass2 quartic vacuum
    hm hq hv U hU.2.1 v s t hst).2
  apply hi.trans
  apply div_le_div_of_nonneg_right _
    (mul_nonneg (le_min (by norm_num) (Real.exp_pos _).le) (le_min (by norm_num) hh.le))
  nlinarith

#print axioms concrete_clock_minus_parity_positive
#print axioms inverse_minus_parity_positive
#print axioms gravity_pair_minus_parity_positive
#print axioms uniform_inverse_clock_lower
#print axioms uniform_inverse_clock_expectation
#print axioms uniform_evolved_inverse_clock_bound
#print axioms hamiltonian_time_floor
#print axioms all_time_inverse_clock_lower
#print axioms all_time_inverse_clock_expectation
#print axioms exists_clock_controlled_evolution

end
end UnifiedTheory.Audit.KFCausalUniformInverseClock
