/- An inverse-clock energy estimate for exact amplitudes. The capacity
boundary is explicit. Absorbing it requires a state-domain estimate;
that estimate is not inferred from finite unitarity or energy alone. -/
import UnifiedTheory.Audit.KFCausalGravityPairCoercivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalInverseClockEnergy
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalQuantumArealCandidate
open UnifiedTheory.Audit.KFCausalConcreteClockConstraint
open UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian (fieldP fieldQx fieldPi fieldPhix fieldPhi)
open UnifiedTheory.Audit.KFCausalExponentialClockDynamics
open UnifiedTheory.Audit.KFCausalQuantumEnergyControl
open UnifiedTheory.Audit.KFCausalExponentialEnergyBound
open UnifiedTheory.Audit.KFCausalGravityPairCoercivity

/-- For t>=0 the extra growing terms have nonnegative coefficients. -/
theorem hamiltonian_minus_gravity_pair_positive (R : ℕ) (r : ℕ → ℝ)
    (hbar mass2 quartic vacuum t : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic)
    (hv : 0 ≤ vacuum) (ht : 0 ≤ t) :
    (exponentialHamiltonian R r hbar mass2 quartic vacuum t-
      (1/2 : ℝ) • exponentialClock R r hbar-
      (1/2 : ℝ) • dephase charge
        (gram (fieldP R r hbar*halfExp (-clockS R r hbar))+
         gram (fieldQx R r hbar*halfExp (-clockS R r hbar)))).PosSemidef := by
  have he : 0 ≤ Real.exp (2*t)-1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hp := (dephase_positive charge _
    ((((gram_positive (fieldPi R r hbar*halfExp (-clockS R r hbar))).smul
       (by norm_num : (0 : ℝ)≤1/2)).add
      ((gram_positive (fieldPhix R r hbar*halfExp (-clockS R r hbar))).smul
       (by norm_num : (0 : ℝ)≤1/2))).add
      (potentialHamiltonian_positive (halfExp (-clockS R r hbar))
        (halfExp (exponentialLongitudinal R r hbar)) (fieldPhi R r hbar)
        mass2 quartic vacuum hm hq hv))).add
    ((growingPart_positive R r hbar mass2 quartic vacuum hm hq hv).smul he)
  convert hp using 1
  simp only [exponentialHamiltonian,exponentialSeed,exponentialKinetic,staticHamiltonian,
    dephase_add,dephase_real_smul]
  rw [show dephase charge (gram (halfExp (clockS R r hbar)))=exponentialClock R r hbar
    from dephase_exponentialClock R r hbar]
  simp only [growingPart,exponentialGrowing,dephase_add,dephase_real_smul]
  module

/-- The desired inverse-clock lower bound, with the exact capacity defect. -/
theorem hamiltonian_inverse_clock_lower (R : ℕ) (hbar mass2 quartic vacuum t : ℝ)
    (hh : 0 ≤ hbar) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (ht : 0 ≤ t) :
    (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum t-
      ((1/2 : ℝ) • exponentialClock R (fun _ => 1) hbar+
       hbar • inverseClock R hbar-(hbar/2 : ℝ) • boundaryClock R hbar)).PosSemidef := by
  have hp := hamiltonian_minus_gravity_pair_positive R (fun _ => 1)
    hbar mass2 quartic vacuum t hm hq hv ht
  change (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum t-
      (1/2 : ℝ) • exponentialClock R (fun _ => 1) hbar-
      (1/2 : ℝ) • dephase charge
        (gram (fieldP R (fun _ => 1) hbar*clockInverseHalf R hbar)+
         gram (fieldQx R (fun _ => 1) hbar*clockInverseHalf R hbar))).PosSemidef at hp
  rw [exact_gravity_pair R hbar hh] at hp
  have hn := ((gravityNumber_positive R).conjTranspose_mul_mul_same
    (clockInverseHalf R hbar)).smul hh
  convert hp.add hn using 1
  module

theorem expectation_sub {n : Type*} [Fintype n] (v : n → ℂ) (A B : Matrix n n ℂ) :
    expectation v (A-B)=expectation v A-expectation v B :=
  (expectationMap v).map_sub A B

/-- This stronger form retains the positive clock term as well. -/
theorem joint_clock_expectation_bound (R : ℕ) (hbar mass2 quartic vacuum t : ℝ)
    (hh : 0 ≤ hbar) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (ht : 0 ≤ t) (v : State R → ℂ) :
    (1/2 : ℝ)*expectation v (exponentialClock R (fun _ => 1) hbar)+
      hbar*expectation v (inverseClock R hbar) ≤
      expectation v (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum t)+
      (hbar/2)*expectation v (boundaryClock R hbar) := by
  have hp := expectation_nonneg v _
    (hamiltonian_inverse_clock_lower R hbar mass2 quartic vacuum t hh hm hq hv ht)
  simp only [expectation_sub,expectation_add,expectation_smul] at hp
  linarith

theorem inverse_clock_expectation_bound (R : ℕ) (hbar mass2 quartic vacuum t : ℝ)
    (hh : 0 ≤ hbar) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (ht : 0 ≤ t) (v : State R → ℂ) :
    hbar*expectation v (inverseClock R hbar) ≤
      expectation v (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum t)+
      (hbar/2)*expectation v (boundaryClock R hbar) := by
  have hp := joint_clock_expectation_bound R hbar mass2 quartic vacuum t hh hm hq hv ht v
  have hc := expectation_nonneg v _ (exponentialClock_positive R (fun _ => 1) hbar).posSemidef
  linarith

/-- Conditional absorption states exactly which boundary-domain estimate
is still needed. It does not assume the desired inverse-clock conclusion. -/
theorem inverse_clock_bound_of_relative_boundary (R : ℕ) (hbar mass2 quartic vacuum t δ : ℝ)
    (hh : 0 < hbar) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (ht : 0 ≤ t) (hδ : δ < 2) (v : State R → ℂ)
    (hb : expectation v (boundaryClock R hbar) ≤ δ*expectation v (inverseClock R hbar)) :
    expectation v (inverseClock R hbar) ≤
      expectation v (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum t)/
        (hbar*(1-δ/2)) := by
  have hp := inverse_clock_expectation_bound R hbar mass2 quartic vacuum t hh.le hm hq hv ht v
  have hd : 0 < hbar*(1-δ/2) := mul_pos hh (by linarith)
  apply (le_div_iff₀ hd).mpr
  nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ hbar/2)]

/-- Combining the proved energy growth with a boundary condition at the
observation time gives a bound in terms of initial energy. -/
theorem evolved_inverse_clock_bound (R : ℕ) (hbar mass2 quartic vacuum δ : ℝ)
    (hh : 0 < hbar) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (hδ : δ < 2)
    (U : ℝ → Matrix (State R) (State R) ℂ)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*((1/hbar : ℝ) : ℂ)) •
      (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum t*U t)) t)
    (v : State R → ℂ) (s t : ℝ) (hst : s ≤ t) (ht : 0 ≤ t)
    (hb : expectation (U t*ᵥv) (boundaryClock R hbar) ≤
      δ*expectation (U t*ᵥv) (inverseClock R hbar)) :
    expectation (U t*ᵥv) (inverseClock R hbar) ≤
      Real.exp (2*(t-s))*expectation (U s*ᵥv)
        (exponentialHamiltonian R (fun _ => 1) hbar mass2 quartic vacuum s)/(hbar*(1-δ/2)) := by
  have hi := inverse_clock_bound_of_relative_boundary R hbar mass2 quartic vacuum t δ
    hh hm hq hv ht hδ (U t*ᵥv) hb
  have he := (exponential_energy_growth R (fun _ => 1) hbar mass2 quartic vacuum
    hm hq hv U hU v s t hst).2
  exact hi.trans (div_le_div_of_nonneg_right he (by nlinarith))

#print axioms hamiltonian_minus_gravity_pair_positive
#print axioms hamiltonian_inverse_clock_lower
#print axioms joint_clock_expectation_bound
#print axioms inverse_clock_expectation_bound
#print axioms inverse_clock_bound_of_relative_boundary
#print axioms evolved_inverse_clock_bound

end
end UnifiedTheory.Audit.KFCausalInverseClockEnergy
