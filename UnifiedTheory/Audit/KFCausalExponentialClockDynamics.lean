/- Exact matrix functions replace the fixed polynomial approximations.
The finite clock remains subject to the trace/boundary obstruction.
Positivity, Jordan reconstruction and global constrained evolution are
proved for this exponential variant; a continuum limit is not assumed. -/
import UnifiedTheory.Audit.KFCausalGlobalPropagator
import UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalExponentialClockDynamics
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.Audit.KFCausalFiniteOccupationLadders
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity
open UnifiedTheory.Audit.KFCausalGradedSpinSource
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalQuantumArealCandidate
open UnifiedTheory.Audit.KFCausalPositiveClockReconstruction
open UnifiedTheory.Audit.KFCausalConcreteClockConstraint
open UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian
open UnifiedTheory.Audit.KFCausalContinuousConstraintFlow
open UnifiedTheory.Audit.KFCausalGlobalPropagator

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local instance : NormedAlgebra ℚ M := NormedAlgebra.restrictScalars ℚ ℂ M

def halfExp (S : M) : M := NormedSpace.exp ((1/2 : ℝ) • S)

theorem halfExp_hermitian (S : M) (hS : S.IsHermitian) : (halfExp S).IsHermitian := by
  have hh : IsSelfAdjoint ((1/2 : ℝ) • S) := by
    change ((1/2 : ℝ) • S)ᴴ=(1/2 : ℝ) • S
    simp [hS.eq]
  exact hh.exp

theorem halfExp_gram_positive (S : M) : (gram (halfExp S)).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (NormedSpace.isUnit_exp _))

theorem halfExp_inverse (S : M) : halfExp S*halfExp (-S)=1 := by
  unfold halfExp
  rw [smul_neg,← NormedSpace.exp_add_of_commute (Commute.refl ((1/2 : ℝ) • S)).neg_right]
  simp

theorem gram_halfExp_eq_exp (S : M) (hS : S.IsHermitian) : gram (halfExp S)=NormedSpace.exp S := by
  rw [gram,(halfExp_hermitian S hS).eq]
  unfold halfExp
  rw [← NormedSpace.exp_add_of_commute (Commute.refl ((1/2 : ℝ) • S))]
  congr 1
  module

theorem clock_inverse_exact (S : M) (hS : S.IsHermitian) :
    gram (halfExp S)*gram (halfExp (-S))=1 := by
  rw [gram_halfExp_eq_exp S hS,gram_halfExp_eq_exp (-S) hS.neg,
    ← NormedSpace.exp_add_of_commute (Commute.refl S).neg_right]
  simp

/-- A matrix function of a neutral clock is neutral, without choosing
a charge-preserving spectral basis. -/
theorem neutral_exp (q : n → ℤ) (S : M) (hS : HasCharge q 0 S) :
    HasCharge q 0 (NormedSpace.exp S) := by
  let Q : M := diagonal (fun i => (q i : ℂ))
  have hc : Commute S Q := by
    ext i j
    simp only [Q,mul_diagonal,diagonal_mul]
    by_cases hq : q i=q j
    · rw [hq,mul_comm]
    · rw [hS i j (sub_ne_zero.mpr hq)]; simp
  intro i j hij
  have he := congrFun (congrFun hc.exp_left.eq i) j
  simp only [Q,mul_diagonal,diagonal_mul] at he
  have hn : (q i : ℂ)-(q j : ℂ) ≠ 0 := by exact_mod_cast hij
  have hz : ((q i : ℂ)-(q j : ℂ))*NormedSpace.exp S i j=0 := by
    linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left hn

theorem halfExp_neutral (q : n → ℤ) (S : M) (hS : HasCharge q 0 S) :
    HasCharge q 0 (halfExp S) :=
  neutral_exp q _ (charge_real_smul q S (1/2) hS)

def exponentialClock (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  gram (halfExp (clockS R r hbar))

def exponentialBase (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  symmetrize (halfExp (-clockS R r hbar)*halfExp (-clockS R r hbar)*clockPs R r hbar)

theorem exponentialClock_positive (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    (exponentialClock R r hbar).PosDef := halfExp_gram_positive _

theorem exponentialClock_neutral (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    spatialDeriv charge (exponentialClock R r hbar)=0 :=
  neutral_spatialDeriv charge _ (charge_gram charge _
    (halfExp_neutral charge _ (clockS_neutral R r hbar)))

theorem exponentialBase_neutral (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    spatialDeriv charge (exponentialBase R r hbar)=0 := by
  have hneg : HasCharge charge 0 (-clockS R r hbar) := by
    intro i j hij; simp [(clockS_neutral R r hbar) i j hij]
  have hD := halfExp_neutral charge _ hneg
  let A := halfExp (-clockS R r hbar)*halfExp (-clockS R r hbar)*clockPs R r hbar
  have hA : HasCharge charge 0 A := by
    simpa only [zero_add] using charge_mul charge 0 0 _ _
      (by simpa only [zero_add] using charge_mul charge 0 0 _ _ hD hD) (clockPs_neutral R r hbar)
  have hAd : HasCharge charge 0 Aᴴ := by
    simpa only [neg_zero] using charge_adjoint charge 0 A hA
  exact neutral_spatialDeriv charge _
    (charge_real_smul charge _ (1/2) (charge_add charge A Aᴴ hA hAd))

def exponentialLongitudinal (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  reconstructed (exponentialClock R r hbar) (exponentialClock_positive R r hbar) charge
    (exponentialBase R r hbar) (source R r hbar)

def exponentialConstraint (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  source R r hbar-matrixJordan (exponentialClock R r hbar)
    (spatialDeriv charge (exponentialLongitudinal R r hbar))

theorem exponentialLongitudinal_hermitian (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    (exponentialLongitudinal R r hbar).IsHermitian :=
  reconstructed_hermitian _ _ charge _ _ (symmetrize_hermitian _)
    (spin_source_hermitian hbar _ _ _ _ _)

theorem exponentialConstraint_identity (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    exponentialConstraint R r hbar=meanPart charge (source R r hbar) :=
  reconstructed_identity _ _ charge (exponentialClock_neutral R r hbar) _ _
    (exponentialBase_neutral R r hbar)

theorem exponentialConstraint_sector (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    exponentialConstraint R r hbar*sector charge 0=0 := by
  rw [exponentialConstraint_identity]
  exact source_annihilates_zero R r hbar

def exponentialKinetic (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  staticHamiltonian (halfExp (clockS R r hbar)) (halfExp (-clockS R r hbar))
    (fieldP R r hbar) (fieldPi R r hbar)

def exponentialGrowing (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ) :
    Matrix (State R) (State R) ℂ :=
  (1/2 : ℝ) • gram (fieldQx R r hbar*halfExp (-clockS R r hbar))+
  (1/2 : ℝ) • gram (fieldPhix R r hbar*halfExp (-clockS R r hbar))+
  potentialHamiltonian (halfExp (-clockS R r hbar))
    (halfExp (exponentialLongitudinal R r hbar)) (fieldPhi R r hbar) mass2 quartic vacuum

def exponentialSeed (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ) :
    Matrix (State R) (State R) ℂ :=
  exponentialKinetic R r hbar+Real.exp (2*t) • exponentialGrowing R r hbar mass2 quartic vacuum

def exponentialHamiltonian (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ) :
    Matrix (State R) (State R) ℂ := dephase charge (exponentialSeed R r hbar mass2 quartic vacuum t)

theorem exponentialHamiltonian_positive (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (exponentialHamiltonian R r hbar mass2 quartic vacuum t).PosSemidef := by
  have hg : (exponentialGrowing R r hbar mass2 quartic vacuum).PosSemidef :=
    (((gram_positive _).smul (by norm_num : (0 : ℝ)≤1/2)).add
      ((gram_positive _).smul (by norm_num : (0 : ℝ)≤1/2))).add
      (potentialHamiltonian_positive _ _ _ _ _ _ hm hq hv)
  exact dephase_positive charge _ ((staticHamiltonian_positive _ _ _ _).add (hg.smul (Real.exp_pos _).le))

theorem exponentialHamiltonian_continuous (R : ℕ) (r : ℕ → ℝ) (hbar mass2 quartic vacuum : ℝ) :
    Continuous (exponentialHamiltonian R r hbar mass2 quartic vacuum) := by
  unfold exponentialHamiltonian dephase exponentialSeed
  fun_prop

local instance stateNonempty (R : ℕ) : Nonempty (State R) :=
  ⟨⟨fun _ => 0,by simp [total]⟩⟩

/-- The exponential model has the same exact finite constraint and
global existence guarantees as the polynomial candidate. No propagator
or clock spectral basis is supplied as an assumption. -/
theorem existsUnique_exponential_dynamics (R : ℕ) (r : ℕ → ℝ)
    (hbar mass2 quartic vacuum : ℝ) (_hh : 0 < hbar)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) :
    ∃! U : ℝ → Matrix (State R) (State R) ℂ,
      U 0=1 ∧
      (∀ t, HasDerivAt U ((-Complex.I*((1/hbar : ℝ) : ℂ)) •
        (exponentialHamiltonian R r hbar mass2 quartic vacuum t*U t)) t) ∧
      (∀ t, (U t)ᴴ*U t=1 ∧ U t*(U t)ᴴ=1) ∧
      (∀ t v, (sector charge 0).mulVec v=v →
        (exponentialConstraint R r hbar).mulVec ((U t).mulVec v)=0) := by
  let H := exponentialHamiltonian R r hbar mass2 quartic vacuum
  let A := fun t => (-Complex.I*((1/hbar : ℝ) : ℂ)) • H t
  have hH (t : ℝ) : (H t).IsHermitian :=
    (exponentialHamiltonian_positive R r hbar mass2 quartic vacuum t hm hq hvac).isHermitian
  have hA : Continuous A := (exponentialHamiltonian_continuous R r hbar mass2 quartic vacuum).const_smul _
  have hs (t : ℝ) : (A t)ᴴ= -A t := by simp [A,Matrix.conjTranspose_smul,(hH t).eq]
  obtain ⟨U,⟨hinit,hU⟩,hunique⟩ := existsUnique_global_propagator A hA hs
  have hd (t : ℝ) : HasDerivAt U ((-Complex.I*((1/hbar : ℝ) : ℂ)) • (H t*U t)) t := by
    simpa only [A,smul_mul_assoc] using hU t
  refine ⟨U,⟨hinit,hd,?_,?_⟩,?_⟩
  · intro t
    exact propagator_unitary H hH (1/hbar) U hd 0 t hinit
  · intro t v hv
    exact constraint_continuous charge _ (exponentialConstraint_sector R r hbar)
      (exponentialSeed R r hbar mass2 quartic vacuum) hH (1/hbar) U hd 0 t hinit v hv
  · intro V hV
    apply hunique V
    refine ⟨hV.1,?_⟩
    intro t
    simpa only [A,H,smul_mul_assoc] using hV.2.1 t

#print axioms halfExp_hermitian
#print axioms halfExp_gram_positive
#print axioms halfExp_inverse
#print axioms gram_halfExp_eq_exp
#print axioms clock_inverse_exact
#print axioms neutral_exp
#print axioms exponentialClock_positive
#print axioms exponentialClock_neutral
#print axioms exponentialBase_neutral
#print axioms exponentialLongitudinal_hermitian
#print axioms exponentialConstraint_identity
#print axioms exponentialConstraint_sector
#print axioms exponentialHamiltonian_positive
#print axioms exponentialHamiltonian_continuous
#print axioms existsUnique_exponential_dynamics

end
end UnifiedTheory.Audit.KFCausalExponentialClockDynamics
