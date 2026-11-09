/- The actual second-order polynomial clock, mean longitudinal datum and
six-flavor source, on the full retained finite occupation simplex.
Positivity and translation neutrality are derived from these matrices. -/
import UnifiedTheory.Audit.KFCausalPositiveClockReconstruction
import UnifiedTheory.Audit.KFCausalContinuousConstraintFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConcreteClockConstraint
noncomputable section
open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalGradedSpinSource
open UnifiedTheory.Audit.KFCausalQuantumArealCandidate
open UnifiedTheory.Audit.KFCausalPositiveClockReconstruction
open UnifiedTheory.Audit.KFCausalContinuousConstraintFlow
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

omit [Fintype n] [DecidableEq n] in
theorem charge_add (q : n → ℤ) (A B : M) (hA : HasCharge q 0 A) (hB : HasCharge q 0 B) :
    HasCharge q 0 (A+B) := by
  intro i j hij; simp [hA i j hij,hB i j hij]

omit [Fintype n] [DecidableEq n] in
theorem charge_real_smul (q : n → ℤ) (A : M) (r : ℝ) (hA : HasCharge q 0 A) :
    HasCharge q 0 (r • A) := by
  intro i j hij; simp [hA i j hij]

omit [Fintype n] in
theorem charge_one (q : n → ℤ) : HasCharge q 0 (1 : M) := by
  intro i j hij
  have hn : i ≠ j := by intro h; subst j; simp at hij
  simp [hn]

omit [DecidableEq n] in
theorem charge_gram (q : n → ℤ) (A : M) (hA : HasCharge q 0 A) :
    HasCharge q 0 (gram A) := by
  simpa [gram] using charge_mul q 0 0 Aᴴ A (by simpa using charge_adjoint q 0 A hA) hA

theorem charge_halfPolynomial (q : n → ℤ) (S : M) (hS : HasCharge q 0 S) :
    HasCharge q 0 (halfPolynomial S) :=
  charge_add q _ _ (charge_real_smul q 1 (1/2) (charge_one q))
    (charge_real_smul q _ (1/8) (charge_gram q _
      (charge_add q S _ hS (charge_real_smul q 1 2 (charge_one q)))))

theorem polynomial_clock_positive (S : M) : (gram (halfPolynomial S)).PosDef := by
  have hp : ((1/4 : ℝ) • (1 : M)).PosDef :=
    (Matrix.PosDef.one : (1 : M).PosDef).smul (by norm_num : (0 : ℝ)<1/4)
  simpa using Matrix.PosDef.posSemidef_add (halfPolynomial_clock_floor S) hp

omit [Fintype n] [DecidableEq n] in
theorem neutral_spatialDeriv (q : n → ℤ) (A : M) (hA : HasCharge q 0 A) :
    spatialDeriv q A=0 := by
  ext i j
  by_cases h : q i=q j
  · simp [spatialDeriv,h]
  · simp [spatialDeriv,hA i j (sub_ne_zero.mpr h)]

omit [Fintype n] [DecidableEq n] in
theorem momentum_hermitian (A : M) : (-Complex.I • skew A).IsHermitian := by
  unfold Matrix.IsHermitian skew
  simp [smul_sub,add_comm]

omit [DecidableEq n] in
theorem current_hermitian (P D : M) (hP : P.IsHermitian) (hD : D.IsHermitian) :
    (current P D).IsHermitian := by
  unfold Matrix.IsHermitian current
  simp [hP.eq,hD.eq,add_comm]

omit [DecidableEq n] in
theorem spin_source_hermitian (hbar : ℝ) (A B C D Z : M) :
    (spinSource hbar A B C D Z).IsHermitian := by
  have hp (X Y : M) : (momentumPair X Y).IsHermitian := by
    simpa [momentumPair,smul_add] using (momentum_hermitian X).add (momentum_hermitian Y)
  have hd (X Y : M) : (gradientPair X Y).IsHermitian := by
    simpa [gradientPair,smul_sub] using (momentum_hermitian X).sub (momentum_hermitian Y)
  have hz : (momentumPair C D-Complex.I • skew Z).IsHermitian := by
    simpa [sub_eq_add_neg,neg_smul] using (hp C D).add (momentum_hermitian Z)
  have hs := (current_hermitian _ _ (hp A B) (hd A B)).add
    (current_hermitian _ _ hz (hd C D))
  unfold Matrix.IsHermitian spinSource
  rw [Matrix.conjTranspose_smul,hs.eq]
  simp

def clockS (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  (Real.sqrt (hbar/2) : ℂ) • (ladder r 0+(ladder r 0)ᴴ)

def clockPs (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  (Real.sqrt (hbar/2) : ℂ) • (-Complex.I • skew (ladder r 0))

def clockC (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  gram (halfPolynomial (clockS R r hbar))

def clockBase (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  polynomialLongitudinal (clockS R r hbar) (clockPs R r hbar)

theorem clockS_hermitian (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    (clockS R r hbar).IsHermitian := by
  unfold Matrix.IsHermitian clockS
  simp [add_comm]

theorem clockPs_hermitian (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    (clockPs R r hbar).IsHermitian := by
  unfold Matrix.IsHermitian clockPs
  rw [Matrix.conjTranspose_smul,(momentum_hermitian _).eq]
  simp

/-- Both half-clock factors are exactly the degree-two Taylor
polynomials used by the executable model. -/
theorem clock_function_polynomials (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    halfPolynomial (clockS R r hbar)=1+(1/2 : ℝ) • clockS R r hbar+
      (1/8 : ℝ) • (clockS R r hbar*clockS R r hbar) ∧
    halfPolynomial (-clockS R r hbar)=1-(1/2 : ℝ) • clockS R r hbar+
      (1/8 : ℝ) • (clockS R r hbar*clockS R r hbar) := by
  constructor
  · exact halfPolynomial_expansion _ (clockS_hermitian R r hbar)
  · simpa [sub_eq_add_neg] using halfPolynomial_expansion _ (clockS_hermitian R r hbar).neg

theorem clockC_positive (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : (clockC R r hbar).PosDef :=
  polynomial_clock_positive _

theorem clockS_neutral (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    HasCharge charge 0 (clockS R r hbar) := by
  have ha : HasCharge (charge (R := R)) 0 (ladder r 0) := by
    simpa [flavorCharge] using ladder_charge (R := R) r 0
  exact charge_smul charge 0 _ _ (charge_add charge _ _ ha
    (by simpa using charge_adjoint charge 0 _ ha))

theorem clockPs_neutral (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    HasCharge charge 0 (clockPs R r hbar) := by
  have ha : HasCharge (charge (R := R)) 0 (ladder r 0) := by
    simpa [flavorCharge] using ladder_charge (R := R) r 0
  exact charge_smul charge 0 _ _ (charge_smul charge 0 _ _
    (charge_sub charge 0 _ _ ha (by simpa using charge_adjoint charge 0 _ ha)))

theorem clockC_neutral (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    spatialDeriv charge (clockC R r hbar)=0 :=
  neutral_spatialDeriv charge _ (charge_gram charge _
    (charge_halfPolynomial charge _ (clockS_neutral R r hbar)))

theorem clockBase_neutral (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    spatialDeriv charge (clockBase R r hbar)=0 := by
  have hS := clockS_neutral R r hbar
  have hneg : HasCharge charge 0 (-clockS R r hbar) := by
    intro i j hij; simp [hS i j hij]
  have hD := charge_halfPolynomial charge _ hneg
  let A := halfPolynomial (-clockS R r hbar)*halfPolynomial (-clockS R r hbar)*clockPs R r hbar
  have hA : HasCharge charge 0 A := by
    simpa only [zero_add] using charge_mul charge 0 0 _ _
      (by simpa only [zero_add] using charge_mul charge 0 0 _ _ hD hD) (clockPs_neutral R r hbar)
  have hAd : HasCharge charge 0 Aᴴ := by
    simpa only [neg_zero] using charge_adjoint charge 0 A hA
  apply neutral_spatialDeriv
  change HasCharge charge 0 ((1/2 : ℝ) • (A+Aᴴ))
  exact charge_real_smul charge _ (1/2) (charge_add charge A Aᴴ hA hAd)

def longitudinal (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  reconstructed (clockC R r hbar) (clockC_positive R r hbar) charge
    (clockBase R r hbar) (source R r hbar)

def constraint (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  source R r hbar-matrixJordan (clockC R r hbar) (spatialDeriv charge (longitudinal R r hbar))

theorem longitudinal_hermitian (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    (longitudinal R r hbar).IsHermitian :=
  reconstructed_hermitian _ _ charge _ _ (symmetrize_hermitian _)
    (spin_source_hermitian hbar _ _ _ _ _)

theorem concrete_constraint_identity (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    constraint R r hbar=meanPart charge (source R r hbar) :=
  reconstructed_identity _ _ charge (clockC_neutral R r hbar) _ _ (clockBase_neutral R r hbar)

theorem concrete_constraint_sector (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    constraint R r hbar*sector charge 0=0 := by
  rw [concrete_constraint_identity]
  exact source_annihilates_zero R r hbar

/-- No externally supplied clock positivity, clock spectral basis,
homogeneous base or source-annihilation hypothesis occurs here. The
specified global time-dependent Schrodinger flow is still an input. -/
theorem concrete_continuous_constraint (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ)
    (H : ℝ → Matrix (State R) (State R) ℂ)
    (hH : ∀ t, (dephase charge (H t)).IsHermitian) (omega : ℝ)
    (U : ℝ → Matrix (State R) (State R) ℂ)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*(omega : ℂ)) • (dephase charge (H t)*U t)) t)
    (t₀ t : ℝ) (hinit : U t₀=1) (v : State R → ℂ)
    (hv : (sector charge 0).mulVec v=v) : (constraint R r hbar).mulVec ((U t).mulVec v)=0 :=
  constraint_continuous charge _ (concrete_constraint_sector R r hbar)
    H hH omega U hU t₀ t hinit v hv

#print axioms clockS_hermitian
#print axioms clockPs_hermitian
#print axioms clock_function_polynomials
#print axioms polynomial_clock_positive
#print axioms spin_source_hermitian
#print axioms clockC_positive
#print axioms clockC_neutral
#print axioms clockBase_neutral
#print axioms longitudinal_hermitian
#print axioms concrete_constraint_identity
#print axioms concrete_constraint_sector
#print axioms concrete_continuous_constraint

end
end UnifiedTheory.Audit.KFCausalConcreteClockConstraint
