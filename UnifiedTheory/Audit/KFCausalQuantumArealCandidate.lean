/-
  A specified finite quantum candidate for the homogeneous reduced
  gravity/scalar Hamiltonian, with explicit positive operator ordering.
  Its polynomial clock construction is nonsingular in every finite
  dimension. This is a model definition, not a deduction from the old
  microscopic law or a quantum gravitational constraint algebra.

  A separate trace theorem exposes why globally positive clock force
  cannot hold in a nontrivial finite quantum clock: the classical
  monotonicity must be recovered only in controlled families of states.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalQuantumArealCandidate
noncomputable section
open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

/-- Classical positive branch c=exp(s), L=p/c. Since {L,c}=-1,
(s,p) is a canonical chart for the original pair (L,-c). -/
theorem positive_clock_chart (s : ℝ) :
    0 < Real.exp s ∧ -(Real.exp (-s))*Real.exp s = -1 := by
  constructor
  · exact Real.exp_pos s
  · rw [neg_mul, ← Real.exp_add]
    simp

theorem clock_chart_one_form (c L dc dL : ℝ) (hc : c ≠ 0) :
    -c*dL = (c*L)*(dc/c)-(c*dL+L*dc) := by field_simp; ring

/-- The canonical change reproduces both backreaction equations. -/
theorem clock_chart_backreaction (c L E W ds dp : ℝ) (hc : c ≠ 0)
    (hs : ds=W/c^2) (hp : dp= -c/2+E/(2*c)+(1+L)*W/c) :
    c*ds=W/c ∧ dp/c-L*ds= -1/2+(E+2*W)/(2*c^2) := by
  rw [hs, hp]
  constructor
  · field_simp
  · field_simp
    ring

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

def gram (A : M) : M := Aᴴ*A

omit [DecidableEq n] in
theorem gram_positive (A : M) : (gram A).PosSemidef := posSemidef_conjTranspose_mul_self A

/-- For Hermitian S this is 1+S/2+S²/8, the second-order exp(S/2)
polynomial. The Gram form also makes its positive floor transparent. -/
def halfPolynomial (S : M) : M :=
  (1/2 : ℝ) • (1 : M)+(1/8 : ℝ) • gram (S+(2 : ℝ) • (1 : M))

theorem halfPolynomial_positive (S : M) : (halfPolynomial S).PosSemidef :=
  ((Matrix.PosSemidef.one : (1 : M).PosSemidef).smul (by norm_num : (0 : ℝ) ≤ 1/2)).add
    ((gram_positive _).smul (by norm_num : (0 : ℝ) ≤ 1/8))

theorem halfPolynomial_expansion (S : M) (hS : S.IsHermitian) :
    halfPolynomial S = 1+(1/2 : ℝ) • S+(1/8 : ℝ) • (S*S) := by
  simp [halfPolynomial, gram, Matrix.conjTranspose_add, hS.eq,
    mul_add, add_mul, smul_smul]
  module

theorem halfPolynomial_clock_floor (S : M) :
    (gram (halfPolynomial S)-(1/4 : ℝ) • (1 : M)).PosSemidef := by
  let K : M := (1/8 : ℝ) • gram (S+(2 : ℝ) • (1 : M))
  have hK : K.PosSemidef := (gram_positive _).smul (by norm_num : (0 : ℝ) ≤ 1/8)
  have he : gram (halfPolynomial S)-(1/4 : ℝ) • (1 : M) = K+gram K := by
    change gram ((1/2 : ℝ) • (1 : M)+K)-(1/4 : ℝ) • (1 : M) = K+gram K
    simp [gram, Matrix.conjTranspose_add, hK.isHermitian.eq,
      mul_add, add_mul, smul_smul]
    module
  rw [he]
  exact hK.add (gram_positive K)

def symmetrize (A : M) : M := (1/2 : ℝ) • (A+Aᴴ)

omit [Fintype n] [DecidableEq n] in
theorem symmetrize_hermitian (A : M) : (symmetrize A).IsHermitian := by
  unfold Matrix.IsHermitian symmetrize
  simp [add_comm]

/-- D approximates exp(-S/2); L approximates the symmetric quantization
of p/c. All operations here have fixed polynomial degree. -/
def polynomialLongitudinal (S Ps : M) : M :=
  symmetrize (halfPolynomial (-S)*halfPolynomial (-S)*Ps)

def staticHamiltonian (F D P pi : M) : M :=
  (1/2 : ℝ) • gram F+(1/2 : ℝ) • gram (P*D)+(1/2 : ℝ) • gram (pi*D)

def potentialHamiltonian (D E phi : M) (mass2 quartic vacuum : ℝ) : M :=
  (mass2/2) • gram (phi*E*D)+(quartic/4) • gram (phi*phi*E*D)+
    vacuum • gram (E*D)

def orderedHamiltonian (F D E P pi phi : M) (mass2 quartic vacuum t : ℝ) : M :=
  staticHamiltonian F D P pi+
    Real.exp (2*t) • potentialHamiltonian D E phi mass2 quartic vacuum

omit [DecidableEq n] in
theorem staticHamiltonian_positive (F D P pi : M) :
    (staticHamiltonian F D P pi).PosSemidef := by
  apply Matrix.PosSemidef.add
  · exact ((gram_positive F).smul (by norm_num : (0 : ℝ) ≤ 1/2)).add
      ((gram_positive (P*D)).smul (by norm_num : (0 : ℝ) ≤ 1/2))
  · exact (gram_positive (pi*D)).smul (by norm_num : (0 : ℝ) ≤ 1/2)

omit [DecidableEq n] in
theorem potentialHamiltonian_positive (D E phi : M) (mass2 quartic vacuum : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (potentialHamiltonian D E phi mass2 quartic vacuum).PosSemidef :=
  (((gram_positive _).smul (by positivity : 0 ≤ mass2/2)).add
    ((gram_positive _).smul (by positivity : 0 ≤ quartic/4))).add
      ((gram_positive _).smul hv)

omit [DecidableEq n] in
/-- Positivity holds without assuming that the finite-spin clock and
matter matrices commute. Their ordering is fixed by these Gram factors. -/
theorem orderedHamiltonian_positive (F D E P pi phi : M) (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (orderedHamiltonian F D E P pi phi mass2 quartic vacuum t).PosSemidef :=
  (staticHamiltonian_positive F D P pi).add
    ((potentialHamiltonian_positive D E phi mass2 quartic vacuum hm hq hv).smul
      (Real.exp_pos _).le)

omit [DecidableEq n] in
/-- Covers a supplied finite graph, including the common-coefficient
gradient factors. It imposes no quantum spatial constraint. -/
theorem graph_gram_sum_positive {ι : Type*} (edges : Finset ι) (factors : ι → M) :
    (∑ i ∈ edges, gram (factors i)).PosSemidef :=
  Matrix.posSemidef_sum edges (fun i _ => gram_positive (factors i))

def polynomialHamiltonian (S Ps P pi phi : M) (mass2 quartic vacuum t : ℝ) : M :=
  orderedHamiltonian (halfPolynomial S) (halfPolynomial (-S))
    (halfPolynomial (polynomialLongitudinal S Ps)) P pi phi mass2 quartic vacuum t

theorem polynomialHamiltonian_positive (S Ps P pi phi : M) (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (polynomialHamiltonian S Ps P pi phi mass2 quartic vacuum t).PosSemidef :=
  orderedHamiltonian_positive _ _ _ _ _ _ _ _ _ _ hm hq hv

/-- Frozen-time exponential steps are unitary. Products of these steps
give the numerical integrator; time-discretization error is separate. -/
theorem hermitian_step_unitary (H : M) (hH : H.IsHermitian) (step : ℝ) :
    NormedSpace.exp (Complex.I • (step • H)) ∈ unitary M := by
  letI : NormedAlgebra ℚ M := NormedAlgebra.restrictScalars ℚ ℂ M
  have hself : IsSelfAdjoint (step • H) := by
    change (step • H)ᴴ = step • H
    simp [hH.eq]
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (hself.smul_mem_skewAdjoint Complex.conj_I)

/-- Heisenberg clock force. It has zero trace for every finite model. -/
def clockForce (H C : M) (hbar : ℝ) : M :=
  (Complex.I/(hbar : ℂ)) • (H*C-C*H)

omit [DecidableEq n] in
theorem clockForce_hermitian (H C : M) (hbar : ℝ)
    (hH : H.IsHermitian) (hC : C.IsHermitian) : (clockForce H C hbar).IsHermitian := by
  unfold Matrix.IsHermitian clockForce
  simp [hH.eq, hC.eq, neg_div, sub_eq_add_neg, add_comm]

omit [DecidableEq n] in
theorem clockForce_trace_zero (H C : M) (hbar : ℝ) :
    (clockForce H C hbar).trace = 0 := by
  simp [clockForce, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm H C]

omit [DecidableEq n] in
theorem nonnegative_clockForce_is_zero (H C : M) (hbar : ℝ)
    (hF : (clockForce H C hbar).PosSemidef) : clockForce H C hbar = 0 :=
  hF.trace_eq_zero_iff.mp (clockForce_trace_zero H C hbar)

theorem nontrivial_clockForce_has_negative_eigenvalue (H C : M) (hbar : ℝ)
    (hF : (clockForce H C hbar).IsHermitian) (hne : clockForce H C hbar ≠ 0) :
    ∃ i, hF.eigenvalues i < 0 := by
  by_contra h
  push_neg at h
  exact hne (nonnegative_clockForce_is_zero H C hbar
    (hF.posSemidef_iff_eigenvalues_nonneg.mpr h))

#print axioms positive_clock_chart
#print axioms clock_chart_one_form
#print axioms clock_chart_backreaction
#print axioms halfPolynomial_expansion
#print axioms halfPolynomial_clock_floor
#print axioms symmetrize_hermitian
#print axioms orderedHamiltonian_positive
#print axioms graph_gram_sum_positive
#print axioms polynomialHamiltonian_positive
#print axioms hermitian_step_unitary
#print axioms clockForce_hermitian
#print axioms clockForce_trace_zero
#print axioms nonnegative_clockForce_is_zero
#print axioms nontrivial_clockForce_has_negative_eigenvalue

end
end UnifiedTheory.Audit.KFCausalQuantumArealCandidate
