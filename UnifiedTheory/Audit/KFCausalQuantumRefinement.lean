/-
  Exact quantum refinement and its dynamical boundary.

  Tensor refinement preserves observable predictions and admits arbitrary
  unitary dynamics. Conversely, autonomous unitary evolution of the full
  retained matrix algebra forces a finite joint unitary to factor.
  This proves consistency and underdetermination, not a TOE or GR.
-/
import UnifiedTheory.LayerB.PartialTrace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalQuantumRefinement
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
open UnifiedTheory.LayerB.PartialTrace

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The same retained observable in a finer tensor description. -/
def liftObservable (A : Matrix m m ℂ) : Matrix (m × n) (m × n) ℂ := A ⊗ₖ 1

omit [DecidableEq m] in
theorem liftObservable_mul (A B : Matrix m m ℂ) :
    liftObservable (n := n) (A * B) = liftObservable A * liftObservable B := by
  simpa [liftObservable] using Matrix.mul_kronecker_mul A B
    (1 : Matrix n n ℂ) (1 : Matrix n n ℂ)

omit [DecidableEq m] in
theorem product_refinement_expectation (rho A : Matrix m m ℂ)
    (sigma : Matrix n n ℂ) (hsigma : sigma.trace = 1) :
    ((rho ⊗ₖ sigma) * liftObservable A).trace = (rho * A).trace := by
  rw [liftObservable, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.trace_kronecker, hsigma, mul_one]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem product_refinement_recovery (rho : Matrix m m ℂ)
    (sigma : Matrix n n ℂ) (hsigma : sigma.trace = 1) :
    partialTrace_right (rho ⊗ₖ sigma) = rho := by
  ext i j
  change (∑ k, rho i j * sigma k k) = rho i j
  rw [← Finset.mul_sum]
  change rho i j * sigma.trace = rho i j
  rw [hsigma, mul_one]

/-- Independent tensor factors commute exactly. This is a finite local
operation identity; it does not construct a spacetime light cone. -/
theorem disjoint_operations_commute (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    (A ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ B) =
      ((1 : Matrix m m ℂ) ⊗ₖ B) * (A ⊗ₖ (1 : Matrix n n ℂ)) := by
  simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem product_unitary_complete (U : Matrix m m ℂ) (W : Matrix n n ℂ)
    (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1) :
    (U ⊗ₖ W)ᴴ * (U ⊗ₖ W) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    hU, hW, Matrix.one_kronecker_one]

omit [DecidableEq m] in
/-- Every unitary U is admitted: consistency alone does not select its
eigenvalues, a Hamiltonian, or the dimension of the retained system. -/
theorem arbitrary_unitary_refinement (U A : Matrix m m ℂ)
    (W : Matrix n n ℂ) (hW : Wᴴ * W = 1) :
    (U ⊗ₖ W)ᴴ * liftObservable A * (U ⊗ₖ W) =
      liftObservable (Uᴴ * A * U) := by
  rw [liftObservable, liftObservable, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, hW]

private theorem lifted_single_left (a b i j : m) (k l : n)
    (T : Matrix (m × n) (m × n) ℂ) :
    (liftObservable (n := n) (Matrix.single a b (1 : ℂ)) * T) (i,k) (j,l) =
      if a = i then T (b,k) (j,l) else 0 := by
  classical
  by_cases h : a = i
  · subst i
    simp [liftObservable, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.single_apply, Matrix.one_apply]
  · simp [liftObservable, Matrix.mul_apply, Matrix.one_apply, h]

private theorem lifted_single_right (a b i j : m) (k l : n)
    (T : Matrix (m × n) (m × n) ℂ) :
    (T * liftObservable (n := n) (Matrix.single a b (1 : ℂ))) (i,k) (j,l) =
      if b = j then T (i,k) (a,l) else 0 := by
  classical
  by_cases h : b = j
  · subst j
    simp [liftObservable, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.single_apply, Matrix.one_apply]
  · simp [liftObservable, Matrix.mul_apply, Matrix.one_apply, h]

/-- The commutant of the complete retained matrix algebra is precisely
the discarded matrix algebra. The witness is an explicit diagonal block. -/
theorem retained_commutant_factor (i0 : m)
    (T : Matrix (m × n) (m × n) ℂ)
    (hT : ∀ A : Matrix m m ℂ, liftObservable A * T = T * liftObservable A) :
    T = (1 : Matrix m m ℂ) ⊗ₖ (fun k l => T (i0,k) (i0,l)) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hij : i = j
  · subst j
    have h := congrFun (congrFun (hT (Matrix.single i i0 1)) (i,k)) (i0,l)
    rw [lifted_single_left, lifted_single_right] at h
    simpa [Matrix.kronecker_apply, Matrix.one_apply] using h.symm
  · have h := congrFun (congrFun (hT (Matrix.single i i 1)) (i,k)) (j,l)
    rw [lifted_single_left, lifted_single_right] at h
    simpa [Matrix.kronecker_apply, Matrix.one_apply, hij] using h

/-- Exact autonomous unitary evolution of every retained observable
forces the joint unitary to be a product. No interaction remains between
retained and discarded factors under these universal hypotheses. -/
theorem autonomous_unitary_factor (i0 : m)
    (Q : Matrix (m × n) (m × n) ℂ) (U : Matrix m m ℂ)
    (hQ : Qᴴ * Q = 1) (hU : Uᴴ * U = 1)
    (hAut : ∀ A : Matrix m m ℂ,
      Qᴴ * liftObservable A * Q = liftObservable (Uᴴ * A * U)) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ Q = U ⊗ₖ W := by
  have hQr : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQ
  let L : Matrix (m × n) (m × n) ℂ := liftObservable U
  have hL : Lᴴ * L = 1 := by
    simpa [L, liftObservable] using product_unitary_complete U (1 : Matrix n n ℂ) hU (by simp)
  have hLr : L * Lᴴ = 1 := mul_eq_one_comm.mp hL
  have hLAut (A : Matrix m m ℂ) :
      Lᴴ * liftObservable A * L = liftObservable (Uᴴ * A * U) := by
    simpa [L, liftObservable] using arbitrary_unitary_refinement U A (1 : Matrix n n ℂ) (by simp)
  let T := Q * Lᴴ
  have hcomm (A : Matrix m m ℂ) : liftObservable A * T = T * liftObservable A := by
    have h := hAut A
    rw [← hLAut A] at h
    have hh := congrArg (fun X => Q * X * Lᴴ) h
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc Q Qᴴ, hQr,
      Matrix.one_mul, ← Matrix.mul_assoc L Lᴴ, hLr, Matrix.mul_one, T] using hh
  let W : Matrix n n ℂ := fun k l => T (i0,k) (i0,l)
  have hT : T = (1 : Matrix m m ℂ) ⊗ₖ W := retained_commutant_factor i0 T hcomm
  have hfactor : Q = U ⊗ₖ W := by
    calc
      Q = T * L := by simp only [T, Matrix.mul_assoc, hL, Matrix.mul_one]
      _ = ((1 : Matrix m m ℂ) ⊗ₖ W) * (U ⊗ₖ (1 : Matrix n n ℂ)) := by rw [hT]; rfl
      _ = _ := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  refine ⟨W, ?_, hfactor⟩
  rw [hfactor, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU] at hQ
  ext k l
  have hh := congrFun (congrFun hQ (i0,k)) (i0,l)
  simpa [Matrix.kronecker_apply, Matrix.one_apply] using hh

theorem autonomous_unitary_iff_product (i0 : m)
    (Q : Matrix (m × n) (m × n) ℂ) (U : Matrix m m ℂ)
    (hQ : Qᴴ * Q = 1) (hU : Uᴴ * U = 1) :
    (∀ A : Matrix m m ℂ,
      Qᴴ * liftObservable A * Q = liftObservable (Uᴴ * A * U)) ↔
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ Q = U ⊗ₖ W := by
  constructor
  · exact autonomous_unitary_factor i0 Q U hQ hU
  · rintro ⟨W, hW, rfl⟩ A
    exact arbitrary_unitary_refinement U A W hW

omit [DecidableEq m] [DecidableEq n] in
/-- Matrix positivity and normalization hold at every tensor-refinement
step, supplying an actual density matrix rather than a formal weight. -/
theorem product_refinement_density (rho : Matrix m m ℂ) (sigma : Matrix n n ℂ)
    (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (htr : rho.trace = 1) (hts : sigma.trace = 1) :
    (rho ⊗ₖ sigma).PosSemidef ∧ (rho ⊗ₖ sigma).trace = 1 := by
  exact ⟨hrho.kronecker hsigma, by rw [Matrix.trace_kronecker, htr, hts, mul_one]⟩

theorem product_evolution_all_steps (U : Matrix m m ℂ) (W : Matrix n n ℂ)
    (k : ℕ) : (U ⊗ₖ W) ^ k = (U ^ k) ⊗ₖ (W ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, ← Matrix.mul_kronecker_mul, ← pow_succ, ← pow_succ]

/-- A unitary change of encoding preserves the full logical observable
algebra, including noncommuting observables. -/
theorem encoded_refinement (S : Matrix (m × n) (m × n) ℂ)
    (hS : Sᴴ * S = 1) (U A : Matrix m m ℂ)
    (W : Matrix n n ℂ) (hW : Wᴴ * W = 1) :
    (S * (U ⊗ₖ W) * Sᴴ)ᴴ * (S * liftObservable A * Sᴴ) *
      (S * (U ⊗ₖ W) * Sᴴ) = S * liftObservable (Uᴴ * A * U) * Sᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hc (B C : Matrix (m × n) (m × n) ℂ) :
      (S * B * Sᴴ) * (S * C * Sᴴ) = S * (B * C) * Sᴴ := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Sᴴ S, hS, Matrix.one_mul]
  rw [← Matrix.mul_assoc S (U ⊗ₖ W)ᴴ Sᴴ, hc, hc,
    arbitrary_unitary_refinement U A W hW]

section Qubit
abbrev Qubit := Fin 2
abbrev QubitMatrix := Matrix Qubit Qubit ℂ

def zeroState : QubitMatrix := !![1, 0; 0, 0]
def plusState : QubitMatrix := fun _ _ => 1/2
def phaseGate : QubitMatrix := !![1, 0; 0, Complex.I]
def flipGate : QubitMatrix := !![0, 1; 1, 0]

theorem phaseGate_complete : phaseGateᴴ * phaseGate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phaseGate, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Complex.I_sq]

theorem flipGate_complete : flipGateᴴ * flipGate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flipGate, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- Both gates satisfy the general refinement construction but make
opposite predictions for this fixed input and fixed projective test. -/
theorem refinement_does_not_select_prediction :
    (phaseGate * zeroState * phaseGateᴴ) 0 0 = 1 ∧
      (flipGate * zeroState * flipGateᴴ) 0 0 = 0 := by
  norm_num [phaseGate, flipGate, zeroState, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]

def cnot : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ :=
  fun i j => if i = (j.1, j.1 + j.2) then 1 else 0

theorem cnot_self_adjoint : cnotᴴ = cnot := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [cnot, Matrix.conjTranspose_apply, Fin.ext_iff, Fin.val_add]

theorem cnot_involutive : cnot * cnot = 1 := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [cnot, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.ext_iff, Fin.val_add]

def diagonalChannel (rho : QubitMatrix) : QubitMatrix :=
  fun i j => if i = j then rho i j else 0

/-- A fixed product preparation gives a valid one-step reduced channel. -/
theorem cnot_prepared_step (rho : QubitMatrix) :
    partialTrace_right (cnot * (rho ⊗ₖ zeroState) * cnotᴴ) = diagonalChannel rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTrace_right, diagonalChannel, cnot, zeroState,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Reusing the same discarded qubit restores the initial joint state
after two steps; iterating the reduced channel loses that memory. -/
theorem cnot_memory_counterexample :
    partialTrace_right
      (cnot * (cnot * (plusState ⊗ₖ zeroState) * cnotᴴ) * cnotᴴ) = plusState ∧
    diagonalChannel (diagonalChannel plusState) ≠ plusState := by
  constructor
  · rw [cnot_self_adjoint]
    have h (X : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) :
        cnot * (cnot * X * cnot) * cnot = X := by
      calc
        _ = (cnot * cnot) * X * (cnot * cnot) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [cnot_involutive, Matrix.one_mul, Matrix.mul_one]
    rw [h]
    exact product_refinement_recovery plusState zeroState (by norm_num [zeroState, Matrix.trace, Fin.sum_univ_two])
  · intro h
    have hh := congrFun (congrFun h 0) 1
    norm_num [diagonalChannel, plusState] at hh
end Qubit

#print axioms product_refinement_expectation
#print axioms product_refinement_recovery
#print axioms disjoint_operations_commute
#print axioms product_unitary_complete
#print axioms arbitrary_unitary_refinement
#print axioms retained_commutant_factor
#print axioms autonomous_unitary_factor
#print axioms product_refinement_density
#print axioms product_evolution_all_steps
#print axioms encoded_refinement
#print axioms refinement_does_not_select_prediction
#print axioms cnot_prepared_step
#print axioms cnot_memory_counterexample

end
end UnifiedTheory.Audit.KFCausalQuantumRefinement
