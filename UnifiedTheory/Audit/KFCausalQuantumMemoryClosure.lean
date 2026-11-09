/-
  An exact interacting reduction with derived retained memory.

  Pinching into the eigenspaces of a conserved involution commutes with
  every allowed operation, including nonunitary measurement branches.
  For CNOT the smallest invariant star algebra containing all system
  observables also contains the target's X record. The resulting reduction
  preserves arbitrary finite experiment probabilities without resetting it.
  This is a finite quantum model, not a causal-growth or gravity derivation.
-/
import UnifiedTheory.Audit.KFCausalQuantumRefinement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalQuantumMemoryClosure
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
open UnifiedTheory.LayerB.PartialTrace
open UnifiedTheory.Audit.KFCausalQuantumRefinement

section General
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Operator" => Matrix ι ι ℂ

def memoryProjection (J rho : Operator) : Operator :=
  (1/2 : ℂ) • (rho + J * rho * J)

def plusProjector (J : Operator) : Operator := (1/2 : ℂ) • (1 + J)
def minusProjector (J : Operator) : Operator := (1/2 : ℂ) • (1 - J)

theorem memoryProjection_kraus (J rho : Operator) (hJ : Jᴴ = J) :
    memoryProjection J rho =
      plusProjector J * rho * (plusProjector J)ᴴ +
      minusProjector J * rho * (minusProjector J)ᴴ := by
  have hc : star (1/2 : ℂ) = (1/2 : ℂ) := by norm_num
  simp only [memoryProjection, plusProjector, minusProjector,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hJ, hc,
    Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one]
  module

theorem memoryProjectors_complete (J : Operator) (hJ : Jᴴ = J) (hJJ : J * J = 1) :
    (plusProjector J)ᴴ * plusProjector J +
      (minusProjector J)ᴴ * minusProjector J = 1 := by
  have hc : star (1/2 : ℂ) = (1/2 : ℂ) := by norm_num
  simp only [plusProjector, minusProjector,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hJ, hc,
    Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, hJJ]
  module

theorem memoryProjection_positive (J rho : Operator) (hJ : Jᴴ = J)
    (hrho : rho.PosSemidef) : (memoryProjection J rho).PosSemidef := by
  rw [memoryProjection_kraus J rho hJ]
  exact (hrho.mul_mul_conjTranspose_same _).add (hrho.mul_mul_conjTranspose_same _)

theorem memoryProjection_trace (J rho : Operator) (hJJ : J * J = 1) :
    (memoryProjection J rho).trace = rho.trace := by
  have h : (J * rho * J).trace = rho.trace := by
    rw [Matrix.trace_mul_cycle, hJJ, Matrix.one_mul]
  simp only [memoryProjection, Matrix.trace_smul, Matrix.trace_add, h, smul_eq_mul]
  ring

theorem memoryProjection_fixed (J rho : Operator) (hJJ : J * J = 1)
    (hcomm : rho * J = J * rho) : memoryProjection J rho = rho := by
  have h : J * rho * J = rho := by
    rw [← hcomm, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  rw [memoryProjection, h]
  module

theorem memoryProjection_commutes (J rho : Operator) (hJJ : J * J = 1) :
    memoryProjection J rho * J = J * memoryProjection J rho := by
  have hleft : (J * rho * J) * J = J * rho := by
    simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hright : J * (J * rho * J) = rho * J := by
    simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  simp only [memoryProjection, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, hleft, hright, add_comm]

theorem memoryProjection_idempotent (J rho : Operator) (hJJ : J * J = 1) :
    memoryProjection J (memoryProjection J rho) = memoryProjection J rho :=
  memoryProjection_fixed J _ hJJ (memoryProjection_commutes J rho hJJ)

omit [DecidableEq ι] in
/-- One outcome operator can be nonunitary. Commuting with the conserved
record is sufficient; no normalization of this individual branch is assumed. -/
theorem memoryProjection_intertwines (J K rho : Operator) (hJ : Jᴴ = J)
    (hK : K * J = J * K) :
    memoryProjection J (K * rho * Kᴴ) = K * memoryProjection J rho * Kᴴ := by
  have hKd : Kᴴ * J = J * Kᴴ := by
    have h := congrArg Matrix.conjTranspose hK
    simpa only [Matrix.conjTranspose_mul, hJ] using h.symm
  have hs : J * (K * rho * Kᴴ) * J = K * (J * rho * J) * Kᴴ := by
    calc
      _ = (J * K) * rho * (Kᴴ * J) := by simp only [Matrix.mul_assoc]
      _ = (K * J) * rho * (J * Kᴴ) := by rw [hK, hKd]
      _ = _ := by simp only [Matrix.mul_assoc]
  simp only [memoryProjection, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, hs]

def runBranch : List Operator → Operator → Operator
  | [], rho => rho
  | K :: rest, rho => runBranch rest (K * rho * Kᴴ)

omit [DecidableEq ι] in
/-- Exact commutation holds for arbitrary finite intervention histories. -/
theorem memoryProjection_all_branches (J : Operator) (hJ : Jᴴ = J)
    (ops : List Operator) (hops : ∀ K ∈ ops, K * J = J * K) (rho : Operator) :
    memoryProjection J (runBranch ops rho) = runBranch ops (memoryProjection J rho) := by
  induction ops generalizing rho with
  | nil => rfl
  | cons K rest ih =>
    simp only [runBranch]
    rw [ih (fun L hL => hops L (List.mem_cons_of_mem K hL)),
      memoryProjection_intertwines J K rho hJ (hops K (by simp))]

/-- For complete physical instruments, these traces are the joint
probabilities of recorded branches. Equality holds before any conditioning. -/
theorem all_branch_probabilities_preserved (J : Operator)
    (hJ : Jᴴ = J) (hJJ : J * J = 1) (ops : List Operator)
    (hops : ∀ K ∈ ops, K * J = J * K) (rho : Operator) :
    (runBranch ops (memoryProjection J rho)).trace = (runBranch ops rho).trace := by
  rw [← memoryProjection_all_branches J hJ ops hops rho, memoryProjection_trace J _ hJJ]
end General

abbrev Joint := Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ

def memoryFlip : Joint := (1 : QubitMatrix) ⊗ₖ flipGate

theorem memoryFlip_self_adjoint : memoryFlipᴴ = memoryFlip := by
  have hx : flipGateᴴ = flipGate := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [flipGate, Matrix.conjTranspose_apply]
  simp only [memoryFlip, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hx]

theorem memoryFlip_involutive : memoryFlip * memoryFlip = 1 := by
  have h := product_unitary_complete (1 : QubitMatrix) flipGate (by simp) flipGate_complete
  change memoryFlipᴴ * memoryFlip = 1 at h
  rwa [memoryFlip_self_adjoint] at h

theorem system_operation_commutes (K : QubitMatrix) :
    liftObservable (n := Qubit) K * memoryFlip = memoryFlip * liftObservable K :=
  disjoint_operations_commute K flipGate

set_option maxRecDepth 4096 in
/-- The conserved record is generated by a system observable and its
one-step Heisenberg image. It is therefore forced by algebraic closure. -/
theorem cnot_exposes_memory :
    liftObservable flipGate * (cnotᴴ * liftObservable flipGate * cnot) = memoryFlip := by
  rw [cnot_self_adjoint]
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [cnot, memoryFlip, flipGate, liftObservable, Matrix.mul_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.ext_iff, Fin.val_add]

def memoryAlgebra : StarSubalgebra ℂ Joint :=
  StarAlgebra.adjoin ℂ (Set.range (liftObservable (m := Qubit) (n := Qubit)) ∪ {memoryFlip})

theorem system_observable_mem (A : QubitMatrix) : liftObservable A ∈ memoryAlgebra :=
  StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨A, rfl⟩)

theorem memoryFlip_mem : memoryFlip ∈ memoryAlgebra :=
  StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)

theorem cnot_decomposition :
    cnot = liftObservable zeroState + liftObservable (1-zeroState) * memoryFlip := by
  simp only [liftObservable, memoryFlip, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul]
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [cnot, zeroState, flipGate, Matrix.one_apply, Fin.ext_iff, Fin.val_add]

theorem cnot_mem : cnot ∈ memoryAlgebra := by
  rw [cnot_decomposition]
  exact add_mem (system_observable_mem _) (mul_mem (system_observable_mem _) memoryFlip_mem)

theorem memoryAlgebra_invariant (A : Joint) (hA : A ∈ memoryAlgebra) :
    cnotᴴ * A * cnot ∈ memoryAlgebra :=
  mul_mem (mul_mem (star_mem cnot_mem) hA) cnot_mem

/-- Minimality is among star algebras containing all system observables
and invariant under the specified interaction. It is not a universal lower
bound for every possible representation of a prediction problem. -/
theorem memoryAlgebra_minimal (S : StarSubalgebra ℂ Joint)
    (hSystem : ∀ A : QubitMatrix, liftObservable A ∈ S)
    (hEvolution : ∀ A ∈ S, cnotᴴ * A * cnot ∈ S) : memoryAlgebra ≤ S := by
  have hJ : memoryFlip ∈ S := by
    rw [← cnot_exposes_memory]
    exact mul_mem (hSystem flipGate) (hEvolution _ (hSystem flipGate))
  apply StarAlgebra.adjoin_le
  rintro X (⟨A, rfl⟩ | hX)
  · exact hSystem A
  · simpa only [Set.mem_singleton_iff.mp hX] using hJ

theorem memoryAlgebra_commutes (A : Joint) (hA : A ∈ memoryAlgebra) :
    A * memoryFlip = memoryFlip * A := by
  have hle : memoryAlgebra ≤ StarSubalgebra.centralizer ℂ {memoryFlip} := by
    apply StarAlgebra.adjoin_le
    rintro X (⟨B, rfl⟩ | hX)
    · apply (StarSubalgebra.mem_centralizer_iff ℂ).2
      intro J hJ
      have hj : J = memoryFlip := Set.mem_singleton_iff.mp hJ
      subst J
      exact ⟨(system_operation_commutes B).symm, by
        change memoryFlipᴴ * _ = _ * memoryFlipᴴ
        rw [memoryFlip_self_adjoint]
        exact (system_operation_commutes B).symm⟩
    · have hx : X = memoryFlip := Set.mem_singleton_iff.mp hX
      subst X
      apply (StarSubalgebra.mem_centralizer_iff ℂ).2
      intro J hJ
      have hj : J = memoryFlip := Set.mem_singleton_iff.mp hJ
      subst J
      exact ⟨rfl, by change memoryFlipᴴ * _ = _ * memoryFlipᴴ; rw [memoryFlip_self_adjoint]⟩
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).1 (hle hA) memoryFlip rfl).1.symm

theorem cnot_commutes_memory : cnot * memoryFlip = memoryFlip * cnot :=
  memoryAlgebra_commutes cnot cnot_mem

def diagonalMemoryBlock (rho : Joint) : QubitMatrix :=
  fun i j => (rho (i,0) (j,0) + rho (i,1) (j,1))/2
def offDiagonalMemoryBlock (rho : Joint) : QubitMatrix :=
  fun i j => (rho (i,0) (j,1) + rho (i,1) (j,0))/2

theorem memoryProjection_expansion (rho : Joint) :
    memoryProjection memoryFlip rho = liftObservable (diagonalMemoryBlock rho) +
      liftObservable (offDiagonalMemoryBlock rho) * memoryFlip := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases k <;> fin_cases l <;>
    simp [memoryProjection, diagonalMemoryBlock, offDiagonalMemoryBlock,
      memoryFlip, flipGate, liftObservable, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, smul_eq_mul] <;> ring

theorem memoryProjection_mem (rho : Joint) : memoryProjection memoryFlip rho ∈ memoryAlgebra := by
  rw [memoryProjection_expansion]
  exact add_mem (system_observable_mem _) (mul_mem (system_observable_mem _) memoryFlip_mem)

/-- The actual positive reduction has exactly the derived minimal algebra
as its fixed-point range. No desired closure is assumed in this statement. -/
theorem memoryProjection_fixed_iff (rho : Joint) :
    memoryProjection memoryFlip rho = rho ↔ rho ∈ memoryAlgebra := by
  constructor
  · intro h
    rw [← h]
    exact memoryProjection_mem rho
  · intro h
    exact memoryProjection_fixed memoryFlip rho memoryFlip_involutive (memoryAlgebra_commutes rho h)

theorem memoryProjection_preserves_system (rho : Joint) :
    partialTrace_right (memoryProjection memoryFlip rho) = partialTrace_right rho := by
  ext i j
  simp [memoryProjection, memoryFlip, flipGate, partialTrace_right, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, smul_eq_mul]
  ring

theorem cnot_with_memory_all_branches (ops : List Joint)
    (hops : ∀ K ∈ ops, K * memoryFlip = memoryFlip * K) (rho : Joint) :
    (runBranch ops (memoryProjection memoryFlip rho)).trace = (runBranch ops rho).trace :=
  all_branch_probabilities_preserved memoryFlip memoryFlip_self_adjoint memoryFlip_involutive ops hops rho

/-- Every finite sequence of the interaction and arbitrary system outcome
operators has identical branch probabilities and final system matrices.
The extra qubit is never reset. -/
theorem cnot_system_history_exact (ops : List Joint)
    (hops : ∀ K ∈ ops, K = cnot ∨ ∃ L : QubitMatrix, K = liftObservable L)
    (rho : Joint) :
    (runBranch ops (memoryProjection memoryFlip rho)).trace = (runBranch ops rho).trace ∧
    partialTrace_right (runBranch ops (memoryProjection memoryFlip rho)) =
      partialTrace_right (runBranch ops rho) := by
  have hcomm : ∀ K ∈ ops, K * memoryFlip = memoryFlip * K := by
    intro K hK
    rcases hops K hK with rfl | ⟨L, rfl⟩
    · exact cnot_commutes_memory
    · exact system_operation_commutes L
  constructor
  · exact cnot_with_memory_all_branches ops hcomm rho
  · rw [← memoryProjection_all_branches memoryFlip memoryFlip_self_adjoint ops hcomm rho]
    exact memoryProjection_preserves_system _

#print axioms memoryProjection_kraus
#print axioms memoryProjectors_complete
#print axioms memoryProjection_positive
#print axioms memoryProjection_trace
#print axioms memoryProjection_idempotent
#print axioms memoryProjection_all_branches
#print axioms all_branch_probabilities_preserved
#print axioms cnot_exposes_memory
#print axioms memoryAlgebra_invariant
#print axioms memoryAlgebra_minimal
#print axioms memoryProjection_fixed_iff
#print axioms memoryProjection_preserves_system
#print axioms cnot_with_memory_all_branches
#print axioms cnot_system_history_exact

end
end UnifiedTheory.Audit.KFCausalQuantumMemoryClosure
