/- Basis-independent positive-clock reconstruction. The spectral theorem
constructs the Jordan inverse using the clock alone. Translation covariance
is then proved in the original occupation basis, so no simultaneous
clock/charge eigenbasis is supplied as an assumption. -/
import UnifiedTheory.Audit.KFCausalSpinSourceIdentity
import UnifiedTheory.Audit.KFCausalQuantumArealCandidate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPositiveClockReconstruction
noncomputable section
open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

def matrixJordan (C X : M) : M := (1/2 : ℂ) • (C*X+X*C)

omit [DecidableEq n] in
theorem map_matrixJordan (E : M ≃⋆ₐ[ℂ] M) (C X : M) :
    E (matrixJordan C X)=matrixJordan (E C) (E X) := by
  simp [matrixJordan]

/-- This uses a clock spectral basis constructed by mathlib, with no
assumption that that chosen basis preserves translation charge. -/
def solveJordan (C : M) (hC : C.PosDef) (K : M) : M :=
  let E := Unitary.conjStarAlgAut ℂ M hC.isHermitian.eigenvectorUnitary
  E (inverseJordan hC.isHermitian.eigenvalues (E.symm K))

theorem solveJordan_spec (C : M) (hC : C.PosDef) (K : M) :
    matrixJordan C (solveJordan C hC K)=K := by
  let E := Unitary.conjStarAlgAut ℂ M hC.isHermitian.eigenvectorUnitary
  have hc : ∀ i, 0 < hC.isHermitian.eigenvalues i := hC.eigenvalues_pos
  have he : E (Matrix.diagonal (fun i => (hC.isHermitian.eigenvalues i : ℂ)))=C :=
    hC.isHermitian.spectral_theorem.symm
  change matrixJordan C (E (inverseJordan _ (E.symm K)))=K
  calc
    _ = matrixJordan (E (Matrix.diagonal (fun i => (hC.isHermitian.eigenvalues i : ℂ))))
        (E (inverseJordan _ (E.symm K))) := by rw [he]
    _ = E (matrixJordan (Matrix.diagonal (fun i => (hC.isHermitian.eigenvalues i : ℂ)))
        (inverseJordan _ (E.symm K))) := (map_matrixJordan E _ _).symm
    _ = E (E.symm K) := by
      rw [show matrixJordan (Matrix.diagonal (fun i => (hC.isHermitian.eigenvalues i : ℂ)))
          (inverseJordan _ (E.symm K)) = jordan hC.isHermitian.eigenvalues
          (inverseJordan _ (E.symm K)) from (jordan_is_anticommutator _ _).symm,
          jordan_inverse _ hc]
    _ = K := E.apply_symm_apply K

omit [Fintype n] [DecidableEq n] in
theorem jordan_injective (c : n → ℝ) (hc : ∀ i, 0 < c i) :
    Function.Injective (jordan c : M → M) := by
  intro A B h
  ext i j
  have he := congrFun (congrFun h i) j
  have hn : ((c i+c j : ℝ) : ℂ)/2 ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast ne_of_gt (add_pos (hc i) (hc j))
    · norm_num
  exact mul_left_cancel₀ hn he

theorem matrixJordan_injective (C : M) (hC : C.PosDef) :
    Function.Injective (matrixJordan C) := by
  let E := Unitary.conjStarAlgAut ℂ M hC.isHermitian.eigenvectorUnitary
  have he' : E (Matrix.diagonal (fun i => (hC.isHermitian.eigenvalues i : ℂ)))=C :=
    hC.isHermitian.spectral_theorem.symm
  have he : E.symm C=Matrix.diagonal (fun i => (hC.isHermitian.eigenvalues i : ℂ)) := by
    exact (congrArg E.symm he'.symm).trans (E.symm_apply_apply _)
  intro A B h
  apply E.symm.injective
  apply jordan_injective _ hC.eigenvalues_pos
  have hh : E.symm (matrixJordan C A)=E.symm (matrixJordan C B) := congrArg E.symm h
  rw [map_matrixJordan,map_matrixJordan,he] at hh
  simpa only [matrixJordan,← jordan_is_anticommutator] using hh

theorem solveJordan_unique (C : M) (hC : C.PosDef) (K X : M)
    (hX : matrixJordan C X=K) : X=solveJordan C hC K :=
  matrixJordan_injective C hC (hX.trans (solveJordan_spec C hC K).symm)

theorem solveJordan_hermitian (C : M) (hC : C.PosDef) (K : M) (hK : K.IsHermitian) :
    (solveJordan C hC K).IsHermitian := by
  apply matrixJordan_injective C hC
  rw [solveJordan_spec]
  have hh := congrArg Matrix.conjTranspose (solveJordan_spec C hC K)
  simpa [matrixJordan,hC.isHermitian.eq,hK.eq,add_comm] using hh.trans hK.eq

omit [Fintype n] [DecidableEq n] in
theorem spatialDeriv_add (q : n → ℤ) (A B : M) :
    spatialDeriv q (A+B)=spatialDeriv q A+spatialDeriv q B := by
  ext i j; simp [spatialDeriv,mul_add]

omit [Fintype n] [DecidableEq n] in
theorem spatialDeriv_smul (q : n → ℤ) (z : ℂ) (A : M) :
    spatialDeriv q (z • A)=z • spatialDeriv q A := by
  ext i j; simp only [spatialDeriv,Matrix.smul_apply,smul_eq_mul]; ring

omit [DecidableEq n] in
theorem spatialDeriv_mul (q : n → ℤ) (A B : M) :
    spatialDeriv q (A*B)=spatialDeriv q A*B+A*spatialDeriv q B := by
  ext i j
  simp only [spatialDeriv,Matrix.mul_apply,Matrix.add_apply,Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

omit [DecidableEq n] in
theorem spatialDeriv_matrixJordan (q : n → ℤ) (C X : M) (hC : spatialDeriv q C=0) :
    spatialDeriv q (matrixJordan C X)=matrixJordan C (spatialDeriv q X) := by
  simp [matrixJordan,spatialDeriv_smul,spatialDeriv_add,spatialDeriv_mul,hC]

def reconstructed (C : M) (hC : C.PosDef) (q : n → ℤ) (base source : M) : M :=
  base+solveJordan C hC (primitive q source)

/-- Exact local constraint in the original basis, with no spectral-basis
matrix or clock eigenvalues as inputs. -/
theorem reconstructed_identity (C : M) (hC : C.PosDef) (q : n → ℤ)
    (hCq : spatialDeriv q C=0) (base source : M) (hb : spatialDeriv q base=0) :
    source-matrixJordan C (spatialDeriv q (reconstructed C hC q base source))=
      meanPart q source := by
  rw [reconstructed,spatialDeriv_add,hb,zero_add,← spatialDeriv_matrixJordan q C _ hCq,
    solveJordan_spec,spatialDeriv_primitive]
  abel

theorem reconstructed_hermitian (C : M) (hC : C.PosDef) (q : n → ℤ)
    (base source : M) (hb : base.IsHermitian) (hs : source.IsHermitian) :
    (reconstructed C hC q base source).IsHermitian :=
  hb.add (solveJordan_hermitian C hC _ (primitive_hermitian q source hs))

#print axioms solveJordan_spec
#print axioms matrixJordan_injective
#print axioms solveJordan_unique
#print axioms solveJordan_hermitian
#print axioms spatialDeriv_mul
#print axioms reconstructed_identity
#print axioms reconstructed_hermitian

end
end UnifiedTheory.Audit.KFCausalPositiveClockReconstruction
