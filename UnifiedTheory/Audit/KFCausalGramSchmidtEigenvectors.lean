/- Orthonormalization preserves prescribed unitary eigencharacters.
The input need not be orthogonal and eigencharacters may coincide. -/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGramSchmidtEigenvectors
noncomputable section
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem eigen_inner (U : H ≃ₗᵢ[ℂ] H) (x y : H) (α β : ℂ)
    (hα : α * star α = 1) (hx : U x = α • x) (hy : U y = β • y) :
    α * inner ℂ x y = β * inner ℂ x y := by
  have he := U.inner_map_map x y
  rw [hx,hy,inner_smul_left,inner_smul_right] at he
  have he' := congrArg (fun z : ℂ => α*z) he
  change α*(star α*(β*inner ℂ x y)) = α*inner ℂ x y at he'
  rw [← mul_assoc,hα,one_mul] at he'
  exact he'.symm

private theorem div_eigen (z α β d : ℂ) (h : α*z = β*z) :
    (z/d)*α = β*(z/d) := by
  linear_combination h/d

set_option maxHeartbeats 800000 in
theorem gramSchmidt_eigen (v : ℕ → H) (U : H ≃ₗᵢ[ℂ] H) (α : ℕ → ℂ)
    (hα : ∀ n, α n * star (α n) = 1) (hv : ∀ n, U (v n) = α n • v n) (n : ℕ) :
    U (gramSchmidt ℂ v n) = α n • gramSchmidt ℂ v n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [gramSchmidt_def]
    simp only [Submodule.starProjection_singleton,map_sub,map_sum,map_smul,hv,
      smul_sub,Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n := Finset.mem_Iio.mp hj
    rw [ih j hjn,smul_smul,smul_smul]
    congr 1
    have he := eigen_inner U (gramSchmidt ℂ v j) (v n) (α j) (α n)
      (hα j) (ih j hjn) (hv n)
    exact div_eigen _ _ _ _ he

theorem gramSchmidtNormed_eigen (v : ℕ → H) (U : H ≃ₗᵢ[ℂ] H) (α : ℕ → ℂ)
    (hα : ∀ n, α n * star (α n) = 1) (hv : ∀ n, U (v n) = α n • v n) (n : ℕ) :
    U (gramSchmidtNormed ℂ v n) = α n • gramSchmidtNormed ℂ v n := by
  rw [gramSchmidtNormed,map_smul,gramSchmidt_eigen v U α hα hv]
  exact smul_comm _ _ _

variable [CompleteSpace H]

def basis (v : ℕ → H) (hi : LinearIndependent ℂ v)
    (hd : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) : HilbertBasis ℕ ℂ H :=
  HilbertBasis.mk (gramSchmidtNormed_orthonormal hi) (by
    rw [span_gramSchmidtNormed_range,span_gramSchmidt,hd])

theorem basis_apply (v : ℕ → H) (hi : LinearIndependent ℂ v)
    (hd : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) (n : ℕ) :
    basis v hi hd n = gramSchmidtNormed ℂ v n := congrFun (HilbertBasis.coe_mk _ _) n

theorem basis_eigen (v : ℕ → H) (hi : LinearIndependent ℂ v)
    (hd : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (U : H ≃ₗᵢ[ℂ] H) (α : ℕ → ℂ) (hα : ∀ n, α n * star (α n) = 1)
    (hv : ∀ n, U (v n) = α n • v n) (n : ℕ) :
    U (basis v hi hd n) = α n • basis v hi hd n := by
  rw [basis_apply]
  exact gramSchmidtNormed_eigen v U α hα hv n

#print axioms gramSchmidt_eigen
#print axioms basis
#print axioms basis_eigen
end
end UnifiedTheory.Audit.KFCausalGramSchmidtEigenvectors
