/- Maximal real diagonal Hamiltonians on the complete occupation space.
The full domain and self-adjointness are proved from coefficient equations.
The actual generally non-diagonal H(t) is not diagonalized by this result. -/
import UnifiedTheory.Audit.KFCausalBosonicNumberEstimate
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalBosonicDiagonalHamiltonian
noncomputable section
open KFCausalBosonicOccupationSpace KFCausalBosonicNumberEstimate
variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq _
variable (w : Occupation ι → ℝ)

def coefficientGraph : Submodule ℂ (Fock ι × Fock ι) where
  carrier := {p | ∀ n, p.2 n = (w n : ℂ)*p.1 n}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro p q hp hq n
    change p.2 n + q.2 n = (w n : ℂ)*(p.1 n+q.1 n)
    rw [hp, hq, mul_add]
  smul_mem' := by
    intro c p hp n
    change c*p.2 n = (w n : ℂ)*(c*p.1 n)
    rw [hp]
    ring

theorem coefficientGraph_singleValued (p : Fock ι × Fock ι)
    (hp : p ∈ coefficientGraph w) (hz : p.1 = 0) : p.2 = 0 := by
  apply lp.ext
  funext n
  have he := hp n
  simpa only [hz, lp.coeFn_zero, Pi.zero_apply, mul_zero] using he

def operator : Fock ι →ₗ.[ℂ] Fock ι := (coefficientGraph w).toLinearPMap

theorem graph_iff (x y : Fock ι) : (x,y) ∈ (operator w).graph ↔
    ∀ n, y n = (w n : ℂ)*x n := by
  rw [operator, Submodule.toLinearPMap_graph_eq _ (coefficientGraph_singleValued w)]
  rfl

theorem core_graph (u : Core ι) : (embed u, embed (diagonal w u)) ∈ (operator w).graph := by
  rw [graph_iff]
  intro n
  simp only [embed_apply, diagonal_apply]

theorem domain_dense : Dense ((operator w).domain : Set (Fock ι)) := by
  apply core_dense.mono
  rintro _ ⟨u, rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (core_graph w u)

theorem operator_apply (x : (operator w).domain) (n : Occupation ι) :
    operator w x n = (w n : ℂ)*(x : Fock ι) n :=
  (graph_iff w x (operator w x)).mp ((operator w).mem_graph x) n

theorem symmetric : (operator w).IsFormalAdjoint (operator w) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [operator_apply, operator_apply]
  change inner ℂ ((w n : ℂ) • (x : Fock ι) n) ((y : Fock ι) n) =
    inner ℂ ((x : Fock ι) n) ((w n : ℂ) • (y : Fock ι) n)
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

def basisDomain (n : Occupation ι) : (operator w).domain :=
  ⟨lp.single 2 n 1, by simpa only [embed_single] using
    LinearPMap.mem_domain_of_mem_graph (core_graph w (Finsupp.single n 1))⟩

theorem basis_value (n : Occupation ι) : operator w (basisDomain w n) = lp.single 2 n (w n : ℂ) := by
  apply lp.ext
  funext m
  rw [operator_apply]
  change (w m : ℂ)*(lp.single 2 n (1 : ℂ) : Fock ι) m =
    (lp.single 2 n (w n : ℂ) : Fock ι) m
  by_cases hm : m = n
  · subst m
    simp
  · simp [lp.single_apply, hm]

theorem adjoint_graph (x : (operator w).adjoint.domain) :
    ((x : Fock ι), (operator w).adjoint x) ∈ (operator w).graph := by
  rw [graph_iff]
  intro n
  have he := LinearPMap.adjoint_isFormalAdjoint (domain_dense w) x (basisDomain w n)
  rw [basis_value] at he
  change inner ℂ ((operator w).adjoint x) (lp.single 2 n 1) =
    inner ℂ (x : Fock ι) (lp.single 2 n (w n : ℂ)) at he
  have hc := congrArg (starRingEnd ℂ) he
  simp only [inner_conj_symm, lp.inner_single_left, RCLike.inner_apply,
    map_one, mul_one, map_intCast] at hc
  simpa only [Complex.conj_ofReal, mul_comm] using hc

theorem selfAdjoint : IsSelfAdjoint (operator w) := by
  have hf : operator w ≤ (operator w).adjoint := (symmetric w).le_adjoint (domain_dense w)
  have hb : (operator w).adjoint.domain ≤ (operator w).domain :=
    fun x hx => LinearPMap.mem_domain_of_mem_graph (adjoint_graph w ⟨x,hx⟩)
  exact LinearPMap.isSelfAdjoint_def.mpr
    (LinearPMap.eq_of_le_of_domain_eq hf (le_antisymm hf.1 hb)).symm

theorem domain_iff (x : Fock ι) : x ∈ (operator w).domain ↔
    Memℓp (fun n => (w n : ℂ)*x n) 2 := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨y, hy⟩
    have he := (graph_iff w x y).mp hy
    simpa only [← he] using lp.memℓp y
  · intro hx
    exact ⟨⟨_, hx⟩, (graph_iff w x _).mpr (fun _ => rfl)⟩

def numberOperator : Fock ι →ₗ.[ℂ] Fock ι := operator (fun n => (particleCount n : ℝ))

theorem numberOperator_selfAdjoint : IsSelfAdjoint (numberOperator (ι := ι)) := selfAdjoint _

theorem numberOperator_core (u : Core ι) :
    (embed u, embed (diagonal (fun n => (particleCount n : ℝ)) u)) ∈
      (numberOperator (ι := ι)).graph := core_graph _ u

end
end UnifiedTheory.Audit.KFCausalBosonicDiagonalHamiltonian
