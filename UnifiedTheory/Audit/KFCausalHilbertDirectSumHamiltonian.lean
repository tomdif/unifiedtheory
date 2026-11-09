/- Maximal Hilbert direct sums of arbitrary self-adjoint operators.
The domain includes exactly the vectors with square-summable operator outputs. -/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHilbertDirectSumHamiltonian
noncomputable section
open scoped Topology
open Filter

variable {ι : Type*} {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)]
variable (A : ∀ i, E i →ₗ.[ℂ] E i)
local instance : DecidableEq ι := Classical.decEq _

abbrev Space := lp E 2

def coordinateGraph : Submodule ℂ (Space (E := E) × Space (E := E)) where
  carrier := {p | ∀ i, (p.1 i, p.2 i) ∈ (A i).graph}
  zero_mem' := fun i => (A i).graph.zero_mem
  add_mem' := by
    intro p q hp hq i
    exact (A i).graph.add_mem (hp i) (hq i)
  smul_mem' := by
    intro c p hp i
    exact (A i).graph.smul_mem c (hp i)

omit [∀ i, CompleteSpace (E i)] in
theorem singleValued (p : Space (E := E) × Space (E := E))
    (hp : p ∈ coordinateGraph A) (hz : p.1 = 0) : p.2 = 0 := by
  apply lp.ext
  funext i
  exact (A i).mem_graph_snd_inj' (hp i) (A i).graph.zero_mem (by simp [hz])

def operator : Space (E := E) →ₗ.[ℂ] Space (E := E) := (coordinateGraph A).toLinearPMap

theorem graph_iff (x y : Space (E := E)) : (x, y) ∈ (operator A).graph ↔
    ∀ i, (x i, y i) ∈ (A i).graph := by
  rw [operator, Submodule.toLinearPMap_graph_eq _ (singleValued A)]
  rfl

theorem single_graph (i : ι) (x : (A i).domain) :
    (lp.single 2 i (x : E i), lp.single 2 i (A i x)) ∈ (operator A).graph := by
  classical
  rw [graph_iff]
  intro j
  by_cases h : j = i
  · subst j
    simpa using (A i).mem_graph x
  · simpa [lp.single_apply, h] using (A j).graph.zero_mem

theorem domain_dense (hA : ∀ i, IsSelfAdjoint (A i)) :
    Dense ((operator A).domain : Set (Space (E := E))) := by
  have hs (i : ι) (x : E i) : lp.single 2 i x ∈
      (operator A).domain.topologicalClosure := by
    have hd : DenseRange (A i).domain.subtype := by simpa using (hA i).dense_domain
    refine hd.induction_on x
      ((operator A).domain.isClosed_topologicalClosure.preimage
        (lp.singleContinuousLinearMap ℂ E 2 i).continuous) ?_
    intro y
    exact (operator A).domain.le_topologicalClosure
      (LinearPMap.mem_domain_of_mem_graph (single_graph A i y))
  intro x
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num) x)
  exact Filter.Eventually.of_forall (fun s =>
    (operator A).domain.topologicalClosure.sum_mem (fun i _ => hs i (x i)))

theorem symmetric (hA : ∀ i, IsSelfAdjoint (A i)) :
    (operator A).IsFormalAdjoint (operator A) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  obtain ⟨u, hu, hv⟩ := (A i).mem_graph_iff.mp
    ((graph_iff A x (operator A x)).mp ((operator A).mem_graph x) i)
  obtain ⟨v, hw, hz⟩ := (A i).mem_graph_iff.mp
    ((graph_iff A y (operator A y)).mp ((operator A).mem_graph y) i)
  dsimp only at hu hv hw hz
  rw [← hu, ← hv, ← hw, ← hz]
  have he := LinearPMap.adjoint_isFormalAdjoint (hA i).dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp (hA i)] at he
  exact he u v

def singleDomain (i : ι) (x : (A i).domain) : (operator A).domain :=
  ⟨lp.single 2 i (x : E i), LinearPMap.mem_domain_of_mem_graph (single_graph A i x)⟩

theorem single_value (i : ι) (x : (A i).domain) :
    operator A (singleDomain A i x) = lp.single 2 i (A i x) :=
  (operator A).mem_graph_snd_inj' ((operator A).mem_graph _) (single_graph A i x) rfl

theorem adjoint_graph (hA : ∀ i, IsSelfAdjoint (A i)) (x : (operator A).adjoint.domain) :
    ((x : Space (E := E)), (operator A).adjoint x) ∈ (operator A).graph := by
  rw [graph_iff]
  intro i
  have hp (u : (A i).domain) :
      inner ℂ ((operator A).adjoint x i) (u : E i) =
        inner ℂ ((x : Space (E := E)) i) (A i u) := by
    have he := LinearPMap.adjoint_isFormalAdjoint (domain_dense A hA) x (singleDomain A i u)
    rw [single_value] at he
    simpa only [singleDomain, lp.inner_single_right] using he
  have hx : (x : Space (E := E)) i ∈ (A i).adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨(operator A).adjoint x i, hp⟩
  have hy := LinearPMap.adjoint_apply_eq (hA i).dense_domain ⟨_, hx⟩ hp
  have hg : ((x : Space (E := E)) i, (operator A).adjoint x i) ∈ (A i).adjoint.graph := by
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨_, hx⟩, rfl, hy⟩
  rwa [LinearPMap.isSelfAdjoint_def.mp (hA i)] at hg

theorem selfAdjoint (hA : ∀ i, IsSelfAdjoint (A i)) : IsSelfAdjoint (operator A) := by
  have hf := (symmetric A hA).le_adjoint (domain_dense A hA)
  have hb : (operator A).adjoint.domain ≤ (operator A).domain :=
    fun x hx => LinearPMap.mem_domain_of_mem_graph (adjoint_graph A hA ⟨x, hx⟩)
  exact LinearPMap.isSelfAdjoint_def.mpr
    (LinearPMap.eq_of_le_of_domain_eq hf (le_antisymm hf.1 hb)).symm

theorem domain_iff (x : Space (E := E)) : x ∈ (operator A).domain ↔
    ∃ (hx : ∀ i, x i ∈ (A i).domain), Memℓp (fun i => A i ⟨x i, hx i⟩) 2 := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨y, hy⟩
    have hg := (graph_iff A x y).mp hy
    let hx := fun i => LinearPMap.mem_domain_of_mem_graph (hg i)
    refine ⟨hx, ?_⟩
    have he (i) : A i ⟨x i, hx i⟩ = y i :=
      (A i).mem_graph_snd_inj' ((A i).mem_graph _) (hg i) rfl
    simpa only [he] using lp.memℓp y
  · rintro ⟨hx, hy⟩
    exact ⟨⟨_, hy⟩, (graph_iff A x _).mpr (fun i => (A i).mem_graph ⟨x i, hx i⟩)⟩

theorem positive (hpos : ∀ i (u : (A i).domain), 0 ≤ (inner ℂ (A i u) (u : E i)).re)
    (x : (operator A).domain) :
    0 ≤ (inner ℂ (operator A x) (x : Space (E := E))).re := by
  rw [lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner _ _)]
  apply tsum_nonneg
  intro i
  obtain ⟨u, hu, hv⟩ := (A i).mem_graph_iff.mp
    ((graph_iff A x (operator A x)).mp ((operator A).mem_graph x) i)
  change (u : E i) = (x : Space (E := E)) i at hu
  change A i u = operator A x i at hv
  rw [← hv, ← hu]
  exact hpos i u

end
end UnifiedTheory.Audit.KFCausalHilbertDirectSumHamiltonian
