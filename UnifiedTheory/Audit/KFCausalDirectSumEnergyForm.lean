/- The full closed energy form of a Hilbert direct sum. Energy-output
summability, rather than Hamiltonian-output summability, defines this domain. -/
import UnifiedTheory.Audit.KFCausalClosedGraphForm
import UnifiedTheory.Audit.KFCausalHilbertDirectSumHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDirectSumEnergyForm
noncomputable section
open scoped Topology ENNReal
open KFCausalClosedGraphForm

variable {ι : Type*} {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
  [∀ i, CompleteSpace (F i)]
variable (D : ∀ i, Data (E i) (F i))
local instance : DecidableEq ι := Classical.decEq _

def coordinateGraph : Submodule ℂ (lp E 2 × lp F 2) where
  carrier := {p | ∀ i, (p.1 i, p.2 i) ∈ (D i).operator.graph}
  zero_mem' := fun i => (D i).operator.graph.zero_mem
  add_mem' := by
    intro p q hp hq i
    exact (D i).operator.graph.add_mem (hp i) (hq i)
  smul_mem' := by
    intro c p hp i
    exact (D i).operator.graph.smul_mem c (hp i)

theorem singleValued (p : lp E 2 × lp F 2)
    (hp : p ∈ coordinateGraph D) (hz : p.1 = 0) : p.2 = 0 := by
  apply lp.ext
  funext i
  exact (D i).operator.mem_graph_snd_inj' (hp i) (D i).operator.graph.zero_mem
    (by simp [hz])

def operator : lp E 2 →ₗ.[ℂ] lp F 2 := (coordinateGraph D).toLinearPMap

theorem graph_iff (x : lp E 2) (y : lp F 2) : (x, y) ∈ (operator D).graph ↔
    ∀ i, (x i, y i) ∈ (D i).operator.graph := by
  rw [operator, Submodule.toLinearPMap_graph_eq _ (singleValued D)]
  rfl

theorem closed : (operator D).IsClosed := by
  change IsClosed ((operator D).graph : Set (lp E 2 × lp F 2))
  rw [operator, Submodule.toLinearPMap_graph_eq _ (singleValued D)]
  change IsClosed {p : lp E 2 × lp F 2 | ∀ i, (p.1 i, p.2 i) ∈ (D i).operator.graph}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro i
  exact (D i).closed.preimage
    (((continuous_apply i).comp (lp.uniformContinuous_coe.continuous.comp continuous_fst)).prodMk
      ((continuous_apply i).comp (lp.uniformContinuous_coe.continuous.comp continuous_snd)))

theorem single_graph (i : ι) (x : E i) (y : F i) (hxy : (x, y) ∈ (D i).operator.graph) :
    (lp.single 2 i x, lp.single 2 i y) ∈ (operator D).graph := by
  rw [graph_iff]
  intro j
  by_cases h : j = i
  · subst j
    simpa using hxy
  · simpa [lp.single_apply, h] using (D j).operator.graph.zero_mem

theorem domain_dense : Dense ((operator D).domain : Set (lp E 2)) := by
  have hs (i : ι) (x : E i) : lp.single 2 i x ∈ (operator D).domain.topologicalClosure := by
    have hd : DenseRange (D i).operator.domain.subtype := by simpa using (D i).dense
    refine hd.induction_on x
      ((operator D).domain.isClosed_topologicalClosure.preimage
        (lp.singleContinuousLinearMap ℂ E 2 i).continuous) ?_
    intro y
    exact (operator D).domain.le_topologicalClosure
      (LinearPMap.mem_domain_of_mem_graph (single_graph D i y _ ((D i).operator.mem_graph y)))
  intro x
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num) x)
  exact Filter.Eventually.of_forall (fun s =>
    (operator D).domain.topologicalClosure.sum_mem (fun i _ => hs i (x i)))

def formData : Data (lp E 2) (lp F 2) := ⟨operator D, closed D, domain_dense D⟩

theorem operator_domain_iff (x : lp E 2) : x ∈ (operator D).domain ↔
    ∃ (hx : ∀ i, x i ∈ (D i).operator.domain),
      Memℓp (fun i => (D i).operator ⟨x i, hx i⟩) 2 := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨y, hy⟩
    have hg := (graph_iff D x y).mp hy
    let hx := fun i => LinearPMap.mem_domain_of_mem_graph (hg i)
    refine ⟨hx, ?_⟩
    have he (i) : (D i).operator ⟨x i, hx i⟩ = y i :=
      (D i).operator.mem_graph_snd_inj' ((D i).operator.mem_graph _) (hg i) rfl
    simpa only [he] using lp.memℓp y
  · rintro ⟨hx, hy⟩
    exact ⟨⟨_, hy⟩, (graph_iff D x _).mpr (fun i => (D i).operator.mem_graph ⟨x i, hx i⟩)⟩

def coordinate (u : FormSpace (formData D)) (i : ι) : FormSpace (D i) :=
  ⟨WithLp.toLp 2 (embedding (formData D) u i, energyOutput (formData D) u i),
    (graph_iff D _ _).mp u.property i⟩

theorem coordinate_embedding (u : FormSpace (formData D)) (i : ι) :
    embedding (D i) (coordinate D u i) = embedding (formData D) u i := rfl

theorem coordinate_output (u : FormSpace (formData D)) (i : ι) :
    energyOutput (D i) (coordinate D u i) = energyOutput (formData D) u i := rfl

def singleForm (i : ι) (v : FormSpace (D i)) : FormSpace (formData D) :=
  ⟨WithLp.toLp 2 (lp.single 2 i (embedding (D i) v), lp.single 2 i (energyOutput (D i) v)),
    single_graph D i _ _ v.property⟩

theorem singleForm_embedding (i : ι) (v : FormSpace (D i)) :
    embedding (formData D) (singleForm D i v) = lp.single 2 i (embedding (D i) v) := rfl

theorem singleForm_output (i : ι) (v : FormSpace (D i)) :
    energyOutput (formData D) (singleForm D i v) = lp.single 2 i (energyOutput (D i) v) := rfl

theorem form_domain_iff (x : lp E 2) :
    (∃ u : FormSpace (formData D), embedding (formData D) u = x) ↔
    ∃ (hx : ∀ i, x i ∈ (D i).operator.domain),
      Summable (fun i => ‖(D i).operator ⟨x i, hx i⟩‖ ^ 2) := by
  have he : (∃ u : FormSpace (formData D), embedding (formData D) u = x) ↔
      x ∈ (operator D).domain := by
    constructor
    · rintro ⟨u, rfl⟩
      exact LinearPMap.mem_domain_of_mem_graph u.property
    · intro hx
      exact ⟨graphVector (formData D) ⟨x, hx⟩, rfl⟩
  rw [he, operator_domain_iff]
  apply exists_congr
  intro hx
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      (f := fun i => (D i).operator ⟨x i, hx i⟩))

theorem energy_hasSum (u : FormSpace (formData D)) :
    HasSum (fun i => ‖energyOutput (D i) (coordinate D u i)‖ ^ 2)
      (‖energyOutput (formData D) u‖ ^ 2) := by
  simpa only [coordinate_output, ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (energyOutput (formData D) u)

theorem energy_identity (u : FormSpace (formData D)) :
    ‖energyOutput (formData D) u‖ ^ 2 =
      ∑' i, ‖energyOutput (D i) (coordinate D u i)‖ ^ 2 :=
  (energy_hasSum D u).tsum_eq.symm

end
end UnifiedTheory.Audit.KFCausalDirectSumEnergyForm
