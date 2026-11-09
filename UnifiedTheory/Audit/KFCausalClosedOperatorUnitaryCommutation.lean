/- A closed operator whose full graph is preserved by a strong unitary
 group commutes with its momentum on the actual composition domains.
 Orbit averages construct a dense graph core with momentum regularity. -/
import UnifiedTheory.Audit.KFCausalUnitaryMomentumCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClosedOperatorUnitaryCommutation
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator
open UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : StrongUnitaryGroup H)

theorem momentum_integral_graph (h : ℝ) (hh : h ≠ 0) (f j : H)
    (hj : (f,j) ∈ (momentum U h).graph) (a : ℝ) :
    U.action a f-f = (Complex.I/(h:ℂ)) • primitive U j a := by
  obtain ⟨v,hv,hj⟩ := (LinearPMap.mem_graph_iff _).mp hj
  have he := generator_integral U v 0 a
  rw [← generator_from_momentum U h hh v,hv,hj,U.initial] at he
  simpa only [primitive,map_smul,intervalIntegral.integral_smul] using he.symm

variable (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
variable (hc : ∀ t f g, (f,g) ∈ T.graph → (U.action t f,U.action t g) ∈ T.graph)

include hT hc in
theorem primitive_graph (f g : H) (hfg : (f,g) ∈ T.graph) (a : ℝ) :
    (primitive U f a,primitive U g a) ∈ T.graph := by
  letI : CompleteSpace T.graph := hT.completeSpace_coe
  let v : ℝ → T.graph := fun t => ⟨(U.action t f,U.action t g),hc t f g hfg⟩
  have hv : Continuous v := ((U.continuous_orbit f).prodMk (U.continuous_orbit g)).subtype_mk _
  let z : T.graph := ∫ t in 0..a, v t
  let p : T.graph →L[ℂ] H := (ContinuousLinearMap.fst ℂ H H).comp T.graph.subtypeL
  let q : T.graph →L[ℂ] H := (ContinuousLinearMap.snd ℂ H H).comp T.graph.subtypeL
  have hp : primitive U f a = p z := p.intervalIntegral_comp_comm (hv.intervalIntegrable 0 a)
  have hq : primitive U g a = q z := q.intervalIntegral_comp_comm (hv.intervalIntegrable 0 a)
  rw [hp,hq]
  exact z.property

include hT hc in
theorem average_graph (f g : H) (hfg : (f,g) ∈ T.graph) (a : ℝ) :
    (average U f a,average U g a) ∈ T.graph :=
  (T.graph.restrictScalars ℝ).smul_mem a⁻¹ (primitive_graph U T hT hc f g hfg a)

include hT hc in
omit [CompleteSpace H] in
theorem graph_derivative (h : ℝ) (hh : h ≠ 0) (f g j k : H)
    (hfg : (f,g) ∈ T.graph) (hj : (f,j) ∈ (momentum U h).graph)
    (hk : (g,k) ∈ (momentum U h).graph) : (j,k) ∈ T.graph := by
  have hf : Tendsto (fun t : ℝ => t⁻¹ • (U.action t f-f)) (𝓝[≠] 0)
      (𝓝 ((Complex.I/(h:ℂ)) • j)) := by
    simpa only [zero_add,U.initial] using ((momentum_graph_iff U h hh f j).mp hj).tendsto_slope_zero
  have hg : Tendsto (fun t : ℝ => t⁻¹ • (U.action t g-g)) (𝓝[≠] 0)
      (𝓝 ((Complex.I/(h:ℂ)) • k)) := by
    simpa only [zero_add,U.initial] using ((momentum_graph_iff U h hh g k).mp hk).tendsto_slope_zero
  have he : ((Complex.I/(h:ℂ)) • j,(Complex.I/(h:ℂ)) • k) ∈ T.graph :=
    hT.mem_of_tendsto (hf.prodMk_nhds hg) (Eventually.of_forall fun t =>
      (T.graph.restrictScalars ℝ).smul_mem t⁻¹ (T.graph.sub_mem (hc t f g hfg) hfg))
  have hs := T.graph.smul_mem (-Complex.I*(h:ℂ)) he
  simpa only [Prod.smul_mk,smul_smul,mul_comm (-Complex.I*(h:ℂ)),
    inverse_coefficient h hh,one_smul] using hs

include hT hc in
theorem graph_interchange (h : ℝ) (hh : h ≠ 0) (f g j k : H)
    (hfg : (f,g) ∈ T.graph) (hj : (f,j) ∈ (momentum U h).graph) :
    (j,k) ∈ T.graph ↔ (g,k) ∈ (momentum U h).graph := by
  constructor
  · intro hjk
    have he (a : ℝ) : U.action a g-g = (Complex.I/(h:ℂ)) • primitive U k a := by
      have ht := T.graph.smul_mem (Complex.I/(h:ℂ)) (primitive_graph U T hT hc j k hjk a)
      change ((Complex.I/(h:ℂ)) • primitive U j a,
        (Complex.I/(h:ℂ)) • primitive U k a) ∈ T.graph at ht
      rw [← momentum_integral_graph U h hh f j hj a] at ht
      exact T.mem_graph_snd_inj (T.graph.sub_mem (hc a f g hfg) hfg) ht rfl
    have hf : (fun a => U.action a g) = (fun a => (Complex.I/(h:ℂ)) • primitive U k a+g) := by
      funext a
      exact sub_eq_iff_eq_add.mp (he a)
    apply (momentum_graph_iff U h hh g k).mpr
    rw [hf]
    simpa only [U.initial] using ((primitive_derivative U k 0).const_smul (Complex.I/(h:ℂ))).add_const g
  · exact graph_derivative U T hT hc h hh f g j k hfg hj

include hT hc in
theorem composition_domain_iff (h : ℝ) (hh : h ≠ 0) (f g j : H)
    (hfg : (f,g) ∈ T.graph) (hj : (f,j) ∈ (momentum U h).graph) :
    j ∈ T.domain ↔ g ∈ (momentum U h).domain := by
  constructor
  · intro hjT
    obtain ⟨k,hjk⟩ := LinearPMap.mem_domain_iff.mp hjT
    exact LinearPMap.mem_domain_of_mem_graph ((graph_interchange U T hT hc h hh f g j k hfg hj).mp hjk)
  · intro hgJ
    obtain ⟨k,hgk⟩ := LinearPMap.mem_domain_iff.mp hgJ
    exact LinearPMap.mem_domain_of_mem_graph ((graph_interchange U T hT hc h hh f g j k hfg hj).mpr hgk)

def regularGraph (h : ℝ) : Submodule ℂ (H × H) :=
  T.graph ⊓ (momentum U h).domain.prod (momentum U h).domain

include hT hc in
theorem average_regular_graph (h : ℝ) (f g : H) (hfg : (f,g) ∈ T.graph) (a : ℝ) :
    (average U f a,average U g a) ∈ regularGraph U T h :=
  ⟨average_graph U T hT hc f g hfg a,
    (averageState U h f a).property,(averageState U h g a).property⟩

include hT hc in
theorem regular_graph_core (h : ℝ) : (regularGraph U T h).topologicalClosure = T.graph := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (fun _ hz => hz.1) hT
  · rintro ⟨f,g⟩ hfg
    exact mem_closure_of_tendsto ((average_tendsto U f).prodMk_nhds (average_tendsto U g))
      (Eventually.of_forall fun a => average_regular_graph U T hT hc h f g hfg a)

include hT hc in
omit [CompleteSpace H] in
theorem common_compositions (h : ℝ) (hh : h ≠ 0) (f g : H)
    (hfg : (f,g) ∈ regularGraph U T h) :
    ∃ j k : H, (f,j) ∈ (momentum U h).graph ∧ (g,k) ∈ (momentum U h).graph ∧ (j,k) ∈ T.graph := by
  obtain ⟨j,hj⟩ := LinearPMap.mem_domain_iff.mp hfg.2.1
  obtain ⟨k,hk⟩ := LinearPMap.mem_domain_iff.mp hfg.2.2
  exact ⟨j,k,hj,hk,graph_derivative U T hT hc h hh f g j k hfg.1 hj hk⟩

#print axioms momentum_integral_graph
#print axioms primitive_graph
#print axioms average_graph
#print axioms graph_derivative
#print axioms graph_interchange
#print axioms composition_domain_iff
#print axioms average_regular_graph
#print axioms regular_graph_core
#print axioms common_compositions
end
end UnifiedTheory.Audit.KFCausalClosedOperatorUnitaryCommutation
