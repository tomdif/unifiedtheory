/- A dense invariant subset of the actual momentum domain is a graph
 core. Paired orbit integration and bounded averaging prove this; no
 compact-core or essential-selfadjointness premise is supplied. -/
import UnifiedTheory.Audit.KFCausalUnitaryMomentumCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalUnitaryInvariantCore
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator
open UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
open UnifiedTheory.Audit.KFCausalUnitaryMomentumCore

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : StrongUnitaryGroup H)

omit [CompleteSpace H] in
def primitiveLinear (a : ℝ) : H →ₗ[ℂ] H where
  toFun x := primitive U x a
  map_add' x y := by
    simp only [primitive,map_add]
    exact intervalIntegral.integral_add ((U.continuous_orbit x).intervalIntegrable 0 a)
      ((U.continuous_orbit y).intervalIntegrable 0 a)
  map_smul' c x := by simp only [primitive,map_smul,intervalIntegral.integral_smul,RingHom.id_apply]

omit [CompleteSpace H] in
theorem primitive_norm (x : H) (a : ℝ) : ‖primitive U x a‖ ≤ |a| * ‖x‖ := by
  simpa only [primitive,sub_zero,mul_comm] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := a) (fun t _ => le_of_eq ((U.action t).norm_map x))

omit [CompleteSpace H] in
def primitiveL (a : ℝ) : H →L[ℂ] H :=
  (primitiveLinear U a).mkContinuous |a| (fun x => primitive_norm U x a)

omit [CompleteSpace H] in
theorem average_continuous (a : ℝ) : Continuous (fun x : H => average U x a) :=
  (primitiveL U a).continuous.const_smul a⁻¹

theorem average_pair_continuous (h a : ℝ) :
    Continuous (fun x : H => (average U x a,momentum U h (averageState U h x a))) := by
  simp only [average_momentum]
  exact (average_continuous U a).prodMk
    (((U.action a).continuous.sub continuous_id).const_smul a⁻¹ |>.const_smul (-Complex.I*(h:ℂ)))

theorem closed_submodule_average (K : Submodule ℂ (H × H)) (hK : IsClosed (K : Set (H × H)))
    (f g : H) (ho : ∀ t, (U.action t f,U.action t g) ∈ K) (a : ℝ) :
    (average U f a,average U g a) ∈ K := by
  letI : CompleteSpace K := hK.completeSpace_coe
  let v : ℝ → K := fun t => ⟨(U.action t f,U.action t g),ho t⟩
  have hv : Continuous v := ((U.continuous_orbit f).prodMk (U.continuous_orbit g)).subtype_mk _
  let z : K := ∫ t in 0..a, v t
  let p : K →L[ℂ] H := (ContinuousLinearMap.fst ℂ H H).comp K.subtypeL
  let q : K →L[ℂ] H := (ContinuousLinearMap.snd ℂ H H).comp K.subtypeL
  have hp : primitive U f a = p z := p.intervalIntegral_comp_comm (hv.intervalIntegrable 0 a)
  have hq : primitive U g a = q z := q.intervalIntegral_comp_comm (hv.intervalIntegrable 0 a)
  change (a⁻¹ • primitive U f a,a⁻¹ • primitive U g a) ∈ K
  rw [hp,hq]
  exact (K.restrictScalars ℝ).smul_mem a⁻¹ z.property

omit [CompleteSpace H] in
theorem momentum_orbit_graph (h t : ℝ) (f g : H) (hfg : (f,g) ∈ (momentum U h).graph) :
    (U.action t f,U.action t g) ∈ (momentum U h).graph := by
  obtain ⟨v,hv,hg⟩ := (LinearPMap.mem_graph_iff _).mp hfg
  have he := (momentum U h).mem_graph (domainAction U t v)
  change (U.action t (v:H),momentum U h (domainAction U t v)) ∈ _ at he
  simpa only [momentum_commutes,hv,hg] using he

def testGraph (h : ℝ) (D : Set H) : Set (H × H) :=
  {p | p ∈ (momentum U h).graph ∧ p.1 ∈ D}

def core (h : ℝ) (D : Set H) : Submodule ℂ (H × H) :=
  (Submodule.span ℂ (testGraph U h D)).topologicalClosure

theorem core_subset (h : ℝ) (hh : h ≠ 0) (D : Set H) : core U h D ≤ (momentum U h).graph :=
  Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr (fun _ hp => hp.1)) (momentum_closed U h hh)

theorem test_average_mem_core (h : ℝ) (D : Set H)
    (hi : ∀ t f, f ∈ D → U.action t f ∈ D)
    (f : (momentum U h).domain) (hf : (f:H) ∈ D) (a : ℝ) :
    (average U (f:H) a,momentum U h (averageState U h (f:H) a)) ∈ core U h D := by
  rw [momentum_average_commutes]
  apply closed_submodule_average U _ (Submodule.span ℂ (testGraph U h D)).isClosed_topologicalClosure (f:H) (momentum U h f) _ a
  intro t
  exact (Submodule.span ℂ (testGraph U h D)).le_topologicalClosure (Submodule.subset_span
    ⟨momentum_orbit_graph U h t (f:H) (momentum U h f) ((momentum U h).mem_graph f),hi t f hf⟩)

theorem invariant_core (h : ℝ) (hh : h ≠ 0) (D : Set H) (hd : Dense D)
    (hdom : D ⊆ (momentum U h).domain) (hi : ∀ t f, f ∈ D → U.action t f ∈ D) :
    core U h D = (momentum U h).graph := by
  have hav (a : ℝ) (f : H) :
      (average U f a,momentum U h (averageState U h f a)) ∈ core U h D := by
    have hs : IsClosed {x : H | (average U x a,momentum U h (averageState U h x a)) ∈ core U h D} :=
      (Submodule.span ℂ (testGraph U h D)).isClosed_topologicalClosure.preimage (average_pair_continuous U h a)
    have hd' := closure_minimal (fun x hx => test_average_mem_core U h D hi ⟨x,hdom hx⟩ hx a) hs
    exact hd' (hd f)
  apply le_antisymm (core_subset U h hh D)
  intro p hp
  obtain ⟨f,hf,hg⟩ := (LinearPMap.mem_graph_iff _).mp hp
  have he : ((f:H),momentum U h f) = p := Prod.ext hf hg
  rw [← he]
  exact (Submodule.span ℂ (testGraph U h D)).isClosed_topologicalClosure.mem_of_tendsto (averaged_graph_tendsto U h f)
    (Eventually.of_forall fun a => hav a f)

#print axioms primitive_norm
#print axioms average_continuous
#print axioms average_pair_continuous
#print axioms closed_submodule_average
#print axioms momentum_orbit_graph
#print axioms core_subset
#print axioms test_average_mem_core
#print axioms invariant_core
end
end UnifiedTheory.Audit.KFCausalUnitaryInvariantCore
