/- A constructed graph core for the actual ordered vacuum factor T.
Both input and output have longitudinal momentum, so both L T and T L
are defined. Density follows from Gaussian spectral regularization and
strong defect-residual decay, not from a common-domain assumption. -/
import UnifiedTheory.Audit.KFCausalClockFloorExponentialMomentumCore
import UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator
import UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectFullDomain
import UnifiedTheory.Audit.KFCausalClockFloorDefectPowerDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCore
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorExponentialMomentumGraph (graph_interchange)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
open UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportOperator (inverseL_coe)
open UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportScalar (value)
open UnifiedTheory.Audit.KFCausalClockFloorInverseHalfMomentum (inverse_momentum_domain)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectMomentum (defect_momentum_graph)
open UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse (responseOperator)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedResponseContraction (shiftedResponse)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectFullDomain (ordered_graph_defect)
open UnifiedTheory.Audit.KFCausalClockFloorDefectPowerDecay
open UnifiedTheory.Audit.KFCausalInvariantRangeCore

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
local notation "L" => longitudinalMomentum ε hε h
local notation "E" => longitudinalExponential ε hε h (1/2)
local notation "T" => orderedExponential ε hε h
local notation "R" => inverseL ε hε
local notation "D" => defectOperator ε hε
local notation "Q" => responseOperator ε hε
local notation "Z" => shiftedDefect ε hε h hh
local notation "S" => shiftedResponse ε hε h hh
local notation "G" => KFCausalClockFloorExponentialMomentumCore.regularGraph ε hε h

def regularGraph : Submodule ℂ (Hilbert × Hilbert) := (T).graph ⊓ (L).domain.prod (L).domain
def coreMap : (Hilbert × Hilbert) →L[ℂ] (Hilbert × Hilbert) :=
  (R).prodMap ((1/(ε:ℂ)) • Z)

theorem inverse_squared (f : Hilbert) : R (R f) = (1/(ε:ℂ)) • D f := by
  apply Lp.ext
  filter_upwards [inverseL_coe ε hε (R f),inverseL_coe ε hε f,
    Lp.coeFn_smul (1/(ε:ℂ)) (D f),defectOperator_coe ε hε f] with x h2 h1 hs hd
  change R (R f) x = _ at h2
  change R f x = _ at h1
  rw [h2,h1,hs]
  simp only [Pi.smul_apply,smul_eq_mul,hd]
  have he : value ε x.1*value ε x.1 = (1/ε)*KFCausalClockFloorCanonicalDefect.defect ε x.1 := by
    rw [← pow_two,value,inv_pow,Real.sq_sqrt (KFCausalClockFloorCanonicalDefect.clock_positive ε x.1 hε.le).le]
    unfold KFCausalClockFloorCanonicalDefect.defect
    field_simp
  have hc : (value ε x.1:ℂ)*(value ε x.1:ℂ) =
      (1/(ε:ℂ))*(KFCausalClockFloorCanonicalDefect.defect ε x.1:ℂ) := by exact_mod_cast he
  rw [← mul_assoc,hc,mul_assoc]

include hne in
theorem defect_regular_graph (f g : Hilbert) (hg : (f,g) ∈ G) : (D f,Z g) ∈ G := by
  let lf := (L) ⟨f,hg.2.1⟩
  let lg := (L) ⟨g,hg.2.2⟩
  have hl : (f,lf) ∈ (L).graph := (L).mem_graph ⟨f,hg.2.1⟩
  have hl' : (g,lg) ∈ (L).graph := (L).mem_graph ⟨g,hg.2.2⟩
  have hel := (graph_interchange ε hε h hne (1/2) f lf g lg hl hg.1).mpr hl'
  have heD := KFCausalClockFloorDefectFullDomain.graph_defect ε hε h hh f g hg.1
  have hdL := defect_momentum_graph ε hε h f lf hl
  change (D f,D lf+(Complex.I*(h:ℂ)/(ε:ℂ)) • D (D (Q f))) ∈ (L).graph at hdL
  have he1 := KFCausalClockFloorDefectFullDomain.graph_defect ε hε h hh lf lg hel
  have he2 := KFCausalClockFloorDefectFullDomain.graph_defect ε hε h hh _ _
    (exponential_response_graph ε hε h hh f g hg.1)
  have heL := (E).graph.add_mem he1 ((E).graph.smul_mem (Complex.I*(h:ℂ)/(ε:ℂ)) he2)
  exact ⟨heD,LinearPMap.mem_domain_of_mem_graph hdL,
    LinearPMap.mem_domain_of_mem_graph
      ((graph_interchange ε hε h hne (1/2) (D f) _ (Z g) _ hdL heD).mp heL)⟩

include hne in
theorem coreMap_regular (z : Hilbert × Hilbert) (hz : z ∈ G) :
    coreMap ε hε h hh z ∈ regularGraph ε hε h := by
  have hd := defect_regular_graph ε hε h hne hh z.1 z.2 hz
  refine ⟨?_,inverse_momentum_domain ε hε h hne z.1 hz.2.1,(L).domain.smul_mem _ hd.2.2⟩
  apply (ordered_graph_iff ε hε h _ _).mpr
  change (R (R z.1),(1/(ε:ℂ)) • Z z.2) ∈ (E).graph
  rw [inverse_squared]
  exact (E).graph.smul_mem (1/(ε:ℂ)) hd.1

include hne hh in
theorem regular_graph_core : (regularGraph ε hε h).topologicalClosure = (T).graph := by
  let K := regularGraph ε hε h
  let A := coreMap ε hε h hh
  have hS : G ≤ K.topologicalClosure.comap A.toLinearMap := by
    intro z hz
    exact K.le_topologicalClosure (coreMap_regular ε hε h hne hh z hz)
  have hc := Submodule.topologicalClosure_minimal _ hS
    (K.isClosed_topologicalClosure.preimage A.continuous)
  rw [KFCausalClockFloorExponentialMomentumCore.regular_graph_core ε hε h hne] at hc
  let P := (D).prodMap Z
  have hP : ∀ z ∈ (T).graph, P z ∈ (T).graph := fun z hz =>
    ordered_graph_defect ε hε h hh z.1 z.2 hz
  have hdec (z : Hilbert × Hilbert) :
      Tendsto (fun n : ℕ => (residual P : Hilbert × Hilbert → Hilbert × Hilbert)^[n] z) atTop (𝓝 0) :=
    prod_residual_tendsto D Z z.1 z.2 (real_response_decay ε hε z.1)
      (shifted_response_decay ε hε h hh z.2)
  have hm : (T).graph.map P.toLinearMap ≤ K.topologicalClosure := by
    rintro _ ⟨⟨f,g⟩,hfg,rfl⟩
    have he := (ordered_graph_iff ε hε h f g).mp hfg
    have hz := hc he
    change (R (R f),(1/(ε:ℂ)) • Z g) ∈ K.topologicalClosure at hz
    rw [inverse_squared] at hz
    have hs := K.topologicalClosure.smul_mem (ε:ℂ) hz
    simpa only [Prod.smul_mk,smul_smul,one_div,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hε.ne'),one_smul] using hs
  have hm' := Submodule.topologicalClosure_minimal _ hm K.isClosed_topologicalClosure
  rw [range_core P (T).graph hP (fun z _ => hdec z)] at hm'
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (fun _ hz => hz.1) (orderedExponential_closed ε hε h)
  · exact (T).graph.le_topologicalClosure.trans hm'

include hne hh in
theorem common_compositions (f tf : Hilbert) (hf : (f,tf) ∈ regularGraph ε hε h) :
    ∃ lf tlf ltf : Hilbert,
      (f,lf) ∈ (L).graph ∧ (lf,tlf) ∈ (T).graph ∧ (tf,ltf) ∈ (L).graph ∧
        ltf-tlf = correction ε hε h hh tf := by
  let lf := (L) ⟨f,hf.2.1⟩
  let ltf := (L) ⟨tf,hf.2.2⟩
  refine ⟨lf,ltf-correction ε hε h hh tf,ltf,(L).mem_graph ⟨f,hf.2.1⟩,?_,
    (L).mem_graph ⟨tf,hf.2.2⟩,?_⟩
  · exact momentum_ordered_graph ε hε h hne hh f lf tf ltf
      ((L).mem_graph ⟨f,hf.2.1⟩) hf.1 ((L).mem_graph ⟨tf,hf.2.2⟩)
  · abel

include hne hh in
theorem graph_approximation (f tf : Hilbert) (hf : (f,tf) ∈ (T).graph) :
    ∃ z : ℕ → Hilbert × Hilbert, (∀ n, z n ∈ regularGraph ε hε h) ∧ Tendsto z atTop (𝓝 (f,tf)) := by
  have hz : (f,tf) ∈ (regularGraph ε hε h).topologicalClosure := by
    rw [regular_graph_core ε hε h hne hh]
    exact hf
  exact mem_closure_iff_seq_limit.mp hz

#print axioms inverse_squared
#print axioms defect_regular_graph
#print axioms coreMap_regular
#print axioms regular_graph_core
#print axioms common_compositions
#print axioms graph_approximation
end
end UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCore
