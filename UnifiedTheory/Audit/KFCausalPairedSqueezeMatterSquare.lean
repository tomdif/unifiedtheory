/- Paired squeeze transports the natural reverse matter graphs and
therefore the actual second matter actions, retaining the field scaling
on both sides of the energy factor. -/
import UnifiedTheory.Audit.KFCausalPairedSqueezeMatter
import UnifiedTheory.Audit.KFCausalClockFloorVacuumSquare
import UnifiedTheory.Audit.KFCausalClockFloorMatterClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalPairedSqueezeMatterSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPairedSqueezeTransport (transport)
open KFCausalPairedSqueezeExponential (exponential_graph_squeeze)
open KFCausalPairedSqueezeClockCommutation (inverse_half_commutes)
open KFCausalClockFloorTrialSpectralDomain (reversedExponential)
open KFCausalClockFloorTrialMatter (matterFactor)
open KFCausalClockFloorMatterClosure (reversedMatterFactor)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalField (physicalField)
open KFCausalTransverseFieldSquare (fieldSquare)

variable (ε : ℝ) (hε : 0 < ε) (h a : ℝ)

theorem reversed_exponential_graph (f g : Hilbert)
    (hfg : (f,g) ∈ (reversedExponential ε hε h).graph) :
    (transport a f,transport a g) ∈ (reversedExponential ε hε h).graph := by
  obtain ⟨u,hu,hg⟩ := (KFCausalClockFloorVacuumSquare.reversed_graph ε hε h f g).mp hfg
  apply (KFCausalClockFloorVacuumSquare.reversed_graph ε hε h _ _).mpr
  refine ⟨transport a u,exponential_graph_squeeze ε hε h (1/2) a f u hu,?_⟩
  rw [hg,inverse_half_commutes]

theorem reverse_matter_graph (M : Hilbert →ₗ.[ℂ] Hilbert) (c : ℂ)
    (hM : ∀ f g, (f,g) ∈ M.graph → (transport a f,c • transport a g) ∈ M.graph)
    (f g : Hilbert) (hfg : (f,g) ∈ (reversedMatterFactor ε hε h M).graph) :
    (transport a f,c • transport a g) ∈ (reversedMatterFactor ε hε h M).graph := by
  obtain ⟨u,hu,hg⟩ := (composition_graph _ _ _ _).mp hfg
  exact (composition_graph _ _ _ _).mpr
    ⟨_,hM f u hu,(reversedExponential ε hε h).graph.smul_mem c
      (reversed_exponential_graph ε hε h a u g hg)⟩

theorem matter_square_graph (M : Hilbert →ₗ.[ℂ] Hilbert) (c : ℂ)
    (hM : ∀ f g, (f,g) ∈ M.graph → (transport a f,c • transport a g) ∈ M.graph)
    (f z : Hilbert)
    (hfz : (f,z) ∈ (composition (reversedMatterFactor ε hε h M) (matterFactor ε hε h M)).graph) :
    (transport a f,(c*c) • transport a z) ∈
      (composition (reversedMatterFactor ε hε h M) (matterFactor ε hε h M)).graph := by
  obtain ⟨u,hu,hz⟩ := (composition_graph _ _ _ _).mp hfz
  apply (composition_graph _ _ _ _).mpr
  refine ⟨_,KFCausalPairedSqueezeMatter.matter_graph ε hε h a M c hM f u hu,?_⟩
  have hr := (reversedMatterFactor ε hε h M).graph.smul_mem c
    (reverse_matter_graph ε hε h a M c hM u z hz)
  simpa only [Prod.smul_mk,smul_smul] using hr

theorem linear_square_graph (f z : Hilbert)
    (hfz : (f,z) ∈ (composition (reversedMatterFactor ε hε h (physicalField pointField))
      (matterFactor ε hε h (physicalField pointField))).graph) :
    (transport a f,((Real.exp a:ℂ)*(Real.exp a:ℂ)) • transport a z) ∈
      (composition (reversedMatterFactor ε hε h (physicalField pointField))
        (matterFactor ε hε h (physicalField pointField))).graph :=
  matter_square_graph ε hε h a _ _ (KFCausalPairedSqueezeMatter.field_graph a) f z hfz

theorem quadratic_square_graph (f z : Hilbert)
    (hfz : (f,z) ∈ (composition (reversedMatterFactor ε hε h (fieldSquare pointField))
      (matterFactor ε hε h (fieldSquare pointField))).graph) :
    (transport a f,((Real.exp (2*a):ℂ)*(Real.exp (2*a):ℂ)) • transport a z) ∈
      (composition (reversedMatterFactor ε hε h (fieldSquare pointField))
        (matterFactor ε hε h (fieldSquare pointField))).graph :=
  matter_square_graph ε hε h a _ _ (KFCausalPairedSqueezeMatter.square_graph a) f z hfz

#print axioms reversed_exponential_graph
#print axioms reverse_matter_graph
#print axioms matter_square_graph
#print axioms linear_square_graph
#print axioms quadratic_square_graph
end
end UnifiedTheory.Audit.KFCausalPairedSqueezeMatterSquare
