/- Rescale the actual pure momentum and longitudinal exponential while
keeping the physical vector fixed. The natural vacuum second action
retains both inverse-half-clock factors. -/
import UnifiedTheory.Audit.KFCausalGaussianVacuumSquare
import UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalVacuumParameterRescale
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential reversedExponential)
open KFCausalClockFloorBoundedInverse (inverseL ordered_graph_iff)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalClockFloorVacuumSquare (square square_graph exponential_rescale)
open KFCausalOrderedOperatorComposition (composition_graph)

theorem pure_graph_scale (ε : ℝ) (hε : 0 < ε) (h c : ℝ) (f g : Hilbert)
    (hg : (f,g) ∈ (pureMomentum ε hε h).graph) :
    (f,(c:ℂ) • g) ∈ (pureMomentum ε hε (c*h)).graph := by
  obtain ⟨v,hv⟩ := (pureMomentum ε hε h).mem_graph_iff'.mp hg
  have hf : (v:Hilbert)=f := congrArg Prod.fst hv
  have ho : pureMomentum ε hε h v=g := congrArg Prod.snd hv
  apply (pureMomentum ε hε (c*h)).mem_graph_iff'.mpr
  refine ⟨v,Prod.ext hf ?_⟩
  rw [← ho]
  change (-Complex.I*((c*h:ℝ):ℂ)) • (_:Hilbert) = (c:ℂ) • ((-Complex.I*(h:ℂ)) • (_:Hilbert))
  rw [smul_smul]
  congr 1
  push_cast
  ring

theorem doubled_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f g : Hilbert) :
    (f,g) ∈ (orderedExponential ε hε (2*h)).graph ↔
      (inverseL ε hε f,g) ∈ (longitudinalExponential ε hε h 1).graph := by
  rw [ordered_graph_iff]
  simpa only [show (1/2:ℝ)*2=1 by norm_num] using
    exponential_rescale ε hε h 2 (1/2) (inverseL ε hε f) g

theorem doubled_square_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f g : Hilbert)
    (hg : (f,g) ∈ (orderedExponential ε hε (2*h)).graph) :
    (f,inverseL ε hε g) ∈ (square ε hε h).graph :=
  (square_graph ε hε h f _).mpr ⟨g,(doubled_graph ε hε h f g).mp hg,rfl⟩

theorem doubled_reverse_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f u g : Hilbert)
    (hu : (f,u) ∈ (orderedExponential ε hε h).graph)
    (hg : (f,g) ∈ (orderedExponential ε hε (2*h)).graph) :
    (u,inverseL ε hε g) ∈ (reversedExponential ε hε h).graph := by
  obtain ⟨u',hu',hz⟩ := (composition_graph _ _ _ _).mp
    (doubled_square_graph ε hε h f g hg)
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hu' hu rfl
  dsimp only at he
  rwa [he] at hz

#print axioms pure_graph_scale
#print axioms doubled_graph
#print axioms doubled_square_graph
#print axioms doubled_reverse_graph
end
end UnifiedTheory.Audit.KFCausalVacuumParameterRescale
