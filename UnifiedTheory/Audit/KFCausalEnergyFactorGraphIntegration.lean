/- Integrate continuous simultaneous natural energy graphs. The ordered
matter graphs are composed only after their closed intermediate graphs
have been integrated. -/
import UnifiedTheory.Audit.KFCausalSourcedCurveDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalEnergyFactorGraphIntegration
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf_selfAdjoint)
open UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph (clockMomentum_closed)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (orderedExponential_closed)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField physicalField_closed)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare fieldSquare_selfAdjoint)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalProjectedKineticResponse (integral_closed_graph)

variable (ε h : ℝ) (hε : 0 < ε) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
  (f : ℝ → Hilbert) (g : Fin 8 → ℝ → Hilbert) (hf : Continuous f)
  (hg : ∀ j, Continuous (g j)) (hfg : ∀ θ j, (f θ,g j θ) ∈ (energyFactor ε hε h v l j).graph)

include hf hg hfg

theorem factor_graph (j : Fin 8) :
    (∫ θ, f θ ∂angleMeasure,∫ θ, g j θ ∂angleMeasure) ∈ (energyFactor ε hε h v l j).graph := by
  have ho := integral_closed_graph _ (orderedExponential_closed ε hε h)
    f (g 7) hf (hg 7) (fun θ => hfg θ 7)
  have hl (θ : ℝ) : (g 7 θ,g 5 θ) ∈ (physicalField l).graph := by
    obtain ⟨Y,hY,hL⟩ := (composition_graph _ _ _ _).mp (hfg θ 5)
    have he := (orderedExponential ε hε h).mem_graph_snd_inj' hY (hfg θ 7) rfl
    dsimp only at he
    exact he ▸ hL
  have hq (θ : ℝ) : (g 7 θ,g 6 θ) ∈ (fieldSquare l).graph := by
    obtain ⟨Y,hY,hQ⟩ := (composition_graph _ _ _ _).mp (hfg θ 6)
    have he := (orderedExponential ε hε h).mem_graph_snd_inj' hY (hfg θ 7) rfl
    dsimp only at he
    exact he ▸ hQ
  fin_cases j
  · exact integral_closed_graph _ (clockHalf_selfAdjoint ε).isClosed f _ hf (hg 0) (fun θ => hfg θ 0)
  · exact integral_closed_graph _ (clockMomentum_closed ε hε h (v 0)) f _ hf (hg 1) (fun θ => hfg θ 1)
  · exact integral_closed_graph _ (clockMomentum_closed ε hε h (v 1)) f _ hf (hg 2) (fun θ => hfg θ 2)
  · exact integral_closed_graph _ (clockMomentum_closed ε hε h (v 2)) f _ hf (hg 3) (fun θ => hfg θ 3)
  · exact integral_closed_graph _ (clockMomentum_closed ε hε h (v 3)) f _ hf (hg 4) (fun θ => hfg θ 4)
  · exact (composition_graph _ _ _ _).mpr ⟨_,ho,
      integral_closed_graph _ (physicalField_closed l) _ _ (hg 7) (hg 5) hl⟩
  · exact (composition_graph _ _ _ _).mpr ⟨_,ho,
      integral_closed_graph _ (fieldSquare_selfAdjoint l).isClosed _ _ (hg 7) (hg 6) hq⟩
  · exact ho

theorem common_domain :
    (∫ θ, f θ ∂angleMeasure) ∈ commonEnergyDomain ε hε h v l :=
  (commonEnergyDomain_iff ε hε h v l _).mpr (fun j => LinearPMap.mem_domain_of_mem_graph
    (factor_graph ε h hε v l f g hf hg hfg j))

#print axioms factor_graph
#print axioms common_domain
end
end UnifiedTheory.Audit.KFCausalEnergyFactorGraphIntegration
