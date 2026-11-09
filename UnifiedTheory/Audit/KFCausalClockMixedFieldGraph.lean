/- Maximal physical field graphs in clock-straightened mixed coordinates.
Bounded inverse and numerator symbols transfer the full multiplication relation. -/
import UnifiedTheory.Audit.KFCausalComplexSpectatorFourier
import UnifiedTheory.Audit.KFCausalPhysicalSpectatorGraph
import UnifiedTheory.Audit.KFCausalClockFloorMixedRadial
import UnifiedTheory.Audit.KFCausalTransverseFieldSquare
import UnifiedTheory.Audit.KFCausalMatterOrderedDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockMixedFieldGraph
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalMixedCoordinates (mixedCoordinates)
open KFCausalClockFloorMixedCoordinates (mixedStraighten mixedStraighten_coe mixedWeight)
open KFCausalClockFloorMixedRadial (clockMixed clockMixed_eq)
open KFCausalClockFloorMixedChart (mixedMap mixedMap_quasiMeasurePreserving)
open KFCausalClockFloorSpectatorChart (backward backward_continuous)
open KFCausalPartialFourierMultiplier (rightMultiplier rightMultiplier_coe)
open KFCausalComplexSpectatorFourier
open KFCausalPhysicalField (physicalField physicalField_graph)
open KFCausalTransverseFieldSquare (fieldSquare fieldSquare_graph)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPairedModeCoordinates (scale)

variable (ε : ℝ) (hε : 0 < ε)

theorem rightMultiplier_transport (v : Block 4 → ℂ) (hv : Measurable v)
    (hb : ∀ y, ‖v y‖ ≤ 1) (f : ProductHilbert 2 4) :
    mixedStraighten ε hε (rightMultiplier 2 4 v hv hb f) =
      rightMultiplier 2 4 (v ∘ backward ε hε)
        (hv.comp (backward_continuous ε hε).measurable)
        (fun y => hb (backward ε hε y)) (mixedStraighten ε hε f) := by
  apply Lp.ext
  filter_upwards [mixedStraighten_coe ε hε (rightMultiplier 2 4 v hv hb f),
    mixedStraighten_coe ε hε f,
    (mixedMap_quasiMeasurePreserving ε hε).ae (rightMultiplier_coe 2 4 v hv hb f),
    rightMultiplier_coe 2 4 (v ∘ backward ε hε)
      (hv.comp (backward_continuous ε hε).measurable)
      (fun y => hb (backward ε hε y)) (mixedStraighten ε hε f)] with x hl hf hm hr
  rw [hl,hr,hf,hm]
  change mixedWeight ε hε x*(v (backward ε hε x.2)*f (mixedMap ε hε x)) = _
  simp only [Function.comp_apply]
  ring

theorem relation_iff (v : Block 4 → ℂ) (hv : Measurable v) (f g : Hilbert) :
    (clockMixed ε hε g =ᵐ[volume] fun x =>
      v (backward ε hε x.2)*(clockMixed ε hε f) x) ↔
    (mixedCoordinates g =ᵐ[volume] fun x => v x.2*(mixedCoordinates f) x) := by
  rw [clockMixed_eq,clockMixed_eq]
  change (mixedStraighten ε hε (mixedCoordinates g) =ᵐ[volume] fun x =>
    (v ∘ backward ε hε) x.2*(mixedStraighten ε hε (mixedCoordinates f)) x) ↔ _
  rw [relation_iff_bounded 2 4 (v ∘ backward ε hε)
    (hv.comp (backward_continuous ε hε).measurable),relation_iff_bounded 2 4 v hv]
  have hi (u : ProductHilbert 2 4) :
      mixedStraighten ε hε (inverseAction 2 4 v hv u) =
      inverseAction 2 4 (v ∘ backward ε hε)
        (hv.comp (backward_continuous ε hε).measurable) (mixedStraighten ε hε u) :=
    rightMultiplier_transport ε hε (inverseSymbol v) (inverse_measurable v hv) (inverse_bound v) u
  have hn (u : ProductHilbert 2 4) :
      mixedStraighten ε hε (numeratorAction 2 4 v hv u) =
      numeratorAction 2 4 (v ∘ backward ε hε)
        (hv.comp (backward_continuous ε hε).measurable) (mixedStraighten ε hε u) :=
    rightMultiplier_transport ε hε (numeratorSymbol v) (numerator_measurable v hv) (numerator_bound v) u
  rw [← hi,← hn]
  exact (mixedStraighten ε hε).injective.eq_iff

theorem field_graph_iff (l : KFCausalTransverseDilationFlow.Transverse →L[ℝ] ℝ)
    (v : Block 4 → ℝ) (hv : Measurable v)
    (hl : ∀ z : KFCausalPhysicalFourierGeneralCoordinates.Product,
      l (KFCausalPhysicalFourierGeneralCoordinates.pairedChart.symm z).2 = v z.2)
    (f g : Hilbert) :
    (f,g) ∈ (physicalField l).graph ↔
      clockMixed ε hε g =ᵐ[volume] fun x =>
        (v (mixedMap ε hε x).2:ℂ)*(clockMixed ε hε f) x := by
  rw [KFCausalPhysicalSpectatorGraph.mixed_field_graph_iff l v hv hl]
  exact (relation_iff ε hε (fun y => (v y:ℂ)) (Complex.measurable_ofReal.comp hv) f g).symm

theorem pointField_graph_iff (f g : Hilbert) :
    (f,g) ∈ (physicalField pointField).graph ↔
      clockMixed ε hε g =ᵐ[volume] fun x =>
        ((2*scale*(mixedMap ε hε x).2 2+(mixedMap ε hε x).2 3:ℝ):ℂ)*
          (clockMixed ε hε f) x := by
  apply field_graph_iff ε hε pointField (fun y => 2*scale*y 2+y 3) (by fun_prop)
  intro z
  rw [KFCausalPhysicalFourierGeneralCoordinates.pairedChart_symm]
  change scale*(z.1 1+z.2 2)+scale*(z.2 2-z.1 1)+z.2 3 = _
  ring

theorem fieldSquare_of_two_fields
    (l : KFCausalTransverseDilationFlow.Transverse →L[ℝ] ℝ) (f g u : Hilbert)
    (hfg : (f,g) ∈ (physicalField l).graph)
    (hgu : (g,u) ∈ (physicalField l).graph) :
    (f,u) ∈ (fieldSquare l).graph := by
  rw [physicalField_graph] at hfg hgu
  rw [fieldSquare_graph]
  filter_upwards [hfg,hgu] with x hf hg
  rw [hg,hf]
  ring

#print axioms rightMultiplier_transport
#print axioms relation_iff
#print axioms field_graph_iff
#print axioms pointField_graph_iff
#print axioms fieldSquare_of_two_fields
end
end UnifiedTheory.Audit.KFCausalClockMixedFieldGraph
