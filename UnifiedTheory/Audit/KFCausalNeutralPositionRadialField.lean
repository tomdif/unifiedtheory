/- The radial cutoff and its heat factor preserve the entire natural
physical field and field-square domains. The unbounded field relation is
identified through the actual partial Fourier unitary by regularization.
The clock exponential in the ordered matter factors remains separate. -/
import UnifiedTheory.Audit.KFCausalChargeSpectatorRelation
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialField
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block Joint split)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square modeIsometry)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField physicalField_graph)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare fieldSquare_graph)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff

def fieldSymbol (x : Block 4) : ℂ := ((2*scale*x 2+x 3:ℝ):ℂ)

theorem fieldSymbol_measurable : Measurable fieldSymbol := by
  unfold fieldSymbol
  fun_prop

theorem fieldSymbol_physical (x : Space) :
    fieldSymbol (split 2 4 (modeIsometry x)).2 =
      (pointField (KFCausalEuclideanConfiguration.split x).2:ℂ) := by
  change ((2*scale*(scale*(x 3+x 4))+x 5:ℝ):ℂ) = ((x 3+x 4+x 5:ℝ):ℂ)
  congr 1
  ring_nf
  rw [scale_square]
  ring

theorem field_power_relation (j : ℕ) (f g : Hilbert) :
    (g =ᵐ[volume] fun x => (pointField x.2:ℂ)^j*f x) ↔
      chargeCoordinates g =ᵐ[volume] fun x => fieldSymbol (split 2 4 x).2^j*(chargeCoordinates f) x :=
  KFCausalChargeSpectatorRelation.physical_relation (fun x => fieldSymbol x^j)
    (fieldSymbol_measurable.pow_const j) (fun x => (pointField x.2:ℂ)^j)
    (fun x => congrArg (fun z : ℂ => z^j) (fieldSymbol_physical x)) f g

variable (h δ v : ℝ) (hδ : 0 < δ)

theorem heat_relation (j : ℕ) (f g : Hilbert)
    (hfg : g =ᵐ[volume] fun x => (pointField x.2:ℂ)^j*f x) :
    heat h δ hδ g =ᵐ[volume] fun x => (pointField x.2:ℂ)^j*heat h δ hδ f x := by
  apply (field_power_relation j _ _).mpr
  have hr := (field_power_relation j f g).mp hfg
  filter_upwards [hr,heat_coe h δ hδ f,heat_coe h δ hδ g] with x hr hf hg
  rw [hg,hf,hr]
  ring

theorem action_relation (j : ℕ) (f g : Hilbert)
    (hfg : g =ᵐ[volume] fun x => (pointField x.2:ℂ)^j*f x) :
    action h δ v hδ g =ᵐ[volume] fun x => (pointField x.2:ℂ)^j*action h δ v hδ f x := by
  apply (field_power_relation j _ _).mpr
  have hr := (field_power_relation j f g).mp hfg
  filter_upwards [hr,action_coe h δ v hδ f,action_coe h δ v hδ g] with x hr hf hg
  rw [hg,hf,hr]
  ring

theorem heat_field_graph (f g : Hilbert) (hfg : (f,g) ∈ (physicalField pointField).graph) :
    (heat h δ hδ f,heat h δ hδ g) ∈ (physicalField pointField).graph := by
  apply (physicalField_graph pointField _ _).mpr
  simpa only [pow_one] using heat_relation h δ hδ 1 f g
    (by simpa only [pow_one] using (physicalField_graph pointField f g).mp hfg)

theorem heat_square_graph (f g : Hilbert) (hfg : (f,g) ∈ (fieldSquare pointField).graph) :
    (heat h δ hδ f,heat h δ hδ g) ∈ (fieldSquare pointField).graph :=
  (fieldSquare_graph pointField _ _).mpr
    (heat_relation h δ hδ 2 f g ((fieldSquare_graph pointField f g).mp hfg))

theorem action_field_graph (f g : Hilbert) (hfg : (f,g) ∈ (physicalField pointField).graph) :
    (action h δ v hδ f,action h δ v hδ g) ∈ (physicalField pointField).graph := by
  apply (physicalField_graph pointField _ _).mpr
  simpa only [pow_one] using action_relation h δ v hδ 1 f g
    (by simpa only [pow_one] using (physicalField_graph pointField f g).mp hfg)

theorem action_square_graph (f g : Hilbert) (hfg : (f,g) ∈ (fieldSquare pointField).graph) :
    (action h δ v hδ f,action h δ v hδ g) ∈ (fieldSquare pointField).graph :=
  (fieldSquare_graph pointField _ _).mpr
    (action_relation h δ v hδ 2 f g ((fieldSquare_graph pointField f g).mp hfg))

#print axioms fieldSymbol_measurable
#print axioms fieldSymbol_physical
#print axioms field_power_relation
#print axioms heat_relation
#print axioms action_relation
#print axioms heat_field_graph
#print axioms heat_square_graph
#print axioms action_field_graph
#print axioms action_square_graph

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialField
