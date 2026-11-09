/- Mixed strip operators preserve the full physical point-field and
field-square graphs. The transverse conjugating unitary's unbounded field
relations are proved, so the shifted output domains are conclusions. -/
import UnifiedTheory.Audit.KFCausalClockFloorTransverseFourierField
import UnifiedTheory.Audit.KFCausalMixedStripExponentialGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalMixedStripFieldGraph
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit (TailSpace)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalMixedStripExponentialGraph (action unitary)
open UnifiedTheory.Audit.KFCausalClockFloorTransverseFourierField (action_field_power inverse_action_field_power)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField physicalField_graph)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare fieldSquare_graph)

variable (ε : ℝ) (hε : 0 < ε)
  (F : ℂ → TailSpace → ℂ) (d M : ℝ)
  (hC : ∀ y, |y| ≤ d → Continuous (fun w : ℝ × TailSpace => F ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2))
  (hM : 0 ≤ M) (hB : ∀ q, |q.im| ≤ d → ∀ z, ‖F q z‖ ≤ M)

theorem field_power_relation (y : ℝ) (hy : |y| ≤ d) (j : ℕ) (f g : Hilbert)
    (hfg : g =ᵐ[volume] fun x => (pointField x.2:ℂ)^j*f x) :
    action ε hε F d M hC hM hB y hy g =ᵐ[volume]
      fun x => (pointField x.2:ℂ)^j*action ε hε F d M hC hM hB y hy f x :=
  (inverse_action_field_power ε hε j _ _).mp
    (KFCausalStripFamilyPhysicalMultiplier.preserves_relation ε hε F d M hC hM hB y hy
      (fun x => (pointField x.2:ℂ)^j) _ _ ((action_field_power ε hε j f g).mp hfg))

theorem field_graph_action (y : ℝ) (hy : |y| ≤ d) (f g : Hilbert)
    (hfg : (f,g) ∈ (physicalField pointField).graph) :
    (action ε hε F d M hC hM hB y hy f,action ε hε F d M hC hM hB y hy g) ∈
      (physicalField pointField).graph := by
  apply (physicalField_graph pointField _ _).mpr
  simpa only [pow_one] using field_power_relation ε hε F d M hC hM hB y hy 1 f g
    (by simpa only [pow_one] using (physicalField_graph pointField f g).mp hfg)

theorem square_graph_action (y : ℝ) (hy : |y| ≤ d) (f g : Hilbert)
    (hfg : (f,g) ∈ (fieldSquare pointField).graph) :
    (action ε hε F d M hC hM hB y hy f,action ε hε F d M hC hM hB y hy g) ∈
      (fieldSquare pointField).graph :=
  (fieldSquare_graph pointField _ _).mpr (field_power_relation ε hε F d M hC hM hB y hy 2 f g
    ((fieldSquare_graph pointField f g).mp hfg))

#print axioms field_power_relation
#print axioms field_graph_action
#print axioms square_graph_action

end
end UnifiedTheory.Audit.KFCausalMixedStripFieldGraph
