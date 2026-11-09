/- Bounded analytic strip multipliers transported through the proved
transverse Fourier unitary preserve the actual natural clock exponential
graph. This gives a general graph theorem for mixed-coordinate tests. -/
import UnifiedTheory.Audit.KFCausalClockFloorTransverseFourierGraph
import UnifiedTheory.Audit.KFCausalStripFamilyExponentialGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalMixedStripExponentialGraph
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space FrequencyHilbert)
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit (TailSpace)
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates (straightening)
open UnifiedTheory.Audit.KFCausalClockFloorExponential (longitudinalExponential)
open UnifiedTheory.Audit.KFCausalClockFloorMixedRadial (clockMixed)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (split)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (modeIsometry)
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates (positionCoordinates_coe)
open UnifiedTheory.Audit.KFCausalClockFloorTransverseFourierGraph (straightening_action_mixed exponential_graph)
open UnifiedTheory.Audit.KFCausalStripFamilyExponentialGraph

abbrev unitary := KFCausalClockFloorTransverseFourierGraph.action

variable (ε : ℝ) (hε : 0 < ε)
  (F : ℂ → TailSpace → ℂ) (d M : ℝ)
  (hC : ∀ y, |y| ≤ d → Continuous (fun w : ℝ × TailSpace => F ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2))
  (hM : 0 ≤ M) (hB : ∀ q, |q.im| ≤ d → ∀ z, ‖F q z‖ ≤ M)

def action (y : ℝ) (hy : |y| ≤ d) : Hilbert →L[ℂ] Hilbert :=
  ((unitary ε hε).symm : Hilbert →L[ℂ] Hilbert).comp
    ((physicalMultiplier F d M hC hM hB ε hε y hy).comp (unitary ε hε : Hilbert →L[ℂ] Hilbert))

theorem unitary_action (y : ℝ) (hy : |y| ≤ d) (f : Hilbert) :
    unitary ε hε (action ε hε F d M hC hM hB y hy f) =
      physicalMultiplier F d M hC hM hB ε hε y hy (unitary ε hε f) :=
  (unitary ε hε).apply_symm_apply _

theorem action_norm (y : ℝ) (hy : |y| ≤ d) (b : ℝ)
    (hb : ∀ x, ‖symbol F y x‖ ≤ b) (f : Hilbert) :
    ‖action ε hε F d M hC hM hB y hy f‖ ≤ b*‖f‖ := by
  rw [← (unitary ε hε).norm_map (action ε hε F d M hC hM hB y hy f),unitary_action,
    ← (unitary ε hε).norm_map f]
  exact physicalMultiplier_norm F d M hC hM hB ε hε y hy b hb _

theorem graph_action (hF : ∀ z q, |q.im| ≤ d → AnalyticAt ℂ (fun q => F q z) q)
    (h : ℝ) (h0 : |(0:ℝ)| ≤ d) (hs : |-h/2| ≤ d) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    (action ε hε F d M hC hM hB 0 h0 f,action ε hε F d M hC hM hB (-h/2) hs g) ∈
      (longitudinalExponential ε hε h (1/2)).graph := by
  apply (exponential_graph ε hε h (1/2) _ _).mpr
  rw [unitary_action,unitary_action]
  exact graph_multiplier F d M hF hC hM hB ε hε h h0 hs _ _
    ((exponential_graph ε hε h (1/2) f g).mp hfg)

theorem unitary_straightening_coe (f : Hilbert) :
    straightening ε hε (unitary ε hε f) =ᵐ[volume]
      fun x => (clockMixed ε hε f) (split 2 4 (modeIsometry x)) := by
  rw [straightening_action_mixed]
  exact positionCoordinates_coe _

theorem action_coe (y : ℝ) (hy : |y| ≤ d) (f : Hilbert) :
    straightening ε hε (unitary ε hε (action ε hε F d M hC hM hB y hy f)) =ᵐ[volume]
      fun x => symbol F y x*(straightening ε hε (unitary ε hε f)) x := by
  rw [unitary_action]
  exact physicalMultiplier_coe F d M hC hM hB ε hε y hy _

#print axioms unitary_action
#print axioms action_norm
#print axioms graph_action
#print axioms unitary_straightening_coe
#print axioms action_coe

end
end UnifiedTheory.Audit.KFCausalMixedStripExponentialGraph
