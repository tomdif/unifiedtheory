/- The actual transverse partial Fourier change in straightened clock
coordinates preserves and reflects the full natural longitudinal
exponential graph. The commutation is derived from the actual full Fourier
unitary and unbounded clock-multiplier relations. -/
import UnifiedTheory.Audit.KFCausalTransverseFourierClock
import UnifiedTheory.Audit.KFCausalClockFloorMixedRadial
import UnifiedTheory.Audit.KFCausalClockFloorExponential
import UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalClockFloorTransverseFourierGraph
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space FrequencyHilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (modePullback)
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates (straightening)
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorMixedRadial (clockMixed)
open UnifiedTheory.Audit.KFCausalTransverseFourierClock

variable (ε : ℝ) (hε : 0 < ε)

def action : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  (straightening ε hε).trans (transverseFourier.trans (straightening ε hε).symm)

theorem straightening_action (f : Hilbert) :
    straightening ε hε (action ε hε f) = transverseFourier (straightening ε hε f) :=
  (straightening ε hε).apply_symm_apply _

theorem straightening_action_mixed (f : Hilbert) :
    straightening ε hε (action ε hε f) = modePullback (coordinates 2 4 (clockMixed ε hε f)) := by
  rw [straightening_action]
  rfl

theorem coupledFourier_action (f : Hilbert) :
    coupledFourier ε hε (action ε hε f) = transverseFourier (coupledFourier ε hε f) := by
  change (Lp.fourierTransformₗᵢ Space ℂ) (straightening ε hε (action ε hε f)) = _
  rw [straightening_action,← transverse_fourier_commutes]
  rfl

theorem exponential_graph (h a : ℝ) (f g : Hilbert) :
    (f,g) ∈ (longitudinalExponential ε hε h a).graph ↔
      (action ε hε f,action ε hε g) ∈ (longitudinalExponential ε hε h a).graph := by
  rw [longitudinal_exponential_graph,longitudinal_exponential_graph,coupledFourier_action,coupledFourier_action]
  exact clock_relation (fun q => (Real.exp (a*(2*Real.pi*h*q)):ℂ)) (by fun_prop) _ _

theorem inverse_exponential_graph (h a : ℝ) (f g : Hilbert) :
    (f,g) ∈ (longitudinalExponential ε hε h a).graph ↔
      ((action ε hε).symm f,(action ε hε).symm g) ∈ (longitudinalExponential ε hε h a).graph := by
  have he := exponential_graph ε hε h a ((action ε hε).symm f) ((action ε hε).symm g)
  rw [LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply] at he
  exact he.symm

#print axioms straightening_action
#print axioms straightening_action_mixed
#print axioms coupledFourier_action
#print axioms exponential_graph
#print axioms inverse_exponential_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorTransverseFourierGraph
