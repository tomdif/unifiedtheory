/- The actual reduced clock-momentum output has a second exponential
 action. The shifted coefficient correction is retained exactly. -/
import UnifiedTheory.Audit.KFCausalSecondShiftClockGraphs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 700000

namespace UnifiedTheory.Audit.KFCausalSecondShiftReducedOutput
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalCoherentMomentumOutputReduction (reducedOutput)
open KFCausalSecondShiftClockGraphs (inverse_graph moment_graph correction_graph)
open KFCausalShiftedClockMomentOperator (inverseOperator momentOperator)
open KFCausalClockFloorOrderedMomentumCommutator (correction)
open KFCausalClockFloorShiftedOutput (shift_bound)
open KFCausalGaussianVacuumSquare (original_strip double_strip)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "hb₂" => double_strip ε h hb

private theorem half_reduced (p : ℝ) (g k : Hilbert) :
    (1/2:ℂ) • reducedOutput ε a (2*h) hε ha hb₂ p g k =
      (-Complex.I*(h:ℂ)) • (((p:ℂ)*Complex.I-1) •
        inverseOperator ε (-(2*h)/2) hε (shift_bound ε (2*h) hb₂) g-
          (2*(a:ℂ)) • momentOperator ε a (-(2*h)/2) ha k)-
            (1/2:ℂ) • correction ε hε (2*h) hb₂ g := by
  unfold reducedOutput
  rw [smul_sub,smul_smul]
  have hc : (1/2:ℂ)*(-Complex.I*((2*h:ℝ):ℂ)) = -Complex.I*(h:ℂ) := by
    push_cast
    ring
  rw [hc]

theorem exponential_graph (p : ℝ) (f g u v : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph)
    (huv : (u,v) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    (reducedOutput ε a h hε ha hb₀ p f u,
      (1/2:ℂ) • reducedOutput ε a (2*h) hε ha hb₂ p g v) ∈
        (longitudinalExponential ε hε h (1/2)).graph := by
  have hi := inverse_graph ε h hε hb f g hfg
  have hm := moment_graph ε h hε hb a ha u v huv
  have hc := correction_graph ε h hε hb f g hfg
  have hr := (longitudinalExponential ε hε h (1/2)).graph.sub_mem
    ((longitudinalExponential ε hε h (1/2)).graph.smul_mem (-Complex.I*(h:ℂ))
      ((longitudinalExponential ε hε h (1/2)).graph.sub_mem
        ((longitudinalExponential ε hε h (1/2)).graph.smul_mem ((p:ℂ)*Complex.I-1) hi)
        ((longitudinalExponential ε hε h (1/2)).graph.smul_mem (2*(a:ℂ)) hm))) hc
  rw [half_reduced ε a h hε ha hb p g v]
  exact hr

#print axioms exponential_graph
end
end UnifiedTheory.Audit.KFCausalSecondShiftReducedOutput
