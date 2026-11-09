/- The full clock second output has a constructed pure-clock graph.
Its derivative is continuous along the same bounded source curves. -/
import UnifiedTheory.Audit.KFCausalFullClockPureDomain
import UnifiedTheory.Audit.KFCausalCoherentSecondCurves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalFullClockPureSourceCurves
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorPureClockDerivative (differential)
open KFCausalClockFloorCoherentDerivative (physicalProfile)
open KFCausalGaussianClockSquare (fullClockFunction)
open KFCausalFullClockPureDomain (preOutput)
open KFCausalClockFloorCoherentBounds (sourceSize)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (p : ℝ)

def output (h : ℝ) (C : ℂ) (b : Fin 5 → ℂ) : Hilbert :=
  (-Complex.I*(h:ℂ)) • preOutput ε a α β hε ha hα hβ hw C p b

theorem graph (h : ℝ) (hh : h ≠ 0) (C : ℂ) (b : Fin 5 → ℂ) :
    (KFCausalGaussianClockSquare.output ε a α β hε ha hα hβ hw C p b,
      output ε a α β hε ha hα hβ hw p h C b) ∈ (pureMomentum ε hε h).graph := by
  let G := physicalProfile C p α β b (fullClockFunction ε a)
  let U := KFCausalGaussianClockSquare.output ε a α β hε ha hα hβ hw C p b
  have hf : MemLp G 2 volume := (Lp.memLp U).ae_eq
    (KFCausalFullClockPureDomain.output_coe ε a α β hε ha hα hβ hw C p b)
  have hd : MemLp (differential ε G) 2 volume :=
    (Lp.memLp (preOutput ε a α β hε ha hα hβ hw C p b)).ae_eq
      (KFCausalFullClockPureDomain.preOutput_coe ε a α β hε ha hα hβ hw C p b)
  have hi : hf.toLp G = U := Lp.ext (hf.coeFn_toLp.trans
    (KFCausalFullClockPureDomain.output_coe ε a α β hε ha hα hβ hw C p b).symm)
  have ho : hd.toLp (differential ε G) = preOutput ε a α β hε ha hα hβ hw C p b :=
    Lp.ext (hd.coeFn_toLp.trans (KFCausalFullClockPureDomain.preOutput_coe ε a α β hε ha hα hβ hw C p b).symm)
  have hg := KFCausalClockFloorPureClockDifferential.differential_graph ε hε h hh G hf hd
    ((KFCausalFullClockPureDomain.profile_smooth ε a α β C p b).differentiable (by norm_num))
  rwa [hi,ho] at hg

theorem output_continuous (B : ℝ) (C : ℝ → ℂ) (b : ℝ → Fin 5 → ℂ)
    (hCc : Continuous C) (hbc : Continuous b) (hC : ∀ θ, ‖C θ‖ ≤ 1)
    (hbB : ∀ θ, sourceSize (b θ) ≤ B) (h : ℝ) :
    Continuous (fun θ => output ε a α β hε ha hα hβ hw p h (C θ) (b θ)) := by
  have hU := KFCausalCoherentSecondCurves.clock_continuous ε a α β hε ha hα hβ hw B
    C (fun _ => p) b hCc continuous_const hbc hC hbB
  have hUhalf := KFCausalCoherentSecondCurves.clock_continuous ε (a/2) α β hε (half_pos ha) hα hβ hw B
    C (fun _ => p) b hCc continuous_const hbc hC hbB
  have hS := KFCausalVariableWidthSourceCurves.state_continuous ε a α β hε ha hα hβ hw B
    C (fun _ => p) b hCc continuous_const hbc hC hbB
  exact continuous_const.smul
    ((((KFCausalPureClockOutputMultipliers.boundedPart ε hε p).continuous.comp hU).sub
      (continuous_const.smul ((KFCausalShiftedClockMomentOperator.momentOperator ε a 0 ha).continuous.comp hUhalf))).add
      ((KFCausalClockFloorMomentumResponse.responseOperator ε hε).continuous.comp hS))

#print axioms graph
#print axioms output_continuous
end
end UnifiedTheory.Audit.KFCausalFullClockPureSourceCurves
