/- Actual pure-clock graphs of shifted coherent Gaussians, with L2
continuity of the derivative outputs along bounded source curves. -/
import UnifiedTheory.Audit.KFCausalWeightedShiftedPureClockGraphs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalShiftedGaussianPureSourceCurves
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorCoherentSpectral (gaussianState)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalRadialMultipliers (controlled_const)
open KFCausalClockFloorCoherentBounds (sourceSize)

variable (ε a α β p y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)

def output (h : ℝ) (C : ℂ) (b : Fin 5 → ℂ) : Hilbert :=
  KFCausalWeightedShiftedPureClockGraphs.output ε a α β p y hε ha hα hβ hw hy
    (fun _ => 1) (fun _ => 0) (controlled_const 1) (controlled_const 0) h C b

theorem graph (h : ℝ) (hh : h ≠ 0) (C : ℂ) (b : Fin 5 → ℂ) :
    (C • gaussianState ε a α β p b y hε ha hα hβ hw hy,
      output ε a α β p y hε ha hα hβ hw hy h C b) ∈ (pureMomentum ε hε h).graph := by
  have hi : KFCausalWeightedShiftedPureClockGraphs.input ε a α β p y hε ha hα hβ hw hy
      (fun _ => 1) (controlled_const 1) C b = C • gaussianState ε a α β p b y hε ha hα hβ hw hy := by
    apply Lp.ext
    filter_upwards [KFCausalWeightedShiftedPureClockGraphs.input_coe ε a α β p y hε ha hα hβ hw hy
      (fun _ => 1) (controlled_const 1) C b,Lp.coeFn_smul C (gaussianState ε a α β p b y hε ha hα hβ hw hy),
      KFCausalShiftedGaussianPhysicalProfile.gaussianState_profile ε a α β p y b hε ha hα hβ hw hy]
      with x hx hc hs
    simp only [hx,hc,Pi.smul_apply,smul_eq_mul,hs,one_mul]
  rw [← hi]
  exact KFCausalWeightedShiftedPureClockGraphs.graph ε a α β p y hε ha hα hβ hw hy
    (fun _ => 1) (fun _ => 0) (controlled_const 1) (controlled_const 0) (differentiable_const 1)
    (fun x => by simp [KFCausalCanonicalClockDerivative.clockDerivative]) h hh C b

theorem output_continuous (B : ℝ) (C : ℝ → ℂ) (b : ℝ → Fin 5 → ℂ)
    (hCc : Continuous C) (hbc : Continuous b) (hbB : ∀ θ, sourceSize (b θ) ≤ B) (h : ℝ) :
    Continuous (fun θ => output ε a α β p y hε ha hα hβ hw hy h (C θ) (b θ)) :=
  KFCausalWeightedShiftedPureClockGraphs.output_continuous ε a α β p y hε ha hα hβ hw hy
    (fun _ => 1) (fun _ => 0) (controlled_const 1) (controlled_const 0) B C b hCc hbc hbB h

#print axioms graph
#print axioms output_continuous
end
end UnifiedTheory.Audit.KFCausalShiftedGaussianPureSourceCurves
