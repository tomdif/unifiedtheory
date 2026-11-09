/- The original charge-compatible radial test preserves the entire natural
longitudinal half-exponential domain. Its graph output is the explicitly
constructed bounded imaginary-shift operator in actual mixed coordinates.
No exponential-domain preservation premise is supplied for the test. -/
import UnifiedTheory.Audit.KFCausalMixedRadialStripFamily
import UnifiedTheory.Audit.KFCausalMixedStripExponentialGraph
import UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialExponential
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (split split_preserves_volume)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (modeIsometry mode_preserves_volume)
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates (straightening)
open UnifiedTheory.Audit.KFCausalClockFloorMixedRadialStrip (radial_transformed_analytic)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action)
open UnifiedTheory.Audit.KFCausalMixedRadialStripFamily
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMultiplier (stripBound)
open UnifiedTheory.Audit.KFCausalMixedStripExponentialGraph (unitary unitary_straightening_coe)
open UnifiedTheory.Audit.KFCausalClockFloorExponential (longitudinalExponential)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shift_bound)

variable (ε h δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)

def shifted (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) : Hilbert →L[ℂ] Hilbert :=
  KFCausalMixedStripExponentialGraph.action ε hε (family ε h δ v) (Real.pi*ε/3) (stripBound ε δ v)
    (family_line_continuous ε h δ v hε) (Real.exp_pos _).le (family_bound ε h δ v hε hδ) y hy

theorem shifted_zero (h0 : |(0:ℝ)| ≤ Real.pi*ε/3) (f : Hilbert) :
    shifted ε h δ v hε hδ 0 h0 f = action h δ v hδ f := by
  apply (unitary ε hε).injective
  apply (straightening ε hε).injective
  apply Lp.ext
  filter_upwards [KFCausalMixedStripExponentialGraph.action_coe ε hε
      (family ε h δ v) (Real.pi*ε/3) (stripBound ε δ v)
      (family_line_continuous ε h δ v hε) (Real.exp_pos _).le (family_bound ε h δ v hε hδ) 0 h0 f,
    unitary_straightening_coe ε hε f,unitary_straightening_coe ε hε (action h δ v hδ f),
    ((split_preserves_volume 2 4).quasiMeasurePreserving.comp mode_preserves_volume.quasiMeasurePreserving).ae
      (radial_transformed_analytic ε h δ v hε hδ f)] with x hn hf hp hr
  change (straightening ε hε (unitary ε hε (shifted ε h δ v hε hδ 0 h0 f))) x = _ at hn
  rw [hn,hp,hf,family_symbol]
  simp only [Complex.ofReal_zero,zero_mul,add_zero]
  exact hr.symm

theorem shifted_norm (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (f : Hilbert) :
    ‖shifted ε h δ v hε hδ y hy f‖ ≤ Real.exp (v^2*y^2/(2*δ*ε^2))*‖f‖ :=
  KFCausalMixedStripExponentialGraph.action_norm ε hε
    (family ε h δ v) (Real.pi*ε/3) (stripBound ε δ v)
    (family_line_continuous ε h δ v hε) (Real.exp_pos _).le (family_bound ε h δ v hε hδ)
    y hy _ (family_slice_bound ε h δ v hε hδ y hy) f

theorem exponential_graph_action (hh : |h| ≤ 2*Real.pi*ε/3) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    (action h δ v hδ f,shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh) g) ∈
      (longitudinalExponential ε hε h (1/2)).graph := by
  have h0 : |(0:ℝ)| ≤ Real.pi*ε/3 := by rw [abs_zero]; positivity
  have hg := KFCausalMixedStripExponentialGraph.graph_action ε hε
    (family ε h δ v) (Real.pi*ε/3) (stripBound ε δ v)
    (family_line_continuous ε h δ v hε) (Real.exp_pos _).le (family_bound ε h δ v hε hδ)
    (family_analytic ε h δ v hε) h h0 (shift_bound ε h hh) f g hfg
  change (shifted ε h δ v hε hδ 0 h0 f,shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh) g) ∈ _ at hg
  rw [shifted_zero] at hg
  exact hg

theorem output_norm (hh : |h| ≤ 2*Real.pi*ε/3) (g : Hilbert) :
    ‖shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh) g‖ ≤
      Real.exp (v^2*h^2/(8*δ*ε^2))*‖g‖ := by
  convert shifted_norm ε h δ v hε hδ (-h/2) (shift_bound ε h hh) g using 1
  congr 2
  ring

#print axioms shifted_zero
#print axioms shifted_norm
#print axioms exponential_graph_action
#print axioms output_norm

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialExponential
