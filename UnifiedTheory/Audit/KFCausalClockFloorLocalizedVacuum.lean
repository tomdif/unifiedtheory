/- Analytic clock localization of the actual ordered vacuum graph.
The shifted output is bounded by dissipation, so every fixed upper
longitudinal spectral half-space of the localized input is detected. -/
import UnifiedTheory.Audit.KFCausalClockFloorLocalizedVacuumScalar
import UnifiedTheory.Audit.KFCausalClockFloorDriftDetection
import UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectFullDomain
import UnifiedTheory.Audit.KFCausalClockFloorLongitudinalTails

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorLocalizedVacuum
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorDefectOperator
open KFCausalClockFloorShiftedDefect
open KFCausalClockFloorShiftedDefectPhysical
open KFCausalClockFloorCanonicalDefect (defect)
open KFCausalClockFloorDefectTransportScalar (drift)
open KFCausalClockFloorDefectTransportOperator (driftOperator driftOperator_coe)
open KFCausalClockFloorInitialDriftPairing
open KFCausalClockFloorDefectProductionCoercivity (scalar_real_pairing)
open KFCausalClockFloorDriftDetection (detection)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalClockFloorBoundedInverse (inverseL)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3)

def clockWeight : Hilbert →L[ℂ] Hilbert :=
  defectOperator ε hε-(defectOperator ε hε).comp (defectOperator ε hε)

def shiftedWeight : Hilbert →L[ℂ] Hilbert :=
  shiftedDefect ε hε h hb-(shiftedDefect ε hε h hb).comp (shiftedDefect ε hε h hb)

theorem shiftedWeight_coe (f : Hilbert) :
    shiftedWeight ε hε h hb f =ᵐ[volume]
      fun x => (physicalSymbol ε h x-(physicalSymbol ε h x)^2)*f x := by
  filter_upwards [Lp.coeFn_sub (shiftedDefect ε hε h hb f)
      (shiftedDefect ε hε h hb (shiftedDefect ε hε h hb f)),
    shiftedDefect_physical_coe ε hε h hb f,
    shiftedDefect_physical_coe ε hε h hb (shiftedDefect ε hε h hb f)] with x hs h1 h2
  change (shiftedDefect ε hε h hb f-shiftedDefect ε hε h hb (shiftedDefect ε hε h hb f)) x = _
  rw [hs,Pi.sub_apply,h2,h1]
  ring

theorem shiftedWeight_detection (f : Hilbert) :
    ‖shiftedWeight ε hε h hb f‖^2 ≤ 64*ε*detection ε hε f := by
  have hi := (L2.integrable_inner (𝕜 := ℂ) f (driftOperator ε hε f)).re
  have he : (fun x : Configuration => (inner ℂ (f x) (driftOperator ε hε f x)).re) =ᵐ[volume]
      fun x => drift ε (defect ε x.1)*‖f x‖^2 := by
    filter_upwards [driftOperator_coe ε hε f] with x hx
    rw [hx,scalar_real_pairing]
  have hd := hi.congr he
  rw [KFCausalAveragedEnergyGraph.l2_norm_square,detection,
    real_multiplier_pairing volume _ _ _ (driftOperator_coe ε hε f),
    ← integral_neg,← integral_const_mul]
  apply integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (shiftedWeight ε hε h hb f))).mp
      (Lp.memLp (shiftedWeight ε hε h hb f)))
    (hd.neg.const_mul (64*ε))
  filter_upwards [shiftedWeight_coe ε hε h hb f] with x hx
  rw [hx,norm_mul,mul_pow]
  exact (mul_le_mul_of_nonneg_right
    (KFCausalClockFloorLocalizedVacuumScalar.physical_localized_norm_square ε hε h hb x)
    (sq_nonneg ‖f x‖)).trans_eq (by simp only [Pi.neg_apply]; ring)

theorem localized_graph (f g : Hilbert)
    (hfg : (f,g) ∈ (orderedExponential ε hε h).graph) :
    (clockWeight ε hε f,shiftedWeight ε hε h hb g) ∈ (orderedExponential ε hε h).graph := by
  have h1 := KFCausalClockFloorOrderedDefectFullDomain.ordered_graph_defect ε hε h hb f g hfg
  have h2 := KFCausalClockFloorOrderedDefectFullDomain.ordered_graph_defect ε hε h hb _ _ h1
  exact (orderedExponential ε hε h).graph.sub_mem h1 h2

include hb in
theorem localized_tail_bound (R : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (orderedExponential ε hε h).graph) :
    KFCausalClockFloorLongitudinalTails.positiveTail ε hε h R
      (inverseL ε hε (clockWeight ε hε f)) ≤
      64*ε*Real.exp (-R)*detection ε hε g := by
  exact (KFCausalClockFloorLongitudinalTails.ordered_positive_tail_bound ε hε h R _ _
    (localized_graph ε hε h hb f g hfg)).trans
    ((mul_le_mul_of_nonneg_left (shiftedWeight_detection ε hε h hb g)
      (Real.exp_pos _).le).trans_eq (by ring))

#print axioms shiftedWeight_coe
#print axioms shiftedWeight_detection
#print axioms localized_graph
#print axioms localized_tail_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorLocalizedVacuum
