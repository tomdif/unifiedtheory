/- One-sided spectral control for the actual coupled longitudinal momentum.
The half-exponential energy controls the positive tail. The translation bound
retains a negative spectral tail and applies to the clock-weighted input of
the actual ordered energy factor. These are not canonical-clock estimates. -/
import UnifiedTheory.Audit.KFCausalClockFloorSpectralTransport
import UnifiedTheory.Audit.KFCausalL2ExponentialTailBound
import UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorLongitudinalTails
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryTransport
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorSpectralTransport
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)

def negativeTail (ε : ℝ) (hε : 0 < ε) (h R : ℝ) (f : Hilbert) : ℝ :=
  ∫ k in {k | symbol h k < -R}, ‖(coupledFourier ε hε f) k‖^2

def positiveTail (ε : ℝ) (hε : 0 < ε) (h R : ℝ) (f : Hilbert) : ℝ :=
  ∫ k in {k | R ≤ symbol h k}, ‖(coupledFourier ε hε f) k‖^2

theorem half_graph_energy (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    Integrable (fun k => Real.exp (symbol h k)*‖(coupledFourier ε hε f) k‖^2) ∧
      (∫ k, Real.exp (symbol h k)*‖(coupledFourier ε hε f) k‖^2) = ‖g‖^2 := by
  obtain ⟨u,hu,hg⟩ := (LinearPMap.mem_graph_iff _).mp hfg
  dsimp only at hu hg
  subst f
  subst g
  exact ⟨(half_exponential_domain ε hε h u).mp u.property,
    (half_exponential_energy ε hε h u).symm⟩

theorem positive_tail_bound (ε : ℝ) (hε : 0 < ε) (h R : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    positiveTail ε hε h R f ≤ Real.exp (-R)*‖g‖^2 := by
  obtain ⟨hi,he⟩ := half_graph_energy ε hε h f g hfg
  have hb := KFCausalL2ExponentialTailBound.positive_tail (symbol h)
    (symbol_measurable h) R (coupledFourier ε hε f) hi
  simpa only [he] using hb

theorem transport_negative_tail_bound (ε : ℝ) (hε : 0 < ε) (h v R : ℝ)
    (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    ‖transport ε hε (h*v) f-f‖^2 ≤
      v^2*(R^2*‖f‖^2+2*‖g‖^2)+4*negativeTail ε hε h R f := by
  obtain ⟨hi,he⟩ := half_graph_energy ε hε h f g hfg
  have hb := KFCausalL2ExponentialTailBound.phase_difference_negative_tail
    (symbol h) (symbol_measurable h) v R (coupledFourier ε hε f) hi
  rw [← scaled_transport_fourier,← map_sub,LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map,he] at hb
  exact hb

theorem ordered_positive_tail_bound (ε : ℝ) (hε : 0 < ε) (h R : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (orderedExponential ε hε h).graph) :
    positiveTail ε hε h R (inverseL ε hε f) ≤ Real.exp (-R)*‖g‖^2 :=
  positive_tail_bound ε hε h R _ g ((ordered_graph_iff ε hε h f g).mp hfg)

theorem ordered_transport_negative_tail_bound (ε : ℝ) (hε : 0 < ε) (h v R : ℝ)
    (f g : Hilbert) (hfg : (f,g) ∈ (orderedExponential ε hε h).graph) :
    ‖transport ε hε (h*v) (inverseL ε hε f)-inverseL ε hε f‖^2 ≤
      v^2*(R^2/ε*‖f‖^2+2*‖g‖^2)+4*negativeTail ε hε h R (inverseL ε hε f) := by
  apply (transport_negative_tail_bound ε hε h v R _ g
    ((ordered_graph_iff ε hε h f g).mp hfg)).trans
  have hn := pow_le_pow_left₀ (norm_nonneg (inverseL ε hε f))
    (inverseAction_norm_bound ε hε f) 2
  rw [mul_pow,inv_pow,Real.sq_sqrt hε.le] at hn
  have hb := mul_le_mul_of_nonneg_left hn (sq_nonneg R)
  have hc := mul_le_mul_of_nonneg_left (add_le_add_right hb (2*‖g‖^2)) (sq_nonneg v)
  rw [div_eq_mul_inv]
  nlinarith only [hc]

theorem positiveTail_smul (ε : ℝ) (hε : 0 < ε) (h R : ℝ) (c : ℂ) (f : Hilbert) :
    positiveTail ε hε h R (c • f) = ‖c‖^2*positiveTail ε hε h R f := by
  unfold positiveTail
  rw [map_smul,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul c (coupledFourier ε hε f))] with k hk
  rw [hk,Pi.smul_apply,norm_smul,mul_pow]

#print axioms half_graph_energy
#print axioms positive_tail_bound
#print axioms transport_negative_tail_bound
#print axioms ordered_positive_tail_bound
#print axioms ordered_transport_negative_tail_bound
#print axioms positiveTail_smul

end
end UnifiedTheory.Audit.KFCausalClockFloorLongitudinalTails
