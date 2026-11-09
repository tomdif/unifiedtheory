/- The true ordered exponential output on the normalized trial approaches
the inverse-clock output strongly in L2. Consequently all bounded output
pairings have the same limit, including clock-dependent drift weights. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianDifferenceRescaling
import UnifiedTheory.Audit.KFCausalBoundedPairingStability
import UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorStrongInitialOutput
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput
open UnifiedTheory.Audit.KFCausalClockFloorGaussianDifferenceEnergy
open UnifiedTheory.Audit.KFCausalClockFloorGaussianDifferenceRescaling
open UnifiedTheory.Audit.KFCausalClockFloorOrderedEnergyLimit (dampedState_mass)
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates

def normalizedDamped (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) : Hilbert :=
  (‖trialState ε a hbar hε ha hh‖⁻¹:ℝ) • dampedState ε a hbar hε ha hh

def normalizedOutput (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) : Hilbert :=
  (‖trialState ε a hbar hε ha hh‖⁻¹:ℝ) • shiftedOutput ε a hbar hε ha hh hb

theorem normalizedDamped_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    (unitTrial ε a hbar hε ha hh,normalizedDamped ε a hbar hε ha hh) ∈ (inverseClockHalf ε).graph :=
  ((inverseClockHalf ε).graph.restrictScalars ℝ).smul_mem
    (‖trialState ε a hbar hε ha hh‖⁻¹) (dampedState_graph ε a hbar hε ha hh)

theorem normalizedOutput_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) :
    (unitTrial ε a hbar hε ha hh,normalizedOutput ε a hbar hε ha hh hb) ∈
      (orderedExponential ε hε hbar).graph :=
  ((orderedExponential ε hε hbar).graph.restrictScalars ℝ).smul_mem
    (‖trialState ε a hbar hε ha hh‖⁻¹) (trialState_shifted_graph ε a hbar hε ha hh hb)

theorem normalizedDamped_norm_square (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    ‖normalizedDamped ε a hbar hε ha hh‖^2 = dampedMass ε a/clockMass ε a := by
  rw [normalizedDamped,norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
    inv_pow,trial_norm_square,dampedState_mass]
  rw [← div_eq_inv_mul]
  exact mul_div_mul_right _ _ (gaussianMass_positive _ _ (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh)).ne'

theorem normalizedDamped_norm (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    ‖normalizedDamped ε a hbar hε ha hh‖ = Real.sqrt (dampedMass ε a/clockMass ε a) := by
  rw [← normalizedDamped_norm_square ε a hbar hε ha hh,Real.sqrt_sq (norm_nonneg _)]

theorem normalized_difference_square (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) :
    ‖normalizedOutput ε a hbar hε ha hh hb-normalizedDamped ε a hbar hε ha hh‖^2 =
      differenceEnergy ε a (groundWidth 1) (neutralWidth 1) hbar/
        (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) := by
  rw [normalizedOutput,normalizedDamped,← smul_sub,norm_smul,mul_pow,
    Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),inv_pow,← div_eq_inv_mul]
  exact ordered_difference_ratio ε a hbar hε ha hh hb

theorem normalized_output_strong_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ‖normalizedOutput ε a (h n) hε ha (hh n) (hb n)-
      normalizedDamped ε a (h n) hε ha (hh n)‖) atTop (𝓝 0) := by
  have hd := (differenceEnergy_continuousAt_zero ε a (groundWidth 1) (neutralWidth 1) hε ha
    (groundWidth_positive 1 one_ne_zero) (neutralWidth_positive 1 one_ne_zero) (neutralWidth_bound 1)).tendsto.comp hz
  rw [differenceEnergy_zero] at hd
  have hs : Tendsto (fun n => ‖normalizedOutput ε a (h n) hε ha (hh n) (hb n)-
      normalizedDamped ε a (h n) hε ha (hh n)‖^2) atTop (𝓝 0) := by
    simp_rw [normalized_difference_square]
    simpa only [zero_div] using hd.div_const (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1))
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs.sqrt

theorem bounded_output_pairing_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (A : Hilbert →L[ℂ] Hilbert) :
    Tendsto (fun n =>
      inner ℂ (normalizedOutput ε a (h n) hε ha (hh n) (hb n))
        (A (normalizedOutput ε a (h n) hε ha (hh n) (hb n)))-
      inner ℂ (normalizedDamped ε a (h n) hε ha (hh n))
        (A (normalizedDamped ε a (h n) hε ha (hh n)))) atTop (𝓝 0) :=
  KFCausalBoundedPairingStability.difference_tendsto A _ _ (Real.sqrt (dampedMass ε a/clockMass ε a))
    (fun n => (normalizedDamped_norm ε a (h n) hε ha (hh n)).le)
    (normalized_output_strong_limit ε a hε ha h hh hb hz)

#print axioms normalizedDamped_graph
#print axioms normalizedOutput_graph
#print axioms normalizedDamped_norm_square
#print axioms normalizedDamped_norm
#print axioms normalized_difference_square
#print axioms normalized_output_strong_limit
#print axioms bounded_output_pairing_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorStrongInitialOutput
