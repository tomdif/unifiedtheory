/- Negative integer clock frequencies suppress each actual ordered output
in physical L2 norm, by dominated convergence. The clock probability
density is unchanged. These are statements about a family of initial
states, not about the long-time evolution of one state. -/
import UnifiedTheory.Audit.KFCausalNegativeFrequencyEnergy
import UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNegativeFrequencyOutputDecay
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalNegativeFrequencyEnergy
open UnifiedTheory.Audit.KFCausalNegativeClockFrequency
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index input_factor_density)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain (factorOutput)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator

theorem phase_decay {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → Lp ℂ 2 μ) (g : Lp ℂ 2 μ) (phase : ℕ → X → ℂ)
    (he : ∀ n, f n =ᵐ[μ] fun x => phase n x*g x)
    (hb : ∀ n x, ‖phase n x‖ ≤ 1)
    (hz : ∀ x, Tendsto (fun n => ‖phase n x‖) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have hi := tendsto_integral_of_dominated_convergence (fun x => ‖g x‖^2)
    (fun n => (Lp.aestronglyMeasurable (f n)).norm.pow 2)
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g))
    (fun n => by
      filter_upwards [he n] with x hx
      change ‖‖f n x‖^2‖ ≤ ‖g x‖^2
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),hx,norm_mul]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_of_le_one_left (norm_nonneg _) (hb n x)) 2)
    (show ∀ᵐ x ∂μ, Tendsto (fun n => ‖f n x‖^2) atTop (𝓝 (0:ℝ)) from by
      filter_upwards [ae_all_iff.mpr he] with x hx
      have ht := ((hz x).mul_const ‖g x‖).pow 2
      simpa only [← norm_mul,← hx,zero_mul,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using ht)
  have hs : Tendsto (fun n => ‖f n‖^2) atTop (𝓝 (0:ℝ)) := by
    simpa only [UnifiedTheory.Audit.KFCausalAveragedEnergyGraph.l2_norm_square,
      integral_zero] using hi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,sub_zero,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hs

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (b : Fin 5 → ℂ)

theorem state_norm_ae_frequency (p q : ℝ) :
    (fun x => ‖state ε a α β hε ha hα hβ hw C p b x‖) =ᵐ[volume]
      fun x => ‖state ε a α β hε ha hα hβ hw C q b x‖ := by
  filter_upwards [state_coe ε a α β hε ha hα hβ hw C p b,
    state_coe ε a α β hε ha hα hβ hw C q b] with x hp hq
  rw [hp,hq,profile_norm_frequency C p q]

theorem defect_expectation_frequency (p q : ℝ) :
    (inner ℂ (state ε a α β hε ha hα hβ hw C p b)
      (defectOperator ε hε (state ε a α β hε ha hα hβ hw C p b))).re =
    (inner ℂ (state ε a α β hε ha hα hβ hw C q b)
      (defectOperator ε hε (state ε a α β hε ha hα hβ hw C q b))).re := by
  rw [KFCausalClockFloorInitialDriftPairing.real_multiplier_pairing volume _ _ _
      (defectOperator_coe ε hε _),
    KFCausalClockFloorInitialDriftPairing.real_multiplier_pairing volume _ _ _
      (defectOperator_coe ε hε _)]
  apply integral_congr_ae
  filter_upwards [state_norm_ae_frequency ε a α β hε ha hα hβ hw C b p q] with x hx
  rw [hx]

theorem ordered_output_tendsto_zero (h : ℝ) (hp : 0 < h)
    (hb : |h| ≤ 2*Real.pi*ε/3) (v : Fin 4 → Transverse)
    (l : Transverse →L[ℝ] ℝ) (j : Fin 3) :
    Tendsto (fun n : ℕ => factorOutput ε a α β hε ha hα hβ hw C (-(n:ℝ)) b
      h hb v l (index j)) atTop (𝓝 0) := by
  apply phase_decay volume _
    (factorOutput ε a α β hε ha hα hβ hw C 0 b h hb v l (index j))
    (fun n => frequencyPhase ε h (-(n:ℝ)))
  · intro n
    filter_upwards [input_factor_density ε a α β hε ha hα hβ hw C (-(n:ℝ)) b h hb v l j,
      input_factor_density ε a α β hε ha hα hβ hw C 0 b h hb v l j] with x hn h0
    rw [hn,h0,amplitude_frequency]
  · intro n x
    exact frequencyPhase_contraction ε h (-(n:ℝ)) hε hp hb
      (neg_nonpos.mpr (Nat.cast_nonneg n)) x
  · exact frequencyPhase_tendsto_zero ε h hε hp hb

#print axioms phase_decay
#print axioms state_norm_ae_frequency
#print axioms defect_expectation_frequency
#print axioms ordered_output_tendsto_zero
end
end UnifiedTheory.Audit.KFCausalNegativeFrequencyOutputDecay
