/- Negative clock modulation leaves all five static energy-factor norms
unchanged and contracts the three ordered factors. These are comparisons
of the actual sourced-Gaussian operator outputs, with the source fixed.
They do not compare independently modulated finite superpositions. -/
import UnifiedTheory.Audit.KFCausalNegativeClockFrequency
import UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNegativeFrequencyEnergy
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum
open UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain (factorOutput)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalGaussianResponseDensities (amplitude)
open UnifiedTheory.Audit.KFCausalNegativeClockFrequency

theorem profile_norm_frequency (C : ℂ) (p q α β : ℝ) (b : Fin 5 → ℂ)
    (g : ℝ → ℂ) (x : Configuration) :
    ‖physicalProfile C p α β b g x‖ = ‖physicalProfile C q α β b g x‖ := by
  simp only [physicalProfile,clockMultiplier,norm_mul,clockPhase_real_norm]

theorem profileState_norm_frequency (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (C : ℂ) (p q : ℝ) (b : Fin 5 → ℂ)
    (g : ℝ → ℂ) (hg : MemLp g 2) :
    ‖profileState α β hα hβ hw C p b g hg‖ =
      ‖profileState α β hα hβ hw C q b g hg‖ := by
  have he : ∀ᵐ x ∂volume,
      ‖profileState α β hα hβ hw C p b g hg x‖ =
        ‖profileState α β hα hβ hw C q b g hg x‖ := by
    filter_upwards [profileState_coe α β hα hβ hw C p b g hg,
      profileState_coe α β hα hβ hw C q b g hg] with x hp hq
    rw [hp,hq,profile_norm_frequency C p q]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.ge)))

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p q : ℝ) (b : Fin 5 → ℂ)

theorem state_norm_frequency :
    ‖state ε a α β hε ha hα hβ hw C p b‖ =
      ‖state ε a α β hε ha hα hβ hw C q b‖ :=
  profileState_norm_frequency α β hα hβ hw C p q b _ _

theorem clockOutput_norm_frequency :
    ‖clockOutput ε a α β hε ha hα hβ hw C p b‖ =
      ‖clockOutput ε a α β hε ha hα hβ hw C q b‖ :=
  profileState_norm_frequency α β hα hβ hw C p q b _ _

theorem momentumOutput_norm_frequency (h : ℝ) (v : Transverse) :
    ‖momentumOutput ε a α β hε ha hα hβ hw C p b h v‖ =
      ‖momentumOutput ε a α β hε ha hα hβ hw C q b h v‖ := by
  unfold momentumOutput
  simp only [norm_smul]
  congr 1
  have he : ∀ᵐ x ∂volume,
      ‖(physicalProfile_derivative_memLp C p α β hα hβ hw b
        (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha) v).toLp _ x‖ =
      ‖(physicalProfile_derivative_memLp C q α β hα hβ hw b
        (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha) v).toLp _ x‖ := by
    filter_upwards [(physicalProfile_derivative_memLp C p α β hα hβ hw b
        (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha) v).coeFn_toLp,
      (physicalProfile_derivative_memLp C q α β hα hβ hw b
        (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha) v).coeFn_toLp]
      with x hp hq
    rw [hp,hq,physicalProfile_derivative,physicalProfile_derivative]
    simp only [clockMultiplier,norm_mul,clockPhase_real_norm]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.ge)))

theorem amplitude_frequency (h : ℝ) (l : Transverse →L[ℝ] ℝ) (n : Fin 3)
    (x : Configuration) :
    amplitude ε a α β p (-h/2) b C l n x =
      frequencyPhase ε h p x * amplitude ε a α β 0 (-h/2) b C l n x := by
  simp only [amplitude,KFCausalRelativeGaussianDifferential.profile,
    KFCausalShiftedGaussianPhysicalProfile.clockAmplitude,
    KFCausalClockFloorCoherentStrip.clockPhase,Complex.ofReal_zero,zero_mul,
    Complex.exp_zero,mul_one,frequencyPhase,KFCausalClockFloorClockVelocity.inversePoint,
    KFCausalClockFloorClockVelocity.argument,KFCausalClockFloorRelativeShift.inverse,
    KFCausalClockFloorRelativeShift.argument]
  rw [mul_comm Complex.I (p:ℂ)]
  ring

theorem ordered_factor_norm_le (h : ℝ) (hh : 0 < h)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hp : p ≤ 0)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    ‖factorOutput ε a α β hε ha hα hβ hw C p b h hb v l
      (KFCausalSourcedResponseFactorBridge.index n)‖ ≤
    ‖factorOutput ε a α β hε ha hα hβ hw C 0 b h hb v l
      (KFCausalSourcedResponseFactorBridge.index n)‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [KFCausalSourcedResponseFactorBridge.input_factor_density
      ε a α β hε ha hα hβ hw C p b h hb v l n,
    KFCausalSourcedResponseFactorBridge.input_factor_density
      ε a α β hε ha hα hβ hw C 0 b h hb v l n] with x hp' h0
  rw [hp',h0,amplitude_frequency,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (frequencyPhase_contraction ε h p hε hh hb hp x)

theorem factor_norm_le (h : ℝ) (hh : 0 < h)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hp : p ≤ 0)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    ‖factorOutput ε a α β hε ha hα hβ hw C p b h hb v l i‖ ≤
      ‖factorOutput ε a α β hε ha hα hβ hw C 0 b h hb v l i‖ := by
  fin_cases i
  · exact (clockOutput_norm_frequency ε a α β hε ha hα hβ hw C p 0 b).le
  · exact (momentumOutput_norm_frequency ε a α β hε ha hα hβ hw C p 0 b h (v 0)).le
  · exact (momentumOutput_norm_frequency ε a α β hε ha hα hβ hw C p 0 b h (v 1)).le
  · exact (momentumOutput_norm_frequency ε a α β hε ha hα hβ hw C p 0 b h (v 2)).le
  · exact (momentumOutput_norm_frequency ε a α β hε ha hα hβ hw C p 0 b h (v 3)).le
  · exact ordered_factor_norm_le ε a α β hε ha hα hβ hw C p b h hh hb hp v l 1
  · exact ordered_factor_norm_le ε a α β hε ha hα hβ hw C p b h hh hb hp v l 2
  · exact ordered_factor_norm_le ε a α β hε ha hα hβ hw C p b h hh hb hp v l 0

theorem weighted_energy_le (h : ℝ) (hh : 0 < h)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hp : p ≤ 0)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (w : Fin 8 → ℝ) (hw' : ∀ i, 0 ≤ w i) :
    (∑ i, w i * ‖factorOutput ε a α β hε ha hα hβ hw C p b h hb v l i‖^2) ≤
      ∑ i, w i * ‖factorOutput ε a α β hε ha hα hβ hw C 0 b h hb v l i‖^2 := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw' i)
  exact pow_le_pow_left₀ (norm_nonneg _)
    (factor_norm_le ε a α β hε ha hα hβ hw C p b h hh hb hp v l i) 2

#print axioms profile_norm_frequency
#print axioms profileState_norm_frequency
#print axioms state_norm_frequency
#print axioms clockOutput_norm_frequency
#print axioms momentumOutput_norm_frequency
#print axioms amplitude_frequency
#print axioms ordered_factor_norm_le
#print axioms factor_norm_le
#print axioms weighted_energy_le
end
end UnifiedTheory.Audit.KFCausalNegativeFrequencyEnergy
