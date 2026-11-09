/- Convergence of the remaining integrated exponential energy and hence
all eight initial unaveraged energy contributions on canonical momentum
boosts. The varying majorant's integral convergence is proved from the
existing Fourier-energy continuity theorem. No limit is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaledLimit
import UnifiedTheory.Audit.KFCausalVaryingDominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (line line_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedEnergyLimit (spectralEnergy spectralEnergy_continuousAt_zero spectralEnergy_eq_line)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaledLimit
open UnifiedTheory.Audit.KFCausalClockFloorBoostedExponentialBound (uniformEnvelope)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorBoostedUniformEnergy (boostedCommon)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyRemainder (remainderLimit energy_remainder_tendsto)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization (gaussianMass)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy (seedEnergy)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

theorem shifted_mass_tendsto (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (h : ℕ → ℝ) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z : ℝ × Grouped, ‖line ε a α β (-h n/2) z‖^2) atTop
      (𝓝 (∫ z : ℝ × Grouped, ‖line ε a α β 0 z‖^2)) := by
  have he (n : ℕ) := spectralEnergy_eq_line ε a α β (h n) hε ha hα hβ hw (hb n)
  have h0 : spectralEnergy ε a α β 0 = ∫ z : ℝ × Grouped, ‖line ε a α β 0 z‖^2 := by
    simpa only [neg_zero,zero_div] using spectralEnergy_eq_line ε a α β 0 hε ha hα hβ hw (by simp; positivity)
  simp_rw [← he]
  rw [← h0]
  exact (spectralEnergy_continuousAt_zero ε a α β hε ha hα hβ hw).tendsto.comp hz

theorem rescaled_mass_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z : ℝ × Grouped, ‖rescaledLine ε a (h n) p z‖^2) atTop
      (𝓝 (∫ z : ℝ × Grouped, limitDensity ε a hε p z)) := by
  let C := (uniformEnvelope ε p)^2
  let α := groundWidth 1/2
  let β := neutralWidth 1/2
  have hα : 0 < α := by dsimp [α]; positivity [groundWidth_positive 1 one_ne_zero]
  have hβ : 0 < β := by dsimp [β]; positivity [neutralWidth_positive 1 one_ne_zero]
  have hw : 32*β ≤ α := by dsimp [α,β]; have := neutralWidth_bound 1; linarith
  have hm (n : ℕ) := line_memLp ε a α β (-h n/2) hε ha hα hβ hw (shift_bound ε (h n) (hb n))
  have hm0 := line_memLp ε a α β 0 hε ha hα hβ hw (by simp; positivity)
  have hi (n : ℕ) := ((memLp_two_iff_integrable_sq_norm (hm n).1).mp (hm n)).const_mul C
  have hi0 := ((memLp_two_iff_integrable_sq_norm hm0.1).mp hm0).const_mul C
  refine KFCausalVaryingDominatedConvergence.integral_tendsto volume
    (fun n z => ‖rescaledLine ε a (h n) p z‖^2)
    (fun n z => C*‖line ε a α β (-h n/2) z‖^2)
    (limitDensity ε a hε p) (fun z => C*‖line ε a α β 0 z‖^2) ?_ hi hi0 ?_ ?_ ?_ ?_ ?_
  · intro n
    have hf := rescaledLine_memLp ε a (h n) hε ha (hb n) p
    exact (memLp_two_iff_integrable_sq_norm hf.1).mp hf
  · exact fun _ _ => sq_nonneg _
  · exact fun n z => rescaled_density_bound ε a (h n) hε (hh n) (hb n) (h1 n) p z
  · exact rescaled_density_tendsto ε a hε p h hh hb hz
  · intro z
    exact (((line_shift_tendsto ε a α β hε z).comp hz).norm.pow 2).const_mul C
  · simp_rw [integral_const_mul]
    exact (shifted_mass_tendsto ε a α β hε ha hα hβ hw h hb hz).const_mul C

def exponentialLimit (ε a : ℝ) (hε : 0 < ε) (p : Configuration) : ℝ :=
  (∫ z : ℝ × Grouped, limitDensity ε a hε p z)/
    (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1))

theorem exponential_energy_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ‖boostedExponentialOutput ε a (h n) hε ha (hh n) (hb n) p‖^2)
      atTop (𝓝 (exponentialLimit ε a hε p)) := by
  simp_rw [rescaled_energy_identity]
  exact (rescaled_mass_tendsto ε a hε ha p h hh hb h1 hz).div_const _

theorem ordered_output_energy_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0)) (g : ℕ → Hilbert)
    (hg : ∀ n, (boostedState ε a (h n) hε ha (hh n) (positionFrequency p.1 p.2),g n) ∈
      (orderedExponential ε hε (h n)).graph) :
    Tendsto (fun n => ‖g n‖^2) atTop (𝓝 (exponentialLimit ε a hε p)) := by
  have he (n : ℕ) := (orderedExponential ε hε (h n)).mem_graph_snd_inj' (hg n)
    (boostedExponential_graph ε a (h n) hε ha (hh n) (hb n) p) rfl
  dsimp only [Prod.snd] at he
  simp_rw [he]
  exact exponential_energy_tendsto ε a hε ha p h hh hb h1 hz

def energyLimit (ε a : ℝ) (hε : 0 < ε) (p : Configuration) (v : Fin 4 → Transverse) (κ t : ℝ) : ℝ :=
  remainderLimit ε a p v t+Real.exp (2*t)*κ*exponentialLimit ε a hε p

theorem seed_energy_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0))
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (m g κ t : ℝ) :
    Tendsto (fun n => seedEnergy ε hε (h n) v l m g κ t
      (boostedCommon ε a (h n) hε ha (hh n) (hb n) p v l)) atTop
      (𝓝 (energyLimit ε a hε p v κ t)) := by
  have hr := energy_remainder_tendsto ε a hε ha h hh hb h1 hz p v l m g κ t
  have he := (exponential_energy_tendsto ε a hε ha p h hh hb h1 hz).const_mul (Real.exp (2*t)*κ)
  simpa only [sub_add_cancel,energyLimit] using hr.add he

theorem form_energy_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0))
    (m g κ t : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) :
    Tendsto (fun n => ‖KFCausalClosedGraphForm.energyOutput _
      (formVector ε a (h n) hε ha (hh n) (hb n) p m g κ t)‖^2) atTop
      (𝓝 (energyLimit ε a hε p modelDirections κ t)) := by
  simp_rw [formVector_energy ε a _ hε ha (hh _) (hb _) p m g κ t hm hg hκ]
  exact seed_energy_tendsto ε a hε ha p h hh hb h1 hz modelDirections pointField m g κ t

#print axioms shifted_mass_tendsto
#print axioms rescaled_mass_tendsto
#print axioms exponential_energy_tendsto
#print axioms ordered_output_energy_tendsto
#print axioms seed_energy_tendsto
#print axioms form_energy_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyLimit
