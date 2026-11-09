/- Seven of the eight actual boosted factor energies have explicit limits.
After subtracting the exact longitudinal exponential contribution, the full
unaveraged seed energy converges to its clock and transverse kinetic value.
The subtracted contribution is uniformly bounded, but its limit is not
assumed or proved here. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedUniformEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyRemainder
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit
open UnifiedTheory.Audit.KFCausalClockFloorBoostedUniformEnergy
open UnifiedTheory.Audit.KFCausalClockFloorBoostedMatterLimit
open UnifiedTheory.Audit.KFCausalClockFloorBoostedMatterBounds (quadraticBudget)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedExponentialBound (exponentialMass)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy

def factorLimit (ε a : ℝ) (p : Configuration) (v : Fin 4 → Transverse) : Fin 7 → ℝ :=
  ![halfMass ε a/clockMass ε a,
    (positionFrequency p.1 p.2 (0,v 0))^2*dampedMass ε a/clockMass ε a,
    (positionFrequency p.1 p.2 (0,v 1))^2*dampedMass ε a/clockMass ε a,
    (positionFrequency p.1 p.2 (0,v 2))^2*dampedMass ε a/clockMass ε a,
    (positionFrequency p.1 p.2 (0,v 3))^2*dampedMass ε a/clockMass ε a,0,0]

theorem factor_energy_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0))
    (p : Configuration) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 7) :
    Tendsto (fun n => ‖factorValue ε hε (h n) v l
      (boostedCommon ε a (h n) hε ha (hh n) (hb n) p v l) i.castSucc‖^2)
      atTop (𝓝 (factorLimit ε a p v i)) := by
  have hg (n : ℕ) (j : Fin 8) := boosted_factor_graph ε a (h n) hε ha (hh n) (hb n) p v l j
  fin_cases i
  · have he (n : ℕ) := clock_output_mass ε a (h n) hε ha (hh n) _ _ (hg n 0)
    change Tendsto (fun n => ‖factorValue ε hε (h n) v l
      (boostedCommon ε a (h n) hε ha (hh n) (hb n) p v l) 0‖^2) atTop
      (𝓝 (halfMass ε a/clockMass ε a))
    simp_rw [he]
    exact tendsto_const_nhds
  · have he (n : ℕ) := (clockMomentum ε (h n) (v 0)).mem_graph_snd_inj' (hg n 1)
      (boostedOutput_graph ε a (h n) hε ha (hh n) (v 0) (positionFrequency p.1 p.2)) rfl
    dsimp only [Prod.snd] at he
    change Tendsto (fun n => ‖factorValue ε hε (h n) v l
      (boostedCommon ε a (h n) hε ha (hh n) (hb n) p v l) 1‖^2) atTop
      (𝓝 ((positionFrequency p.1 p.2 (0,v 0))^2*dampedMass ε a/clockMass ε a))
    simp_rw [he]
    exact boostedOutput_energy_limit ε a hε ha h hh hz (v 0) (positionFrequency p.1 p.2)
  · have he (n : ℕ) := (clockMomentum ε (h n) (v 1)).mem_graph_snd_inj' (hg n 2)
      (boostedOutput_graph ε a (h n) hε ha (hh n) (v 1) (positionFrequency p.1 p.2)) rfl
    dsimp only [Prod.snd] at he
    change Tendsto (fun n => ‖factorValue ε hε (h n) v l
      (boostedCommon ε a (h n) hε ha (hh n) (hb n) p v l) 2‖^2) atTop
      (𝓝 ((positionFrequency p.1 p.2 (0,v 1))^2*dampedMass ε a/clockMass ε a))
    simp_rw [he]
    exact boostedOutput_energy_limit ε a hε ha h hh hz (v 1) (positionFrequency p.1 p.2)
  · have he (n : ℕ) := (clockMomentum ε (h n) (v 2)).mem_graph_snd_inj' (hg n 3)
      (boostedOutput_graph ε a (h n) hε ha (hh n) (v 2) (positionFrequency p.1 p.2)) rfl
    dsimp only [Prod.snd] at he
    change Tendsto (fun n => ‖factorValue ε hε (h n) v l
      (boostedCommon ε a (h n) hε ha (hh n) (hb n) p v l) 3‖^2) atTop
      (𝓝 ((positionFrequency p.1 p.2 (0,v 2))^2*dampedMass ε a/clockMass ε a))
    simp_rw [he]
    exact boostedOutput_energy_limit ε a hε ha h hh hz (v 2) (positionFrequency p.1 p.2)
  · have he (n : ℕ) := (clockMomentum ε (h n) (v 3)).mem_graph_snd_inj' (hg n 4)
      (boostedOutput_graph ε a (h n) hε ha (hh n) (v 3) (positionFrequency p.1 p.2)) rfl
    dsimp only [Prod.snd] at he
    change Tendsto (fun n => ‖factorValue ε hε (h n) v l
      (boostedCommon ε a (h n) hε ha (hh n) (hb n) p v l) 4‖^2) atTop
      (𝓝 ((positionFrequency p.1 p.2 (0,v 3))^2*dampedMass ε a/clockMass ε a))
    simp_rw [he]
    exact boostedOutput_energy_limit ε a hε ha h hh hz (v 3) (positionFrequency p.1 p.2)
  · have ht : Tendsto (fun n => |h n| *(exponentialMass ε a p+quadraticBudget ε a p l)/clockMass ε a)
        atTop (𝓝 0) := by
      simpa only [abs_zero,zero_mul,zero_div] using
        (hz.abs.mul_const (exponentialMass ε a p+quadraticBudget ε a p l)).div_const (clockMass ε a)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => sq_nonneg _) (fun n => linear_output_rate ε a (h n) hε ha (hh n) (hb n) (h1 n) p l _ (hg n 5))
  · have ht : Tendsto (fun n => (h n)^2*quadraticBudget ε a p l/clockMass ε a) atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0),zero_mul,zero_div] using
        ((hz.pow 2).mul_const (quadraticBudget ε a p l)).div_const (clockMass ε a)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => sq_nonneg _) (fun n => quadratic_output_rate ε a (h n) hε ha (hh n) (hb n) (h1 n) p l _ (hg n 6))

def remainderLimit (ε a : ℝ) (p : Configuration) (v : Fin 4 → Transverse) (t : ℝ) : ℝ :=
  (factorLimit ε a p v 0+factorLimit ε a p v 1+factorLimit ε a p v 2)/2+
    Real.exp (2*t)*((factorLimit ε a p v 3+factorLimit ε a p v 4)/2)

theorem energy_remainder_identity (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (v : Fin 4 → Transverse)
    (l : Transverse →L[ℝ] ℝ) (m g κ t : ℝ) :
    seedEnergy ε hε h v l m g κ t (boostedCommon ε a h hε ha hh hb p v l)-
        Real.exp (2*t)*κ*‖boostedExponentialOutput ε a h hε ha hh hb p‖^2 =
      seedEnergy ε hε h v l m g 0 t (boostedCommon ε a h hε ha hh hb p v l) := by
  have he := (orderedExponential ε hε h).mem_graph_snd_inj'
    (boosted_factor_graph ε a h hε ha hh hb p v l 7)
    (boostedExponential_graph ε a h hε ha hh hb p) rfl
  dsimp only [Prod.snd] at he
  unfold seedEnergy
  rw [he]
  ring

theorem energy_remainder_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0))
    (p : Configuration) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (m g κ t : ℝ) :
    Tendsto (fun n => seedEnergy ε hε (h n) v l m g κ t
        (boostedCommon ε a (h n) hε ha (hh n) (hb n) p v l)-
      Real.exp (2*t)*κ*‖boostedExponentialOutput ε a (h n) hε ha (hh n) (hb n) p‖^2)
      atTop (𝓝 (remainderLimit ε a p v t)) := by
  simp_rw [energy_remainder_identity]
  have ht (i : Fin 7) := factor_energy_tendsto ε a hε ha h hh hb h1 hz p v l i
  have H := (((ht 0).add (ht 1)).add (ht 2)).div_const 2 |>.add
    (((((ht 3).add (ht 4)).div_const 2).add ((ht 5).const_mul (m/2))).add
      ((ht 6).const_mul (g/4)) |>.const_mul (Real.exp (2*t)))
  convert H using 1 <;> simp [seedEnergy,remainderLimit,factorLimit]

#print axioms factor_energy_tendsto
#print axioms energy_remainder_identity
#print axioms energy_remainder_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyRemainder
