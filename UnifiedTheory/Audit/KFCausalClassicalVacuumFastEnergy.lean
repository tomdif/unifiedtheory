/- Actual global trajectories in the zero-transverse invariant sector of
the averaged classical vacuum candidate recover the clock while exp(-t)E
diverges. No identification with a quantum trajectory is made. -/
import UnifiedTheory.Audit.KFCausalClockFloorVacuumEnergyGrowth
import UnifiedTheory.Audit.KFCausalClassicalAveragedVacuumSector

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumFastEnergy
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect clock_positive)
open UnifiedTheory.Audit.KFCausalClockFloorVacuumReduction

theorem canonical_discounted_energy_tendsto_atTop (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (s p : ℝ → ℝ)
    (hs : ∀ t, HasDerivAt s (deriv (canonicalHamiltonian ε κ t (s t)) (p t)) t)
    (hp : ∀ t, HasDerivAt p (-deriv (fun x => canonicalHamiltonian ε κ t x (p t)) (s t)) t) :
    Tendsto (fun t => Real.exp (-t)*canonicalHamiltonian ε κ t (s t) (p t)) atTop atTop := by
  have hd (t : ℝ) := longitudinal_equations ε κ hε s p t (hs t) (hp t)
  have he (t : ℝ) : canonicalHamiltonian ε κ t (s t) (p t) =
      energy ε κ t (s t) (p t/clock ε (s t)) := by
    have hc := (clock_positive ε (s t) hε.le).ne'
    simpa only [mul_div_cancel₀ _ hc] using energy_canonical ε κ t (s t) (p t/clock ε (s t)) hε
  simpa only [he] using KFCausalClockFloorVacuumEnergyGrowth.discounted_energy_tendsto_atTop
    ε κ hε s (fun t => p t/clock ε (s t)) (fun t => (hd t).1) (fun t => (hd t).2) hκ

open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuumSector

theorem exists_global_recovery_with_fast_energy (ε κ s₀ p₀ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ s p : ℝ → ℝ, s 0 = s₀ ∧ p 0 = p₀ ∧
      (∀ t, HasDerivAt s (clockRate ε κ t 0 (s t) (p t)) t) ∧
      (∀ t, HasDerivAt p (momentumRate ε κ t 0 (s t) (p t)) t) ∧
      (∀ t z, HasDerivAt (fun u : ℝ => hamiltonian ε κ t (u • z) (s t) (p t)) 0 0) ∧
      Tendsto (fun t => defect ε (s t)) atTop (𝓝 0) ∧
      Tendsto (fun t => Real.exp (-t)*hamiltonian ε κ t 0 (s t) (p t)) atTop atTop := by
  obtain ⟨s,p,hs0,hp0,hs,hp,_⟩ :=
    KFCausalClockFloorVacuumReconstruction.exists_global_canonical ε κ s₀ p₀ hε
  have hs' (t : ℝ) : HasDerivAt s (clockRate ε κ t 0 (s t) (p t)) t := by
    have he : canonicalHamiltonian ε κ t (s t) =
        hamiltonian ε κ t 0 (s t) := funext (fun p => (hamiltonian_zero ε κ t (s t) p).symm)
    simpa only [he, (hamiltonian_momentum_derivative ε κ t 0 (s t) (p t)).deriv] using hs t
  have hp' (t : ℝ) : HasDerivAt p (momentumRate ε κ t 0 (s t) (p t)) t := by
    have he : (fun x => canonicalHamiltonian ε κ t x (p t)) =
        (fun x => hamiltonian ε κ t 0 x (p t)) := funext (fun x => (hamiltonian_zero ε κ t x (p t)).symm)
    simpa only [he, (hamiltonian_clock_derivative ε κ t hε.le 0 (s t) (p t)).deriv, neg_neg] using hp t
  refine ⟨s,p,hs0,hp0,hs',hp',fun t z => transverse_derivative_zero ε κ t (s t) (p t) z,
    KFCausalClassicalAveragedVacuumDecay.defect_tendsto_zero ε κ hε (fun _ => 0) s p hs' hp' hκ,?_⟩
  simpa only [hamiltonian_zero] using canonical_discounted_energy_tendsto_atTop ε κ hε hκ s p hs hp

#print axioms canonical_discounted_energy_tendsto_atTop
#print axioms exists_global_recovery_with_fast_energy
end
end UnifiedTheory.Audit.KFCausalClassicalVacuumFastEnergy
