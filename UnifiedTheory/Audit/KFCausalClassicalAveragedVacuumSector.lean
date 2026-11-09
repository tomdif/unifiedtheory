/- The earlier reduced vacuum system embeds in the charge-averaged classical
candidate: its transverse Hamiltonian derivatives vanish at zero, its clock
Hamiltonian is exactly the earlier one, and global reduced trajectories exist.
This validates this classical sector, not its quantum dynamical limit. -/
import UnifiedTheory.Audit.KFCausalClassicalAveragedVacuumDecay
import UnifiedTheory.Audit.KFCausalClockFloorVacuumReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalAveragedVacuumSector
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalChargeLaplace
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuumDecay (defect_tendsto_zero)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)

theorem zero_values (C t : ℝ) : kineticMean t 0 = 0 ∧
    exponentialMean C 0 = 1 ∧ tiltedShear C 0 = 0 := by
  have hr (θ : ℝ) : rotate θ (0:Phase) = 0 := by
    simpa only [zero_smul] using rotate_smul θ 0 (0:Phase)
  have hd : shear (0:Phase) = 0 := by simp [shear_eq, diagonalPairing]
  constructor
  · simp [kineticMean_eq]
  · simp [exponentialMean, tiltedShear, hr, hd, mean_const]

theorem hamiltonian_zero (ε κ t s p : ℝ) :
    hamiltonian ε κ t 0 s p = KFCausalClockFloorVacuumReduction.canonicalHamiltonian ε κ t s p := by
  rw [hamiltonian, (zero_values (clock ε s) t).1, (zero_values (clock ε s) t).2.1]
  simp [amplitude, KFCausalClockFloorVacuumReduction.canonicalHamiltonian,
    KFCausalClockFloorClassicalBackreaction.hamiltonian,
    KFCausalClockFloorClassicalBackreaction.potential,
    KFCausalClockFloorCanonicalDefect.longitudinal, Real.exp_add]
  ring

theorem kineticMean_smul (t a : ℝ) (z : Phase) : kineticMean t (a • z) = a^2*kineticMean t z := by
  simp only [kineticMean, rotate_smul, kinetic_smul]
  simp_rw [mul_comm (a^2)]
  exact mean_mul_const _ _

theorem transverse_derivative_zero (ε κ t s p : ℝ) (z : Phase) :
    HasDerivAt (fun u : ℝ => hamiltonian ε κ t (u • z) s p) 0 0 := by
  let C := clock ε s
  have he (u : ℝ) : exponentialMean C (u • z) =
      mean (fun θ => Real.exp ((u^2/C)*shear (rotate θ z))) := by
    simp only [exponentialMean, rotate_smul, shear_smul]
    congr 1
    funext θ
    congr 1
    ring
  have hq : HasDerivAt (fun u : ℝ => u^2) 0 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).pow 2
  have he' := (mean_exp_derivative (fun θ => shear (rotate θ z)) (shear_continuous z) ((0:ℝ)^2/C)).comp 0
    (show HasDerivAt (fun u : ℝ => u^2/C) 0 0 by simpa using hq.div_const C)
  have hd : HasDerivAt (fun u : ℝ => exponentialMean C (u • z)) 0 0 := by
    simpa only [Function.comp_def, mul_zero, ← he] using he'
  have h := (((hq.mul_const (kineticMean t z)).add (hd.const_mul (amplitude ε κ t s p))).div_const C).const_add (C/2)
  convert h using 1
  · funext u
    rw [hamiltonian, kineticMean_smul]
    rfl
  · ring

/-- An actual globally defined classical solution in the zero transverse
sector, with the transverse directional derivatives and clock equations
explicitly verified for the averaged candidate. -/
theorem exists_global_zero_sector (ε κ s₀ p₀ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ s p : ℝ → ℝ, s 0 = s₀ ∧ p 0 = p₀ ∧
      (∀ t, HasDerivAt s (clockRate ε κ t 0 (s t) (p t)) t) ∧
      (∀ t, HasDerivAt p (momentumRate ε κ t 0 (s t) (p t)) t) ∧
      (∀ t z, HasDerivAt (fun u : ℝ => hamiltonian ε κ t (u • z) (s t) (p t)) 0 0) ∧
      Tendsto (fun t => defect ε (s t)) atTop (𝓝 0) := by
  obtain ⟨s,p,hs0,hp0,hs,hp,_⟩ :=
    KFCausalClockFloorVacuumReconstruction.exists_global_canonical ε κ s₀ p₀ hε
  have hs' (t : ℝ) : HasDerivAt s (clockRate ε κ t 0 (s t) (p t)) t := by
    have he : KFCausalClockFloorVacuumReduction.canonicalHamiltonian ε κ t (s t) =
        hamiltonian ε κ t 0 (s t) := funext (fun p => (hamiltonian_zero ε κ t (s t) p).symm)
    simpa only [he, (hamiltonian_momentum_derivative ε κ t 0 (s t) (p t)).deriv] using hs t
  have hp' (t : ℝ) : HasDerivAt p (momentumRate ε κ t 0 (s t) (p t)) t := by
    have he : (fun x => KFCausalClockFloorVacuumReduction.canonicalHamiltonian ε κ t x (p t)) =
        (fun x => hamiltonian ε κ t 0 x (p t)) := funext (fun x => (hamiltonian_zero ε κ t x (p t)).symm)
    simpa only [he, (hamiltonian_clock_derivative ε κ t hε.le 0 (s t) (p t)).deriv, neg_neg] using hp t
  exact ⟨s,p,hs0,hp0,hs',hp',fun t z => transverse_derivative_zero ε κ t (s t) (p t) z,
    defect_tendsto_zero ε κ hε (fun _ => 0) s p hs' hp' hκ⟩

#print axioms zero_values
#print axioms hamiltonian_zero
#print axioms kineticMean_smul
#print axioms transverse_derivative_zero
#print axioms exists_global_zero_sector

end
end UnifiedTheory.Audit.KFCausalClassicalAveragedVacuumSector
