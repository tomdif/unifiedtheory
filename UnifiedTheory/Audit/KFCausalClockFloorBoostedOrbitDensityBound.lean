/- The recentered full line densities have one small-hbar Gaussian
envelope for the whole actual boosted charge orbit. The envelope retains
the clock Gaussian; integral change of variables is a separate step. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedDensityBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedOrbitDensityBound
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedDensityBound
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedLineDensity (boostedLine boostedLine_norm)
open UnifiedTheory.Audit.KFCausalClockFloorCenteredEstimates
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase (shear)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (Phase rotate physicalTail)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

theorem amplitudeBound_continuous (ε : ℝ) :
    Continuous (fun z : Transverse × Transverse => amplitudeBound ε z.1 z.2) := by
  simp [amplitudeBound,energy_eq,momentumBound,coefficients,shear,
    KFCausalTransverseDilationFlow.velocity,Fin.sum_univ_succ]
  fun_prop

theorem amplitudeBound_orbit (ε : ℝ) (z : Phase) :
    ∃ K : ℝ, ∀ θ, amplitudeBound ε (physicalTail (rotate (-θ) z).1) (physicalTail (rotate (-θ) z).2) ≤ K := by
  have hQ : Continuous (fun θ => physicalTail (rotate θ z).1) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [physicalTail,KFCausalPairedModeCoordinates.backward,rotate] <;> fun_prop
  have hP : Continuous (fun θ => physicalTail (rotate θ z).2) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [physicalTail,KFCausalPairedModeCoordinates.backward,rotate] <;> fun_prop
  have hc := (amplitudeBound_continuous ε).comp
    (f := fun θ => (physicalTail (rotate θ z).1,physicalTail (rotate θ z).2)) (hQ.prodMk hP)
  have hp : Function.Periodic
      (fun θ => amplitudeBound ε (physicalTail (rotate θ z).1) (physicalTail (rotate θ z).2)) (2*Real.pi) := by
    intro θ
    dsimp only
    rw [KFCausalDisplacedClassicalAverage.rotate_period]
  obtain ⟨K,hK⟩ := (hp.compact_of_continuous (by positivity) hc).bddAbove
  exact ⟨K,fun θ => hK ⟨-θ,rfl⟩⟩

theorem boostedLine_uniform_bound (ε a : ℝ) (hε : 0 < ε) (ha : 0 ≤ a) (p : Configuration) :
    ∃ B : ℝ, ∀ (θ u h : ℝ), h ≠ 0 → |h| ≤ 2*Real.pi*ε/3 → |h| ≤ ε/2 → |h| ≤ 1 →
      ∀ ξ : Transverse, ‖boostedLine ε a hε u h p θ ξ‖^2 ≤
        B*‖clockFactor a (u:ℂ)‖^2*Real.exp (-energy ξ/4) := by
  obtain ⟨K,hK⟩ := amplitudeBound_orbit ε (0,KFCausalClassicalPhysicalPhase.toPaired p)
  refine ⟨Real.exp (|p.1|/ε+a/2)*K,?_⟩
  intro θ u h hh hb hsmall h1 ξ
  rw [boostedLine_norm ε a hε u h hh]
  apply (centeredLine_bound ε a u h p.1 hε ha hh hb hsmall h1 _ _ ξ).trans
  gcongr
  exact hK θ

#print axioms amplitudeBound_continuous
#print axioms amplitudeBound_orbit
#print axioms boostedLine_uniform_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedOrbitDensityBound
