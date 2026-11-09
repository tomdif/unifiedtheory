/- The neutral position is cyclic in the full averaged vacuum Hamiltonian,
so its conjugate momentum is conserved under the derived canonical ODE. -/
import UnifiedTheory.Audit.KFCausalClassicalVacuumClockComponents

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumNeutral
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE

def neutralShift (u : ℝ) (z : Phase) : Phase := z+u • positionBasis (.inr 3)

theorem neutralShift_clock (u : ℝ) (z : Phase) :
    q (.inr 0) (neutralShift u z) = q (.inr 0) z ∧
    p (.inr 0) (neutralShift u z) = p (.inr 0) z := by
  simp [neutralShift,q_apply,p_apply,positionBasis,PiLp.basisFun_apply]

theorem shear_neutralShift (θ u : ℝ) (z : Phase) :
    shear (rotate θ (neutralShift u z)) = shear (rotate θ z) := by
  simp [shear_rotate,diagonalPairing,crossPairing,neutralShift,positionBasis,PiLp.basisFun_apply]

theorem kineticMean_neutralShift (t u : ℝ) (z : Phase) :
    kineticMean t (neutralShift u z) = kineticMean t z := by
  simp [kineticMean_eq,neutralShift,positionBasis,PiLp.basisFun_apply]

theorem exponentialMean_neutralShift (C u : ℝ) (z : Phase) :
    exponentialMean C (neutralShift u z) = exponentialMean C z := by
  simp only [exponentialMean,shear_neutralShift]

theorem fullHamiltonian_neutralShift (ε κ t u : ℝ) (z : Phase) :
    fullHamiltonian ε κ (t,neutralShift u z) = fullHamiltonian ε κ (t,z) := by
  simp only [fullHamiltonian,(neutralShift_clock u z).1,(neutralShift_clock u z).2,
    hamiltonian,kineticMean_neutralShift,exponentialMean_neutralShift]

theorem field_neutralMomentum (ε κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    p (.inr 3) (field ε κ x).2 = 0 := by
  have hd : HasFDerivAt (fullHamiltonian ε κ) (fderiv ℝ (fullHamiltonian ε κ) x) x :=
    ((fullHamiltonian_contDiff ε κ hε 1).differentiable (by norm_num) x).hasFDerivAt
  have hl : HasDerivAt (fun u : ℝ => (x.1,neutralShift u x.2))
      (0,positionBasis (.inr 3)) 0 := by
    convert (hasDerivAt_const (0:ℝ) x.1).prodMk
      ((hasDerivAt_const (0:ℝ) x.2).add ((hasDerivAt_id (0:ℝ)).smul_const (positionBasis (.inr 3)))) using 1
    simp
  have hc := hd.comp_hasDerivAt_of_eq 0 hl (by simp [neutralShift])
  have hz : HasDerivAt (fun u : ℝ => fullHamiltonian ε κ (x.1,neutralShift u x.2)) 0 0 := by
    simpa only [fullHamiltonian_neutralShift] using hasDerivAt_const (0:ℝ) (fullHamiltonian ε κ x)
  change -fderiv ℝ (fullHamiltonian ε κ) x (0,positionBasis (.inr 3)) = 0
  rw [hc.unique hz,neg_zero]

theorem neutralMomentum_constant (ε κ : ℝ) (hε : 0 ≤ ε) (γ : ℝ → TimePhase)
    (hγ : ∀ t, HasDerivAt γ (field ε κ (γ t)) t) (t : ℝ) :
    p (.inr 3) (γ t).2 = p (.inr 3) (γ 0).2 := by
  have hd (u : ℝ) : HasDerivAt (fun v => p (.inr 3) (γ v).2) 0 u := by
    have h : HasDerivAt (fun v => p (.inr 3) (γ v).2) (p (.inr 3) (field ε κ (γ u)).2) u :=
      (p (.inr 3)).hasFDerivAt.comp_hasDerivAt u (hγ u).snd
    simpa only [field_neutralMomentum ε κ hε] using h
  exact is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0

#print axioms neutralShift_clock
#print axioms shear_neutralShift
#print axioms kineticMean_neutralShift
#print axioms exponentialMean_neutralShift
#print axioms fullHamiltonian_neutralShift
#print axioms field_neutralMomentum
#print axioms neutralMomentum_constant

end
end UnifiedTheory.Audit.KFCausalClassicalVacuumNeutral
