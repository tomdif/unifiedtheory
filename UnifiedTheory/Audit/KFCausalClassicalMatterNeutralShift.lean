/- Neutral-position velocity is obtained by shifting its conjugate momentum.
Matter changes neutral momentum, but its field weight is independent of that
momentum; this gives an exact weighted integral for the position velocity. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterNeutralShift
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalWeightedLaplace
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p q_apply p_apply TimePhase)
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE (momentumBasis)
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum (kineticMean kineticMean_eq)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)

def momentumShift (u : ℝ) (z : Phase) : Phase := z+u • momentumBasis (.inr 3)

def slope (θ : ℝ) (z : Phase) : ℝ :=
  2*scale*(Real.sin θ*p (.inl 1) z+Real.cos θ*q (.inr 2) z)

def neutralMean (m g κ C : ℝ) (z : Phase) : ℝ :=
  mean (fun θ => potential m g κ (rotate θ z)*Real.exp (shear (rotate θ z)/C)*slope θ z)

theorem slope_continuous (z : Phase) : Continuous (fun θ => slope θ z) := by
  unfold slope
  fun_prop

theorem momentumShift_clock (u : ℝ) (z : Phase) :
    q (.inr 0) (momentumShift u z) = q (.inr 0) z ∧
    p (.inr 0) (momentumShift u z) = p (.inr 0) z := by
  simp [momentumShift,q_apply,p_apply,momentumBasis,PiLp.basisFun_apply]

theorem fieldValue_momentumShift (θ u : ℝ) (z : Phase) :
    fieldValue (rotate θ (momentumShift u z)) = fieldValue (rotate θ z) := by
  simp [fieldValue_rotate,momentumShift,momentumBasis,PiLp.basisFun_apply]

theorem shear_momentumShift (θ u : ℝ) (z : Phase) :
    shear (rotate θ (momentumShift u z)) = shear (rotate θ z)+u*slope θ z := by
  simp [shear_rotate,diagonalPairing,crossPairing,momentumShift,momentumBasis,
    PiLp.basisFun_apply,slope,q_apply,p_apply]
  ring

theorem kineticMean_momentumShift (t u : ℝ) (z : Phase) :
    kineticMean t (momentumShift u z) = kineticMean t z+p (.inr 3) z*u+u^2/2 := by
  simp [kineticMean_eq,momentumShift,momentumBasis,PiLp.basisFun_apply,p_apply]
  ring

theorem weightedMean_momentum_derivative (m g κ C : ℝ) (z : Phase) :
    HasDerivAt (fun u => weightedMean m g κ C (momentumShift u z)) (neutralMean m g κ C z/C) 0 := by
  let w : ℝ → ℝ := fun θ => potential m g κ (rotate θ z)*Real.exp (shear (rotate θ z)/C)
  let f : ℝ → ℝ := fun θ => slope θ z/C
  have hw : Continuous w := by
    have hp := potential_continuous m g κ z
    have hs := shear_continuous z
    dsimp [w]
    fun_prop
  have hf : Continuous f := (slope_continuous z).div_const C
  have hd := mean_weighted_exp_derivative w f hw hf 0
  have he (u : ℝ) : mean (fun θ => w θ*Real.exp (u*f θ)) =
      weightedMean m g κ C (momentumShift u z) := by
    unfold weightedMean
    congr 1
    funext θ
    simp only [potential,fieldValue_momentumShift,shear_momentumShift,w,f]
    rw [add_div,Real.exp_add,show u*(slope θ z/C) = u*slope θ z/C by ring]
    ring
  simp only [he,zero_mul,Real.exp_zero,mul_one] at hd
  convert hd using 1
  unfold neutralMean
  rw [div_eq_mul_inv,← mean_mul_const]
  congr 1
  funext θ
  dsimp [w,f]
  ring

theorem fullHamiltonian_momentum_derivative (ε m g κ : ℝ) (x : TimePhase) :
    HasDerivAt (fun u => fullHamiltonian ε m g κ (x.1,momentumShift u x.2))
      (p (.inr 3) x.2/clock ε (q (.inr 0) x.2)+
        amplitude ε x.1 (q (.inr 0) x.2) (p (.inr 0) x.2)*
          neutralMean m g κ (clock ε (q (.inr 0) x.2)) x.2/(clock ε (q (.inr 0) x.2))^2) 0 := by
  have hk : HasDerivAt (fun u => kineticMean x.1 (momentumShift u x.2)) (p (.inr 3) x.2) 0 := by
    simp_rw [kineticMean_momentumShift]
    convert (((hasDerivAt_id (0:ℝ)).const_mul (p (.inr 3) x.2)).add
      (((hasDerivAt_id (0:ℝ)).pow 2).div_const 2)).const_add (kineticMean x.1 x.2) using 1
    · funext u; simp only [id_eq,Pi.add_apply,Pi.pow_apply]; ring
    · simp
  have hf := (weightedMean_momentum_derivative m g κ (clock ε (q (.inr 0) x.2)) x.2).const_mul
    (amplitude ε x.1 (q (.inr 0) x.2) (p (.inr 0) x.2))
  have h := ((hk.add hf).div_const (clock ε (q (.inr 0) x.2))).const_add (clock ε (q (.inr 0) x.2)/2)
  simp only [fullHamiltonian,(momentumShift_clock _ _).1,(momentumShift_clock _ _).2,hamiltonian]
  convert h using 1
  ring

theorem field_neutralPosition (ε m g κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    q (.inr 3) (field ε m g κ x).2 =
      p (.inr 3) x.2/clock ε (q (.inr 0) x.2)+
        amplitude ε x.1 (q (.inr 0) x.2) (p (.inr 0) x.2)*
          neutralMean m g κ (clock ε (q (.inr 0) x.2)) x.2/(clock ε (q (.inr 0) x.2))^2 := by
  have hd : HasFDerivAt (fullHamiltonian ε m g κ) (fderiv ℝ (fullHamiltonian ε m g κ) x) x :=
    ((fullHamiltonian_contDiff ε m g κ hε 1).differentiable (by norm_num) x).hasFDerivAt
  have hl : HasDerivAt (fun u : ℝ => (x.1,momentumShift u x.2)) (0,momentumBasis (.inr 3)) 0 := by
    convert (hasDerivAt_const (0:ℝ) x.1).prodMk
      ((hasDerivAt_const (0:ℝ) x.2).add ((hasDerivAt_id (0:ℝ)).smul_const (momentumBasis (.inr 3)))) using 1
    simp
  have hc := hd.comp_hasDerivAt_of_eq 0 hl (by simp [momentumShift])
  change fderiv ℝ (fullHamiltonian ε m g κ) x (0,momentumBasis (.inr 3)) = _
  exact hc.unique (fullHamiltonian_momentum_derivative ε m g κ x)

#print axioms slope_continuous
#print axioms momentumShift_clock
#print axioms fieldValue_momentumShift
#print axioms shear_momentumShift
#print axioms kineticMean_momentumShift
#print axioms weightedMean_momentum_derivative
#print axioms fullHamiltonian_momentum_derivative
#print axioms field_neutralPosition

end
end UnifiedTheory.Audit.KFCausalClassicalMatterNeutralShift
