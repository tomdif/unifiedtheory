/- Uniform estimates on finite time windows. Constants depend on the initial
state and window, but not on an auxiliary phase cutoff. -/
import UnifiedTheory.Audit.KFCausalClassicalVacuumMomentumBounds
import UnifiedTheory.Audit.KFCausalClassicalVacuumCoercivity
import UnifiedTheory.Audit.KFCausalClassicalVacuumDamping

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumWindow
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergy
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds
open UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds
open UnifiedTheory.Audit.KFCausalClassicalVacuumMomentumBounds
open UnifiedTheory.Audit.KFCausalClassicalVacuumTranslation
open UnifiedTheory.Audit.KFCausalClassicalVacuumCoercivity
open UnifiedTheory.Audit.KFCausalClassicalVacuumDamping

theorem scalar_drift_bound (f d : ℝ → ℝ) (T M : ℝ) (hT : 0 ≤ T)
    (hd : ∀ u ∈ Icc (-T) T, HasDerivAt f (d u) u)
    (hb : ∀ u ∈ Icc (-T) T, |d u| ≤ M) (t : ℝ) (ht : t ∈ Icc (-T) T) :
    |f t-f 0| ≤ M*|t| := by
  simpa only [Real.norm_eq_abs,sub_zero] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hd u hu).hasDerivWithinAt)
      (fun u hu => by simpa only [Real.norm_eq_abs] using hb u hu)
      (convex_Icc (-T) T) (show (0:ℝ) ∈ Icc (-T) T by constructor <;> linarith) ht

theorem scalar_window_value_bound (f d : ℝ → ℝ) (T M : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hd : ∀ u ∈ Icc (-T) T, HasDerivAt f (d u) u)
    (hb : ∀ u ∈ Icc (-T) T, |d u| ≤ M) (t : ℝ) (ht : t ∈ Icc (-T) T) :
    |f t| ≤ |f 0|+M*T := by
  have h := scalar_drift_bound f d T M hT hd hb t ht
  have ht' : |t| ≤ T := abs_le.mpr ht
  have ha : |f t| ≤ |f t-f 0|+|f 0| := by
    simpa only [Real.norm_eq_abs] using norm_le_norm_sub_add (f t) (f 0)
  nlinarith [mul_le_mul_of_nonneg_left ht' hM]

theorem damped_scalar_bound (c v M : ℝ) (hc : c ∈ Icc (0:ℝ) 1) (hM : |v| ≤ M) :
    |c*v| ≤ M := by
  rw [abs_mul,abs_of_nonneg hc.1]
  exact (mul_le_of_le_one_left (abs_nonneg v) hc.2).trans hM

theorem clockSpeed_bound (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 ≤ κ) (x : TimePhase) :
    |clockRate ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)| ≤ fullHamiltonian ε κ x/ε := by
  have hF : 0 ≤ exponentialMean (KFCausalClockFloorFlow.clock ε (q (.inr 0) x.2)) x.2 :=
    le_trans (by norm_num) (exponentialMean_ge_one _ _)
  have h : 0 ≤ clockRate ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) :=
    div_nonneg (mul_nonneg (amplitude_nonnegative ε κ _ _ _ hκ) hF) (sq_nonneg _)
  rw [abs_of_nonneg h]
  exact clockRate_energy_bound ε κ hε hκ x

theorem momentumSpeed_bounded (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (T E : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : TimePhase, |x.1| ≤ T → fullHamiltonian ε κ x ≤ E →
      |momentumRate ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)| ≤ M := by
  let g : ℝ × ℝ → ℝ := fun v => |momentumEnvelope ε κ v.1 v.2|+|upperMomentumEnvelope ε κ v.1 v.2|
  have hn : ∀ v : ℝ × ℝ, κ*Real.exp (2*v.1) ≠ 0 :=
    fun v => mul_ne_zero hκ.ne' (Real.exp_ne_zero _)
  have hc : Continuous g := by
    dsimp [g,momentumEnvelope,upperMomentumEnvelope]
    fun_prop (disch := exact hn)
  obtain ⟨M,hM⟩ := (((isCompact_Icc : IsCompact (Icc (-T) T)).prod
    (isCompact_Icc : IsCompact (Icc (0:ℝ) E))).image hc).isBounded.exists_norm_le
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro x ht he
  have hH := (energy_bounds ε κ hε.le hκ.le x).1
  have hm := hM _ (Set.mem_image_of_mem g (show (x.1,fullHamiltonian ε κ x) ∈
    Icc (-T) T ×ˢ Icc (0:ℝ) E from ⟨abs_le.mp ht,⟨hH.le,he⟩⟩))
  have hm' : |momentumEnvelope ε κ x.1 (fullHamiltonian ε κ x)|+
      |upperMomentumEnvelope ε κ x.1 (fullHamiltonian ε κ x)| ≤ max M 0 := by
    apply le_trans _ (le_max_left _ _)
    simp only [g,Real.norm_eq_abs] at hm
    rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))] at hm
    exact hm
  have hlo := momentumRate_energy_lower ε κ hε hκ.le x
  have hhi := momentumRate_energy_upper ε κ hε hκ x
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (momentumEnvelope ε κ x.1 (fullHamiltonian ε κ x)),
    le_abs_self (upperMomentumEnvelope ε κ x.1 (fullHamiltonian ε κ x)),
    abs_nonneg (momentumEnvelope ε κ x.1 (fullHamiltonian ε κ x)),
    abs_nonneg (upperMomentumEnvelope ε κ x.1 (fullHamiltonian ε κ x))]

theorem phaseSize_window_bound (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ)
    (T E : ℝ) (x : TimePhase) (ht : |x.1| ≤ T) (he : fullHamiltonian ε κ x ≤ E) :
    phaseSize x.2 ≤ 4*(1+Real.exp (2*T))*E^2 := by
  apply (phaseSize_energy_bound ε κ hε hκ x).trans
  have hH := (energy_bounds ε κ hε hκ x).1
  have ht' := (abs_le.mp ht).1
  have hex : Real.exp (-2*x.1) ≤ Real.exp (2*T) := Real.exp_le_exp.mpr (by linarith)
  have hs : (fullHamiltonian ε κ x)^2 ≤ E^2 := pow_le_pow_left₀ hH.le he 2
  exact mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add le_rfl hex) (by norm_num))
    hs (sq_nonneg _) (by positivity)

#print axioms scalar_drift_bound
#print axioms scalar_window_value_bound
#print axioms damped_scalar_bound
#print axioms clockSpeed_bound
#print axioms momentumSpeed_bounded
#print axioms phaseSize_window_bound

end
end UnifiedTheory.Audit.KFCausalClassicalVacuumWindow
