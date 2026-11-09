/- Finite-window speed bounds for matter. Neutral-position speed is bounded
before its position is used to bound clock-momentum drift. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterNeutralBounds
import UnifiedTheory.Audit.KFCausalClassicalMatterMomentumBounds
import UnifiedTheory.Audit.KFCausalClassicalMatterDamping
import UnifiedTheory.Audit.KFCausalClassicalVacuumWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterWindow
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalMatterEnergy
open UnifiedTheory.Audit.KFCausalClassicalMatterEnergyBounds
open UnifiedTheory.Audit.KFCausalClassicalMatterOrbitBounds
open UnifiedTheory.Audit.KFCausalClassicalMatterNeutralBounds
open UnifiedTheory.Audit.KFCausalClassicalMatterMomentumBounds
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p TimePhase)
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds (phaseSize)
open UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds (phaseSize_nonnegative)
open UnifiedTheory.Audit.KFCausalClassicalVacuumMomentumBounds (upperMomentumEnvelope)

theorem clockSpeed_bound (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) (x : TimePhase) :
    |clockRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)| ≤ fullHamiltonian ε m g κ x/ε := by
  have hF : 0 ≤ weightedMean m g κ (KFCausalClockFloorFlow.clock ε (q (.inr 0) x.2)) x.2 :=
    hκ.trans (weightedMean_lower m g κ _ hm hg hκ _)
  have h : 0 ≤ clockRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) :=
    div_nonneg (mul_nonneg (Real.exp_pos _).le hF) (sq_nonneg _)
  rw [abs_of_nonneg h]
  exact clockRate_energy_bound ε m g κ hε hm hg hκ x

theorem phaseSize_window_bound (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (R E : ℝ) (x : TimePhase) (ht : |x.1| ≤ R) (he : fullHamiltonian ε m g κ x ≤ E) :
    phaseSize x.2 ≤ 4*(1+Real.exp (2*R))*E^2 := by
  apply (phaseSize_energy_bound ε m g κ hε hm hg hκ x).trans
  have hH := (energy_bounds ε m g κ hε hm hg hκ x).1
  have ht' := (abs_le.mp ht).1
  have hex : Real.exp (-2*x.1) ≤ Real.exp (2*R) := Real.exp_le_exp.mpr (by linarith)
  have hs : (fullHamiltonian ε m g κ x)^2 ≤ E^2 := pow_le_pow_left₀ hH.le he 2
  exact mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add le_rfl hex) (by norm_num))
    hs (sq_nonneg _) (by positivity)

theorem neutralSpeed_window_bound (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (E P : ℝ) (x : TimePhase) (he : fullHamiltonian ε m g κ x ≤ E) (hp : phaseSize x.2 ≤ P) :
    |q (.inr 3) (field ε m g κ x).2| ≤ (P+1)/ε+E*(4*(P+1))/ε := by
  apply (neutralSpeed_energy_bound ε m g κ hε hm hg hκ x).trans
  have hH := (energy_bounds ε m g κ hε.le hm hg hκ x).1
  have hP := phaseSize_nonnegative x.2
  have hE : 0 ≤ E := hH.le.trans he
  apply add_le_add
  · exact div_le_div_of_nonneg_right (by linarith) hε.le
  · apply div_le_div_of_nonneg_right _ hε.le
    exact mul_le_mul he (by linarith) (by positivity) hE

theorem momentumSpeed_bounded (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
    (R E P N : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : TimePhase,
      |x.1| ≤ R → fullHamiltonian ε m g κ x ≤ E → phaseSize x.2 ≤ P → |q (.inr 3) x.2| ≤ N →
        |momentumRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)| ≤ M := by
  let G : ℝ × ℝ × ℝ × ℝ → ℝ := fun v =>
    |lowerMomentumEnvelope ε m g κ v.1 v.2.1 v.2.2.1 v.2.2.2|+|upperMomentumEnvelope ε κ v.1 v.2.1|
  have hn : ∀ v : ℝ × ℝ × ℝ × ℝ, κ*Real.exp (2*v.1) ≠ 0 :=
    fun v => mul_ne_zero hκ.ne' (Real.exp_ne_zero _)
  have hc : Continuous G := by
    dsimp [G,lowerMomentumEnvelope,potentialEnvelope,upperMomentumEnvelope]
    fun_prop (disch := exact hn)
  have hcompact : IsCompact (Icc (-R) R ×ˢ Icc (0:ℝ) E ×ˢ Icc (0:ℝ) P ×ˢ Icc (0:ℝ) N) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  obtain ⟨M,hM⟩ := (hcompact.image hc).isBounded.exists_norm_le
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro x ht he hp hn
  have hH := (energy_bounds ε m g κ hε.le hm hg hκ.le x).1
  have hb := hM _ (Set.mem_image_of_mem G (show
    (x.1,fullHamiltonian ε m g κ x,phaseSize x.2,|q (.inr 3) x.2|) ∈
      Icc (-R) R ×ˢ Icc (0:ℝ) E ×ˢ Icc (0:ℝ) P ×ˢ Icc (0:ℝ) N from
        ⟨abs_le.mp ht,⟨hH.le,he⟩,⟨phaseSize_nonnegative x.2,hp⟩,⟨abs_nonneg _,hn⟩⟩))
  have hb' : |lowerMomentumEnvelope ε m g κ x.1 (fullHamiltonian ε m g κ x) (phaseSize x.2) (|q (.inr 3) x.2|)| +
      |upperMomentumEnvelope ε κ x.1 (fullHamiltonian ε m g κ x)| ≤ max M 0 := by
    apply le_trans _ (le_max_left _ _)
    simp only [G,Real.norm_eq_abs] at hb
    rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))] at hb
    exact hb
  have hlo := momentumRate_envelope_lower ε m g κ hε hm hg hκ.le x
  have hhi := momentumRate_energy_upper ε m g κ hε hm hg hκ x
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (lowerMomentumEnvelope ε m g κ x.1 (fullHamiltonian ε m g κ x) (phaseSize x.2) |q (.inr 3) x.2|),
    le_abs_self (upperMomentumEnvelope ε κ x.1 (fullHamiltonian ε m g κ x)),
    abs_nonneg (lowerMomentumEnvelope ε m g κ x.1 (fullHamiltonian ε m g κ x) (phaseSize x.2) |q (.inr 3) x.2|),
    abs_nonneg (upperMomentumEnvelope ε κ x.1 (fullHamiltonian ε m g κ x))]

#print axioms clockSpeed_bound
#print axioms phaseSize_window_bound
#print axioms neutralSpeed_window_bound
#print axioms momentumSpeed_bounded

end
end UnifiedTheory.Audit.KFCausalClassicalMatterWindow
