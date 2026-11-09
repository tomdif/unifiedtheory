/- Bounds uniform over bounded initial data, supplying continuous dependence
of the actual full matter flow. No continuity of the solution map is assumed. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterWindow
import UnifiedTheory.Audit.KFCausalClassicalVacuumCoercivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterInitialBounds
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalMatterEnergy
open UnifiedTheory.Audit.KFCausalClassicalMatterDamping
open UnifiedTheory.Audit.KFCausalClassicalMatterWindow
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p TimePhase)
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds (phaseSize)
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE (positionBasis)
open UnifiedTheory.Audit.KFCausalClassicalVacuumCoercivity (phase_norm_bound)
open UnifiedTheory.Audit.KFCausalClassicalVacuumWindow (scalar_window_value_bound damped_scalar_bound)

theorem finite_window_bound (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
    (R₀ E₀ T : ℝ) (hR₀ : 0 ≤ R₀) (hE₀ : 0 < E₀) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : ℝ → ℝ) (γ : ℝ → TimePhase), ‖γ 0‖ ≤ R₀ → fullHamiltonian ε m g κ (γ 0) ≤ E₀ →
      (∀ t ∈ Icc (-T) T, c t ∈ Icc (0:ℝ) 1) →
      (∀ t ∈ Icc (-T) T, HasDerivAt γ (dampedField ε m g κ (c t) (γ t)) t) →
      ∀ t ∈ Icc (-T) T, ‖γ t‖ ≤ B := by
  let R := R₀+T
  let E := Real.exp (2*T)*E₀
  have hR : 0 ≤ R := add_nonneg hR₀ hT
  have hE : 0 < E := mul_pos (Real.exp_pos _) hE₀
  let K := 4*(1+Real.exp (2*R))*E^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let N := (K+1)/ε+E*(4*(K+1))/ε
  have hN : 0 ≤ N := by dsimp [N]; positivity
  let A := R₀+N*T
  obtain ⟨M,hM,hMb⟩ := momentumSpeed_bounded ε m g κ hε hm hg hκ R E K A
  let Q := R₀+(E/ε)*T
  let P := R₀+M*T
  let S := Q+P+K+1
  let B := max R (S+A*‖positionBasis (.inr 3)‖)
  refine ⟨B,le_trans hR (le_max_left _ _),?_⟩
  intro c γ h₀ henergy hc hγ
  have ht₀ : |(γ 0).1| ≤ R₀ := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le (γ 0)).trans h₀
  have hq₀ (i : KFCausalClassicalVacuumSmooth.Index) : |q i (γ 0).2| ≤ R₀ := by
    exact (PiLp.norm_apply_le (γ 0).2.1 i).trans
      ((norm_fst_le (γ 0).2).trans ((norm_snd_le (γ 0)).trans h₀))
  have hp₀ (i : KFCausalClassicalVacuumSmooth.Index) : |p i (γ 0).2| ≤ R₀ := by
    exact (PiLp.norm_apply_le (γ 0).2.2 i).trans
      ((norm_snd_le (γ 0).2).trans ((norm_snd_le (γ 0)).trans h₀))
  have he (t : ℝ) (ht : t ∈ Icc (-T) T) : fullHamiltonian ε m g κ (γ t) ≤ E := by
    exact (KFCausalClassicalMatterDamping.energy_interval_bound ε m g κ hε.le hm hg hκ.le c γ T hT hγ t ht).trans
      (mul_le_mul_of_nonneg_left henergy (Real.exp_pos _).le)
  have ht (t : ℝ) (hu : t ∈ Icc (-T) T) : |(γ t).1| ≤ R := by
    have hd (u : ℝ) (hu : u ∈ Icc (-T) T) : HasDerivAt (fun v => (γ v).1) 1 u := (hγ u hu).fst
    have h := scalar_window_value_bound (fun v => (γ v).1) (fun _ => 1) T 1 hT (by norm_num)
      hd (fun _ _ => by norm_num) t hu
    simpa only [one_mul] using h.trans (add_le_add ht₀ le_rfl)
  have hk (t : ℝ) (hu : t ∈ Icc (-T) T) : phaseSize (γ t).2 ≤ K :=
    phaseSize_window_bound ε m g κ hε.le hm hg hκ.le R E (γ t) (ht t hu) (he t hu)
  have hn (t : ℝ) (hu : t ∈ Icc (-T) T) : |q (.inr 3) (γ t).2| ≤ A := by
    let d : ℝ → ℝ := fun u => c u*q (.inr 3) (field ε m g κ (γ u)).2
    have hd (u : ℝ) (hu : u ∈ Icc (-T) T) : HasDerivAt (fun v => q (.inr 3) (γ v).2) (d u) u := by
      simpa only [d,dampedField,map_smul,smul_eq_mul] using
        (q (.inr 3)).hasFDerivAt.comp_hasDerivAt u (hγ u hu).snd
    have hb (u : ℝ) (hu : u ∈ Icc (-T) T) : |d u| ≤ N := by
      apply damped_scalar_bound _ _ _ (hc u hu)
      exact neutralSpeed_window_bound ε m g κ hε hm hg hκ.le E K (γ u) (he u hu) (hk u hu)
    exact (scalar_window_value_bound _ d T N hT hN hd hb t hu).trans
      (add_le_add (hq₀ (.inr 3)) le_rfl)
  have hq (t : ℝ) (hu : t ∈ Icc (-T) T) : |q (.inr 0) (γ t).2| ≤ Q := by
    let d : ℝ → ℝ := fun u => c u*clockRate ε m g κ (γ u).1 (γ u).2 (q (.inr 0) (γ u).2) (p (.inr 0) (γ u).2)
    have hd (u : ℝ) (hu : u ∈ Icc (-T) T) : HasDerivAt (fun v => q (.inr 0) (γ v).2) (d u) u := by
      simpa only [d,damped_clock ε m g κ (c u) hε.le] using
        (q (.inr 0)).hasFDerivAt.comp_hasDerivAt u (hγ u hu).snd
    have hb (u : ℝ) (hu : u ∈ Icc (-T) T) : |d u| ≤ E/ε :=
      damped_scalar_bound _ _ _ (hc u hu) ((clockSpeed_bound ε m g κ hε hm hg hκ.le (γ u)).trans
        (div_le_div_of_nonneg_right (he u hu) hε.le))
    exact (scalar_window_value_bound _ d T (E/ε) hT (by positivity) hd hb t hu).trans
      (add_le_add (hq₀ (.inr 0)) le_rfl)
  have hp (t : ℝ) (hu : t ∈ Icc (-T) T) : |p (.inr 0) (γ t).2| ≤ P := by
    let d : ℝ → ℝ := fun u => c u*momentumRate ε m g κ (γ u).1 (γ u).2 (q (.inr 0) (γ u).2) (p (.inr 0) (γ u).2)
    have hd (u : ℝ) (hu : u ∈ Icc (-T) T) : HasDerivAt (fun v => p (.inr 0) (γ v).2) (d u) u := by
      simpa only [d,damped_clockMomentum ε m g κ (c u) hε.le] using
        (p (.inr 0)).hasFDerivAt.comp_hasDerivAt u (hγ u hu).snd
    have hb (u : ℝ) (hu : u ∈ Icc (-T) T) : |d u| ≤ M :=
      damped_scalar_bound _ _ _ (hc u hu) (hMb (γ u) (ht u hu) (he u hu) (hk u hu) (hn u hu))
    exact (scalar_window_value_bound _ d T M hT hM hd hb t hu).trans
      (add_le_add (hp₀ (.inr 0)) le_rfl)
  intro t hu
  change max ‖(γ t).1‖ ‖(γ t).2‖ ≤ max R (S+A*‖positionBasis (.inr 3)‖)
  apply max_le_max (by simpa only [Real.norm_eq_abs] using ht t hu)
  have h := phase_norm_bound (γ t).2
  have hn' := mul_le_mul_of_nonneg_right (hn t hu) (norm_nonneg (positionBasis (.inr 3)))
  dsimp [S]
  linarith [hq t hu,hp t hu,hk t hu]

theorem bounded_initial_window (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g)
    (hκ : 0 < κ) (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ γ : ℝ → TimePhase, ‖γ 0‖ ≤ R →
      (∀ t ∈ Icc (-T) T, HasDerivAt γ (field ε m g κ (γ t)) t) →
      ∀ t ∈ Icc (-T) T, ‖γ t‖ ≤ B := by
  have hc := (fullHamiltonian_contDiff ε m g κ hε.le 1).continuous
  obtain ⟨M,hM⟩ := ((isCompact_closedBall (0 : TimePhase) R).image hc).isBounded.exists_norm_le
  obtain ⟨B,hB,hbound⟩ := finite_window_bound ε m g κ hε hm hg hκ R (|M|+1) T hR (by positivity) hT
  refine ⟨B,hB,?_⟩
  intro γ h₀ hγ
  have he : fullHamiltonian ε m g κ (γ 0) ≤ |M|+1 := by
    have hh := hM _ (mem_image_of_mem _ (by
      simpa only [Metric.mem_closedBall,dist_zero_right] using h₀))
    rw [Real.norm_eq_abs] at hh
    linarith only [hh,le_abs_self (fullHamiltonian ε m g κ (γ 0)),le_abs_self M]
  exact hbound (fun _ => 1) γ h₀ he (fun _ _ => by constructor <;> norm_num)
    (fun t ht => by simpa only [dampedField_one] using hγ t ht)

#print axioms finite_window_bound
#print axioms bounded_initial_window

end
end UnifiedTheory.Audit.KFCausalClassicalMatterInitialBounds
