/- A finite-window bound for every component of the full classical phase.
The bound is uniform over all phase dampings with values in [0,1], so it can
be used before choosing the compact cutoff in the existence construction. -/
import UnifiedTheory.Audit.KFCausalClassicalVacuumWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumUniformBound
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergy
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds
open UnifiedTheory.Audit.KFCausalClassicalVacuumTranslation
open UnifiedTheory.Audit.KFCausalClassicalVacuumCoercivity
open UnifiedTheory.Audit.KFCausalClassicalVacuumDamping
open UnifiedTheory.Audit.KFCausalClassicalVacuumWindow

theorem finite_window_bound (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (x₀ : TimePhase) (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : ℝ → ℝ) (γ : ℝ → TimePhase), γ 0 = x₀ →
      (∀ t ∈ Icc (-T) T, c t ∈ Icc (0:ℝ) 1) →
      (∀ t ∈ Icc (-T) T, HasDerivAt γ (dampedField ε κ (c t) (γ t)) t) →
      ∀ t ∈ Icc (-T) T, ‖γ t‖ ≤ B := by
  let R := |x₀.1|+T
  let E := Real.exp (2*T)*fullHamiltonian ε κ x₀
  have hR : 0 ≤ R := add_nonneg (abs_nonneg _) hT
  have hE : 0 < E := mul_pos (Real.exp_pos _) (energy_bounds ε κ hε.le hκ.le x₀).1
  obtain ⟨M,hM,hMb⟩ := momentumSpeed_bounded ε κ hε hκ R E
  let Q := |q (.inr 0) x₀.2|+(E/ε)*T
  let P := |p (.inr 0) x₀.2|+M*T
  let K := 4*(1+Real.exp (2*R))*E^2
  let S := Q+P+K+1
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  obtain ⟨N,hN,hNb⟩ := neutralSpeed_bounded ε κ hε.le (max R S)
  let A := |q (.inr 3) x₀.2|+N*T
  let B := max R (S+A*‖positionBasis (.inr 3)‖)
  refine ⟨B,le_trans hR (le_max_left _ _),?_⟩
  intro c γ h₀ hc hγ
  have he (t : ℝ) (ht : t ∈ Icc (-T) T) : fullHamiltonian ε κ (γ t) ≤ E := by
    simpa only [h₀] using KFCausalClassicalVacuumDamping.energy_interval_bound ε κ hε.le hκ.le c γ T hT hγ t ht
  have ht (t : ℝ) (hu : t ∈ Icc (-T) T) : |(γ t).1| ≤ R := by
    have hd (u : ℝ) (hu : u ∈ Icc (-T) T) : HasDerivAt (fun v => (γ v).1) 1 u := (hγ u hu).fst
    have h := scalar_window_value_bound (fun v => (γ v).1) (fun _ => 1) T 1 hT (by norm_num)
      hd (fun _ _ => by norm_num) t hu
    simpa only [h₀,one_mul] using h
  have hq (t : ℝ) (hu : t ∈ Icc (-T) T) : |q (.inr 0) (γ t).2| ≤ Q := by
    let d : ℝ → ℝ := fun u => c u*clockRate ε κ (γ u).1 (γ u).2 (q (.inr 0) (γ u).2) (p (.inr 0) (γ u).2)
    have hd (u : ℝ) (hu : u ∈ Icc (-T) T) : HasDerivAt (fun v => q (.inr 0) (γ v).2) (d u) u := by
      simpa only [d,damped_clock ε κ (c u) hε.le] using
        (q (.inr 0)).hasFDerivAt.comp_hasDerivAt u (hγ u hu).snd
    have hb (u : ℝ) (hu : u ∈ Icc (-T) T) : |d u| ≤ E/ε :=
      damped_scalar_bound _ _ _ (hc u hu) ((clockSpeed_bound ε κ hε hκ.le (γ u)).trans
        (div_le_div_of_nonneg_right (he u hu) hε.le))
    simpa only [h₀] using scalar_window_value_bound _ d T (E/ε) hT (by positivity) hd hb t hu
  have hp (t : ℝ) (hu : t ∈ Icc (-T) T) : |p (.inr 0) (γ t).2| ≤ P := by
    let d : ℝ → ℝ := fun u => c u*momentumRate ε κ (γ u).1 (γ u).2 (q (.inr 0) (γ u).2) (p (.inr 0) (γ u).2)
    have hd (u : ℝ) (hu : u ∈ Icc (-T) T) : HasDerivAt (fun v => p (.inr 0) (γ v).2) (d u) u := by
      simpa only [d,damped_clockMomentum ε κ (c u) hε.le] using
        (p (.inr 0)).hasFDerivAt.comp_hasDerivAt u (hγ u hu).snd
    have hb (u : ℝ) (hu : u ∈ Icc (-T) T) : |d u| ≤ M :=
      damped_scalar_bound _ _ _ (hc u hu) (hMb (γ u) (ht u hu) (he u hu))
    simpa only [h₀] using scalar_window_value_bound _ d T M hT hM hd hb t hu
  have hk (t : ℝ) (hu : t ∈ Icc (-T) T) : phaseSize (γ t).2 ≤ K :=
    phaseSize_window_bound ε κ hε.le hκ.le R E (γ t) (ht t hu) (he t hu)
  have hs (t : ℝ) (hu : t ∈ Icc (-T) T) : ‖eraseNeutral (γ t).2‖ ≤ S := by
    have h := erased_norm_bound (γ t).2
    dsimp [S]
    linarith [hq t hu,hp t hu,hk t hu]
  have hn (t : ℝ) (hu : t ∈ Icc (-T) T) : |q (.inr 3) (γ t).2| ≤ A := by
    let d : ℝ → ℝ := fun u => c u*q (.inr 3) (field ε κ (γ u)).2
    have hd (u : ℝ) (hu : u ∈ Icc (-T) T) : HasDerivAt (fun v => q (.inr 3) (γ v).2) (d u) u := by
      simpa only [d,dampedField,map_smul,smul_eq_mul] using
        (q (.inr 3)).hasFDerivAt.comp_hasDerivAt u (hγ u hu).snd
    have hb (u : ℝ) (hu : u ∈ Icc (-T) T) : |d u| ≤ N := by
      apply damped_scalar_bound _ _ _ (hc u hu)
      apply hNb (γ u)
      rw [Prod.norm_def,Real.norm_eq_abs]
      exact max_le_max (ht u hu) (hs u hu)
    simpa only [h₀] using scalar_window_value_bound _ d T N hT hN hd hb t hu
  intro t hu
  change max ‖(γ t).1‖ ‖(γ t).2‖ ≤ max R (S+A*‖positionBasis (.inr 3)‖)
  apply max_le_max (by simpa only [Real.norm_eq_abs] using ht t hu)
  have h := phase_norm_bound (γ t).2
  have hn' := mul_le_mul_of_nonneg_right (hn t hu) (norm_nonneg (positionBasis (.inr 3)))
  dsimp [S]
  linarith [hq t hu,hp t hu,hk t hu]

#print axioms finite_window_bound

end
end UnifiedTheory.Audit.KFCausalClassicalVacuumUniformBound
