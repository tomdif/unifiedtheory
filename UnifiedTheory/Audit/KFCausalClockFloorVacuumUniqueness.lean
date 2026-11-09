/- Uniqueness of the globally constructed vacuum clock dynamics. -/
import UnifiedTheory.Audit.KFCausalClockFloorVacuumReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorVacuumUniqueness
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorReducedODE
open UnifiedTheory.Audit.KFCausalClockFloorVacuumReduction
open UnifiedTheory.Audit.KFCausalClockFloorVacuumReconstruction

theorem vacuum_unique (ε κ : ℝ) (hε : 0 < ε) (s₁ L₁ s₂ L₂ : ℝ → ℝ)
    (hs₁ : ∀ t, HasDerivAt s₁ (amplitude ε κ t (s₁ t) (L₁ t)/clock ε (s₁ t)) t)
    (hL₁ : ∀ t, HasDerivAt L₁ (response ε (s₁ t)*(-1/2+amplitude ε κ t (s₁ t) (L₁ t)/clock ε (s₁ t))) t)
    (hs₂ : ∀ t, HasDerivAt s₂ (amplitude ε κ t (s₂ t) (L₂ t)/clock ε (s₂ t)) t)
    (hL₂ : ∀ t, HasDerivAt L₂ (response ε (s₂ t)*(-1/2+amplitude ε κ t (s₂ t) (L₂ t)/clock ε (s₂ t))) t)
    (hs0 : s₁ 0 = s₂ 0) (hL0 : L₁ 0 = L₂ 0) : s₁ = s₂ ∧ L₁ = L₂ := by
  let J := invariant ε κ 0 (s₁ 0) (L₁ 0)
  have hJ : invariant ε κ 0 (s₂ 0) (L₂ 0) = J := by rw [← hs0,← hL0]
  have hds₁ := clock_reduction ε κ hε s₁ L₁ hs₁ hL₁
  have hds₂ := clock_reduction ε κ hε s₂ L₂ hs₂ hL₂
  rw [hJ] at hds₂
  have hseq : s₁ = s₂ := ODE_solution_unique_univ
    (v := fun _ : ℝ => rate ε J) (s := fun _ => Set.univ) (t₀ := 0)
    (fun _ => (rate_lipschitz ε J hε).lipschitzOnWith)
    (fun t => ⟨hds₁ t,Set.mem_univ _⟩) (fun t => ⟨hds₂ t,Set.mem_univ _⟩) hs0
  refine ⟨hseq,?_⟩
  have hp₁ (t : ℝ) : HasDerivAt L₁ (response ε (s₁ t)*(-1/2+rate ε J (s₁ t))) t := by
    dsimp only [J]
    rw [← invariant_constant ε κ hε s₁ L₁ hs₁ hL₁ t,rate_identity ε κ t (s₁ t) (L₁ t) hε]
    exact hL₁ t
  have hp₂ (t : ℝ) : HasDerivAt L₂ (response ε (s₁ t)*(-1/2+rate ε J (s₁ t))) t := by
    rw [hseq,← hJ,← invariant_constant ε κ hε s₂ L₂ hs₂ hL₂ t,rate_identity ε κ t (s₂ t) (L₂ t) hε]
    exact hL₂ t
  have hd (t : ℝ) : HasDerivAt (fun u => L₁ u-L₂ u) 0 t := by
    simpa only [sub_self] using (hp₁ t).sub (hp₂ t)
  funext t
  have he := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t 0
  rw [hL0,sub_self] at he
  exact sub_eq_zero.mp he

theorem canonical_unique (ε κ : ℝ) (hε : 0 < ε) (s₁ p₁ s₂ p₂ : ℝ → ℝ)
    (hs₁ : ∀ t, HasDerivAt s₁ (deriv (canonicalHamiltonian ε κ t (s₁ t)) (p₁ t)) t)
    (hp₁ : ∀ t, HasDerivAt p₁ (-deriv (fun x => canonicalHamiltonian ε κ t x (p₁ t)) (s₁ t)) t)
    (hs₂ : ∀ t, HasDerivAt s₂ (deriv (canonicalHamiltonian ε κ t (s₂ t)) (p₂ t)) t)
    (hp₂ : ∀ t, HasDerivAt p₂ (-deriv (fun x => canonicalHamiltonian ε κ t x (p₂ t)) (s₂ t)) t)
    (hs0 : s₁ 0 = s₂ 0) (hp0 : p₁ 0 = p₂ 0) : s₁ = s₂ ∧ p₁ = p₂ := by
  have hinit : p₁ 0/clock ε (s₁ 0) = p₂ 0/clock ε (s₂ 0) := by rw [hs0,hp0]
  obtain ⟨hseq,hLeq⟩ := vacuum_unique ε κ hε s₁ (fun t => p₁ t/clock ε (s₁ t))
    s₂ (fun t => p₂ t/clock ε (s₂ t))
    (fun t => (longitudinal_equations ε κ hε s₁ p₁ t (hs₁ t) (hp₁ t)).1)
    (fun t => (longitudinal_equations ε κ hε s₁ p₁ t (hs₁ t) (hp₁ t)).2)
    (fun t => (longitudinal_equations ε κ hε s₂ p₂ t (hs₂ t) (hp₂ t)).1)
    (fun t => (longitudinal_equations ε κ hε s₂ p₂ t (hs₂ t) (hp₂ t)).2) hs0 hinit
  refine ⟨hseq,?_⟩
  funext t
  have he := congrFun hLeq t
  change p₁ t/clock ε (s₁ t) = p₂ t/clock ε (s₂ t) at he
  rw [hseq] at he
  exact (div_left_inj' (clock_positive ε (s₂ t) hε.le).ne').mp he

#print axioms vacuum_unique
#print axioms canonical_unique

end
end UnifiedTheory.Audit.KFCausalClockFloorVacuumUniqueness
