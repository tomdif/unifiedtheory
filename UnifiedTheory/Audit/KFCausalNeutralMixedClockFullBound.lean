/- The full signed Hamiltonian-form response has an energy-relative
lower bound on every finite mixed-clock neutral polynomial state.
One constant works at every physical time. This does not assert that
the family is preserved by the actual Hamiltonian evolution. -/
import UnifiedTheory.Audit.KFCausalNeutralMixedClockHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralMixedClockFullBound
noncomputable section
open UnifiedTheory.Audit.KFCausalNeutralMixedClockState (output)
open UnifiedTheory.Audit.KFCausalNeutralMixedClockFactorResponse
  (factorEnergy factorRate clock_energy_bounds kinetic_bounds)
open UnifiedTheory.Audit.KFCausalNeutralMixedClockPotential (potentialEnergy potentialResponse)
open UnifiedTheory.Audit.KFCausalNeutralMixedClockHamiltonian

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
  (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (t : ℝ)
local notation "E" => factorEnergy ε h hε hh hb N a p ha b C P
local notation "R" => factorRate ε h hε hh hb N a p ha b C P
local notation "Ep" => potentialEnergy ε h N a p b C P hε hh ha hb
local notation "Rp" => potentialResponse ε h N a p b C P hε hh ha hb
local notation "Et" => fullEnergy ε h hε hh hb N a p ha b C P 1 1 1 t
local notation "Rt" => fullResponse ε h hε hh hb N a p ha b C P 1 1 1 t

theorem fullEnergy_nonnegative : 0 ≤ Et := sq_nonneg _

theorem full_relative_lower (κ : ℝ) (hκ : 1/(4*ε) ≤ κ) (hpot : -κ*Ep ≤ Rp) :
    -κ*Et ≤ Rt := by
  have hκ0 : 0 ≤ κ := (by positivity : 0 ≤ 1/(4*ε)).trans hκ
  have hE (i : Fin 8) : 0 ≤ E i := sq_nonneg _
  have hc := (clock_energy_bounds ε h hε hh hb N a p ha b C P).1
  have hc' : -κ*E 0 ≤ R 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hκ) (hE 0)]
  have h1 := (kinetic_bounds ε h hε hh hb N a p ha b C P 0).1
  have h2 := (kinetic_bounds ε h hε hh hb N a p ha b C P 1).1
  have h3 := (kinetic_bounds ε h hε hh hb N a p ha b C P 2).1
  have h4 := (kinetic_bounds ε h hε hh hb N a p ha b C P 3).1
  change 0 ≤ R 1 at h1
  change 0 ≤ R 2 at h2
  change 0 ≤ R 3 at h3
  change 0 ≤ R 4 at h4
  have h12 : -κ*((E 1+E 2)/2) ≤ (R 1+R 2)/2 := by
    nlinarith [mul_nonneg hκ0 (add_nonneg (hE 1) (hE 2))]
  have h34 : -κ*((E 3+E 4)/2+Ep) ≤ (R 3+R 4)/2+Rp := by
    nlinarith [mul_nonneg hκ0 (add_nonneg (hE 3) (hE 4))]
  have ht := mul_le_mul_of_nonneg_left h34 (Real.exp_pos (2*t)).le
  rw [unit_full_energy,unit_full_response]
  nlinarith

omit ε hε hh hb N a p ha b C P t in
theorem exists_uniform_full_response_bound (hh : h ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ hb : |h| ≤ 2*Real.pi*ε/3,
      ∀ (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
        (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (t : ℝ),
        -((M+2)/ε)*fullEnergy ε h hε hh hb N a p ha b C P 1 1 1 t ≤
          fullResponse ε h hε hh hb N a p ha b C P 1 1 1 t := by
  obtain ⟨M,hM,hbound⟩ := KFCausalNeutralMixedClockBound.exists_uniform_physical_response_bound h hh
  refine ⟨M,hM,?_⟩
  intro ε hε hb N a p ha b C P t
  have hκ : 1/(4*ε) ≤ (M+2)/ε := by
    calc
      _ = (1/4)/ε := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith : (1/4:ℝ) ≤ M+2) hε.le
  exact full_relative_lower ε h hε hh hb N a p ha b C P t ((M+2)/ε) hκ
    (hbound ε hε hb N a p ha b C P)

omit N a p ha b C P t in
theorem full_response_lower_exists :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
      (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (t : ℝ),
      -κ*fullEnergy ε h hε hh hb N a p ha b C P 1 1 1 t ≤
        fullResponse ε h hε hh hb N a p ha b C P 1 1 1 t := by
  obtain ⟨M,hM,hbound⟩ := exists_uniform_full_response_bound h hh
  exact ⟨(M+2)/ε,by positivity,hbound ε hε hb⟩

#print axioms fullEnergy_nonnegative
#print axioms full_relative_lower
#print axioms exists_uniform_full_response_bound
#print axioms full_response_lower_exists
end
end UnifiedTheory.Audit.KFCausalNeutralMixedClockFullBound
