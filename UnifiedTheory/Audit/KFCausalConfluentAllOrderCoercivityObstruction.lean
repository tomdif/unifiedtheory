/- The exact Gamma polynomial hierarchy underlying zero-phase charged cooling
has no positive degree-independent marginal coercivity coefficient. This is
an obstruction to a proof method, not a counterexample to the actual clock
response (which vanishes at zero imaginary shift). -/
import UnifiedTheory.Audit.KFCausalJointFourierBoundaryGammaForm
import UnifiedTheory.Audit.KFCausalChargedCoolingConfluentThreeCoercivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalConfluentAllOrderCoercivityObstruction
noncomputable section
open MeasureTheory Set
open KFCausalJointFourierBoundaryGammaForm (weight moment moment_integrable moment_integral)

/-- Rate-two moments, using the rate-one Gamma integral and the coordinate t/2. -/
def scaledMoment (n : ℕ) : ℝ := moment n / 2^n

def energy (n : ℕ) : ℝ := ∫ t in Ioi (0:ℝ), weight t*(t/2)^(2*n)
def cooling (n : ℕ) : ℝ := ∫ t in Ioi (0:ℝ),
  weight t*(2*(t/2)^(2*n)-2*(n:ℝ)*(t/2)^(2*n-1))

private theorem scaledMoment_positive (n : ℕ) : 0 < scaledMoment n := by
  unfold scaledMoment moment
  apply div_pos
  · apply Finset.prod_pos
    intro i hi
    positivity
  · positivity

private theorem scaledMoment_succ (n : ℕ) :
    scaledMoment (n+1)=((n:ℝ)+3/2)/2*scaledMoment n := by
  simp only [scaledMoment,moment,Finset.prod_range_succ,pow_succ]
  ring

theorem scaled_moment_integrable (n : ℕ) :
    IntegrableOn (fun t => weight t*(t/2)^n) (Ioi 0) := by
  change Integrable _ (volume.restrict (Ioi 0))
  convert (moment_integrable n).div_const ((2:ℝ)^n) using 1
  ext t
  simp only [div_pow]
  ring

theorem scaled_moment_integral (n : ℕ) :
    (∫ t in Ioi (0:ℝ), weight t*(t/2)^n)=scaledMoment n*Real.Gamma (3/2) := by
  have he : (fun t : ℝ => weight t*(t/2)^n)=
      (fun t => (weight t*t^n)/(2:ℝ)^n) := by funext t; rw [div_pow]; ring
  rw [he,integral_div,moment_integral]
  unfold scaledMoment
  ring

theorem energy_positive (n : ℕ) : 0 < energy n := by
  rw [energy,scaled_moment_integral]
  exact mul_pos (scaledMoment_positive _) (Real.Gamma_pos_of_pos (by norm_num))

theorem cooling_integrable (n : ℕ) :
    IntegrableOn (fun t : ℝ =>
      weight t*(2*(t/2)^(2*n)-2*(n:ℝ)*(t/2)^(2*n-1))) (Ioi 0) := by
  change Integrable _ (volume.restrict (Ioi 0))
  convert ((scaled_moment_integrable (2*n)).const_mul 2).sub
    ((scaled_moment_integrable (2*n-1)).const_mul (2*(n:ℝ))) using 1
  ext t
  dsimp only [Pi.sub_apply]
  ring

theorem cooling_integral (n : ℕ) :
    cooling n=(2*scaledMoment (2*n)-2*(n:ℝ)*scaledMoment (2*n-1))*Real.Gamma (3/2) := by
  have he : (fun t : ℝ =>
      weight t*(2*(t/2)^(2*n)-2*(n:ℝ)*(t/2)^(2*n-1)))=
      (fun t => 2*(weight t*(t/2)^(2*n))-2*(n:ℝ)*(weight t*(t/2)^(2*n-1))) := by
    funext t
    ring
  rw [cooling,he,integral_sub ((scaled_moment_integrable _).const_mul _)
    ((scaled_moment_integrable _).const_mul _)]
  simp only [integral_const_mul,scaled_moment_integral]
  ring

theorem exact_quotient (n : ℕ) :
    cooling n=(2/(4*(n:ℝ)+1))*energy n := by
  rw [cooling_integral,energy,scaled_moment_integral]
  cases n with
  | zero => norm_num [scaledMoment,moment]
  | succ n =>
    have hi : 2*(n+1)=((2*n+1)+1) := by omega
    have hj : 2*(n+1)-1=2*n+1 := by omega
    rw [hj,hi,scaledMoment_succ]
    push_cast
    have hd : (4*((n:ℝ)+1)+1) ≠ 0 := by positivity
    field_simp [hd]
    ring

theorem exists_strict_loss (c : ℝ) (hc : 0 < c) :
    ∃ n : ℕ, cooling n < c*energy n := by
  obtain ⟨n,hn⟩ := exists_nat_gt (1/c)
  have hnc : 1 < (n:ℝ)*c := (div_lt_iff₀ hc).mp hn
  have hd : 0 < 4*(n:ℝ)+1 := by positivity
  have hlt : 2/(4*(n:ℝ)+1) < c := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  exact ⟨n,by rw [exact_quotient]; exact mul_lt_mul_of_pos_right hlt (energy_positive n)⟩

theorem no_uniform_positive_coercivity :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c*energy n ≤ cooling n := by
  rintro ⟨c,hc,h⟩
  obtain ⟨n,hn⟩ := exists_strict_loss c hc
  exact (not_lt_of_ge (h n)) hn

theorem low_degree_gram (i : Fin 3) :
    energy i.val =
      (KFCausalChargedCoolingConfluentThreeCoercivity.gram 0 i i).re*Real.Gamma (3/2) := by
  rw [energy,scaled_moment_integral]
  fin_cases i <;>
    norm_num [scaledMoment,moment,Finset.prod_range_succ,
      KFCausalChargedCoolingConfluentThreeCoercivity.gram,
      KFCausalChargedCoolingConfluentThreeCoercivity.hermitianThree]

theorem low_degree_cooling (i : Fin 3) :
    cooling i.val =
      (KFCausalChargedCoolingConfluentThreeCoercivity.cooling 0 0 i i).re*Real.Gamma (3/2) := by
  rw [cooling_integral]
  fin_cases i <;>
    norm_num [scaledMoment,moment,Finset.prod_range_succ,
      KFCausalChargedCoolingConfluentThreeCoercivity.cooling,
      KFCausalChargedCoolingConfluentThreeCoercivity.hermitianThree]

#print axioms scaled_moment_integrable
#print axioms scaled_moment_integral
#print axioms energy_positive
#print axioms cooling_integrable
#print axioms cooling_integral
#print axioms exact_quotient
#print axioms exists_strict_loss
#print axioms no_uniform_positive_coercivity
#print axioms low_degree_gram
#print axioms low_degree_cooling
end
end UnifiedTheory.Audit.KFCausalConfluentAllOrderCoercivityObstruction
