/- Full common-real-source quartic norm: finite imaginary increments
and the exact physical field-slope derivative. The charged family stays
coherent, and no differentiation of an infinite series is used. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianMonotonicity
noncomputable section
open MeasureTheory
open KFCausalCommonRealGaussianEnergy
open KFCausalChargedGaussianMomentSeries (weightedEnergy)
open KFCausalChargedEvenMomentImaginaryBound (gamma)
variable {ι : Type*} [Fintype ι]

theorem energy_nonnegative (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) :
    0 ≤ energy β B L p d w c := by
  apply integral_nonneg
  intro x
  have hn : 0 ≤ neutralLine β B L x.1.2 := integral_nonneg (fun t =>
    mul_nonneg (KFCausalQuarticPlaneDomination.potential_positive _).le (Real.exp_pos _).le)
  unfold density
  positivity

theorem actual_scaled_le (α a β B L b₁ b₂ : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂) (hb₂ : b₂ < a)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ)
    (hd : ∀ i, 8*β*b₂^2 < α*(a^2-b₂^2)*w i) :
    b₁^2*energy β B L (gamma α ((a:ℂ)+Complex.I*(b₁:ℂ))) (8*β*b₁^2) w c ≤
    b₂^2*energy β B L (gamma α ((a:ℂ)+Complex.I*(b₂:ℂ))) (8*β*b₂^2) w c := by
  have hb₂0 := lt_of_lt_of_le hb₁ hb
  have hb₁a := lt_of_le_of_lt hb hb₂
  have hs : b₁^2 ≤ b₂^2 := by nlinarith
  have hd₁ : ∀ i, 8*β*b₁^2 < α*(a^2-b₁^2)*w i := by
    intro i
    have hwi := hw i
    have hpos : 0 ≤ (8*β+α*w i)*(b₂^2-b₁^2) := mul_nonneg (by positivity) (sub_nonneg.mpr hs)
    nlinarith [hd i]
  have hp (b : ℝ) (hb0 : 0 < b) (hba : b < a) : 0 < (gamma α ((a:ℂ)+Complex.I*(b:ℂ))).re := by
    apply KFCausalChargedCoolingFixedV.actual_gamma_re_positive α _ hα
    simpa [abs_of_pos hb0] using hba
  have hre (b : ℝ) : 2*(gamma α ((a:ℂ)+Complex.I*(b:ℂ))).re=α*(a^2-b^2) := by
    simp [gamma,pow_two,Complex.mul_re,Complex.mul_im]
    ring
  rw [energy_decomposition β B L _ _ w c hβ (hp b₁ hb₁ hb₁a) hw
    (by intro i; rw [hre]; exact hd₁ i),
    energy_decomposition β B L _ _ w c hβ (hp b₂ hb₂0 hb₂) hw
    (by intro i; rw [hre]; exact hd i)]
  obtain ⟨h0,h1,h2⟩ := coefficients_nonnegative β B L
  have he (m : ℕ) (hm : m ≤ 2) :=
    KFCausalChargedGaussianMomentSeries.actual_scaled_le α a β b₁ b₂ hα hβ.le hb₁ hb hb₂ m hm w hw c hd
  nlinarith [mul_le_mul_of_nonneg_left (he 0 (by omega)) h0,
    mul_le_mul_of_nonneg_left (he 1 (by omega)) h1,
    mul_le_mul_of_nonneg_left (he 2 (by omega)) h2]

theorem field_derivative (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    HasDerivAt (fun t => energy β B t p d w c)
      (2*L*(neutralMoment β B 0/2+3*neutralMoment β B 2/2)*weightedEnergy 1 p d w c+
        L^3*neutralMoment β B 0*weightedEnergy 2 p d w c) L := by
  have he : (fun t => energy β B t p d w c) = fun t =>
      coefficient0 β B*weightedEnergy 0 p d w c+
      t^2*(neutralMoment β B 0/2+3*neutralMoment β B 2/2)*weightedEnergy 1 p d w c+
      t^4*neutralMoment β B 0/4*weightedEnergy 2 p d w c := by
    funext t
    exact energy_decomposition β B t p d w c hβ hp hw hd
  rw [he]
  convert ((hasDerivAt_const L (coefficient0 β B*weightedEnergy 0 p d w c)).add
    ((((hasDerivAt_id L).pow 2).mul_const _).mul_const _)).add
    (((((hasDerivAt_id L).pow 4).mul_const _).div_const 4).mul_const _) using 1
  simp only [id_eq]
  ring

theorem field_derivative_bounds (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    0 ≤ L*deriv (fun t => energy β B t p d w c) L ∧
      L*deriv (fun t => energy β B t p d w c) L ≤ 4*energy β B L p d w c := by
  rw [(field_derivative β B L p d w c hβ hp hw hd).deriv,
    energy_decomposition β B L p d w c hβ hp hw hd]
  have hv (m : ℕ) : 0 ≤ weightedEnergy m p d w c := integral_nonneg (fun _ => by positivity)
  obtain ⟨h0,h1,h2⟩ := coefficients_nonnegative β B L
  have he : L*(2*L*(neutralMoment β B 0/2+3*neutralMoment β B 2/2)*weightedEnergy 1 p d w c+
        L^3*neutralMoment β B 0*weightedEnergy 2 p d w c) =
      2*(coefficient1 β B L*weightedEnergy 1 p d w c)+4*(coefficient2 β B L*weightedEnergy 2 p d w c) := by
    unfold coefficient1 coefficient2
    ring
  rw [he]
  constructor <;> nlinarith [mul_nonneg h0 (hv 0),mul_nonneg h1 (hv 1),mul_nonneg h2 (hv 2)]

#print axioms energy_nonnegative
#print axioms actual_scaled_le
#print axioms field_derivative
#print axioms field_derivative_bounds
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianMonotonicity
