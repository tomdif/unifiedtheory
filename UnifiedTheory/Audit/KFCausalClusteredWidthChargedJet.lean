/- The charged holomorphic derivative has a spacing-independent envelope
and the correct polynomial limit. This supplies the charged part of a
future dominated clock-derivative limit; no integral derivative is inferred. -/
import UnifiedTheory.Audit.KFCausalClusteredWidthProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClusteredWidthChargedJet
noncomputable section
open Filter
open scoped Topology
open KFCausalClusteredWidthProfiles (widths coefficients quotient)
open KFCausalReciprocalWedgeLaplace (laplaceSum)

def jet (n : ℕ) (δ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-z)*((n:ℂ)*quotient δ z^(n-1)*Complex.exp (-(δ:ℂ)*z)-quotient δ z^n)
def limitJet (n : ℕ) (z : ℂ) : ℂ := Complex.exp (-z)*((n:ℂ)*z^(n-1)-z^n)

theorem quotient_derivative (δ : ℝ) (hδ : δ ≠ 0) (z : ℂ) :
    HasDerivAt (quotient δ) (Complex.exp (-(δ:ℂ)*z)) z := by
  have hd := ((hasDerivAt_const z (1:ℂ)).sub (((hasDerivAt_id z).const_mul (-(δ:ℂ))).cexp)).div_const (δ:ℂ)
  convert hd using 1
  have hh : (δ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ
  simp only [id_eq]
  field_simp
  ring

theorem profile_derivative (n : ℕ) (δ : ℝ) (hδ : δ ≠ 0) (z : ℂ) :
    HasDerivAt (fun x => Complex.exp (-x)*quotient δ x^n) (jet n δ z) z := by
  convert (((hasDerivAt_id z).neg.cexp).mul ((quotient_derivative δ hδ z).pow n)) using 1
  dsimp [jet]
  ring

theorem laplaceSum_derivative (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (z : ℂ) :
    HasDerivAt (laplaceSum (n+1) (widths n δ) (coefficients n δ)) (jet n δ z) z := by
  have he := funext (KFCausalClusteredWidthProfiles.laplaceSum_exact n δ hδ)
  rw [he]
  exact profile_derivative n δ hδ.ne' z

theorem exponential_norm_le_one (δ : ℝ) (z : ℂ) (hδ : 0 ≤ δ) (hz : 0 ≤ z.re) :
    ‖Complex.exp (-(δ:ℂ)*z)‖ ≤ 1 := by
  rw [Complex.norm_exp,Real.exp_le_one_iff]
  simpa only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
    Complex.ofReal_im,neg_zero,zero_mul,sub_zero,neg_mul] using neg_nonpos.mpr (mul_nonneg hδ hz)

theorem jet_norm_le (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖jet n δ z‖ ≤ Real.exp (-z.re)*((n:ℝ)*‖z‖^(n-1)+‖z‖^n) := by
  have hq := KFCausalClusteredWidthProfiles.quotient_norm_le δ z hδ hz
  have hn := pow_le_pow_left₀ (norm_nonneg _) hq n
  have hn' := pow_le_pow_left₀ (norm_nonneg _) hq (n-1)
  have he := exponential_norm_le_one δ z hδ.le hz
  unfold jet
  rw [norm_mul,Complex.norm_exp,Complex.neg_re]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply (norm_sub_le _ _).trans
  simp only [norm_mul,norm_pow,Complex.norm_natCast]
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hn' (Nat.cast_nonneg n)) he
    (norm_nonneg _) (by positivity : 0 ≤ (n:ℝ)*‖z‖^(n-1))
  simpa only [mul_one] using add_le_add hm hn

theorem jet_tendsto (n : ℕ) (z : ℂ) :
    Tendsto (fun δ : ℝ => jet n δ z) (𝓝[>] 0) (𝓝 (limitJet n z)) := by
  have he : Tendsto (fun δ : ℝ => Complex.exp (-(δ:ℂ)*z)) (𝓝[>] 0) (𝓝 (1:ℂ)) := by
    have hc : ContinuousAt (fun δ : ℝ => Complex.exp (-(δ:ℂ)*z)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hq := KFCausalClusteredWidthProfiles.quotient_tendsto z
  simpa only [jet,limitJet,mul_one] using
    (((hq.pow (n-1)).const_mul (n:ℂ)).mul he |>.sub (hq.pow n)).const_mul (Complex.exp (-z))

theorem moving_laplaceSum_derivative (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (z : ℝ → ℂ) (v : ℂ) (s : ℝ) (hz : HasDerivAt z v s) :
    HasDerivAt (fun t => laplaceSum (n+1) (widths n δ) (coefficients n δ) (z t))
      (jet n δ (z s)*v) s := by
  simpa only [Function.comp_def,smul_eq_mul,mul_comm] using
    (laplaceSum_derivative n δ hδ (z s)).scomp s hz

#print axioms quotient_derivative
#print axioms profile_derivative
#print axioms laplaceSum_derivative
#print axioms exponential_norm_le_one
#print axioms jet_norm_le
#print axioms jet_tendsto
#print axioms moving_laplaceSum_derivative
end
end UnifiedTheory.Audit.KFCausalClusteredWidthChargedJet
