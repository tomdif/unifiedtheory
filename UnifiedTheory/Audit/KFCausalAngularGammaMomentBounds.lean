/- Actual endpoint-weighted Gamma moment integrability and a vanishing
endpoint tail. The singular factor is integrated explicitly, rather than
replaced by an assumed convergence or uniform majorant at the endpoint. -/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularGammaMomentBounds
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

def density (j : ℕ) (u : ℝ) : ℝ := Real.exp (-u)*u^((j:ℝ)-1/2)
def correction (z u : ℝ) : ℝ := (1-u/(2*z))^(-(1/2:ℝ))
def kernel (j : ℕ) (z u : ℝ) : ℝ := density j u*correction z u
def moment (j : ℕ) (z : ℝ) : ℝ := ∫ u in 0..(2*z), kernel j z u
def tail (j : ℕ) (z : ℝ) : ℝ := ∫ u in z..(2*z), kernel j z u

theorem density_integrable (j : ℕ) : IntegrableOn (density j) (Ioi 0) := by
  have hh := Real.GammaIntegral_convergent (s := (j:ℝ)+1/2) (by positivity)
  convert hh using 1
  funext u
  unfold density
  congr 2
  ring

theorem correction_nonnegative (z u : ℝ) : 0 ≤ correction z u := by
  unfold correction
  by_cases hb : 0 ≤ 1-u/(2*z)
  · exact Real.rpow_nonneg hb _
  · rw [Real.rpow_def_of_neg (lt_of_not_ge hb)]
    have he : (-(1/2:ℝ))*Real.pi= -(Real.pi/2) := by ring
    rw [he,Real.cos_neg,Real.cos_pi_div_two,mul_zero]

theorem kernel_nonnegative (j : ℕ) (z u : ℝ) (hu : 0 ≤ u) : 0 ≤ kernel j z u := by
  unfold kernel density
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hu _))
    (correction_nonnegative z u)

private theorem base_integrable :
    IntervalIntegrable (fun t : ℝ => (1-t)^(-(1/2:ℝ))) volume 0 1 := by
  have hh : IntervalIntegrable (fun t : ℝ => t^(-(1/2:ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  simpa only [sub_zero,sub_self] using (hh.comp_sub_left 1).symm

theorem correction_integrable (z : ℝ) (_hz : 0 < z) :
    IntervalIntegrable (correction z) volume 0 (2*z) := by
  change IntervalIntegrable (fun u : ℝ => (1-u/(2*z))^(-(1/2:ℝ))) volume 0 (2*z)
  have hh := base_integrable.comp_mul_right (c := (2*z)⁻¹)
  simpa only [zero_div,one_div,inv_inv,correction,div_eq_mul_inv,zero_mul,one_mul] using hh

theorem correction_integral (z : ℝ) (hz : 0 < z) :
    (∫ u in 0..(2*z), correction z u)=4*z := by
  unfold correction
  rw [intervalIntegral.integral_comp_div (fun t : ℝ => (1-t)^(-(1/2:ℝ)))
    (by positivity : 2*z ≠ 0)]
  rw [zero_div,div_self (by positivity : 2*z ≠ 0)]
  rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^(-(1/2:ℝ))) 1]
  norm_num [integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -(1/2:ℝ))),smul_eq_mul]
  ring

theorem correction_left_bound (z u : ℝ) (hz : 0 < z) (hu : u ∈ Icc 0 z) :
    correction z u ≤ 2 := by
  have hb : (1/2:ℝ) ≤ 1-u/(2*z) := by
    have hd := (div_le_div_iff_of_pos_right (by positivity : 0<2*z)).mpr hu.2
    have he : z/(2*z)=(1/2:ℝ) := by field_simp
    rw [he] at hd
    linarith
  have hr := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<1/2) hb
    (by norm_num : -(1/2:ℝ)≤0)
  have hs := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ)≤1) (by norm_num : (-1:ℝ)≤ -(1/2:ℝ))
  norm_num [Real.rpow_neg_one] at hs
  exact hr.trans hs

private theorem correction_continuous_left (z : ℝ) (hz : 0 < z) :
    ContinuousOn (correction z) (Icc 0 z) := by
  apply ContinuousOn.rpow_const (by fun_prop)
  intro u hu
  left
  have hd := (div_le_div_iff_of_pos_right (by positivity : 0<2*z)).mpr hu.2
  have he : z/(2*z)=(1/2:ℝ) := by field_simp
  rw [he] at hd
  linarith

private theorem density_continuous_right (j : ℕ) (z : ℝ) (hz : 0 < z) :
    ContinuousOn (density j) (Icc z (2*z)) := by
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.rpow_const continuousOn_id
  intro u hu
  exact Or.inl (ne_of_gt (hz.trans_le hu.1))

theorem kernel_integrable (j : ℕ) (z : ℝ) (hz : 0 < z) :
    IntervalIntegrable (kernel j z) volume 0 (2*z) := by
  have hd : IntervalIntegrable (density j) volume 0 z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mpr
      ((density_integrable j).mono_set Ioc_subset_Ioi_self)
  have hl := hd.mul_continuousOn (by
    simpa only [uIcc_of_le hz.le] using correction_continuous_left z hz)
  have hc : IntervalIntegrable (correction z) volume z (2*z) :=
    (correction_integrable z hz).mono_set (by
      rw [uIcc_of_le (by linarith : (0:ℝ)≤2*z),uIcc_of_le (by linarith : z≤2*z)]
      exact Icc_subset_Icc hz.le le_rfl)
  have hr := hc.continuousOn_mul (by
    simpa only [uIcc_of_le (by linarith : z≤2*z)] using density_continuous_right j z hz)
  exact hl.trans hr

theorem tail_bound (j : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    0 ≤ tail j z ∧ tail j z ≤ 4*z*(2*z)^j*Real.exp (-z) := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hzi : z ≤ 2*z := by linarith
  have hc : IntervalIntegrable (correction z) volume z (2*z) :=
    (correction_integrable z hz0).mono_set (by
      rw [uIcc_of_le (by linarith : (0:ℝ)≤2*z),uIcc_of_le hzi]
      exact Icc_subset_Icc hz0.le le_rfl)
  have hk : IntervalIntegrable (kernel j z) volume z (2*z) :=
    (kernel_integrable j z hz0).mono_set (by
      rw [uIcc_of_le (by linarith : (0:ℝ)≤2*z),uIcc_of_le hzi]
      exact Icc_subset_Icc hz0.le le_rfl)
  have hmajor : ∀ u ∈ Icc z (2*z),
      kernel j z u ≤ (Real.exp (-z)*(2*z)^j)*correction z u := by
    intro u hu
    have hu1 : 1 ≤ u := hz.trans hu.1
    have hp : u^((j:ℝ)-1/2) ≤ (2*z)^j := by
      have hh := Real.rpow_le_rpow_of_exponent_le hu1
        (by linarith : (j:ℝ)-1/2≤(j:ℝ))
      rw [Real.rpow_natCast] at hh
      exact hh.trans (pow_le_pow_left₀ (by linarith) hu.2 j)
    have he : Real.exp (-u) ≤ Real.exp (-z) := Real.exp_le_exp.mpr (by linarith [hu.1])
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul he hp (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le)
      (correction_nonnegative z u)
  have ht := intervalIntegral.integral_mono_on hzi hk
    (hc.const_mul (Real.exp (-z)*(2*z)^j)) hmajor
  rw [intervalIntegral.integral_const_mul] at ht
  have hs := intervalIntegral.integral_mono_interval hz0.le hzi le_rfl
    (Eventually.of_forall (fun u => correction_nonnegative z u)) (correction_integrable z hz0)
  rw [correction_integral z hz0] at hs
  constructor
  · exact intervalIntegral.integral_nonneg hzi (fun u hu => kernel_nonnegative j z u (by linarith [hu.1]))
  · exact ht.trans ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring))

theorem tail_tendsto (j : ℕ) : Tendsto (tail j) atTop (𝓝 0) := by
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (j+1)).const_mul (4*(2:ℝ)^j)
  have he : (fun z : ℝ => (4*(2:ℝ)^j)*(z^(j+1)*Real.exp (-z))) =
      fun z => 4*z*(2*z)^j*Real.exp (-z) := by
    funext z
    rw [mul_pow,pow_succ]
    ring
  rw [he] at ht
  apply squeeze_zero' ?_ ?_ (by simpa using ht)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with z hz
    exact (tail_bound j z hz).1
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with z hz
    exact (tail_bound j z hz).2

#print axioms density_integrable
#print axioms correction_nonnegative
#print axioms kernel_nonnegative
#print axioms correction_integrable
#print axioms correction_integral
#print axioms correction_left_bound
#print axioms kernel_integrable
#print axioms tail_bound
#print axioms tail_tendsto
end
end UnifiedTheory.Audit.KFCausalAngularGammaMomentBounds
