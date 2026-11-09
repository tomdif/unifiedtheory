/- Positivity of the literal normalized volume and radial Jacobian factors
on a fixed coordinate box. Every bound is obtained from the actual positive
parameter integral, with its mass and integrability proved. -/
import UnifiedTheory.Audit.KFCausalConformal4DNormalizedVolume

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DVolumePositivity
noncomputable section
open Real MeasureTheory Set
open KFCausalConformal4DBoostedMoments KFCausalConformal4DTemporalVariation
open KFCausalConformal4DNormalizedVolume

theorem time_bound (M m A B x y z : ℝ) (hM : 0 ≤ M)
    (hm : |m| ≤ M/2) (hA : |A| ≤ M/2) (hB : |B| ≤ M/2)
    (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1)
    (hz : z ∈ Icc (-1:ℝ) 1) : |time 1 m A B x y z| ≤ M := by
  have hyz : |y*z| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg hy.1]
    exact mul_le_one₀ hy.2 (abs_nonneg _) (abs_le.mpr hz)
  have hax : |A*x| ≤ (M/2)*x := by
    rw [abs_mul,abs_of_nonneg hx.1]
    exact mul_le_mul_of_nonneg_right hA hx.1
  have hbx : |B*(1-x)*y*z| ≤ (M/2)*(1-x) := by
    calc |B*(1-x)*y*z| = (|B| *(1-x))*|y*z| := by
           rw [show B*(1-x)*y*z=(B*(1-x))*(y*z) by ring,
             abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hx.2)]
         _ ≤ ((M/2)*(1-x))*1 :=
           mul_le_mul (mul_le_mul_of_nonneg_right hB (sub_nonneg.mpr hx.2))
             hyz (abs_nonneg _) (mul_nonneg (div_nonneg hM (by norm_num)) (sub_nonneg.mpr hx.2))
         _ = _ := mul_one _
  calc |time 1 m A B x y z| = |m+A*x+B*(1-x)*y*z| := by simp only [time,mul_one]
       _ ≤ |m+A*x|+|B*(1-x)*y*z| := abs_add_le _ _
       _ ≤ (|m|+|A*x|)+|B*(1-x)*y*z| := by linarith [abs_add_le m (A*x)]
       _ ≤ M/2+(M/2)*x+(M/2)*(1-x) := add_le_add (add_le_add hm hax) hbx
       _ = M := by ring

theorem average_mono_on (M t r : ℝ) (hM : 0 ≤ M) (ht : |t| ≤ M) (hr : |r| ≤ M)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ s : ℝ, |s| ≤ M → f s ≤ g s) : average t r f ≤ average t r g := by
  have ht' : |t/2| ≤ M/2 := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right ht (by norm_num)
  have hr' : |r/2| ≤ M/2 := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right hr (by norm_num)
  obtain ⟨hfi,hfm,hfo⟩ := coordinate_integrable 1 (t/2) (t/2) (r/2) hf
  obtain ⟨hgi,hgm,hgo⟩ := coordinate_integrable 1 (t/2) (t/2) (r/2) hg
  unfold KFCausalConformal4DNormalizedVolume.average coordinateIntegral
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on (by norm_num) hfo hgo
  intro x hx
  apply intervalIntegral.integral_mono_on (by norm_num) (hfm x) (hgm x)
  intro y hy
  apply intervalIntegral.integral_mono_on (by norm_num) (hfi x y) (hgi x y)
  intro z hz
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add
      (hfg _ (time_bound M (t/2) (t/2) (r/2) x y z hM ht' ht' hr' hx hy hz))
      (hfg _ (time_bound M (t/2) (-(t/2)) (r/2) x y z hM ht'
        (by simpa only [abs_neg] using ht') hr' hx hy hz))
  · change 0 ≤ (1-x)^3*y^2
    have : 0 ≤ 1-x := sub_nonneg.mpr hx.2
    positivity

theorem average_bounds (M t r L U : ℝ) (hM : 0 ≤ M) (ht : |t| ≤ M) (hr : |r| ≤ M)
    {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ s : ℝ, |s| ≤ M → L ≤ f s ∧ f s ≤ U) :
    L ≤ average t r f ∧ average t r f ≤ U := by
  constructor
  · simpa only [average_const] using average_mono_on M t r hM ht hr
      continuous_const hf (fun s hs => (h s hs).1)
  · simpa only [average_const] using average_mono_on M t r hM ht hr
      hf continuous_const (fun s hs => (h s hs).2)

private theorem parameter_bound (c s : ℝ) (hc : |c| ≤ 1/54) (hs : |s| ≤ 3) :
    |c*s^2| ≤ 1/6 := by
  have hs2 : s^2 ≤ 9 := by
    have ha := abs_le.mp hs
    nlinarith [sq_nonneg (s-3),sq_nonneg (s+3)]
  calc |c*s^2| = |c| *s^2 := by rw [abs_mul,abs_of_nonneg (sq_nonneg s)]
       _ ≤ (1/54)*9 := mul_le_mul hc hs2 (sq_nonneg _) (by norm_num)
       _ = 1/6 := by norm_num

theorem normalized_bounds (c t r : ℝ) (hc : |c| ≤ 1/54)
    (ht : |t| ≤ 3) (hr : |r| ≤ 3) :
    (5/6:ℝ)^4 ≤ normalized c t r ∧ normalized c t r ≤ (7/6:ℝ)^4 := by
  apply average_bounds 3 t r _ _ (by norm_num) ht hr (f := density c)
  · rw [show density c=(fun s => (1+c*s^2)^4) from funext (density_polynomial c)]
    fun_prop
  · intro s hs
    rw [density_polynomial]
    have hp := abs_le.mp (parameter_bound c s hc hs)
    have hl : (5/6:ℝ) ≤ 1+c*s^2 := by linarith
    have hu : 1+c*s^2 ≤ (7/6:ℝ) := by linarith
    exact ⟨pow_le_pow_left₀ (by norm_num) hl 4,
      pow_le_pow_left₀ (by linarith) hu 4⟩

theorem jacobian_factor_lower (c t r : ℝ) (hc : |c| ≤ 1/54)
    (ht : |t| ≤ 3) (hr : |r| ≤ 3) :
    (5/6:ℝ)^3/2 ≤ jacobianFactor c t r := by
  have h := average_mono_on 3 t r (by norm_num) ht hr
    (f := fun _ => (5/6:ℝ)^3/2)
    (g := fun s => (1+c*s^2)^3*(1+3*c*s^2)) continuous_const (by fun_prop) ?_
  · simpa only [average_const,jacobianFactor] using h
  · intro s hs
    have hp := abs_le.mp (parameter_bound c s hc hs)
    have hl : (5/6:ℝ) ≤ 1+c*s^2 := by linarith
    have hl' : (1/2:ℝ) ≤ 1+3*c*s^2 := by linarith
    calc (5/6:ℝ)^3/2 = (5/6:ℝ)^3*(1/2) := by ring
         _ ≤ (1+c*s^2)^3*(1+3*c*s^2) :=
           mul_le_mul (pow_le_pow_left₀ (by norm_num) hl 3) hl' (by norm_num)
             (pow_nonneg (by linarith) _)

theorem normalized_pos (c t r : ℝ) (hc : |c| ≤ 1/54)
    (ht : |t| ≤ 3) (hr : |r| ≤ 3) : 0 < normalized c t r :=
  lt_of_lt_of_le (by norm_num) (normalized_bounds c t r hc ht hr).1

theorem jacobian_factor_pos (c t r : ℝ) (hc : |c| ≤ 1/54)
    (ht : |t| ≤ 3) (hr : |r| ≤ 3) : 0 < jacobianFactor c t r :=
  lt_of_lt_of_le (by norm_num) (jacobian_factor_lower c t r hc ht hr)

#print axioms time_bound
#print axioms average_mono_on
#print axioms average_bounds
#print axioms normalized_bounds
#print axioms jacobian_factor_lower
#print axioms normalized_pos
#print axioms jacobian_factor_pos
end
end UnifiedTheory.Audit.KFCausalConformal4DVolumePositivity
