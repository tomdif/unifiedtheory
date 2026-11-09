/- A diagnostic periodic amplitude, not the Wilson ground state. Uniform
first-log bounds and a quadratic lower second-log bound do not force
summability of distant mixed ratios. The collective two-phase mode survives
at every pair of distinct coordinates. -/
import UnifiedTheory.Clay.YangMills.GibbsMixedInteraction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CollectiveCoshObstruction
noncomputable section

theorem cosh_comparison (x y : ℝ) :
    Real.cosh x ≤ Real.exp |x-y| * Real.cosh y := by
  have hp : Real.exp x ≤ Real.exp |x-y| * Real.exp y := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [le_abs_self (x-y)]
  have hm : Real.exp (-x) ≤ Real.exp |x-y| * Real.exp (-y) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [neg_le_abs (x-y)]
  rw [Real.cosh_eq, Real.cosh_eq]
  nlinarith

theorem log_cosh_lipschitz (x y : ℝ) :
    |Real.log (Real.cosh x)-Real.log (Real.cosh y)| ≤ |x-y| := by
  have hp := Real.log_le_log (Real.cosh_pos x) (cosh_comparison x y)
  have hm := Real.log_le_log (Real.cosh_pos y) (cosh_comparison y x)
  rw [Real.log_mul (Real.exp_ne_zero _) (Real.cosh_pos y).ne', Real.log_exp] at hp
  rw [Real.log_mul (Real.exp_ne_zero _) (Real.cosh_pos x).ne', Real.log_exp,
    abs_sub_comm y x] at hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem log_cosh_midpoint (x y : ℝ) :
    2*Real.log (Real.cosh x) ≤
      Real.log (Real.cosh (x+y))+Real.log (Real.cosh (x-y)) := by
  have he : Real.cosh (x+y)*Real.cosh (x-y) = (Real.cosh x)^2+(Real.sinh y)^2 := by
    calc
      _ = (Real.cosh x)^2*(Real.cosh y)^2-(Real.sinh x)^2*(Real.sinh y)^2 := by
        rw [Real.cosh_add, Real.cosh_sub]
        ring
      _ = _ := by rw [Real.cosh_sq y, Real.cosh_sq x]; ring
  have h := Real.log_le_log (sq_pos_of_pos (Real.cosh_pos x))
    (show (Real.cosh x)^2 ≤ Real.cosh (x+y)*Real.cosh (x-y) by
      rw [he]; exact le_add_of_nonneg_right (sq_nonneg _))
  rw [Real.log_pow, Real.log_mul (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'] at h
  norm_num at h ⊢
  exact h

variable {I : Type*} [Fintype I]

def amplitude (κ : ℝ) (u : I → ℝ) : ℝ := Real.cosh (κ*∑ i, Real.sin (u i))

def logAmplitude (κ : ℝ) (u : I → ℝ) : ℝ := Real.log (amplitude κ u)

theorem amplitude_pos (κ : ℝ) (u : I → ℝ) : 0 < amplitude κ u := Real.cosh_pos _

theorem amplitude_continuous (κ : ℝ) : Continuous (amplitude (I := I) κ) := by
  unfold amplitude
  fun_prop

theorem logAmplitude_continuous (κ : ℝ) : Continuous (logAmplitude (I := I) κ) :=
  (amplitude_continuous κ).log (fun u => (amplitude_pos κ u).ne')

theorem amplitude_smooth (κ : ℝ) : ContDiff ℝ ⊤ (amplitude (I := I) κ) := by
  unfold amplitude
  fun_prop

/-- The constant is independent of the number of coordinates. -/
theorem log_first_bound (κ : ℝ) (hκ : 0 ≤ κ) (u v : I → ℝ) :
    |logAmplitude κ u-logAmplitude κ v| ≤ κ*∑ i, |Real.sin (u i)-Real.sin (v i)| := by
  have h := log_cosh_lipschitz (κ*∑ i, Real.sin (u i)) (κ*∑ i, Real.sin (v i))
  change |logAmplitude κ u-logAmplitude κ v| ≤ _ at h
  rw [← mul_sub, abs_mul, abs_of_nonneg hκ, ← Finset.sum_sub_distrib] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hκ)

theorem log_first_angular (κ : ℝ) (hκ : 0 ≤ κ) (u v : I → ℝ) :
    |logAmplitude κ u-logAmplitude κ v| ≤ κ*∑ i, |u i-v i| :=
  (log_first_bound κ hκ u v).trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i _ => Real.abs_sin_sub_sin_le (u i) (v i))) hκ)

theorem sin_increment_chord (u δ : ℝ) :
    |Real.sin (u+δ)-Real.sin u| ≤ Real.sqrt (2*(1-Real.cos δ)) := by
  have he : (Real.sin (u+δ)-Real.sin u)^2+(Real.cos (u+δ)-Real.cos u)^2 =
      2*(1-Real.cos δ) := by
    calc
      _ = ((Real.sin (u+δ))^2+(Real.cos (u+δ))^2)+
          ((Real.sin u)^2+(Real.cos u)^2)-
          2*(Real.cos (u+δ)*Real.cos u+Real.sin (u+δ)*Real.sin u) := by ring
      _ = _ := by
        rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq, ← Real.cos_sub]
        simp
        ring
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt (mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.cos_le_one δ)))]
  nlinarith [sq_nonneg (Real.cos (u+δ)-Real.cos u)]

/-- The first bound also holds in actual circle chord displacements. -/
theorem log_first_chord (κ : ℝ) (hκ : 0 ≤ κ) (u δ : I → ℝ) :
    |logAmplitude κ (fun i => u i+δ i)-logAmplitude κ u| ≤
      κ*∑ i, Real.sqrt (2*(1-Real.cos (δ i))) :=
  (log_first_bound κ hκ _ u).trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i _ => sin_increment_chord (u i) (δ i))) hκ)

/-- A joint quadratic lower bound still allows collective distant correlations.
For circle rotations, 2*(1-cos δ) is squared chord displacement. -/
theorem log_second_lower (κ : ℝ) (hκ : 0 ≤ κ) (u δ : I → ℝ) :
    -(2*κ*∑ i, (1-Real.cos (δ i))) ≤
      logAmplitude κ (fun i => u i+δ i)+logAmplitude κ (fun i => u i-δ i)-
        2*logAmplitude κ u := by
  let M := ∑ i, Real.sin (u i)*Real.cos (δ i)
  let D := ∑ i, Real.cos (u i)*Real.sin (δ i)
  let S := ∑ i, Real.sin (u i)
  have hp : (∑ i, Real.sin (u i+δ i)) = M+D := by
    simp only [Real.sin_add, Finset.sum_add_distrib, M, D]
  have hm : (∑ i, Real.sin (u i-δ i)) = M-D := by
    simp only [Real.sin_sub, Finset.sum_sub_distrib, M, D]
  have hMS : |M-S| ≤ ∑ i, (1-Real.cos (δ i)) := by
    change |(∑ i, Real.sin (u i)*Real.cos (δ i))-(∑ i, Real.sin (u i))| ≤ _
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    have hc := sub_nonneg.mpr (Real.cos_le_one (δ i))
    calc
      _ = |Real.sin (u i)| * (1-Real.cos (δ i)) := by
        rw [← mul_sub_one, abs_mul, abs_sub_comm, abs_of_nonneg hc]
      _ ≤ 1*(1-Real.cos (δ i)) := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) hc
      _ = _ := one_mul _
  have hl := log_cosh_lipschitz (κ*M) (κ*S)
  rw [← mul_sub, abs_mul, abs_of_nonneg hκ] at hl
  have hb := hl.trans (mul_le_mul_of_nonneg_left hMS hκ)
  have hmid := log_cosh_midpoint (κ*M) (κ*D)
  simp only [logAmplitude, amplitude, hp, hm, mul_add, mul_sub]
  change _ ≤ Real.log (Real.cosh (κ*M+κ*D))+Real.log (Real.cosh (κ*M-κ*D))-
    2*Real.log (Real.cosh (κ*S))
  linarith [(abs_le.mp hb).1]

variable [DecidableEq I]

theorem sin_sum_update (u : I → ℝ) (e : I) (t : ℝ) :
    (∑ i, Real.sin (Function.update u e t i)) =
      (∑ i, Real.sin (u i))-Real.sin (u e)+Real.sin t := by
  have he : (fun i => Real.sin (Function.update u e t i)) =
      Function.update (fun i => Real.sin (u i)) e (Real.sin t) := by
    exact Function.comp_update Real.sin u e t
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ e)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hs := Finset.sum_erase_add Finset.univ (fun i => Real.sin (u i)) (Finset.mem_univ e)
  linarith

/-- Periodicity lets the amplitude descend to a finite product of circles. -/
theorem amplitude_periodic (κ : ℝ) (u : I → ℝ) (e : I) :
    amplitude κ (Function.update u e (u e+2*Real.pi)) = amplitude κ u := by
  unfold amplitude
  rw [sin_sum_update, Real.sin_add_two_pi]
  simp

def mixedRatio (κ t : ℝ) (e d : I) : ℝ :=
  amplitude κ (fun _ : I => 0)*
      amplitude κ (Function.update (Function.update (fun _ : I => 0) d t) e t) /
    (amplitude κ (Function.update (fun _ : I => 0) e t)*
      amplitude κ (Function.update (fun _ : I => 0) d t))-1

/-- The same strictly positive mixed ratio occurs at every distinct pair. -/
theorem mixedRatio_eq (κ t : ℝ) (e d : I) (hed : e ≠ d) :
    mixedRatio κ t e d = (Real.tanh (κ*Real.sin t))^2 := by
  unfold mixedRatio amplitude
  simp only [sin_sum_update, Function.update_of_ne hed, Real.sin_zero,
    Finset.sum_const_zero, sub_zero, zero_add, mul_zero, Real.cosh_zero, one_mul]
  rw [show κ*(Real.sin t+Real.sin t) = 2*(κ*Real.sin t) by ring,
    Real.cosh_two_mul, Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos (κ*Real.sin t)).ne']
  ring

/-- Removing any fixed-size near set leaves a sum proportional to its complement. -/
theorem far_sum_eq (κ t : ℝ) (e : I) (near : Finset I) (he : e ∈ near) :
    (∑ d ∈ Finset.univ \ near, |mixedRatio κ t e d|) =
      ((Finset.univ \ near).card : ℝ)*(Real.tanh (κ*Real.sin t))^2 := by
  have hd (d : I) (h : d ∈ Finset.univ \ near) : e ≠ d := by
    intro hed
    exact (Finset.mem_sdiff.mp h).2 (hed ▸ he)
  calc
    _ = ∑ d ∈ Finset.univ \ near, (Real.tanh (κ*Real.sin t))^2 := by
      apply Finset.sum_congr rfl
      intro d h
      rw [mixedRatio_eq κ t e d (hd d h), abs_of_nonneg (sq_nonneg _)]
    _ = _ := by simp

def exampleFar (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.univ \ ({0} : Finset (Fin (N+1))),
    |mixedRatio 1 (Real.pi/2) (0 : Fin (N+1)) d|

theorem exampleFar_eq (N : ℕ) : exampleFar N = (N : ℝ)*(Real.tanh 1)^2 := by
  unfold exampleFar
  rw [far_sum_eq 1 (Real.pi/2) (0 : Fin (N+1)) {0} (Finset.mem_singleton_self _)]
  simp [Finset.card_sdiff]

/-- There is no dimension-independent far-sum bound for this periodic family. -/
theorem far_unbounded (R : ℝ) : ∃ N : ℕ, R < exampleFar N := by
  have ht : 0 < Real.tanh 1 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos _)
  have hp := sq_pos_of_pos ht
  obtain ⟨N, hN⟩ := exists_nat_gt (R/(Real.tanh 1)^2)
  refine ⟨N, ?_⟩
  rw [exampleFar_eq]
  exact (div_lt_iff₀ hp).mp hN

end
end UnifiedTheory.Clay.YangMills.CollectiveCoshObstruction
