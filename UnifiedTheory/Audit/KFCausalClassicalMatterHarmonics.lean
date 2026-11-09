/- Nonvanishing and positive overlap for the exact harmonic degrees appearing
in the classical matter field and shear. These are scalar charge profiles. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterHarmonics
noncomputable section
open Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalChargeMean

def first (a : Fin 3 → ℝ) (θ : ℝ) : ℝ :=
  a 0+a 1*Real.cos θ+a 2*Real.sin θ

def second (b : Fin 4 → ℝ) (θ : ℝ) : ℝ :=
  b 0*(Real.cos θ^2-Real.sin θ^2)+b 1*(Real.sin θ*Real.cos θ)+
    b 2*Real.sin θ+b 3*Real.cos θ

theorem first_continuous (a : Fin 3 → ℝ) : Continuous (first a) := by
  unfold first
  fun_prop

theorem second_continuous (b : Fin 4 → ℝ) : Continuous (second b) := by
  unfold second
  fun_prop

theorem first_analytic (a : Fin 3 → ℝ) : AnalyticOnNhd ℝ (first a) univ := by
  intro x _
  exact ((analyticAt_const.add (analyticAt_const.mul Real.analyticAt_cos)).add
    (analyticAt_const.mul Real.analyticAt_sin))

theorem second_analytic (b : Fin 4 → ℝ) : AnalyticOnNhd ℝ (second b) univ := by
  intro x _
  exact (((analyticAt_const.mul ((Real.analyticAt_cos.pow 2).sub (Real.analyticAt_sin.pow 2))).add
    (analyticAt_const.mul (Real.analyticAt_sin.mul Real.analyticAt_cos))).add
    (analyticAt_const.mul Real.analyticAt_sin)).add (analyticAt_const.mul Real.analyticAt_cos)

theorem first_eq_zero_iff (a : Fin 3 → ℝ) : first a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have hp := congrFun h Real.pi
    have hh := congrFun h (Real.pi/2)
    simp only [first,Pi.zero_apply,Real.cos_zero,Real.sin_zero,Real.cos_pi,
      Real.sin_pi,Real.cos_pi_div_two,Real.sin_pi_div_two,mul_one,mul_zero,mul_neg_one,
      add_zero] at h0 hp hh
    have ha0 : a 0 = 0 := by linarith
    have ha1 : a 1 = 0 := by linarith
    have ha2 : a 2 = 0 := by linarith
    funext i
    fin_cases i <;> simp [ha0,ha1,ha2]
  · rintro rfl
    funext θ
    simp [first]

theorem second_eq_zero_iff (b : Fin 4 → ℝ) : second b = 0 ↔ b = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have hp := congrFun h Real.pi
    have hh := congrFun h (Real.pi/2)
    have hn := congrFun h (Real.pi/2+Real.pi)
    simp [second,Real.sin_add_pi,Real.cos_add_pi] at h0 hp hh hn
    have hb0 : b 0 = 0 := by linarith
    have hb2 : b 2 = 0 := by linarith
    have hb3 : b 3 = 0 := by linarith
    have hq := congrFun h (Real.pi/4)
    have hsqrt : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    simp only [second,Pi.zero_apply,hb0,hb2,hb3,zero_mul,zero_add,add_zero,
      Real.sin_pi_div_four,Real.cos_pi_div_four] at hq
    have hb1 : b 1 = 0 := by nlinarith
    funext i
    fin_cases i <;> simp [hb0,hb1,hb2,hb3]
  · rintro rfl
    funext θ
    simp [second]

theorem second_mean_zero (b : Fin 4 → ℝ) : mean (second b) = 0 := by
  have he : second b = fun θ =>
      (Real.cos θ^2-Real.sin θ^2)*b 0+(Real.sin θ*Real.cos θ)*b 1+
        Real.sin θ*b 2+Real.cos θ*b 3 := by funext θ; unfold second; ring
  rw [he,mean_add _ _ (by fun_prop) (by fun_prop),
    mean_add _ _ (by fun_prop) (by fun_prop),mean_add _ _ (by fun_prop) (by fun_prop)]
  simp only [mean_mul_const]
  rw [mean_sub _ _ (by fun_prop) (by fun_prop),mean_trig.1,mean_trig.2.1,
    mean_trig.2.2.1,mean_trig.2.2.2.1,mean_trig.2.2.2.2]
  ring

theorem analytic_nonzero_on_open (f : ℝ → ℝ) (hf : AnalyticOnNhd ℝ f univ)
    (hn : f ≠ 0) (U : Set ℝ) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ θ ∈ U, f θ ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨x,hx⟩ := hUne
  have he : f =ᶠ[𝓝 x] 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact h y hy
  exact hn (hf.eq_of_eventuallyEq (fun _ _ => analyticAt_const) he)

theorem second_positive_somewhere (b : Fin 4 → ℝ) (hb : b ≠ 0) :
    ∃ θ ∈ Ioo (0:ℝ) (2*Real.pi), 0 < second b θ := by
  by_contra hn
  push_neg at hn
  obtain ⟨θ,hθ,hne⟩ := analytic_nonzero_on_open (second b) (second_analytic b)
    (fun h => hb ((second_eq_zero_iff b).mp h)) (Ioo (0:ℝ) (2*Real.pi)) isOpen_Ioo
    ⟨Real.pi,by constructor <;> linarith [Real.pi_pos]⟩
  have hle : ∀ x ∈ Icc (0:ℝ) (2*Real.pi), second b x ≤ 0 := by
    have hsub : Ioo (0:ℝ) (2*Real.pi) ⊆ {x | second b x ≤ 0} := hn
    have hc := closure_minimal hsub (isClosed_le (second_continuous b) continuous_const)
    rw [closure_Ioo (by positivity : (0:ℝ) < 2*Real.pi).ne] at hc
    exact hc
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by positivity : (0:ℝ) < 2*Real.pi) (second_continuous b).continuousOn continuousOn_const
    (fun x hx => hle x (Ioc_subset_Icc_self hx))
    ⟨θ,Ioo_subset_Icc_self hθ,lt_of_le_of_ne (hn θ hθ) hne⟩
  have hm : mean (second b) < 0 := by
    unfold mean
    have hi' : (∫ x in (0:ℝ)..2*Real.pi, second b x) < 0 := by simpa using hi
    exact mul_neg_of_pos_of_neg (by positivity) hi'
  rw [second_mean_zero] at hm
  exact (lt_irrefl 0) hm

theorem overlap_positive (a : Fin 3 → ℝ) (b : Fin 4 → ℝ) (k : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    0 < mean (fun θ => (first a θ)^(2*k)*max (second b θ) 0) := by
  obtain ⟨θ,hθ,hpos⟩ := second_positive_somewhere b hb
  let U := Ioo (0:ℝ) (2*Real.pi) ∩ {x | 0 < second b x}
  have ho : IsOpen U := isOpen_Ioo.inter (isOpen_lt continuous_const (second_continuous b))
  obtain ⟨x,hx,hf⟩ := analytic_nonzero_on_open (first a) (first_analytic a)
    (fun h => ha ((first_eq_zero_iff a).mp h)) U ho ⟨θ,hθ,hpos⟩
  have hp : 0 < (first a x)^(2*k) := by
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero hf) _
  unfold mean
  apply mul_pos (by positivity)
  apply intervalIntegral.integral_pos (by positivity)
    ((first_continuous a).pow _ |>.mul ((second_continuous b).max continuous_const)).continuousOn
    (fun y _ => mul_nonneg (Even.pow_nonneg (even_two_mul k) _) (le_max_right _ _))
  exact ⟨x,Ioo_subset_Icc_self hx.1,mul_pos hp (lt_max_iff.mpr (Or.inl hx.2))⟩

#print axioms first_continuous
#print axioms second_continuous
#print axioms first_analytic
#print axioms second_analytic
#print axioms first_eq_zero_iff
#print axioms second_eq_zero_iff
#print axioms second_mean_zero
#print axioms analytic_nonzero_on_open
#print axioms second_positive_somewhere
#print axioms overlap_positive

end
end UnifiedTheory.Audit.KFCausalClassicalMatterHarmonics

