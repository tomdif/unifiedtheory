/- Complex continuation of the five transverse shear coordinates. The
neutral row is retained and the two rotated factors remain ordered.
The norm estimates use a normalized neutral coupling at most one quarter. -/
import UnifiedTheory.Audit.KFCausalComplexQuadraticPerturbation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalComplexShearPerturbation
noncomputable section
open scoped BigOperators
abbrev Space := EuclideanSpace ℂ (Fin 5)

def flow (σ : ℝ) (z : ℂ) (x : Space) : Space := WithLp.toLp 2
  ![Complex.exp (-z/2)*x 0,Complex.exp (-z/2)*x 1,
    Complex.exp (z/2)*x 2,Complex.exp (z/2)*x 3,
    x 4+2*(σ:ℂ)*(Complex.exp (z/2)-1)*x 3]

def diagonal (c : Fin 5 → ℂ) (x : Space) : Space := WithLp.toLp 2 (fun i => c i*x i)

theorem diagonal_bound (c : Fin 5 → ℂ) (x : Space) (d : ℝ)
    (hd : 0 ≤ d) (hc : ∀ i, ‖c i‖ ≤ d) : ‖diagonal c x‖ ≤ d*‖x‖ := by
  have hs : ‖diagonal c x‖^2 ≤ d^2*‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change ‖c i*x i‖^2 ≤ d^2*‖x i‖^2
    rw [norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hd).mpr (hc i)) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hd (norm_nonneg _))).mp (by nlinarith)

theorem exp_half_bound (z : ℂ) (hz : ‖z‖ ≤ 1/5) :
    ‖Complex.exp (z/2)-1‖ ≤ ‖z‖/2+(‖z‖/2)^2 := by
  have hn : ‖z/2‖=‖z‖/2 := by rw [norm_div]; norm_num
  have hh : ‖z/2‖ ≤ 1 := by rw [hn]; linarith [norm_nonneg z]
  have ht := Complex.norm_exp_sub_one_sub_id_le hh
  have he := norm_add_le (Complex.exp (z/2)-1-z/2) (z/2)
  rw [sub_add_cancel] at he
  rw [hn] at ht he
  linarith

theorem flow_difference (σ : ℝ) (hσ : |σ| ≤ 1/4) (z : ℂ) (hz : ‖z‖ ≤ 1/5) (x : Space) :
    ‖flow σ z x-x‖ ≤ (5/6:ℝ)*‖z‖*‖x‖ := by
  let d : ℝ := ‖z‖/2+(‖z‖/2)^2
  let c : Fin 5 → ℂ := ![Complex.exp (-z/2)-1,Complex.exp (-z/2)-1,
    Complex.exp (z/2)-1,Complex.exp (z/2)-1,0]
  let e : ℂ := 2*(σ:ℂ)*(Complex.exp (z/2)-1)*x 3
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hp := exp_half_bound z hz
  have hm := exp_half_bound (-z) (by simpa only [norm_neg] using hz)
  simp only [norm_neg] at hm
  have hc : ∀ i, ‖c i‖ ≤ d := by
    intro i
    fin_cases i <;> norm_num [c] <;> assumption
  have hs : flow σ z x-x = diagonal c x+(WithLp.toLp 2 (Pi.single (4:Fin 5) e) : Space) := by
    ext i
    fin_cases i <;> simp [flow,diagonal,c,e] <;> ring
  have he : ‖(WithLp.toLp 2 (Pi.single (4:Fin 5) e) : Space)‖ ≤ d/2*‖x‖ := by
    rw [PiLp.norm_toLp_single]
    have hx := PiLp.norm_apply_le x (3:Fin 5)
    have hn : ‖e‖=2*|σ| *‖Complex.exp (z/2)-1‖*‖x 3‖ := by
      dsimp [e]
      rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      norm_num
    rw [hn]
    calc
      2*|σ| *‖Complex.exp (z/2)-1‖*‖x 3‖ ≤ 2*(1/4)*d*‖x‖ := by
        gcongr
      _ = d/2*‖x‖ := by ring
  have hd' : 3/2*d ≤ (5/6:ℝ)*‖z‖ := by
    dsimp [d]
    nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hz)]
  rw [hs]
  calc
    ‖diagonal c x+(WithLp.toLp 2 (Pi.single (4:Fin 5) e) : Space)‖ ≤
        ‖diagonal c x‖+‖(WithLp.toLp 2 (Pi.single (4:Fin 5) e) : Space)‖ := norm_add_le _ _
    _ ≤ d*‖x‖+d/2*‖x‖ := add_le_add (diagonal_bound c x d hd hc) he
    _ = (3/2*d)*‖x‖ := by ring
    _ ≤ (5/6:ℝ)*‖z‖*‖x‖ := mul_le_mul_of_nonneg_right hd' (norm_nonneg _)

def rotatedFlow (U : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (z : ℂ) (x : Space) : Space :=
  U.symm (flow σ z (U x))

theorem rotated_difference (U : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (hσ : |σ| ≤ 1/4)
    (z : ℂ) (hz : ‖z‖ ≤ 1/5) (x : Space) :
    ‖rotatedFlow U σ z x-x‖ ≤ (5/6:ℝ)*‖z‖*‖x‖ := by
  have he : rotatedFlow U σ z x-x=U.symm (flow σ z (U x)-U x) := by
    rw [map_sub,U.symm_apply_apply]; rfl
  rw [he,U.symm.norm_map]
  simpa only [U.norm_map] using flow_difference σ hσ z hz (U x)

theorem rotated_norm (U : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (hσ : |σ| ≤ 1/4)
    (z : ℂ) (hz : ‖z‖ ≤ 1/5) (x : Space) :
    ‖rotatedFlow U σ z x‖ ≤ (1+(5/6:ℝ)*‖z‖)*‖x‖ := by
  have h' := norm_add_le (rotatedFlow U σ z x-x) x
  rw [sub_add_cancel] at h'
  nlinarith [rotated_difference U σ hσ z hz x]

theorem ordered_difference (U V : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (hσ : |σ| ≤ 1/4)
    (z t : ℂ) (hzt : ‖z‖+‖t‖ ≤ 1/5) (x : Space) :
    ‖rotatedFlow U σ z (rotatedFlow V σ t x)-x‖ ≤ (3/17:ℝ)*‖x‖ := by
  have hz : ‖z‖ ≤ 1/5 := by linarith [norm_nonneg t]
  have ht : ‖t‖ ≤ 1/5 := by linarith [norm_nonneg z]
  have ha := rotated_difference U σ hσ z hz (rotatedFlow V σ t x)
  have hb := rotated_difference V σ hσ t ht x
  have hc := rotated_norm V σ hσ t ht x
  have hd := norm_add_le
    (rotatedFlow U σ z (rotatedFlow V σ t x)-rotatedFlow V σ t x)
    (rotatedFlow V σ t x-x)
  rw [sub_add_sub_cancel] at hd
  have hm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (5/6:ℝ)*‖z‖)
  have hn : (5/6:ℝ)*‖z‖*(1+(5/6:ℝ)*‖t‖)+(5/6:ℝ)*‖t‖ ≤ 3/17 := by
    nlinarith [sq_nonneg (‖z‖-‖t‖),sq_le_sq₀ (by positivity : 0 ≤ ‖z‖+‖t‖) (by norm_num : (0:ℝ) ≤ 1/5) |>.mpr hzt]
  have hn' := mul_le_mul_of_nonneg_right hn (norm_nonneg x)
  nlinarith

theorem baseline_norm (U : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (hσ : |σ| ≤ 1/4)
    (z : ℂ) (hz : ‖z‖ ≤ 1/5) (x : Space) :
    ‖rotatedFlow U σ z x‖ ≤ (20/17:ℝ)*‖x‖ := by
  have h := rotated_norm U σ hσ z hz x
  nlinarith [mul_le_mul_of_nonneg_right hz (norm_nonneg x),norm_nonneg x]

#print axioms diagonal_bound
#print axioms exp_half_bound
#print axioms flow_difference
#print axioms rotated_difference
#print axioms rotated_norm
#print axioms ordered_difference
#print axioms baseline_norm
end
end UnifiedTheory.Audit.KFCausalComplexShearPerturbation
