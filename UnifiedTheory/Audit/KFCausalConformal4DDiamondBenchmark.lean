import Mathlib
import UnifiedTheory.LayerA.MetricToRiemann
import UnifiedTheory.Audit.KFCausalCSpecRSSConformal

/-!
Actual metric attachment for the previously proved conformal coordinate-region
integral.  The metric is Ω² diag(-1,1,1,1). Its first and second coordinate
derivatives, volume density, and Lorentzian curvature contractions are computed
here. No causal-diamond/geodesic identification or curved BDG limit is asserted.
-/

namespace UnifiedTheory.Audit.KFCausalConformal4DDiamondBenchmark

noncomputable section

open scoped BigOperators
open UnifiedTheory.LayerA.MetricConstruction

abbrev Point := Fin 4 → ℝ

def coefficient (att spatial : ℝ) (i : Fin 4) : ℝ := if i = 0 then att else spatial

def sign (i : Fin 4) : ℝ := if i = 0 then -1 else 1

def eta (a b : Fin 4) : ℝ := if a = b then sign a else 0

def omega (att spatial : ℝ) (p : Point) : ℝ :=
  1 + att * p 0 ^ 2 / 2 + spatial * (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) / 2

def shift (p : Point) (e : Fin 4) (t : ℝ) : Point :=
  fun i => p i + if i = e then t else 0

def metric (att spatial : ℝ) (p : Point) (a b : Fin 4) : ℝ :=
  omega att spatial p ^ 2 * eta a b

def metricFirst (att spatial : ℝ) (p : Point) (e a b : Fin 4) : ℝ :=
  2 * omega att spatial p * coefficient att spatial e * p e * eta a b

def metricSecond (att spatial : ℝ) (e f a b : Fin 4) : ℝ :=
  2 * (if e = f then coefficient att spatial e else 0) * eta a b

theorem omega_line (att spatial : ℝ) (p : Point) (e : Fin 4) (t : ℝ) :
    omega att spatial (shift p e t) = omega att spatial p +
      coefficient att spatial e * p e * t + coefficient att spatial e * t ^ 2 / 2 := by
  have h2 : (⟨2, by decide⟩ : Fin 4) = 2 := rfl
  have h3 : (⟨3, by decide⟩ : Fin 4) = 3 := rfl
  fin_cases e <;> simp only [h2, h3] <;>
    norm_num [omega, shift, coefficient, Fin.ext_iff] <;> ring

theorem omega_line_derivative (att spatial : ℝ) (p : Point) (e : Fin 4) (t : ℝ) :
    HasDerivAt (fun q => omega att spatial (shift p e q))
      (coefficient att spatial e * (p e + t)) t := by
  simp_rw [omega_line]
  convert ((hasDerivAt_const t (omega att spatial p)).add
    ((hasDerivAt_id t).const_mul (coefficient att spatial e * p e))).add
    (((hasDerivAt_id t).pow 2).const_mul (coefficient att spatial e / 2)) using 1
  · funext q; simp; ring
  · simp; ring

theorem metric_first_derivative (att spatial : ℝ) (p : Point) (e a b : Fin 4) :
    HasDerivAt (fun t => metric att spatial (shift p e t) a b)
      (metricFirst att spatial p e a b) 0 := by
  convert ((omega_line_derivative att spatial p e 0).pow 2).mul_const (eta a b) using 1
  have hs : shift p e 0 = p := by funext i; simp [shift]
  simp only [hs, metricFirst, Nat.cast_ofNat, Nat.reduceSub, pow_one, add_zero]
  ring

theorem metric_second_derivative (att spatial : ℝ) (e f a b : Fin 4) :
    HasDerivAt (fun t => metricFirst att spatial (shift 0 e t) f a b)
      (metricSecond att spatial e f a b) 0 := by
  have hc : HasDerivAt (fun t : ℝ => (shift 0 e t) f)
      (if f = e then 1 else 0) 0 := by
    by_cases h : f = e <;> simp only [shift, Pi.zero_apply, zero_add, h, if_true, if_false]
    · exact hasDerivAt_id 0
    · exact hasDerivAt_const 0 0
  convert ((((omega_line_derivative att spatial 0 e 0).const_mul 2).mul_const
    (coefficient att spatial f)).mul hc).mul_const (eta a b) using 1
  by_cases h : e = f
  · subst f
    simp [metricSecond, omega, shift]
  · simp [metricSecond, omega, shift, h, Ne.symm h]

theorem normal_coordinate_first_zero (att spatial : ℝ) (e a b : Fin 4) :
    metricFirst att spatial 0 e a b = 0 := by simp [metricFirst]

def derivativeData (att spatial : ℝ) : MetricDerivs 4 where
  h := metricSecond att spatial
  h_metric := by
    intro e f a b
    by_cases h : a = b
    · subst b; rfl
    · simp [metricSecond, eta, h, Ne.symm h]
  h_comm := by
    intro e f a b
    by_cases h : e = f
    · subst f; rfl
    · simp [metricSecond, h, Ne.symm h]
  k := fun _ _ _ _ _ => 0
  k_metric := by intros; rfl
  k_sym12 := by intros; rfl
  k_sym23 := by intros; rfl

noncomputable def ricci (att spatial : ℝ) (b d : Fin 4) : ℝ :=
  ∑ a, sign a * R_metric (derivativeData att spatial) a b a d

noncomputable def scalar (att spatial : ℝ) : ℝ :=
  ∑ b, sign b * ricci att spatial b b

theorem ricci_time (att spatial : ℝ) : ricci att spatial 0 0 = -3 * att + 3 * spatial := by
  simp +decide only [ricci, R_metric, derivativeData, metricSecond, eta, sign, coefficient,
    Fin.sum_univ_four, ite_true, ite_false]
  ring

theorem ricci_spatial (att spatial : ℝ) (i : Fin 4) (hi : i ≠ 0) :
    ricci att spatial i i = att - 5 * spatial := by
  fin_cases i <;> simp +decide only [ricci, R_metric, derivativeData, metricSecond, eta, sign,
    coefficient, Fin.sum_univ_four, ite_true, ite_false] at * <;> ring

theorem scalar_curvature (att spatial : ℝ) : scalar att spatial = 6 * att - 18 * spatial := by
  simp +decide only [scalar, ricci, R_metric, derivativeData, metricSecond, eta, sign,
    coefficient, Fin.sum_univ_four, ite_true, ite_false]
  ring

theorem metric_determinant (att spatial : ℝ) (p : Point) :
    Matrix.det (metric att spatial p) = -(omega att spatial p)^8 := by
  have hm : metric att spatial p = Matrix.diagonal
      (fun i => omega att spatial p ^ 2 * sign i) := by
    ext i j
    by_cases h : i = j <;> simp [metric, eta, Matrix.diagonal, h]
  rw [hm, Matrix.det_diagonal]
  norm_num [Fin.prod_univ_succ, sign]
  ring

theorem metric_volume_density (att spatial : ℝ) (p : Point) :
    Real.sqrt |Matrix.det (metric att spatial p)| = omega att spatial p ^ 4 := by
  rw [metric_determinant, abs_neg, abs_of_nonneg (by positivity)]
  rw [show omega att spatial p ^ 8 = (omega att spatial p ^ 4)^2 by ring]
  exact Real.sqrt_sq (by positivity)

theorem metric_causal_sign (att spatial : ℝ) (p v : Point)
    (h : 0 < omega att spatial p) :
    (∑ a, ∑ b, metric att spatial p a b * v a * v b) ≤ 0 ↔
      (∑ a, ∑ b, eta a b * v a * v b) ≤ 0 := by
  have he : (∑ a, ∑ b, metric att spatial p a b * v a * v b) =
      omega att spatial p ^ 2 * (∑ a, ∑ b, eta a b * v a * v b) := by
    simp only [Finset.mul_sum, metric]
    congr 1
    ext a
    congr 1
    ext b
    ring
  rw [he]
  simpa using (mul_le_mul_iff_right₀ (sq_pos_of_pos h) :
    omega att spatial p ^ 2 * (∑ a, ∑ b, eta a b * v a * v b) ≤
      omega att spatial p ^ 2 * 0 ↔ (∑ a, ∑ b, eta a b * v a * v b) ≤ 0)

theorem geometric_volume_coefficient (att spatial : ℝ) :
    (3 * spatial - 2 * att) / 15 = -scalar att spatial / 180 + ricci att spatial 0 0 / 30 := by
  rw [scalar_curvature, ricci_time]
  ring

#print axioms omega_line
#print axioms omega_line_derivative
#print axioms metric_first_derivative
#print axioms metric_second_derivative
#print axioms normal_coordinate_first_zero
#print axioms ricci_time
#print axioms ricci_spatial
#print axioms scalar_curvature
#print axioms metric_determinant
#print axioms metric_volume_density
#print axioms metric_causal_sign
#print axioms geometric_volume_coefficient

end

end UnifiedTheory.Audit.KFCausalConformal4DDiamondBenchmark
