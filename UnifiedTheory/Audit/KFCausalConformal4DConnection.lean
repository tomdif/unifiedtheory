import UnifiedTheory.Audit.KFCausalConformal4DDiamondBenchmark

/-!
Coordinate Levi-Civita curvature of the actual conformal metric.  We use
R^a_{bcd}=∂c Γ^a_{db}−∂d Γ^a_{cb}+Γ^a_{ce}Γ^e_{db}−Γ^a_{de}Γ^e_{cb}.
At the origin Γ=0. Lowering with η agrees exactly with the repository's
MetricConstruction.R_metric convention. This is a coordinate calculation;
no causal-domain identification or curved BDG limit is asserted.
-/

namespace UnifiedTheory.Audit.KFCausalConformal4DConnection

noncomputable section

open scoped BigOperators
open UnifiedTheory.LayerA.MetricConstruction
open KFCausalConformal4DDiamondBenchmark

def inverseMetric (att spatial : ℝ) (p : Point) (a b : Fin 4) : ℝ :=
  (omega att spatial p ^ 2)⁻¹ * eta a b

def christoffel (att spatial : ℝ) (p : Point) (a b d : Fin 4) : ℝ :=
  (∑ k, inverseMetric att spatial p a k *
    (metricFirst att spatial p b k d + metricFirst att spatial p d k b -
      metricFirst att spatial p k b d)) / 2

def numerator (att spatial : ℝ) (p : Point) (a b d : Fin 4) : ℝ :=
  (if a = b then coefficient att spatial d * p d else 0) +
  (if a = d then coefficient att spatial b * p b else 0) -
  eta b d * sign a * coefficient att spatial a * p a

def connectionPartial (att spatial : ℝ) (e a b d : Fin 4) : ℝ :=
  (if a = b then coefficient att spatial d * (if d = e then 1 else 0) else 0) +
  (if a = d then coefficient att spatial b * (if b = e then 1 else 0) else 0) -
  eta b d * sign a * coefficient att spatial a * (if a = e then 1 else 0)

theorem inverse_metric (att spatial : ℝ) (p : Point) (h : omega att spatial p ≠ 0)
    (a b : Fin 4) :
    (∑ k, metric att spatial p a k * inverseMetric att spatial p k b) =
      if a = b then 1 else 0 := by
  have h2 : (⟨2, by decide⟩ : Fin 4) = 2 := rfl
  have h3 : (⟨3, by decide⟩ : Fin 4) = 3 := rfl
  fin_cases a <;> fin_cases b <;> simp only [h2, h3] <;>
    simp +decide only [metric, inverseMetric, eta, sign, Fin.sum_univ_four,
      ite_true, ite_false] <;> norm_num <;> field_simp

theorem christoffel_formula (att spatial : ℝ) (p : Point) (a b d : Fin 4) :
    christoffel att spatial p a b d = numerator att spatial p a b d / omega att spatial p := by
  by_cases h : omega att spatial p = 0
  · simp [christoffel, inverseMetric, metricFirst, h]
  · have h2 : (⟨2, by decide⟩ : Fin 4) = 2 := rfl
    have h3 : (⟨3, by decide⟩ : Fin 4) = 3 := rfl
    fin_cases a <;> fin_cases b <;> fin_cases d <;> simp only [h2, h3] <;>
      simp +decide only [christoffel, inverseMetric, metricFirst, numerator, eta, sign,
        Fin.sum_univ_four, ite_true, ite_false] <;> norm_num <;> field_simp

theorem christoffel_origin (att spatial : ℝ) (a b d : Fin 4) :
    christoffel att spatial 0 a b d = 0 := by
  rw [christoffel_formula]
  simp [numerator]

private theorem coordinate_derivative (e i : Fin 4) :
    HasDerivAt (fun t : ℝ => (shift 0 e t) i) (if i = e then 1 else 0) 0 := by
  by_cases h : i = e
  · simpa [shift, h] using hasDerivAt_id (0 : ℝ)
  · simpa [shift, h] using hasDerivAt_const (0 : ℝ) (0 : ℝ)

theorem christoffel_derivative (att spatial : ℝ) (e a b d : Fin 4) :
    HasDerivAt (fun t => christoffel att spatial (shift 0 e t) a b d)
      (connectionPartial att spatial e a b d) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => if a = b then
      coefficient att spatial d * (shift 0 e t) d else 0)
      (if a = b then coefficient att spatial d * (if d = e then 1 else 0) else 0) 0 := by
    by_cases h : a = b
    · simpa [h] using (coordinate_derivative e d).const_mul (coefficient att spatial d)
    · simpa [h] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => if a = d then
      coefficient att spatial b * (shift 0 e t) b else 0)
      (if a = d then coefficient att spatial b * (if b = e then 1 else 0) else 0) 0 := by
    by_cases h : a = d
    · simpa [h] using (coordinate_derivative e b).const_mul (coefficient att spatial b)
    · simpa [h] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have hn := (h1.add h2).sub ((coordinate_derivative e a).const_mul
    (eta b d * sign a * coefficient att spatial a))
  have hd := hn.div (omega_line_derivative att spatial 0 e 0)
    (by norm_num [omega, shift] : omega att spatial (shift 0 e 0) ≠ 0)
  simp only [christoffel_formula]
  convert hd using 1
  simp [connectionPartial, omega, shift]

noncomputable def connectionRiemann (att spatial : ℝ) (a b c d : Fin 4) : ℝ :=
  sign a * (connectionPartial att spatial c a d b - connectionPartial att spatial d a c b +
    ∑ e, (christoffel att spatial 0 a c e * christoffel att spatial 0 e d b -
      christoffel att spatial 0 a d e * christoffel att spatial 0 e c b))

theorem connection_riemann_eq (att spatial : ℝ) (a b c d : Fin 4) :
    connectionRiemann att spatial a b c d =
      R_metric (derivativeData att spatial) a b c d := by
  simp only [connectionRiemann, christoffel_origin, mul_zero, sub_self, Finset.sum_const_zero,
    add_zero]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp +decide only [connectionPartial, R_metric, derivativeData, metricSecond, eta, sign,
      coefficient, ite_true, ite_false] <;> ring

theorem actual_curvature_eq (att spatial : ℝ) (a b c d : Fin 4) :
    sign a * (deriv (fun t => christoffel att spatial (shift 0 c t) a d b) 0 -
      deriv (fun t => christoffel att spatial (shift 0 d t) a c b) 0 +
      ∑ e, (christoffel att spatial 0 a c e * christoffel att spatial 0 e d b -
        christoffel att spatial 0 a d e * christoffel att spatial 0 e c b)) =
        R_metric (derivativeData att spatial) a b c d := by
  rw [(christoffel_derivative att spatial c a d b).deriv,
    (christoffel_derivative att spatial d a c b).deriv]
  exact connection_riemann_eq att spatial a b c d

theorem connection_ricci_time (att spatial : ℝ) :
    (∑ a, sign a * connectionRiemann att spatial a 0 a 0) = -3 * att + 3 * spatial := by
  simp_rw [connection_riemann_eq]
  exact ricci_time att spatial

theorem connection_scalar (att spatial : ℝ) :
    (∑ b, sign b * ∑ a, sign a * connectionRiemann att spatial a b a b) =
      6 * att - 18 * spatial := by
  simp_rw [connection_riemann_eq]
  exact scalar_curvature att spatial

#print axioms inverse_metric
#print axioms christoffel_formula
#print axioms christoffel_origin
#print axioms christoffel_derivative
#print axioms connection_riemann_eq
#print axioms actual_curvature_eq
#print axioms connection_ricci_time
#print axioms connection_scalar

end

end UnifiedTheory.Audit.KFCausalConformal4DConnection
