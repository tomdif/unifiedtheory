/- A positive polynomial weight controls the physical coordinates and
their quadratic products. Its square is bounded by pure fourth moments,
which will provide the L2 majorant for the second shear differential. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalShearRadius
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)

def radius (q : Transverse) : ℝ := 1+∑ i, (q i)^2
def fourth (q : Transverse) : ℝ := 1+∑ i, (q i)^4

theorem radius_one_le (q : Transverse) : 1 ≤ radius q := by
  have hs : 0 ≤ ∑ i : Fin 5, (q i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (q i))
  unfold radius
  linarith

theorem radius_positive (q : Transverse) : 0 < radius q := lt_of_lt_of_le zero_lt_one (radius_one_le q)

theorem coordinate_square_le (q : Transverse) (i : Fin 5) : (q i)^2 ≤ radius q := by
  have hs := Finset.single_le_sum (f := fun j : Fin 5 => (q j)^2)
    (fun j _ => sq_nonneg (q j)) (Finset.mem_univ i)
  unfold radius
  linarith

theorem coordinate_abs_le (q : Transverse) (i : Fin 5) : |q i| ≤ radius q := by
  have hs := Finset.single_le_sum (f := fun j : Fin 5 => (q j)^2)
    (fun j _ => sq_nonneg (q j)) (Finset.mem_univ i)
  have ha := sq_nonneg (|q i|-1)
  unfold radius
  nlinarith [sq_abs (q i)]

theorem coordinate_product_le (q : Transverse) (i j : Fin 5) : |q i*q j| ≤ radius q := by
  have hi := coordinate_square_le q i
  have hj := coordinate_square_le q j
  have hs := sq_nonneg (|q i|-|q j|)
  rw [abs_mul]
  nlinarith [sq_abs (q i),sq_abs (q j)]

theorem mix_abs_le (q : Transverse) : |q 2+q 3| ≤ 2*radius q := by
  have ha := abs_add_le (q 2) (q 3)
  linarith [coordinate_abs_le q 2,coordinate_abs_le q 3]

theorem mix_square_le (q : Transverse) : (q 2+q 3)^2 ≤ 4*radius q := by
  nlinarith [sq_nonneg (q 2-q 3),coordinate_square_le q 2,coordinate_square_le q 3]

theorem neutral_mix_le (q : Transverse) : |q 4*(q 2+q 3)| ≤ 2*radius q := by
  have ha := abs_add_le (q 4*q 2) (q 4*q 3)
  rw [mul_add]
  linarith [coordinate_product_le q 4 2,coordinate_product_le q 4 3]

theorem radius_square_le_fourth (q : Transverse) : (radius q)^2 ≤ 10*fourth q := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin 5 => (1:ℝ)) (fun i => (q i)^2)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,← pow_mul] at hc
  norm_num only [Nat.reduceMul] at hc
  have hs := sq_nonneg ((∑ i : Fin 5, (q i)^2)-1)
  have hq : 0 ≤ ∑ i : Fin 5, (q i)^4 := Finset.sum_nonneg (fun i _ => by positivity)
  unfold radius fourth
  nlinarith

#print axioms radius_one_le
#print axioms radius_positive
#print axioms coordinate_square_le
#print axioms coordinate_abs_le
#print axioms coordinate_product_le
#print axioms mix_abs_le
#print axioms mix_square_le
#print axioms neutral_mix_le
#print axioms radius_square_le_fourth
end
end UnifiedTheory.Audit.KFCausalShearRadius
