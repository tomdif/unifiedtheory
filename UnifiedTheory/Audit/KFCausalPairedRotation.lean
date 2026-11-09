/- Simultaneous rotations of the two standing-wave planes. The coordinate
order is (two antisymmetric coordinates; clock, two symmetric coordinates,
neutral matter). These are genuine orthogonal, volume-preserving maps. -/
import UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPairedRotation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates

abbrev Space := Joint 2 4

def rotate (θ : ℝ) (x : Space) : Space := WithLp.toLp 2 fun
  | .inl i => ![Real.cos θ*x (.inl 0)-Real.sin θ*x (.inr 1),
    Real.cos θ*x (.inl 1)-Real.sin θ*x (.inr 2)] i
  | .inr i => ![x (.inr 0),Real.sin θ*x (.inl 0)+Real.cos θ*x (.inr 1),
    Real.sin θ*x (.inl 1)+Real.cos θ*x (.inr 2),x (.inr 3)] i

theorem rotate_zero (x : Space) : rotate 0 x = x := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [rotate]

theorem rotate_compose (θ φ : ℝ) (x : Space) :
    rotate θ (rotate φ x) = rotate (θ+φ) x := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [rotate, Real.sin_add, Real.cos_add] <;> ring

theorem rotate_reverse (θ : ℝ) (x : Space) : rotate (-θ) (rotate θ x) = x := by
  rw [rotate_compose, neg_add_cancel, rotate_zero]

theorem rotate_period (θ : ℝ) (x : Space) : rotate (θ+2*Real.pi) x = rotate θ x := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [rotate]

theorem pair_inner (θ a b c d : ℝ) :
    (Real.cos θ*a-Real.sin θ*b)*(Real.cos θ*c-Real.sin θ*d)+
    (Real.sin θ*a+Real.cos θ*b)*(Real.sin θ*c+Real.cos θ*d) = a*c+b*d := by
  calc
    _ = (Real.sin θ^2+Real.cos θ^2)*(a*c+b*d) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]

def rotationEquiv (θ : ℝ) : Space ≃ₗ[ℝ] Space where
  toFun := rotate θ
  invFun := rotate (-θ)
  left_inv := rotate_reverse θ
  right_inv x := by simpa only [neg_neg] using rotate_reverse (-θ) x
  map_add' x y := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [rotate] <;> ring
  map_smul' c x := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [rotate] <;> ring

theorem rotation_inner (θ : ℝ) (x y : Space) :
    inner ℝ (rotationEquiv θ x) (rotationEquiv θ y) = inner ℝ x y := by
  have h1 := pair_inner θ (x (.inl 0)) (x (.inr 1)) (y (.inl 0)) (y (.inr 1))
  have h2 := pair_inner θ (x (.inl 1)) (x (.inr 2)) (y (.inl 1)) (y (.inr 2))
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
  simp [rotationEquiv, rotate, RCLike.inner_apply]
  linear_combination h1+h2

def rotationIsometry (θ : ℝ) : Space ≃ₗᵢ[ℝ] Space where
  toLinearEquiv := rotationEquiv θ
  norm_map' := ((rotationEquiv θ).toLinearMap.isometryOfInner (rotation_inner θ)).norm_map

theorem rotation_preserves_volume (θ : ℝ) : MeasurePreserving (rotationIsometry θ) :=
  (rotationIsometry θ).measurePreserving

theorem rotate_clock (θ : ℝ) (x : Space) : rotate θ x (.inr 0) = x (.inr 0) := rfl
theorem rotate_neutral (θ : ℝ) (x : Space) : rotate θ x (.inr 3) = x (.inr 3) := rfl

theorem rotate_continuous : Continuous (fun p : ℝ × Space => rotate p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ⊕ Fin 4 => ℝ)).comp
  apply continuous_pi
  intro i
  rcases i with i | i <;> fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals fun_prop

#print axioms rotate_zero
#print axioms rotate_compose
#print axioms rotate_reverse
#print axioms rotate_period
#print axioms pair_inner
#print axioms rotation_inner
#print axioms rotationIsometry
#print axioms rotation_preserves_volume
#print axioms rotate_clock
#print axioms rotate_neutral
#print axioms rotate_continuous

end
end UnifiedTheory.Audit.KFCausalPairedRotation
