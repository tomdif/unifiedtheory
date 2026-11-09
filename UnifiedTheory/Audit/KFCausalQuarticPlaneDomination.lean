/- A degree-independent upper derivative bound in fixed complex-neutral
coordinates. The negative quadratic Gaussian derivative absorbs the
quartic field shear. No polynomial derivative or degree constant occurs.
The geometric hypotheses are explicit, not claimed for an unevaluated
projected source family. -/
import UnifiedTheory.Audit.KFCausalWeightedPolynomialLocalResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalQuarticPlaneDomination
noncomputable section

def potential (x : ℝ) : ℝ := 1+x^2/2+x^4/4
def potentialSlope (x : ℝ) : ℝ := x+x^3

theorem potential_positive (x : ℝ) : 0 < potential x := by unfold potential; positivity

theorem potential_derivative (x : ℝ) : HasDerivAt potential (potentialSlope x) x := by
  convert (((hasDerivAt_id x).pow 2).div_const 2).const_add 1 |>.add
    (((hasDerivAt_id x).pow 4).div_const 4) using 1
  dsimp [potential,potentialSlope]
  ring

theorem potentialSlope_bound (x : ℝ) : |potentialSlope x| ≤ 2*potential x := by
  have h1 : |x| ≤ (1+x^2)/2 := by nlinarith [sq_nonneg (|x|-1),sq_abs x]
  have h3 : |x|^3 ≤ (x^2+x^4)/2 := by
    have hs := sq_nonneg (x^2-|x|)
    nlinarith [sq_abs x]
  unfold potentialSlope potential
  apply (abs_add_le _ _).trans
  rw [abs_pow]
  linarith

theorem quadratic_absorption (v l y : ℝ) (hv : 0 < v) :
    -v*y^2+2*|l| * |y| ≤ l^2/v := by
  apply (le_div_iff₀ hv).mpr
  have hs := sq_nonneg (v*|y| - |l|)
  rw [sub_sq,mul_pow,sq_abs,sq_abs] at hs
  nlinarith

theorem score_bound (J v L l x y : ℝ) (hv : 0 < v) :
    (J-v*y^2)*potential (x+L*y)+l*y*potentialSlope (x+L*y) ≤
      (J+l^2/v)*potential (x+L*y) := by
  have hp := (potential_positive (x+L*y)).le
  have hs : l*y*potentialSlope (x+L*y) ≤ 2*|l| * |y| * potential (x+L*y) := by
    calc
      _ ≤ |l*y*potentialSlope (x+L*y)| := le_abs_self _
      _ = |l| * |y| * |potentialSlope (x+L*y)| := by rw [abs_mul,abs_mul]
      _ ≤ _ := (mul_le_mul_of_nonneg_left (potentialSlope_bound (x+L*y))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq (by ring)
  have ha := mul_le_mul_of_nonneg_right (quadratic_absorption v l y hv) hp
  nlinarith

def density (D β lam L : ℝ) (P : Polynomial ℂ) (x y : ℝ) : ℝ :=
  D*Real.exp (-2*β*x^2-lam*y^2)*potential (x+L*y)*‖P.eval ((x:ℂ)+(y:ℂ)*Complex.I)‖^2

def derivativeDensity (D D' β lam lam' L L' : ℝ) (P : Polynomial ℂ) (x y : ℝ) : ℝ :=
  Real.exp (-2*β*x^2-lam*y^2)*‖P.eval ((x:ℂ)+(y:ℂ)*Complex.I)‖^2*
    ((D'-D*lam'*y^2)*potential (x+L*y)+D*L'*y*potentialSlope (x+L*y))

theorem density_nonnegative (D β lam L : ℝ) (hD : 0 ≤ D) (P : Polynomial ℂ) (x y : ℝ) :
    0 ≤ density D β lam L P x y := by
  unfold density
  exact mul_nonneg (mul_nonneg (mul_nonneg hD (Real.exp_pos _).le)
    (potential_positive _).le) (sq_nonneg _)

theorem density_derivative (D lam L : ℝ → ℝ) (D' lam' L' β s : ℝ)
    (hD : HasDerivAt D D' s) (hlam : HasDerivAt lam lam' s) (hL : HasDerivAt L L' s)
    (P : Polynomial ℂ) (x y : ℝ) :
    HasDerivAt (fun t => density (D t) β (lam t) (L t) P x y)
      (derivativeDensity (D s) D' β (lam s) lam' (L s) L' P x y) s := by
  have he := ((hlam.mul_const (y^2)).const_sub (-2*β*x^2)).exp
  have hp := (potential_derivative (x+L s*y)).comp s ((hL.mul_const y).const_add x)
  convert ((hD.mul he).mul hp).mul_const (‖P.eval ((x:ℂ)+(y:ℂ)*Complex.I)‖^2) using 1
  dsimp [derivativeDensity]
  ring

theorem derivativeDensity_bound (D D' β lam lam' L L' : ℝ) (hD : 0 < D) (hlam' : 0 < lam')
    (P : Polynomial ℂ) (x y : ℝ) :
    derivativeDensity D D' β lam lam' L L' P x y ≤
      (D'/D+L'^2/lam')*density D β lam L P x y := by
  have hs := mul_le_mul_of_nonneg_left (score_bound (D'/D) lam' L L' x y hlam') hD.le
  have he : D*((D'/D-lam'*y^2)*potential (x+L*y)+L'*y*potentialSlope (x+L*y)) =
      (D'-D*lam'*y^2)*potential (x+L*y)+D*L'*y*potentialSlope (x+L*y) := by
    field_simp
  rw [he] at hs
  have ht := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (Real.exp_pos (-2*β*x^2-lam*y^2)).le
      (sq_nonneg ‖P.eval ((x:ℂ)+(y:ℂ)*Complex.I)‖))
  convert ht using 1
  unfold density
  ring

#print axioms potential_positive
#print axioms potential_derivative
#print axioms potentialSlope_bound
#print axioms quadratic_absorption
#print axioms score_bound
#print axioms density_nonnegative
#print axioms density_derivative
#print axioms derivativeDensity_bound
end
end UnifiedTheory.Audit.KFCausalQuarticPlaneDomination
