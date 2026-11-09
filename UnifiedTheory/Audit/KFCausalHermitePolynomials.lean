/- Pure polynomial Hermite definitions, shared by the physical packet
domains and the analytic completeness development. Declaration names and
normalizations agree with the existing neutral packet family. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalNeutralHermiteDomain
noncomputable section
/-- Physicists' convention: H₀=1, H₁=2X, Hₙ₊₂=2X Hₙ₊₁−2(n+1) Hₙ. -/
def physicistsHermite : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => Polynomial.C 2*Polynomial.X
  | n+2 => Polynomial.C 2*Polynomial.X*physicistsHermite (n+1)-
      Polynomial.C (2*((n+1:ℕ):ℂ))*physicistsHermite n

theorem physicistsHermite_zero : physicistsHermite 0 = 1 := rfl
theorem physicistsHermite_one : physicistsHermite 1 = Polynomial.C 2*Polynomial.X := rfl
theorem physicistsHermite_recurrence (n : ℕ) :
    physicistsHermite (n+2) = Polynomial.C 2*Polynomial.X*physicistsHermite (n+1)-
      Polynomial.C (2*((n+1:ℕ):ℂ))*physicistsHermite n := rfl

def multiplier (w B : ℝ) (n : ℕ) : Polynomial ℂ :=
  Polynomial.C ((Real.sqrt ((2:ℝ)^n*n.factorial):ℂ)⁻¹)*
    (physicistsHermite n).comp
      (Polynomial.C (Real.sqrt (2*w):ℂ)*(Polynomial.X-Polynomial.C (B:ℂ)))

theorem multiplier_eval (w B : ℝ) (n : ℕ) (x : ℂ) :
    (multiplier w B n).eval x =
      (physicistsHermite n).eval ((Real.sqrt (2*w):ℂ)*(x-(B:ℂ)))/
        (Real.sqrt ((2:ℝ)^n*n.factorial):ℂ) := by
  simp only [multiplier,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_comp,
    Polynomial.eval_sub,Polynomial.eval_X,div_eq_mul_inv]
  ring

end
end UnifiedTheory.Audit.KFCausalNeutralHermiteDomain
