/- The autonomous scalar clock equation obtained from the conserved vacuum
Hamiltonian combination. Its vector field is globally Lipschitz at every
fixed positive floor, so it has a global integral curve for every datum. -/
import UnifiedTheory.Audit.KFCausalClockFloorClassicalBackreaction
import UnifiedTheory.Audit.KFCausalGlobalLipschitzODE

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorReducedODE
noncomputable section
open scoped NNReal
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock clock_above_floor)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)

/-- The conserved parameter is H-2*(exp(s)+epsilon*s). -/
def rate (ε J s : ℝ) : ℝ := 3/2+(J-2*ε+2*ε*s)/clock ε s

def slopeBound (ε J : ℝ) : ℝ := 2+|J-2*ε|/ε+2*ε*(1+1/ε^2)

theorem inverse_clock_bound (ε s : ℝ) (hε : 0 < ε) : 1/clock ε s ≤ 1/ε :=
  one_div_le_one_div_of_le hε (clock_above_floor ε s).le

theorem exponential_clock_bound (ε s : ℝ) (hε : 0 < ε) :
    0 ≤ Real.exp s/(clock ε s)^2 ∧ Real.exp s/(clock ε s)^2 ≤ 1/ε := by
  have hc := clock_positive ε s hε.le
  refine ⟨by positivity,?_⟩
  apply (div_le_div_iff₀ (sq_pos_of_pos hc) hε).mpr
  unfold clock
  nlinarith only [sq_nonneg (Real.exp s),sq_nonneg ε,mul_pos hε (Real.exp_pos s)]

theorem weighted_coordinate_bound (ε s : ℝ) (hε : 0 < ε) :
    |s| *Real.exp s/(clock ε s)^2 ≤ 1+1/ε^2 := by
  have hc := clock_positive ε s hε.le
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs]
    have hsexp : s ≤ Real.exp s := by linarith only [Real.add_one_le_exp s]
    have hnum : s*Real.exp s ≤ (clock ε s)^2 := by
      have h := mul_le_mul_of_nonneg_right hsexp (Real.exp_pos s).le
      unfold clock
      nlinarith only [h,sq_nonneg ε,mul_pos hε (Real.exp_pos s)]
    have hb : s*Real.exp s/(clock ε s)^2 ≤ 1 := (div_le_one (sq_pos_of_pos hc)).mpr hnum
    exact hb.trans (le_add_of_nonneg_right (by positivity))
  · rw [abs_of_neg (lt_of_not_ge hs)]
    have hn : -s ≤ Real.exp (-s) := by linarith only [Real.add_one_le_exp (-s)]
    have hb := mul_le_mul_of_nonneg_right hn (Real.exp_pos s).le
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero] at hb
    have hsq : ε^2 ≤ (clock ε s)^2 := (sq_le_sq₀ hε.le hc.le).mpr (clock_above_floor ε s).le
    calc
      _ ≤ 1/(clock ε s)^2 := div_le_div_of_nonneg_right hb (sq_nonneg _)
      _ ≤ 1/ε^2 := one_div_le_one_div_of_le (sq_pos_of_pos hε) hsq
      _ ≤ _ := le_add_of_nonneg_left zero_le_one

theorem rate_derivative (ε J s : ℝ) (hε : 0 < ε) :
    HasDerivAt (rate ε J)
      (2*ε/clock ε s-(J-2*ε)*(Real.exp s/(clock ε s)^2)-
        2*ε*(s*Real.exp s/(clock ε s)^2)) s := by
  have hc := (clock_positive ε s hε.le).ne'
  have hn := ((hasDerivAt_id s).const_mul (2*ε)).const_add (J-2*ε)
  have hd := (hn.div ((Real.hasDerivAt_exp s).add_const ε) hc).const_add (3/2)
  convert hd using 1
  change _ = (2*ε*1*clock ε s-(J-2*ε+2*ε*s)*Real.exp s)/(clock ε s)^2
  field_simp
  ring

theorem rate_contDiff (ε J : ℝ) (hε : 0 < ε) : ContDiff ℝ 1 (rate ε J) := by
  have hN : ContDiff ℝ 1 (fun s : ℝ => J-2*ε+2*ε*s) := by fun_prop
  exact contDiff_const.add (hN.div (Real.contDiff_exp.add contDiff_const)
    (fun s => (clock_positive ε s hε.le).ne'))

theorem slopeBound_nonnegative (ε J : ℝ) (hε : 0 < ε) : 0 ≤ slopeBound ε J := by
  unfold slopeBound
  positivity

theorem rate_derivative_bound (ε J s : ℝ) (hε : 0 < ε) :
    ‖deriv (rate ε J) s‖ ≤ slopeBound ε J := by
  have hc := clock_positive ε s hε.le
  have he := exponential_clock_bound ε s hε
  have h0 : |2*ε/clock ε s| ≤ 2 := by
    rw [abs_of_pos (by positivity : 0 < 2*ε/clock ε s)]
    apply (div_le_iff₀ hc).mpr
    linarith only [(clock_above_floor ε s).le]
  have h1 : |(J-2*ε)*(Real.exp s/(clock ε s)^2)| ≤ |J-2*ε|/ε := by
    rw [abs_mul,abs_of_nonneg he.1]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left he.2 (abs_nonneg (J-2*ε))
  have h2 : |2*ε*(s*Real.exp s/(clock ε s)^2)| ≤ 2*ε*(1+1/ε^2) := by
    rw [abs_mul,abs_of_pos (by positivity : 0 < 2*ε),abs_div,abs_mul,
      abs_of_pos (Real.exp_pos s),abs_of_nonneg (sq_nonneg (clock ε s))]
    exact mul_le_mul_of_nonneg_left (weighted_coordinate_bound ε s hε) (by positivity)
  rw [(rate_derivative ε J s hε).deriv,Real.norm_eq_abs]
  exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
    (add_le_add (add_le_add h0 h1) h2)

def lipschitzConstant (ε J : ℝ) (hε : 0 < ε) : ℝ≥0 := ⟨slopeBound ε J,slopeBound_nonnegative ε J hε⟩

theorem rate_lipschitz (ε J : ℝ) (hε : 0 < ε) : LipschitzWith (lipschitzConstant ε J hε) (rate ε J) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun s => (rate_derivative ε J s hε).differentiableAt)
  intro s
  exact rate_derivative_bound ε J s hε

theorem exists_global_clock (ε J s₀ : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ → ℝ, s 0 = s₀ ∧ ∀ t, HasDerivAt s (rate ε J (s t)) t :=
  KFCausalGlobalLipschitzODE.exists_global (rate ε J) (rate_contDiff ε J hε)
    (lipschitzConstant ε J hε) (rate_lipschitz ε J hε) s₀

#print axioms inverse_clock_bound
#print axioms exponential_clock_bound
#print axioms weighted_coordinate_bound
#print axioms rate_derivative
#print axioms rate_contDiff
#print axioms slopeBound_nonnegative
#print axioms rate_derivative_bound
#print axioms rate_lipschitz
#print axioms exists_global_clock

end
end UnifiedTheory.Audit.KFCausalClockFloorReducedODE
