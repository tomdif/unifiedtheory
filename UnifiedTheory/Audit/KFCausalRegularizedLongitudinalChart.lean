/- A candidate domain repair for longitudinal translations. The mobility
1/(c+epsilon) yields q= c+epsilon*log(c), a complete real coordinate for
every epsilon>0. This is a change of the longitudinal model and is not
yet a constructed quantum Hamiltonian or a proved regulator limit. -/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
noncomputable section
open Filter Set
open scoped Topology

def chart (ε s : ℝ) : ℝ := Real.exp s+ε*s

theorem chart_derivative (ε s : ℝ) : HasDerivAt (chart ε) (Real.exp s+ε) s := by
  simpa [chart] using (Real.hasDerivAt_exp s).add ((hasDerivAt_id s).const_mul ε)

theorem chart_continuous (ε : ℝ) : Continuous (chart ε) := by
  exact continuous_iff_continuousAt.mpr (fun s => (chart_derivative ε s).continuousAt)

theorem chart_strictMono (ε : ℝ) (hε : 0 < ε) : StrictMono (chart ε) := by
  intro a b hab
  have he := Real.exp_lt_exp.mpr hab
  dsimp [chart]
  nlinarith

theorem chart_atTop (ε : ℝ) (hε : 0 < ε) : Tendsto (chart ε) atTop atTop := by
  apply tendsto_atTop_mono (fun s => show ε*s ≤ chart ε s by dsimp [chart]; linarith [Real.exp_pos s])
  exact tendsto_id.const_mul_atTop hε

theorem chart_atBot (ε : ℝ) (hε : 0 < ε) : Tendsto (chart ε) atBot atBot := by
  exact Real.tendsto_exp_atBot.add_atBot (tendsto_id.const_mul_atBot hε)

theorem chart_surjective (ε : ℝ) (hε : 0 < ε) : Function.Surjective (chart ε) :=
  (chart_continuous ε).surjective (chart_atTop ε hε) (chart_atBot ε hε)

def chartIso (ε : ℝ) (hε : 0 < ε) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (chart ε) (chart_strictMono ε hε) (chart_surjective ε hε)

theorem chartIso_apply (ε : ℝ) (hε : 0 < ε) (s : ℝ) : chartIso ε hε s=chart ε s := rfl

def logFlow (ε : ℝ) (hε : 0 < ε) (s₀ t : ℝ) : ℝ :=
  (chartIso ε hε).symm (chart ε s₀+t)
def clockFlow (ε : ℝ) (hε : 0 < ε) (s₀ t : ℝ) : ℝ := Real.exp (logFlow ε hε s₀ t)

theorem chart_logFlow (ε : ℝ) (hε : 0 < ε) (s₀ t : ℝ) :
    chart ε (logFlow ε hε s₀ t)=chart ε s₀+t :=
  (chartIso ε hε).apply_symm_apply _

theorem logFlow_initial (ε : ℝ) (hε : 0 < ε) (s₀ : ℝ) : logFlow ε hε s₀ 0=s₀ := by
  simp only [logFlow,add_zero,← chartIso_apply ε hε,(chartIso ε hε).symm_apply_apply]

theorem logFlow_comp (ε : ℝ) (hε : 0 < ε) (s₀ t u : ℝ) :
    logFlow ε hε (logFlow ε hε s₀ t) u=logFlow ε hε s₀ (t+u) := by
  unfold logFlow
  rw [show chart ε ((chartIso ε hε).symm (chart ε s₀+t))=chart ε s₀+t
    from (chartIso ε hε).apply_symm_apply _]
  rw [add_assoc]

theorem chartInverse_derivative (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    HasDerivAt (chartIso ε hε).symm
      (Real.exp ((chartIso ε hε).symm q)+ε)⁻¹ q := by
  apply (chart_derivative ε ((chartIso ε hε).symm q)).of_local_left_inverse
    (chartIso ε hε).symm.toHomeomorph.continuous.continuousAt
    (by positivity : Real.exp ((chartIso ε hε).symm q)+ε ≠ 0)
  exact Filter.Eventually.of_forall (fun y => (chartIso ε hε).apply_symm_apply y)

theorem logFlow_derivative (ε : ℝ) (hε : 0 < ε) (s₀ t : ℝ) :
    HasDerivAt (logFlow ε hε s₀) (1/(clockFlow ε hε s₀ t+ε)) t := by
  have h := (chartInverse_derivative ε hε (chart ε s₀+t)).comp t
    ((hasDerivAt_id t).const_add (chart ε s₀))
  simpa [logFlow,clockFlow,one_div] using h

theorem clockFlow_positive (ε : ℝ) (hε : 0 < ε) (s₀ t : ℝ) : 0 < clockFlow ε hε s₀ t :=
  Real.exp_pos _

/-- Complete flow for the regularized canonical generator. At epsilon=0
the formal c velocity is one and the positive chart is incomplete. -/
theorem clockFlow_derivative (ε : ℝ) (hε : 0 < ε) (s₀ t : ℝ) :
    HasDerivAt (clockFlow ε hε s₀)
      (clockFlow ε hε s₀ t/(clockFlow ε hε s₀ t+ε)) t := by
  simpa [clockFlow,div_eq_mul_inv] using (logFlow_derivative ε hε s₀ t).exp

theorem clockFlow_initial (ε : ℝ) (hε : 0 < ε) (s₀ : ℝ) :
    clockFlow ε hε s₀ 0=Real.exp s₀ := by rw [clockFlow,logFlow_initial]

/-- The candidate changes the canonical clock speed by at most epsilon/a
on any region c>=a>0. This is not a uniform estimate near c=0. -/
theorem clock_speed_error (ε a c : ℝ) (hε : 0 ≤ ε) (ha : 0 < a) (hc : a ≤ c) :
    |c/(c+ε)-1| ≤ ε/a := by
  have hc0 : 0 < c := ha.trans_le hc
  have hd : 0 < c+ε := by positivity
  have he : c/(c+ε)-1= -(ε/(c+ε)) := by field_simp; ring
  rw [he,abs_neg,abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left hε ha (by linarith)

theorem inverse_mobility_error (ε a c : ℝ) (hε : 0 ≤ ε) (ha : 0 < a) (hc : a ≤ c) :
    |1/(c+ε)-1/c| ≤ ε/a^2 := by
  have hc0 : 0 < c := ha.trans_le hc
  have hd : 0 < c+ε := by positivity
  have he : 1/(c+ε)-1/c= -(ε/(c*(c+ε))) := by field_simp; ring
  rw [he,abs_neg,abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_left hε (sq_pos_of_pos ha)
  nlinarith

/-- Existence is constructed by the global chart inverse, rather than
assumed as a premise about a desired positive solution. -/
theorem exists_global_regularized_clock (ε c₀ : ℝ) (hε : 0 < ε) (hc₀ : 0 < c₀) :
    ∃ c : ℝ → ℝ, c 0=c₀ ∧ (∀ t, 0 < c t) ∧
      (∀ t, HasDerivAt c (c t/(c t+ε)) t) := by
  refine ⟨clockFlow ε hε (Real.log c₀),?_,clockFlow_positive ε hε _,clockFlow_derivative ε hε _⟩
  rw [clockFlow_initial,Real.exp_log hc₀]

#print axioms chart_strictMono
#print axioms chart_atTop
#print axioms chart_atBot
#print axioms chart_surjective
#print axioms logFlow_comp
#print axioms chartInverse_derivative
#print axioms logFlow_derivative
#print axioms clockFlow_positive
#print axioms clockFlow_derivative
#print axioms clock_speed_error
#print axioms inverse_mobility_error
#print axioms exists_global_regularized_clock

end
end UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
