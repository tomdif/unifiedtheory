/- A corrected even-line comparison yields a corrected angular-radius
comparison. This is a general real-variable lemma; the actual neutral
family discharges its hypotheses in the successor module. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslatedMarginal
import UnifiedTheory.Audit.KFCausalCompactAngularDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrectedAngularComparison
noncomputable section
open MeasureTheory Set
open scoped Topology

def evenCorrected (U : ℝ → ℝ) (a v : ℝ) : ℝ := Real.exp (a*v^2)*(U v+U (-v))
def angular (U : ℝ → ℝ) (ρ : ℝ) : ℝ := (∫ θ in -Real.pi..Real.pi, U (ρ*Real.sin θ))/(2*Real.pi)
def angularSlope (U' : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  (∫ θ in -Real.pi..Real.pi, Real.sin θ*U' (ρ*Real.sin θ))/(2*Real.pi)
def radialPair (U : ℝ → ℝ) (a ρ θ : ℝ) : ℝ :=
  Real.exp (a*ρ^2)*(U (ρ*Real.sin θ)+U (-(ρ*Real.sin θ)))

theorem evenCorrected_abs (U : ℝ → ℝ) (a v : ℝ) :
    evenCorrected U a |v| = evenCorrected U a v := by
  by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hv]
  · rw [abs_of_neg (lt_of_not_ge hv)]
    simp only [evenCorrected,neg_sq,neg_neg,add_comm]

theorem radialPair_factor (U : ℝ → ℝ) (a ρ θ : ℝ) :
    radialPair U a ρ θ = Real.exp (a*ρ^2*(1-(Real.sin θ)^2))*evenCorrected U a (ρ*Real.sin θ) := by
  unfold radialPair evenCorrected
  rw [← mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem radialPair_monotone (U : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a) (hU : ∀ x, 0 ≤ U x)
    (hm : MonotoneOn (evenCorrected U a) (Ici 0)) (θ : ℝ) :
    MonotoneOn (fun ρ => radialPair U a ρ θ) (Ici 0) := by
  intro ρ hρ σ hσ hρσ
  have hρ' : 0 ≤ ρ := hρ
  have hσ' : 0 ≤ σ := hσ
  have hs : (Real.sin θ)^2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq θ,sq_nonneg (Real.cos θ)]
  have hk : 0 ≤ a*(1-(Real.sin θ)^2) := mul_nonneg ha (by linarith)
  have hq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ' hρσ 2) hk
  have he : Real.exp (a*ρ^2*(1-(Real.sin θ)^2)) ≤ Real.exp (a*σ^2*(1-(Real.sin θ)^2)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hv : |ρ*Real.sin θ| ≤ |σ*Real.sin θ| := by
    simpa only [abs_mul,abs_of_nonneg hρ',abs_of_nonneg hσ'] using
      mul_le_mul_of_nonneg_right hρσ (abs_nonneg (Real.sin θ))
  have hh := hm (abs_nonneg (ρ*Real.sin θ)) (abs_nonneg (σ*Real.sin θ)) hv
  rw [evenCorrected_abs,evenCorrected_abs] at hh
  change radialPair U a ρ θ ≤ radialPair U a σ θ
  rw [radialPair_factor,radialPair_factor]
  exact mul_le_mul he hh (mul_nonneg (Real.exp_pos _).le (add_nonneg (hU _) (hU _))) (Real.exp_pos _).le

theorem angular_symmetrized (U : ℝ → ℝ) (hU : Continuous U) (a ρ : ℝ) :
    Real.exp (a*ρ^2)*angular U ρ = (∫ θ in -Real.pi..Real.pi, radialPair U a ρ θ)/(4*Real.pi) := by
  have hi : Continuous (fun θ => U (ρ*Real.sin θ)) := by fun_prop
  have hj : Continuous (fun θ => U (-(ρ*Real.sin θ))) := by fun_prop
  have hn : (∫ θ in -Real.pi..Real.pi, U (-(ρ*Real.sin θ))) =
      ∫ θ in -Real.pi..Real.pi, U (ρ*Real.sin θ) := by
    have he := intervalIntegral.integral_comp_neg (fun θ => U (ρ*Real.sin θ)) (a := -Real.pi) (b := Real.pi)
    simpa only [Real.sin_neg,mul_neg,neg_neg] using he
  unfold angular radialPair
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (hi.intervalIntegrable _ _) (hj.intervalIntegrable _ _),hn]
  field_simp
  ring

theorem angular_corrected_monotone (U : ℝ → ℝ) (hU : Continuous U) (a : ℝ) (ha : 0 ≤ a)
    (hpos : ∀ x, 0 ≤ U x) (hm : MonotoneOn (evenCorrected U a) (Ici 0)) :
    MonotoneOn (fun ρ => Real.exp (a*ρ^2)*angular U ρ) (Ici 0) := by
  intro ρ hρ σ hσ hρσ
  change Real.exp (a*ρ^2)*angular U ρ ≤ Real.exp (a*σ^2)*angular U σ
  rw [angular_symmetrized U hU,angular_symmetrized U hU]
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 4*Real.pi)
  have hi (r : ℝ) : Continuous (radialPair U a r) := by unfold radialPair; fun_prop
  exact intervalIntegral.integral_mono (by linarith [Real.pi_pos])
    ((hi ρ).intervalIntegrable _ _) ((hi σ).intervalIntegrable _ _)
    (fun θ => radialPair_monotone U a ha hpos hm θ hρ hσ hρσ)

theorem angular_derivative (U U' : ℝ → ℝ) (hU : Continuous U) (hU' : Continuous U')
    (hd : ∀ v, HasDerivAt U (U' v) v) (ρ : ℝ) :
    HasDerivAt (angular U) (angularSlope U' ρ) ρ := by
  have he := KFCausalCompactAngularDerivative.integral_hasDerivAt
    (fun r θ => U (r*Real.sin θ)) (fun r θ => Real.sin θ*U' (r*Real.sin θ))
    (by unfold Function.uncurry; fun_prop) (by unfold Function.uncurry; fun_prop)
    (fun r θ => by
      convert (hd (r*Real.sin θ)).comp r ((hasDerivAt_id r).mul_const (Real.sin θ)) using 1
      dsimp
      ring) ρ
  exact he.div_const _

theorem corrected_angular_derivative (U U' : ℝ → ℝ) (hU : Continuous U) (hU' : Continuous U')
    (hd : ∀ v, HasDerivAt U (U' v) v) (a ρ : ℝ) :
    HasDerivAt (fun r => Real.exp (a*r^2)*angular U r)
      (Real.exp (a*ρ^2)*(angularSlope U' ρ+2*a*ρ*angular U ρ)) ρ := by
  have he := (((hasDerivAt_id ρ).pow 2).const_mul a).exp
  convert he.mul (angular_derivative U U' hU hU' hd ρ) using 1
  dsimp
  ring

theorem radial_derivative_lower (U U' : ℝ → ℝ) (hU : Continuous U) (hU' : Continuous U')
    (hd : ∀ v, HasDerivAt U (U' v) v) (a : ℝ)
    (hm : MonotoneOn (fun r => Real.exp (a*r^2)*angular U r) (Ici 0))
    (ρ : ℝ) (hρ : 0 < ρ) : -2*a*ρ*angular U ρ ≤ deriv (angular U) ρ := by
  have hh : 0 ≤ Real.exp (a*ρ^2)*(angularSlope U' ρ+2*a*ρ*angular U ρ) := by
    rw [← (corrected_angular_derivative U U' hU hU' hd a ρ).deriv,
      ← derivWithin_of_mem_nhds (Ici_mem_nhds hρ)]
    exact hm.derivWithin_nonneg
  have hp := (mul_nonneg_iff_of_pos_left (Real.exp_pos (a*ρ^2))).mp hh
  rw [(angular_derivative U U' hU hU' hd ρ).deriv]
  linarith

#print axioms evenCorrected_abs
#print axioms radialPair_factor
#print axioms radialPair_monotone
#print axioms angular_symmetrized
#print axioms angular_corrected_monotone
#print axioms angular_derivative
#print axioms corrected_angular_derivative
#print axioms radial_derivative_lower
end
end UnifiedTheory.Audit.KFCausalCorrectedAngularComparison
