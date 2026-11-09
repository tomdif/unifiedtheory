/- A precise domain obstruction for the naive Gaussian ansatz after
straightening the coupled longitudinal transport. The dilation momentum
weight exp(-phase) defeats every Gaussian in the straight clock coordinate.
This rules out that proposed weight integral, not every possible common
domain or the full model. -/
import UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoupledGaussianObstruction
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow

def weightedGaussianDensity (ε a s : ℝ) : ℝ :=
  (Real.exp s+ε)*Real.exp (-phase ε s-a*(chart ε s)^2)

theorem chart_negative_square_bound (ε x : ℝ) (hx : 1 ≤ x) :
    (chart ε (-x))^2 ≤ (2+2*ε^2)*x^2 := by
  have hx0 : 0 ≤ x := by linarith
  have he : Real.exp (-x) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hx0)
  have hep := Real.exp_pos (-x)
  have he2 : (Real.exp (-x))^2 ≤ 1 := by nlinarith
  have hx2 : 1 ≤ x^2 := by nlinarith
  dsimp [chart]
  nlinarith [sq_nonneg (Real.exp (-x)+ε*x)]

theorem weightedGaussian_tail_lower (ε a : ℝ) (hε : 0 < ε) (ha : 0 ≤ a) :
    ∀ᶠ x : ℝ in atTop, ε ≤ weightedGaussianDensity ε a (-x) := by
  have he := (Real.tendsto_exp_div_pow_atTop 2).eventually
    (eventually_ge_atTop (a*(2+2*ε^2)/ε))
  filter_upwards [he,eventually_ge_atTop (1:ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have he' := (le_div_iff₀ (sq_pos_of_pos hx0)).mp hx
  have hm := mul_le_mul_of_nonneg_left he' hε.le
  have hid : ε*((a*(2+2*ε^2)/ε)*x^2) = a*(2+2*ε^2)*x^2 := by field_simp
  rw [hid] at hm
  have hq := mul_le_mul_of_nonneg_left (chart_negative_square_bound ε x hx1) ha
  have hp : 0 ≤ -phase ε (-x)-a*(chart ε (-x))^2 := by
    simp only [phase,neg_neg]
    nlinarith
  have hexp : 1 ≤ Real.exp (-phase ε (-x)-a*(chart ε (-x))^2) :=
    Real.one_le_exp_iff.mpr hp
  have hfactor : ε ≤ Real.exp (-x)+ε := by linarith [Real.exp_pos (-x)]
  unfold weightedGaussianDensity
  nlinarith [mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ Real.exp (-x)+ε)]

theorem weightedGaussian_not_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 ≤ a) :
    ¬ Integrable (weightedGaussianDensity ε a) := by
  intro hint
  obtain ⟨R,hR⟩ := eventually_atTop.mp (weightedGaussian_tail_lower ε a hε ha)
  have hb (s : ℝ) (hs : s ∈ Iic (-R)) : ε ≤ weightedGaussianDensity ε a s := by
    have hh := hR (-s) (by have := hs; simp only [mem_Iic] at this; linarith)
    simpa only [neg_neg] using hh
  have hc : IntegrableOn (fun _ : ℝ => ε) (Iic (-R)) := by
    change Integrable (fun _ : ℝ => ε) (volume.restrict (Iic (-R)))
    have hi : Integrable (weightedGaussianDensity ε a) (volume.restrict (Iic (-R))) := hint.integrableOn
    apply hi.mono' (f := fun _ : ℝ => ε) aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
    simpa only [Real.norm_eq_abs,abs_of_pos hε] using hb s hs
  simp [integrableOn_const_iff,hε.ne'] at hc

#print axioms chart_negative_square_bound
#print axioms weightedGaussian_tail_lower
#print axioms weightedGaussian_not_integrable

end
end UnifiedTheory.Audit.KFCausalCoupledGaussianObstruction
