/- A uniform forward squared Hilbert increment bound derived from the
actual weak equation and decreasing rescaled energy. No strong physical
state derivative or propagated momentum domain is required. -/
import UnifiedTheory.Audit.KFCausalClockFloorExponentialVariation
import UnifiedTheory.Audit.KFCausalClockFloorRescaledEnergy

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPhysicalVariation
noncomputable section
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorAveragedFormFlow (formFlow formFlow_initial formFlow_compose formFlow_physical_norm)
open KFCausalClockFloorAveragedEvolution (evolution evolution_embedding evolution_norm)
open KFCausalClockFloorAveragedTimeControl (timeEnergy timeEnergy_nonneg)
open KFCausalClockFloorExponentialVariation (variationConstant pairing_variation)

private theorem gap_pairing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) (hn : ‖x‖=‖y‖) :
    ‖x-y‖^2 ≤ 2*‖inner ℂ x y-inner ℂ y y‖ := by
  have hs := norm_sub_sq (𝕜 := ℂ) x y
  have hi : (inner ℂ y y).re=‖y‖^2 := by
    simpa only [RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜 := ℂ) y
  have hb := (neg_le_abs (inner ℂ x y-inner ℂ y y).re).trans
    (Complex.abs_re_le_norm (inner ℂ x y-inner ℂ y y))
  simp only [RCLike.re_eq_complex_re,hn] at hs
  rw [Complex.sub_re,hi] at hb
  linarith only [hs,hb]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "F" => formFlow ε hε h hne hb m g k
local notation "E" => evolution ε hε h hne hb m g k
local notation "q" => timeEnergy ε hε h hne hb m g k

def bound (s : ℝ) (v : V) : ℝ := 2*|1/h| *Real.exp (-2*s)*(2*q s v+1)

theorem bound_nonnegative (s : ℝ) (v : V) : 0 ≤ bound ε hε h hne hb m g k s v := by
  have hq := timeEnergy_nonneg ε hε h hne hb m g k s v
  unfold bound
  positivity

theorem restarted_constant_bound (s a : ℝ) (hsa : s ≤ a) (v : V) :
    2*variationConstant ε hε h hne hb m g k a (F s a v) (F s a v) ≤
      bound ε hε h hne hb m g k s v := by
  have he := KFCausalClockFloorRescaledEnergy.scaled_antitone ε hε h hne hb m g k s v hsa
  change Real.exp (-2*a)*q a (F s a v) ≤ Real.exp (-2*s)*q s (F s s v) at he
  rw [formFlow_initial] at he
  have hexp := Real.exp_le_exp.mpr (show -2*a ≤ -2*s by linarith only [hsa])
  have hs : Real.exp (-2*a)*(q a (F s a v)+q a (F s a v)+1) ≤
      Real.exp (-2*s)*(2*q s v+1) := by nlinarith only [he,hexp]
  have hh := mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg (1/h)))
  unfold variationConstant bound
  nlinarith only [hh]

theorem increment_square_bound (s a b : ℝ) (hsa : s ≤ a) (hab : a ≤ b) (v : V) :
    ‖E s b (J v)-E s a (J v)‖^2 ≤
      bound ε hε h hne hb m g k s v*Real.exp (2*b)*(b-a) := by
  have hp := pairing_variation ε hε h hne hb m g k a a b le_rfl hab (F s a v) (F s a v)
  simp only [evolution_embedding,formFlow_compose,formFlow_initial] at hp
  have hg := gap_pairing (J (F s b v)) (J (F s a v))
    ((formFlow_physical_norm ε hε h hne hb m g k s b v).trans
      (formFlow_physical_norm ε hε h hne hb m g k s a v).symm)
  have hbnd := restarted_constant_bound ε hε h hne hb m g k s a hsa v
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbnd (Real.exp_pos (2*b)).le) (sub_nonneg.mpr hab)
  simp only [evolution_embedding]
  exact hg.trans ((mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 2)).trans
    ((show 2*(variationConstant ε hε h hne hb m g k a (F s a v) (F s a v)*
        Real.exp (2*b)*(b-a)) =
      (2*variationConstant ε hε h hne hb m g k a (F s a v) (F s a v))*
        Real.exp (2*b)*(b-a) by ring).le.trans hmul))

#print axioms bound_nonnegative
#print axioms restarted_constant_bound
#print axioms increment_square_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorPhysicalVariation
