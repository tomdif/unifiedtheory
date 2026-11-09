/- Quantitative growth of the actual full classical clock from the
explicit weighted-tilt estimate. This does not identify a quantum limit. -/
import UnifiedTheory.Audit.KFCausalClassicalExplicitTiltControl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClassicalClockGrowth
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (Phase)
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalExplicitTiltControl (adjusted evolve_interval_lower)
open UnifiedTheory.Audit.KFCausalClassicalMatterEvolution
open UnifiedTheory.Audit.KFCausalClassicalMatterDefect (clock_derivative clockRate_positive)
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (TimePhase q p)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect

def boost (ε s : ℝ) : ℝ := Real.exp (65538*Real.log (clock ε s))

def growth (ε κ : ℝ) (x : TimePhase) : ℝ :=
  43692*κ*response ε (q (.inr 0) x.2)*Real.exp (2*x.1+adjusted ε x.2)

def envelope (ε κ : ℝ) (x : TimePhase) (t : ℝ) : ℝ :=
  boost ε (q (.inr 0) x.2)+growth ε κ x*(Real.exp (3*t/2)-1)

theorem boost_positive (ε s : ℝ) : 0 < boost ε s := Real.exp_pos _

theorem growth_positive (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (x : TimePhase) :
    0 < growth ε κ x := by
  have hr := (response_bounds ε (q (.inr 0) x.2) hε).1
  unfold growth
  positivity

theorem boost_div_clock_sq (ε s : ℝ) (hε : 0 < ε) :
    boost ε s/(clock ε s)^2 = Real.exp (65536*Real.log (clock ε s)) := by
  have hc := clock_positive ε s hε.le
  have he : Real.exp (2*Real.log (clock ε s)) = (clock ε s)^2 := by
    rw [two_mul,Real.exp_add,Real.exp_log hc]
    ring
  rw [boost,show 65538*Real.log (clock ε s) =
    65536*Real.log (clock ε s)+2*Real.log (clock ε s) by ring,Real.exp_add,he]
  exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hc.ne')

theorem response_monotone (ε : ℝ) (hε : 0 < ε) : Monotone (response ε) := by
  intro a b hab
  have hc : clock ε a ≤ clock ε b := by
    unfold clock
    linarith only [Real.exp_le_exp.mpr hab]
  have hd := div_le_div_of_nonneg_left hε.le (clock_positive ε a hε.le) hc
  have ha := response_add_defect ε a hε.le
  have hb := response_add_defect ε b hε.le
  change defect ε b ≤ defect ε a at hd
  linarith only [ha,hb,hd]

variable (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
local notation "Φ" => evolve ε m g κ hε hm hg hκ

theorem evolve_clock_derivative (x : TimePhase) (t : ℝ) :
    HasDerivAt (fun u => q (.inr 0) (Φ u x).2)
      (clockRate ε m g κ (t+x.1) (Φ t x).2 (q (.inr 0) (Φ t x).2) (p (.inr 0) (Φ t x).2)) t := by
  have he := clock_derivative ε m g κ hε.le (fun u => Φ u x) t
    (evolve_derivative ε m g κ hε hm hg hκ x t)
  rw [evolve_time] at he
  exact he

theorem evolve_clock_monotone (x : TimePhase) : Monotone (fun t => q (.inr 0) (Φ t x).2) :=
  monotone_of_hasDerivAt_nonneg (evolve_clock_derivative ε m g κ hε hm hg hκ x)
    (fun t => (clockRate_positive ε m g κ (t+x.1) (q (.inr 0) (Φ t x).2)
      (p (.inr 0) (Φ t x).2) hε.le hm hg hκ (Φ t x).2).le)

theorem evolve_response_lower (x : TimePhase) (t : ℝ) (ht : 0 ≤ t) :
    response ε (q (.inr 0) x.2) ≤ response ε (q (.inr 0) (Φ t x).2) := by
  have hs := evolve_clock_monotone ε m g κ hε hm hg hκ x ht
  dsimp only at hs
  rw [evolve_zero] at hs
  exact response_monotone ε hε hs

theorem evolve_boost_derivative (x : TimePhase) (t : ℝ) :
    HasDerivAt (fun u => boost ε (q (.inr 0) (Φ u x).2))
      (65538*response ε (q (.inr 0) (Φ t x).2)*
        weightedMean m g κ (clock ε (q (.inr 0) (Φ t x).2)) (Φ t x).2*
          Real.exp (2*(t+x.1)+adjusted ε (Φ t x).2)) t := by
  let s := q (.inr 0) (Φ t x).2
  let r := p (.inr 0) (Φ t x).2
  have hs := evolve_clock_derivative ε m g κ hε hm hg hκ x t
  have hc := clock_positive ε s hε.le
  have hd : HasDerivAt (fun u => boost ε (q (.inr 0) (Φ u x).2))
      (65538*response ε s*clockRate ε m g κ (t+x.1) (Φ t x).2 s r*boost ε s) t := by
    convert (((hs.exp.add_const ε).log hc.ne').const_mul 65538).exp using 1
    simp only [boost,response,clock,s,r]
    ring
  have he : boost ε s*amplitude ε (t+x.1) s r/(clock ε s)^2 =
      Real.exp (2*(t+x.1)+adjusted ε (Φ t x).2) := by
    calc
      _ = (boost ε s/(clock ε s)^2)*amplitude ε (t+x.1) s r := by ring
      _ = _ := by
        rw [boost_div_clock_sq ε s hε,amplitude,← Real.exp_add]
        congr 1
        simp only [adjusted,s,r]
        ring
  convert hd using 1
  calc
    _ = (65538*response ε s*weightedMean m g κ (clock ε s) (Φ t x).2)*
        (boost ε s*amplitude ε (t+x.1) s r/(clock ε s)^2) := by rw [he]
    _ = _ := by unfold clockRate; ring

theorem evolve_boost_rate_lower (x : TimePhase) (t : ℝ) (ht : 0 ≤ t) :
    growth ε κ x*(3/2)*Real.exp (3*t/2) ≤
      65538*response ε (q (.inr 0) (Φ t x).2)*
        weightedMean m g κ (clock ε (q (.inr 0) (Φ t x).2)) (Φ t x).2*
          Real.exp (2*(t+x.1)+adjusted ε (Φ t x).2) := by
  have hQ := evolve_interval_lower ε m g κ hε hm hg hκ x 0 t ht
  rw [evolve_zero,sub_zero] at hQ
  have he : Real.exp ((2*x.1+adjusted ε x.2)+3*t/2) ≤
      Real.exp (2*(t+x.1)+adjusted ε (Φ t x).2) := Real.exp_le_exp.mpr (by linarith only [hQ])
  have hr := evolve_response_lower ε m g κ hε hm hg hκ x t ht
  have hW := weightedMean_lower m g κ (clock ε (q (.inr 0) (Φ t x).2)) hm hg hκ.le (Φ t x).2
  have hrp := (response_bounds ε (q (.inr 0) (Φ t x).2) hε).1
  have h1 := mul_le_mul hr hW hκ.le hrp.le
  have h2 := mul_le_mul h1 he (Real.exp_pos _).le (mul_nonneg hrp.le (hκ.le.trans hW))
  have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 65538)
  convert h3 using 1
  · simp only [growth,Real.exp_add]
    ring
  · ring

theorem evolve_boost_comparison_monotone (x : TimePhase) :
    MonotoneOn (fun t => boost ε (q (.inr 0) (Φ t x).2)-
      growth ε κ x*(Real.exp (3*t/2)-1)) (Ici 0) := by
  have hd (t : ℝ) := (evolve_boost_derivative ε m g κ hε hm hg hκ x t).sub
    (((((hasDerivAt_id t).const_mul 3).div_const 2).exp.sub_const 1).const_mul (growth ε κ x))
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    ((continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).continuousOn)
    (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hd t).deriv]
  simp only [id_eq,mul_one]
  have he := evolve_boost_rate_lower ε m g κ hε hm hg hκ x t (interior_subset ht)
  nlinarith only [he]

theorem evolve_boost_lower (x : TimePhase) (t : ℝ) (ht : 0 ≤ t) :
    envelope ε κ x t ≤ boost ε (q (.inr 0) (Φ t x).2) := by
  have he := evolve_boost_comparison_monotone ε m g κ hε hm hg hκ x
    (by simp : (0:ℝ) ∈ Ici 0) ht ht
  simp only [evolve_zero,mul_zero,zero_div,Real.exp_zero,sub_self,sub_zero] at he
  unfold envelope
  linarith only [he]

#print axioms boost_positive
#print axioms growth_positive
#print axioms boost_div_clock_sq
#print axioms response_monotone
#print axioms evolve_clock_derivative
#print axioms evolve_clock_monotone
#print axioms evolve_response_lower
#print axioms evolve_boost_derivative
#print axioms evolve_boost_rate_lower
#print axioms evolve_boost_comparison_monotone
#print axioms evolve_boost_lower
end
end UnifiedTheory.Audit.KFCausalClassicalClockGrowth
