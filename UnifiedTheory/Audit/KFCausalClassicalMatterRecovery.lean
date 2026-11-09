/- The derived uniform matter tilt control forces the clock to infinity
along every global solution of the actual clock Hamilton equations. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterAdjustedDrift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterRecovery
noncomputable section
open Filter Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterAdjustedDrift
open UnifiedTheory.Audit.KFCausalClassicalMatterTiltControl
open UnifiedTheory.Audit.KFCausalClassicalMatterDefect (clockRate_positive)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive defect)

variable (ε m g κ τ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
  (z : ℝ → Phase) (s p : ℝ → ℝ)
  (hs : ∀ t, HasDerivAt s (clockRate ε m g κ (t+τ) (z t) (s t) (p t)) t)
  (hp : ∀ t, HasDerivAt p (momentumRate ε m g κ (t+τ) (z t) (s t) (p t)) t)

include hε hm hg hκ hs hp in
theorem bounded_clock_rate_lower (N : ℝ) (hN : 0 ≤ N)
    (hT : ∀ (C : ℝ) (w : Phase), -N*weightedMean m g κ C w ≤
      weightedMean m g κ C w+weightedTilt m g κ C w)
    (R : ℝ) (hR : ∀ t, s t ≤ R) :
    ∃ v : ℝ, 0 < v ∧ ∀ t, 0 ≤ t →
      v ≤ clockRate ε m g κ (t+τ) (z t) (s t) (p t) := by
  let Q := Real.exp (2*τ+p 0/clock ε (s 0)+N*Real.log (clock ε (s 0))-N*Real.log (clock ε R))
  have hQ : 0 < Q := Real.exp_pos _
  have hCR := clock_positive ε R hε.le
  refine ⟨Q*κ/(clock ε R)^2,div_pos (mul_pos hQ hκ) (sq_pos_of_pos hCR),?_⟩
  intro t ht
  have hC := clock_positive ε (s t) hε.le
  have hCupper : clock ε (s t) ≤ clock ε R := by
    unfold clock
    linarith only [Real.exp_le_exp.mpr (hR t)]
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_log hC hCupper) hN
  have hlinear := corrected_linear_lower ε m g κ τ hε z s p hs hp N hT t ht
  have hA : Q ≤ amplitude ε (t+τ) (s t) (p t) := by
    apply Real.exp_le_exp.mpr
    linarith only [hlog,hlinear,ht]
  have hF := weightedMean_lower m g κ (clock ε (s t)) hm hg hκ.le (z t)
  have hnum : Q*κ ≤ amplitude ε (t+τ) (s t) (p t)*weightedMean m g κ (clock ε (s t)) (z t) :=
    (mul_le_mul_of_nonneg_right hA hκ.le).trans
      (mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le)
  unfold clockRate
  apply le_trans _ (div_le_div_of_nonneg_right hnum (sq_nonneg (clock ε (s t))))
  apply div_le_div_of_nonneg_left (mul_pos hQ hκ).le (sq_pos_of_pos hC)
  nlinarith only [hCupper,hC,hCR]

include hε hm hg hκ hs hp in
theorem logClock_tendsto_atTop : Tendsto s atTop atTop := by
  obtain ⟨N,hN,hbound⟩ := exists_uniform_tilt_control
  have hT (C : ℝ) (w : Phase) := hbound m g κ C hm hg hκ.le w
  have hmono : Monotone s := monotone_of_hasDerivAt_nonneg hs (fun t =>
    (clockRate_positive ε m g κ (t+τ) (s t) (p t) hε.le hm hg hκ (z t)).le)
  apply tendsto_atTop_atTop_of_monotone hmono
  intro R
  by_contra hn
  push_neg at hn
  obtain ⟨v,hv,hvel⟩ := bounded_clock_rate_lower ε m g κ τ hε hm hg hκ z s p hs hp N hN hT R
    (fun t => (hn t).le)
  have hd (t : ℝ) := (hs t).sub ((hasDerivAt_id t).const_mul v)
  have hmon : MonotoneOn (fun t => s t-v*t) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      ((continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).continuousOn)
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hd t).deriv]
    simpa only [mul_one,sub_nonneg] using hvel t (interior_subset ht)
  let t := max 0 ((R-s 0+1)/v)
  have ht : 0 ≤ t := le_max_left _ _
  have hlinear := hmon (by simp : (0:ℝ) ∈ Ici 0) ht ht
  have hlarge : R-s 0+1 ≤ t*v := (div_le_iff₀ hv).mp (le_max_right _ _)
  have hupper := hn t
  dsimp only at hlinear
  rw [mul_zero,sub_zero] at hlinear
  nlinarith only [hlinear,hlarge,hupper]

include hε hm hg hκ hs hp in
theorem defect_tendsto_zero :
    Tendsto (fun t => defect ε (s t)) atTop (𝓝 0) := by
  have hc : Tendsto (fun t => clock ε (s t)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (logClock_tendsto_atTop ε m g κ τ hε hm hg hκ z s p hs hp)).atTop_add
      tendsto_const_nhds
  exact hc.const_div_atTop ε

#print axioms bounded_clock_rate_lower
#print axioms logClock_tendsto_atTop
#print axioms defect_tendsto_zero

end
end UnifiedTheory.Audit.KFCausalClassicalMatterRecovery

