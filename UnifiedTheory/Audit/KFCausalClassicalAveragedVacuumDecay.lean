/- Recovery of the clock along every global trajectory satisfying the clock
Hamilton equations of the full charge-averaged classical vacuum candidate.
All transverse coordinates may move: no frozen/transverse-zero sector is
assumed. Global existence and the quantum-to-classical identification are
separate open problems; they are not hidden in this trajectory theorem. -/
import UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalAveragedVacuumDecay
noncomputable section
open Filter Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect

/-- An explicit primitive of the positive function C(s)^2. -/
def clockPrimitive (ε s : ℝ) : ℝ := Real.exp (2*s)/2+2*ε*Real.exp s+ε^2*s

theorem clockPrimitive_derivative (ε s : ℝ) :
    HasDerivAt (clockPrimitive ε) ((clock ε s)^2) s := by
  have h := ((((hasDerivAt_id s).const_mul 2).exp.div_const 2).add
    ((Real.hasDerivAt_exp s).const_mul (2*ε))).add ((hasDerivAt_id s).const_mul (ε^2))
  convert h using 1
  simp only [id_eq]
  rw [show Real.exp (2*s) = (Real.exp s)^2 by rw [← Real.exp_nat_mul]; norm_num]
  unfold clock
  ring

theorem clockPrimitive_monotone (ε : ℝ) : Monotone (clockPrimitive ε) :=
  monotone_of_hasDerivAt_nonneg (clockPrimitive_derivative ε) (fun _ => sq_nonneg _)

variable (ε κ : ℝ) (hε : 0 < ε) (z : ℝ → Phase) (s p : ℝ → ℝ)
  (hs : ∀ t, HasDerivAt s (clockRate ε κ t (z t) (s t) (p t)) t)
  (hp : ∀ t, HasDerivAt p (momentumRate ε κ t (z t) (s t) (p t)) t)

include hε hs hp in
theorem longitudinal_derivative (t : ℝ) :
    HasDerivAt (fun u => p u/clock ε (s u))
      (longitudinalRate ε κ t (z t) (s t) (p t)) t := by
  have hc := (clock_positive ε (s t) hε.le).ne'
  have h := (hp t).div (((Real.hasDerivAt_exp (s t)).comp t (hs t)).add_const ε) hc
  convert h using 1
  rw [longitudinalRate_eq ε κ t hε.le (z t) (s t) (p t)]
  simp only [Function.comp_apply]
  change _ = (momentumRate ε κ t (z t) (s t) (p t)*clock ε (s t)-
    p t*(Real.exp (s t)*clockRate ε κ t (z t) (s t) (p t)))/(clock ε (s t))^2
  field_simp

include hε hs hp in
theorem longitudinal_linear_lower (hκ : 0 ≤ κ) (t : ℝ) (ht : 0 ≤ t) :
    p 0/clock ε (s 0)-t/2 ≤ p t/clock ε (s t) := by
  have hd (u : ℝ) := (longitudinal_derivative ε κ hε z s p hs hp u).add
    ((hasDerivAt_id u).div_const 2)
  have hm : Monotone (fun u => p u/clock ε (s u)+u/2) := by
    apply monotone_of_hasDerivAt_nonneg (fun u => hd u)
    intro u
    change 0 ≤ longitudinalRate ε κ u (z u) (s u) (p u)+1/2
    linarith [longitudinalRate_lower ε κ u hε hκ (z u) (s u) (p u)]
  have h := hm ht
  dsimp only at h
  linarith

include hε hs hp in
theorem amplitude_future_lower (hκ : 0 ≤ κ) (t : ℝ) (ht : 0 ≤ t) :
    κ*Real.exp (p 0/clock ε (s 0)) ≤ amplitude ε κ t (s t) (p t) := by
  apply mul_le_mul_of_nonneg_left _ hκ
  apply Real.exp_le_exp.mpr
  linarith [longitudinal_linear_lower ε κ hε z s p hs hp hκ t ht]

include hε hs in
theorem clockPrimitive_trajectory_derivative (t : ℝ) :
    HasDerivAt (fun u => clockPrimitive ε (s u))
      (amplitude ε κ t (s t) (p t)*exponentialMean (clock ε (s t)) (z t)) t := by
  have h := (clockPrimitive_derivative ε (s t)).comp t (hs t)
  have hc := (clock_positive ε (s t) hε.le).ne'
  convert h using 1
  unfold clockRate
  field_simp

include hε hs hp in
theorem clockPrimitive_linear_lower (hκ : 0 ≤ κ) (t : ℝ) (ht : 0 ≤ t) :
    clockPrimitive ε (s 0)+κ*Real.exp (p 0/clock ε (s 0))*t ≤ clockPrimitive ε (s t) := by
  let A := κ*Real.exp (p 0/clock ε (s 0))
  have hd (u : ℝ) : HasDerivAt (fun v => clockPrimitive ε (s v)-A*v)
      (amplitude ε κ u (s u) (p u)*exponentialMean (clock ε (s u)) (z u)-A) u := by
    simpa only [mul_one] using (clockPrimitive_trajectory_derivative ε κ hε z s p hs u).sub
      ((hasDerivAt_id u).const_mul A)
  have hm : MonotoneOn (fun u => clockPrimitive ε (s u)-A*u) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      ((continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)).continuousOn)
      (fun u _ => (hd u).differentiableAt.differentiableWithinAt)
    intro u hu
    rw [(hd u).deriv]
    have ha := amplitude_future_lower ε κ hε z s p hs hp hκ u (interior_subset hu)
    have hA : 0 ≤ amplitude ε κ u (s u) (p u) := mul_nonneg hκ (Real.exp_pos _).le
    exact sub_nonneg.mpr (ha.trans (le_mul_of_one_le_right hA (exponentialMean_ge_one _ _)))
  have h := hm (by simp : (0:ℝ) ∈ Ici 0) ht ht
  dsimp only at h
  rw [mul_zero, sub_zero] at h
  linarith only [h]

include hε hs hp in
theorem logClock_tendsto_atTop (hκ : 0 < κ) : Tendsto s atTop atTop := by
  have hg : Tendsto (fun t => clockPrimitive ε (s t)) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      ((eventually_ge_atTop (0:ℝ)).mono
        (fun t ht => clockPrimitive_linear_lower ε κ hε z s p hs hp hκ.le t ht))
    exact tendsto_const_nhds.add_atTop (tendsto_id.const_mul_atTop (mul_pos hκ (Real.exp_pos _)))
  apply tendsto_atTop.2
  intro R
  filter_upwards [hg.eventually (eventually_gt_atTop (clockPrimitive ε R))] with t ht
  by_contra hn
  have h := clockPrimitive_monotone ε (le_of_not_ge hn)
  exact (not_lt_of_ge h) ht

include hε hs hp in
theorem defect_tendsto_zero (hκ : 0 < κ) :
    Tendsto (fun t => defect ε (s t)) atTop (𝓝 0) := by
  have hc : Tendsto (fun t => clock ε (s t)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (logClock_tendsto_atTop ε κ hε z s p hs hp hκ)).atTop_add tendsto_const_nhds
  exact hc.const_div_atTop ε

#print axioms clockPrimitive_derivative
#print axioms clockPrimitive_monotone
#print axioms longitudinal_derivative
#print axioms longitudinal_linear_lower
#print axioms amplitude_future_lower
#print axioms clockPrimitive_trajectory_derivative
#print axioms clockPrimitive_linear_lower
#print axioms logClock_tendsto_atTop
#print axioms defect_tendsto_zero

end
end UnifiedTheory.Audit.KFCausalClassicalAveragedVacuumDecay
