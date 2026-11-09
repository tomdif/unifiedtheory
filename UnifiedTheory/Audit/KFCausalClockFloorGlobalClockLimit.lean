/- One subsequence of actual clock-defect expectations converges on every
compact time set to a continuous path on all real times. Its balance law
retains the actual comparison-rate integrals. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockLimit
import UnifiedTheory.Audit.KFCausalCharacteristicCompactUniformity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGlobalClockLimit
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockWindow
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockIntegral
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockLimit
open UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness
open UnifiedTheory.Audit.KFCausalCharacteristicCompactUniformity

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g κ s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
  (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
include hm hg hκ hz

theorem clock_equicontinuity : EventuallyLocallyEquicontinuous
    (fun n t => (clockExpectation ε a (h n) hε ha (hh n) (hb n) m g κ s p t : ℂ)) := by
  intro x η hη
  let T := |x-s|+1
  let L := speedConstant ε a m g κ s T p
  have hL : 0 ≤ L := speedConstant_nonnegative ε a m g κ s T hε p
  have hLp : 0 < L+1 := by linarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (clockExpectation_window_lipschitz ε a hε ha m g κ s p hm hg hκ h hh hb hz T)
  refine ⟨min 1 (η/(L+1)), lt_min zero_lt_one (div_pos hη hLp), N, ?_⟩
  intro n hn y hy
  have hxy : |y-x| < min 1 (η/(L+1)) := by simpa only [Real.dist_eq] using hy
  have hxy1 := hxy.trans_le (min_le_left 1 (η/(L+1)))
  have hx : |x-s| ≤ T := by dsimp [T]; linarith
  have hyT : |y-s| ≤ T := by
    have hh' := abs_add_le (y-x) (x-s)
    rw [sub_add_sub_cancel] at hh'
    dsimp [T]
    linarith
  have hnear := hN n hn x y hx hyT
  have hsmall : (L+1)*|y-x| < η := by
    have hlt := (lt_div_iff₀ hLp).mp (hxy.trans_le (min_le_right 1 (η/(L+1))))
    simpa only [mul_comm] using hlt
  have hle : L*|y-x| ≤ (L+1)*|y-x| := by nlinarith [abs_nonneg (y-x)]
  simpa only [dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    using hnear.trans_lt (hle.trans_lt hsmall)

theorem clock_global_subsequence :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℝ → ℝ,
      Continuous f ∧ (∀ t, f t ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ t, Tendsto (fun n => clockExpectation ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p t)
        atTop (𝓝 (f t))) ∧
      (∀ S, IsCompact S → TendstoUniformlyOn
        (fun n => clockExpectation ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p) f atTop S) ∧
      (∀ T r t : ℝ, |r-s| ≤ T → |t-s| ≤ T →
        |f t-f r| ≤ speedConstant ε a m g κ s T p*|t-r|) := by
  let F : ℕ → ℝ → ℂ := fun n t => (clockExpectation ε a (h n) hε ha (hh n) (hb n) m g κ s p t : ℂ)
  have he := clock_equicontinuity ε a hε ha m g κ s p hm hg hκ h hh hb hz
  have hF (n : ℕ) (t : ℝ) : ‖F n t‖ ≤ 1 := by
    have hbt := clockExpectation_bounds ε a (h n) hε ha (hh n) (hb n) m g κ s p t
    simpa only [F,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hbt.1] using hbt.2
  obtain ⟨φ,hφ,c,hc,hlim,_⟩ := exists_continuous_subsequence F hF he
  let f : ℝ → ℝ := fun t => (c t).re
  have hf (t : ℝ) : Tendsto
      (fun n => clockExpectation ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p t)
      atTop (𝓝 (f t)) := by
    simpa only [F,Function.comp_def,Complex.ofReal_re] using
      (Complex.continuous_re.tendsto (c t)).comp (hlim t)
  refine ⟨φ,hφ,f,Complex.continuous_re.comp hc,?_,hf,?_,?_⟩
  · intro t
    exact ⟨ge_of_tendsto' (hf t) (fun n =>
      (clockExpectation_bounds ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p t).1),
      le_of_tendsto' (hf t) (fun n =>
      (clockExpectation_bounds ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p t).2)⟩
  · intro S hS
    simpa only [F,Function.comp_def,Complex.ofReal_re] using
      Complex.uniformContinuous_re.comp_tendstoUniformlyOn
        (compact_uniform_convergence F he φ hφ c hlim S hS)
  · intro T r t hr ht
    apply le_of_tendsto ((hf t).sub (hf r)).abs
    filter_upwards [hφ.tendsto_atTop.eventually
      (clockExpectation_window_lipschitz ε a hε ha m g κ s p hm hg hκ h hh hb hz T)] with n hn
    exact hn r t hr ht

theorem clock_global_balance :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℝ → ℝ,
      Continuous f ∧ (∀ t, f t ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ t, Tendsto (fun n => clockExpectation ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p t)
        atTop (𝓝 (f t))) ∧
      (∀ S, IsCompact S → TendstoUniformlyOn
        (fun n => clockExpectation ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p) f atTop S) ∧
      (∀ T r t : ℝ, |r-s| ≤ T → |t-s| ≤ T →
        |f t-f r| ≤ speedConstant ε a m g κ s T p*|t-r|) ∧
      (∀ r t : ℝ, Tendsto (fun n => ∫ u in r..t,
        comparisonRate ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p u)
        atTop (𝓝 (f t-f r))) := by
  obtain ⟨φ,hφ,f,hf,hbounds,hpoint,huniform,hlip⟩ :=
    clock_global_subsequence ε a hε ha m g κ s p hm hg hκ h hh hb hz
  refine ⟨φ,hφ,f,hf,hbounds,hpoint,huniform,hlip,?_⟩
  intro r t
  let T := max |r-s| |t-s|
  have he := (clockResidual_tendsto ε a hε ha m g κ s T p hm hg hκ h hh hb hz r t
    (le_max_left _ _) (le_max_right _ _)).comp hφ.tendsto_atTop
  have ht := ((hpoint t).sub (hpoint r)).sub he
  have hid (n : ℕ) :
      clockExpectation ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p t-
      clockExpectation ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p r-
      clockResidual ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p r t =
        ∫ u in r..t, comparisonRate ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p u := by
    unfold clockResidual
    ring
  simpa only [Function.comp_def,hid,sub_zero] using ht

#print axioms clock_equicontinuity
#print axioms clock_global_subsequence
#print axioms clock_global_balance

end
end UnifiedTheory.Audit.KFCausalClockFloorGlobalClockLimit
