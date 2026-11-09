/- Actual clock-Gaussian cutoff convergence at every fixed vertical center.
The scalar multiplier and its L2 section lift converge strongly to the
identity by actual representatives and an eventual uniform bound. No
extra state domain or growing-operator conclusion is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingTransport
import UnifiedTheory.Audit.KFCausalDominatedRepresentedL2Limit
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingApproximation
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorGaussianGrowingTransport
  (gaussian centered line stripCap centered_bound action action_coe action_norm)

private theorem line_le (ε a y s : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖line ε a y s‖ ≤ Real.exp (y^2) := by
  have hl := centered_bound a ha 0 y
    (KFCausalRegularizedLongitudinalChart.chart ε s:ℂ) (by simp)
  simp only [stripCap,abs_zero,add_zero,sq_abs] at hl
  apply hl.trans
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg y])

variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]

theorem action_tendsto (ε y : ℝ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hz : Tendsto a l (𝓝 0)) (f : Hilbert) :
    Tendsto (fun i => action ε (a i) (ha i) y f) l (𝓝 f) := by
  have ha1 : ∀ᶠ i in l, a i ≤ 1 :=
    (hz.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun i hi => hi.le)
  have hD : MemLp (fun x => Real.exp (y^2)*‖f x‖) 2 volume :=
    (Lp.memLp f).norm.const_mul _
  have ht := KFCausalDominatedRepresentedL2Limit.represented_tendsto
    (fun i => action ε (a i) (ha i) y f)
    (fun i x => line ε (a i) y x.1*f x) f (Lp.memLp f)
    (fun x => Real.exp (y^2)*‖f x‖) hD
    (Eventually.of_forall (fun i => action_coe ε (a i) (ha i) y f))
    (ha1.mono (fun i hi => Eventually.of_forall (fun x => by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg
        (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_right (line_le ε (a i) y x.1 (ha i) hi) (norm_nonneg _))))
    (Eventually.of_forall (fun x => by
      have hc : Continuous (fun b : ℝ => line ε b y x.1) := by
        unfold line centered gaussian
        fun_prop
      have hh := (hc.tendsto 0).comp hz
      simpa only [line,centered,gaussian,Complex.ofReal_zero,neg_zero,zero_mul,
        Complex.exp_zero,one_mul] using hh.mul_const (f x)))
  simpa only [Lp.toLp_coeFn] using ht

theorem section_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ε y : ℝ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hz : Tendsto a l (𝓝 0)) (f : Lp Hilbert 2 μ) :
    Tendsto (fun i => (action ε (a i) (ha i) y).compLpL 2 μ f) l (𝓝 f) := by
  let B := Real.exp (y^2)
  have hBn : 0 ≤ B := (Real.exp_pos _).le
  have ha1 : ∀ᶠ i in l, a i ≤ 1 :=
    (hz.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun i hi => hi.le)
  have hb : ∀ᶠ i in l, ∀ x : Hilbert, ‖action ε (a i) (ha i) y x‖ ≤ B*‖x‖ := by
    filter_upwards [ha1] with i hi x
    exact (action_norm ε (a i) (ha i) y x).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg y])) (norm_nonneg _))
  have hF := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have ht : Tendsto (fun i => ∫ x, ‖action ε (a i) (ha i) y (f x)-f x‖^2 ∂μ) l (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := l)
      (F := fun i x => ‖action ε (a i) (ha i) y (f x)-f x‖^2)
      (f := fun _ => (0:ℝ)) (bound := fun x => (B+1)^2*‖f x‖^2)
      (Eventually.of_forall (fun i =>
        (((action ε (a i) (ha i) y).continuous.comp_aestronglyMeasurable
          (Lp.aestronglyMeasurable f)).sub (Lp.aestronglyMeasurable f)).norm.pow 2))
      (hb.mono (fun i hi => Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        have hd : ‖action ε (a i) (ha i) y (f x)-f x‖ ≤ (B+1)*‖f x‖ :=
          (norm_sub_le _ _).trans (by nlinarith [hi (f x)])
        exact (pow_le_pow_left₀ (norm_nonneg _) hd 2).trans_eq (by ring))))
      (hF.const_mul _) (Eventually.of_forall (fun x => by
        simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using
          ((action_tendsto ε y a ha hz (f x)).sub_const (f x)).norm.pow 2))
    simpa only [integral_zero] using hh
  have he (i : ι) :
      ‖(action ε (a i) (ha i) y).compLpL 2 μ f-f‖^2=
        ∫ x, ‖action ε (a i) (ha i) y (f x)-f x‖^2 ∂μ := by
    rw [KFCausalAveragedEnergyGraph.l2_norm_square]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((action ε (a i) (ha i) y).compLpL 2 μ f) f,
      (action ε (a i) (ha i) y).coeFn_compLp f] with x hs hx
    change ‖((action ε (a i) (ha i) y).compLpL 2 μ f-f) x‖^2=_
    rw [hs]
    change ‖((action ε (a i) (ha i) y).compLp f) x-f x‖^2=_
    rw [hx]
  have hn : Tendsto (fun i => ‖(action ε (a i) (ha i) y).compLpL 2 μ f-f‖^2) l (𝓝 0) := by
    simpa only [he] using ht
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs

theorem sequence_tendsto (ε y : ℝ) (f : Hilbert) :
    Tendsto (fun n : ℕ => action ε (((n:ℝ)+1)⁻¹) (by positivity) y f) atTop (𝓝 f) := by
  apply action_tendsto ε y _ _ _ f
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

#print axioms action_tendsto
#print axioms section_tendsto
#print axioms sequence_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingApproximation
