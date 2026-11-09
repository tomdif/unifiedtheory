/- Contractive strongly vanishing powers remain strongly vanishing after
pointwise lifting to vector-valued L2. No uniform convergence rate or
finite-measure hypothesis is used. -/
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph
import UnifiedTheory.Audit.KFCausalInvariantRangeCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalLpStrongPowerDecay
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)
open UnifiedTheory.Audit.KFCausalInvariantRangeCore (residual)

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem residual_compLpL (R : E →L[ℂ] E) :
    (residual R).compLpL 2 μ = residual (R.compLpL 2 μ) := by
  apply ContinuousLinearMap.ext
  intro f
  change (residual R).compLp f = f-R.compLp f
  apply Lp.ext
  filter_upwards [(residual R).coeFn_compLp f,R.coeFn_compLp f,Lp.coeFn_sub f (R.compLp f)]
    with x hr hR hs
  rw [hr,hs]
  simp only [Pi.sub_apply,hR]
  rfl

theorem iterate_coe (R : E →L[ℂ] E) (n : ℕ) (f : Lp E 2 μ) :
    (R.compLpL 2 μ : Lp E 2 μ → Lp E 2 μ)^[n] f =ᵐ[μ] fun x => (R : E → E)^[n] (f x) := by
  induction n with
  | zero => exact Filter.EventuallyEq.rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      filter_upwards [R.coeFn_compLpL ((R.compLpL 2 μ : Lp E 2 μ → Lp E 2 μ)^[n] f),ih] with x hr hn
      rw [hr,hn,Function.iterate_succ_apply']

theorem iterate_norm (R : E →L[ℂ] E) (hR : ∀ y, ‖R y‖ ≤ ‖y‖) (n : ℕ) (f : Lp E 2 μ) :
    ‖(R.compLpL 2 μ : Lp E 2 μ → Lp E 2 μ)^[n] f‖ ≤ ‖f‖ := by
  have hL (g : Lp E 2 μ) : ‖R.compLpL 2 μ g‖ ≤ ‖g‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [R.coeFn_compLpL g] with x hx
    rw [hx]
    exact hR _
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (hL _).trans ih

theorem iterate_tendsto_zero (R : E →L[ℂ] E) (hR : ∀ y, ‖R y‖ ≤ ‖y‖)
    (hdec : ∀ y, Tendsto (fun n : ℕ => (R : E → E)^[n] y) atTop (𝓝 0)) (f : Lp E 2 μ) :
    Tendsto (fun n : ℕ => (R.compLpL 2 μ : Lp E 2 μ → Lp E 2 μ)^[n] f) atTop (𝓝 0) := by
  have hp (n : ℕ) (y : E) : ‖(R : E → E)^[n] y‖ ≤ ‖y‖ := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (hR _).trans ih
  have hi : Tendsto (fun n : ℕ => ∫ x, ‖(R : E → E)^[n] (f x)‖^2 ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖^2)
      (fun n : ℕ => (((R.continuous.iterate n).comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).norm.pow 2))
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f))
      (fun n => Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hp n (f x)) 2))
      (Filter.Eventually.of_forall (fun x => by
        simpa only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using (hdec (f x)).norm.pow 2))
    simpa only [integral_zero] using ht
  have hs : Tendsto (fun n : ℕ => ‖(R.compLpL 2 μ : Lp E 2 μ → Lp E 2 μ)^[n] f‖^2) atTop (𝓝 0) := by
    convert hi using 1
    funext n
    rw [l2_norm_square μ]
    apply integral_congr_ae
    filter_upwards [iterate_coe R n f] with x hx
    rw [hx]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,sub_zero,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hs

theorem residual_tendsto_zero (R : E →L[ℂ] E)
    (hR : ∀ x, ‖residual R x‖ ≤ ‖x‖)
    (hdec : ∀ x, Tendsto (fun n : ℕ => (residual R : E → E)^[n] x) atTop (𝓝 0))
    (f : Lp E 2 μ) :
    Tendsto (fun n : ℕ => (residual (R.compLpL 2 μ) : Lp E 2 μ → Lp E 2 μ)^[n] f)
      atTop (𝓝 0) := by
  rw [← residual_compLpL]
  exact iterate_tendsto_zero (residual R) hR hdec f

theorem residual_norm (R : E →L[ℂ] E) (hR : ∀ x, ‖residual R x‖ ≤ ‖x‖)
    (f : Lp E 2 μ) : ‖residual (R.compLpL 2 μ) f‖ ≤ ‖f‖ := by
  rw [← residual_compLpL]
  exact iterate_norm (residual R) hR 1 f

#print axioms residual_tendsto_zero
#print axioms residual_norm

#print axioms residual_compLpL
#print axioms iterate_coe
#print axioms iterate_norm
#print axioms iterate_tendsto_zero

end
end UnifiedTheory.Audit.KFCausalLpStrongPowerDecay
