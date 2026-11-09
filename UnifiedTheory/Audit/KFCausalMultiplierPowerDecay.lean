/- A pointwise strictly contractive multiplier has strongly vanishing
iterates on L2. No uniform gap below one is required. -/
import UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalMultiplierPowerDecay
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy (l2_norm_square)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (m : X → ℂ)
  (hA : ∀ f : Lp ℂ 2 μ, A f =ᵐ[μ] fun x => m x*f x)

include hA

theorem iterate_coe (n : ℕ) (f : Lp ℂ 2 μ) :
    (A : Lp ℂ 2 μ → Lp ℂ 2 μ)^[n] f =ᵐ[μ] fun x => m x^n*f x := by
  induction n with
  | zero => filter_upwards [] with x; simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      filter_upwards [hA ((A : Lp ℂ 2 μ → Lp ℂ 2 μ)^[n] f),ih] with x hx hn
      rw [hx,hn,pow_succ']
      ring

theorem iterate_norm (hb : ∀ x, ‖m x‖ ≤ 1) (n : ℕ) (f : Lp ℂ 2 μ) :
    ‖(A : Lp ℂ 2 μ → Lp ℂ 2 μ)^[n] f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [iterate_coe A m hA n f] with x hx
  rw [hx,norm_mul,norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hb x))

theorem iterate_tendsto_zero (hm : Measurable m) (hb : ∀ x, ‖m x‖ < 1) (f : Lp ℂ 2 μ) :
    Tendsto (fun n : ℕ => (A : Lp ℂ 2 μ → Lp ℂ 2 μ)^[n] f) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => ∫ x, ‖m x^n*f x‖^2 ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖^2)
      (fun n : ℕ => (((hm.pow_const n).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)).norm.pow 2))
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f))
      (fun n => Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _)
        simp only [Pi.mul_apply]
        rw [norm_mul,norm_pow]
        exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hb x).le)))
      (Filter.Eventually.of_forall (fun x => by
        have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hb x)).mul_const (f x)
        simpa only [zero_mul,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using hp.norm.pow 2))
    simpa only [integral_zero] using ht
  have hs : Tendsto (fun n : ℕ => ‖(A : Lp ℂ 2 μ → Lp ℂ 2 μ)^[n] f‖^2) atTop (𝓝 0) := by
    convert hi using 1
    funext n
    rw [l2_norm_square]
    apply integral_congr_ae
    filter_upwards [iterate_coe A m hA n f] with x hx
    rw [hx]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,sub_zero,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hs

#print axioms iterate_coe
#print axioms iterate_norm
#print axioms iterate_tendsto_zero

end
end UnifiedTheory.Audit.KFCausalMultiplierPowerDecay
