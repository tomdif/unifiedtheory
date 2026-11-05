/- Stability of the source error under subleading coupling corrections.
The hypothesis is convergence of beta/log(1/a) to a specified slope, not
identification of that slope with a physical Yang--Mills trajectory. -/
import UnifiedTheory.Clay.YangMills.HybridSourceApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CouplingTrajectoryRobustness
noncomputable section
open Filter Topology

/-- The rescaled local error, with logarithmic scale and coupling independent. -/
def rescaledError (t β r : ℝ) : ℝ :=
  Real.exp (4 * t) * β ^ 2 * Real.exp (-4 * β * r)

theorem rescaledError_nonneg (t β r : ℝ) : 0 ≤ rescaledError t β r := by
  unfold rescaledError
  positivity

theorem rescaledError_eq (t β r : ℝ) :
    rescaledError t β r = β ^ 2 * Real.exp (4 * t - 4 * β * r) := by
  unfold rescaledError
  rw [show Real.exp (4 * t) * β ^ 2 * Real.exp (-4 * β * r) =
    β ^ 2 * (Real.exp (4 * t) * Real.exp (-4 * β * r)) by ring,
    ← Real.exp_add]
  congr 2
  ring

/-- Any coupling with the same limiting slope has the same strict-margin
error decay. The scale may be indexed by any filter. -/
theorem rescaledError_tendsto {ι : Type*} {l : Filter ι}
    (t β : ι → ℝ) (b r : ℝ)
    (ht : Tendsto t l atTop) (hβ : Tendsto (fun i => β i / t i) l (𝓝 b))
    (hmargin : 1 < b * r) :
    Tendsto (fun i => rescaledError (t i) (β i) r) l (𝓝 0) := by
  let δ : ℝ := (4 * b * r - 4) / 2
  have hδ : 0 < δ := by dsimp [δ]; nlinarith
  have he : Tendsto (fun i => 4 - 4 * r * (β i / t i)) l (𝓝 (4 - 4 * r * b)) :=
    tendsto_const_nhds.sub (hβ.const_mul (4 * r))
  have hm : 4 - 4 * r * b < -δ := by dsimp [δ]; nlinarith
  have hbound : ∀ᶠ i in l,
      t i ^ 2 * Real.exp (4 * t i - 4 * β i * r) ≤
        t i ^ 2 * Real.exp (-δ * t i) := by
    filter_upwards [ht.eventually_gt_atTop 0, he.eventually_lt_const hm] with i hi hei
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have hid : 4 * t i - 4 * β i * r = (4 - 4 * r * (β i / t i)) * t i := by
      field_simp
    rw [hid]
    exact mul_le_mul_of_nonneg_right hei.le hi.le
  have hpoly : Tendsto (fun i => t i ^ 2 * Real.exp (-δ * t i)) l (𝓝 0) := by
    simpa only [Real.rpow_two, Function.comp_apply] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 δ hδ).comp ht
  have hsmall : Tendsto (fun i => t i ^ 2 * Real.exp (4 * t i - 4 * β i * r))
      l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) hbound hpoly
  have hprod := (hβ.pow 2).mul hsmall
  simp only [mul_zero] at hprod
  apply hprod.congr'
  filter_upwards [ht.eventually_gt_atTop 0] with i hi
  rw [rescaledError_eq]
  field_simp

/-- The logarithmic scale of any positive cutoff tending to zero diverges. -/
theorem log_inverse_tendsto {ι : Type*} {l : Filter ι} (a : ι → ℝ)
    (ha : Tendsto a l (𝓝[>] 0)) :
    Tendsto (fun i => Real.log (a i)⁻¹) l atTop :=
  Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp ha)

/-- The actual cutoff rescaling agrees with the logarithmic parameterization. -/
theorem cutoffError_eq {a : ℝ} (ha : 0 < a) (β r : ℝ) :
    (a ^ 4)⁻¹ * β ^ 2 * Real.exp (-4 * β * r) =
      rescaledError (Real.log a⁻¹) β r := by
  unfold rescaledError
  have he : Real.exp (4 * Real.log a⁻¹) = (a ^ 4)⁻¹ := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.exp_nat_mul, Real.exp_log (inv_pos.mpr ha), inv_pow]
  rw [he]

/-- The strict-margin estimate survives all subleading corrections in beta.
Neither the physical slope nor existence of an interacting limit is asserted. -/
theorem cutoffError_tendsto {ι : Type*} {l : Filter ι}
    (a β : ι → ℝ) (b r : ℝ) (ha : Tendsto a l (𝓝[>] 0))
    (hβ : Tendsto (fun i => β i / Real.log (a i)⁻¹) l (𝓝 b))
    (hmargin : 1 < b * r) :
    Tendsto (fun i => (a i ^ 4)⁻¹ * β i ^ 2 * Real.exp (-4 * β i * r)) l (𝓝 0) := by
  have h := rescaledError_tendsto (fun i => Real.log (a i)⁻¹) β b r
    (log_inverse_tendsto a ha) hβ hmargin
  apply h.congr'
  filter_upwards [ha.eventually self_mem_nhdsWithin] with i hi
  exact (cutoffError_eq hi (β i) r).symm

/-- A positive limiting logarithmic slope forces the coupling to diverge. -/
theorem coupling_tendsto_atTop {ι : Type*} {l : Filter ι}
    (a β : ι → ℝ) (b : ℝ) (hb : 0 < b) (ha : Tendsto a l (𝓝[>] 0))
    (hβ : Tendsto (fun i => β i / Real.log (a i)⁻¹) l (𝓝 b)) :
    Tendsto β l atTop := by
  have ht := log_inverse_tendsto a ha
  have h := hβ.pos_mul_atTop hb ht
  apply h.congr'
  filter_upwards [ht.eventually_gt_atTop 0] with i hi
  exact div_mul_cancel₀ _ hi.ne'

/-- A sublinear additive correction does not change the limiting slope. -/
theorem slope_of_sublinear {ι : Type*} {l : Filter ι}
    (t δ : ι → ℝ) (b : ℝ) (ht : Tendsto t l atTop)
    (hδ : Tendsto (fun i => δ i / t i) l (𝓝 0)) :
    Tendsto (fun i => (b * t i + δ i) / t i) l (𝓝 b) := by
  have h : Tendsto (fun i => b + δ i / t i) l (𝓝 (b + 0)) :=
    tendsto_const_nhds.add hδ
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [ht.eventually_gt_atTop 0] with i hi
  field_simp

/-- Logarithmic corrections in log(1/a), of either sign, preserve the slope. -/
theorem log_corrected_slope (b c d : ℝ) :
    Tendsto (fun t : ℝ => (b * t + c * Real.log t + d) / t) atTop (𝓝 b) := by
  have hc : Tendsto (fun t : ℝ => c * Real.log t / t) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul c
  have hd : Tendsto (fun t : ℝ => d / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hs := slope_of_sublinear id (fun t => c * Real.log t + d) b tendsto_id
    (by simpa only [add_div, add_zero, id_eq] using hc.add hd)
  simpa only [id_eq, add_assoc] using hs

theorem log_corrected_error_tendsto (b c d r : ℝ) (hmargin : 1 < b * r) :
    Tendsto (fun t : ℝ => rescaledError t (b * t + c * Real.log t + d) r)
      atTop (𝓝 0) :=
  rescaledError_tendsto id _ b r tendsto_id (log_corrected_slope b c d) hmargin

/-- A norm error bounded by the actual rescaled expression vanishes on the
same trajectory; no boundedness or positivity of a continuum field follows. -/
theorem cutoff_norm_error_tendsto {ι E : Type*} {l : Filter ι}
    [NormedAddCommGroup E] (a β : ι → ℝ) (b r C : ℝ) (F : ι → E)
    (ha : Tendsto a l (𝓝[>] 0))
    (hβ : Tendsto (fun i => β i / Real.log (a i)⁻¹) l (𝓝 b))
    (hmargin : 1 < b * r)
    (hF : ∀ᶠ i in l,
      ‖F i‖ ≤ C * ((a i ^ 4)⁻¹ * β i ^ 2 * Real.exp (-4 * β i * r))) :
    Tendsto F l (𝓝 0) := by
  apply squeeze_zero_norm' hF
  simpa only [mul_zero] using (cutoffError_tendsto a β b r ha hβ hmargin).const_mul C

/-- The continuous exact/approximate source splitting works for a general
positive cutoff and any coupling with a strict limiting slope margin. -/
theorem cutoff_hybrid_error_tendsto {ι E : Type*} {l : Filter ι}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a β radius : ι → ℝ) (b r₀ r₁ C : ℝ) (Y P : ι → E)
    (ha : Tendsto a l (𝓝[>] 0))
    (hβ : Tendsto (fun i => β i / Real.log (a i)⁻¹) l (𝓝 b))
    (hcut : r₀ < r₁) (hC : 0 ≤ C) (hmargin : 1 < b * r₀)
    (hgood : ∀ᶠ i in l, r₀ ≤ radius i →
      ‖Y i - P i‖ ≤ C * β i ^ 2 * Real.exp (-4 * β i * r₀)) :
    Tendsto (fun i => (a i ^ 4)⁻¹ •
      (Y i - HybridSourceApproximation.hybrid r₀ r₁ (radius i) (Y i) (P i)))
      l (𝓝 0) := by
  apply cutoff_norm_error_tendsto a β b r₀ C _ ha hβ hmargin
  filter_upwards [hgood] with i hi
  have hε : 0 ≤ C * β i ^ 2 * Real.exp (-4 * β i * r₀) := by positivity
  have hs : 0 ≤ (a i ^ 4)⁻¹ := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  calc
    _ ≤ (a i ^ 4)⁻¹ * (C * β i ^ 2 * Real.exp (-4 * β i * r₀)) :=
      mul_le_mul_of_nonneg_left
        (HybridSourceApproximation.hybrid_error_le r₀ r₁ (radius i) _ hcut hε
          (Y i) (P i) hi) hs
    _ = _ := by ring

end
end UnifiedTheory.Clay.YangMills.CouplingTrajectoryRobustness
