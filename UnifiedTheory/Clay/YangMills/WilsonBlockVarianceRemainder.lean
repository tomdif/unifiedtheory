/- The correlated exterior variance and local approximation error remain
explicit. A block estimate cannot silently become a global factorization. -/
import UnifiedTheory.Clay.YangMills.WilsonLocalBlockCoercivity
import UnifiedTheory.Clay.YangMills.WilsonHighFieldDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonBlockVarianceRemainder
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonHaarRefresh WilsonPhysicalVariance WilsonHighFieldDecay CompactDensityEntropy

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

/-- The actual law of total variance, with the exterior contribution retained. -/
theorem total_variance (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) :
    variance n β hβ f = heatBathEnergy n β hβ S f +
      ProbabilityTheory.variance (fiberMean n β hβ S f) (outsideLaw n β hβ S) := by
  letI := groundLaw_probability n β hβ
  letI := outsideLaw_probability n β hβ S
  have hm (g : C(Slice n, ℝ)) : (∫ r, fiberMean n β hβ S g r ∂outsideLaw n β hβ S) =
      ∫ u, g u ∂groundLaw n β hβ := disintegration n β hβ S g g.continuous
  have hv (r : Outside n S) : ProbabilityTheory.variance (fiber n S f r)
      (conditionalLaw n β hβ S r) = fiberMean n β hβ S (f^2) r-(fiberMean n β hβ S f r)^2 := by
    letI := conditionalLaw_probability n β hβ S r
    exact CompactLikelihoodVariance.variance_formula _ _ (fiber n S f r).continuous
  rw [WilsonGroundHeatBathVariance.heatBathEnergy_eq_conditional_variance n β hβ S f f.continuous]
  change variance n β hβ f =
    (∫ r, ProbabilityTheory.variance (fiber n S f r) (conditionalLaw n β hβ S r)
      ∂outsideLaw n β hβ S)+_
  simp_rw [hv]
  rw [integral_sub (continuous_integrable _ _ (fiberMean_continuous n β hβ S (f^2)))
    (continuous_integrable _ _ ((fiberMean_continuous n β hβ S f).pow 2)),
    CompactLikelihoodVariance.variance_formula _ _ (fiberMean_continuous n β hβ S f),
    hm, hm, variance_formula]
  simp only [ContinuousMap.pow_apply]
  ring

theorem variance_approximation (β : ℝ) (hβ : 0 ≤ β) (f g : C(Slice n, ℝ)) :
    variance n β hβ f ≤ 2*variance n β hβ g+2*mass n β hβ (f-g) := by
  letI := groundLaw_probability n β hβ
  let m := ∫ u, g u ∂groundLaw n β hβ
  have hi (h : C(Slice n, ℝ)) : Integrable (fun u => (h u-m)^2) (groundLaw n β hβ) :=
    continuous_integrable _ _ ((h.continuous.sub continuous_const).pow 2)
  have he := continuous_integrable (groundLaw n β hβ) _ ((f-g).continuous.pow 2)
  have hh := integral_mono (hi f) (((hi g).const_mul 2).add (he.const_mul 2))
    (fun u => show (f u-m)^2 ≤ 2*(g u-m)^2+2*((f-g) u)^2 by
      simp only [ContinuousMap.sub_apply]
      nlinarith [sq_nonneg (f u-2*g u+m)])
  simp only [Pi.add_apply] at hh
  rw [integral_add ((hi g).const_mul 2) (he.const_mul 2), integral_const_mul,
    integral_const_mul] at hh
  have hv := CompactCrossVariance.variance_le_square (groundLaw n β hβ) f f.continuous m
  simp only [variance]
  rw [ProbabilityTheory.variance_eq_integral g.continuous.measurable.aemeasurable]
  exact hv.trans hh

theorem heatBath_approximation (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f g : C(Slice n, ℝ)) :
    heatBathEnergy n β hβ S g ≤ 2*heatBathEnergy n β hβ S f+
      2*heatBathEnergy n β hβ S (f-g) := by
  letI := edgeLaw_probability n β hβ S
  have hi (h : C(Slice n, ℝ)) : Integrable (fun z : Slice n × Slice n => (h z.1-h z.2)^2)
      (edgeLaw n β hβ S) := continuous_integrable _ _
        (((h.continuous.comp continuous_fst).sub (h.continuous.comp continuous_snd)).pow 2)
  have hh := integral_mono (hi g) (((hi f).const_mul 2).add ((hi (f-g)).const_mul 2))
    (fun z => show (g z.1-g z.2)^2 ≤ 2*(f z.1-f z.2)^2+2*((f-g) z.1-(f-g) z.2)^2 by
      simp only [ContinuousMap.sub_apply]
      nlinarith [sq_nonneg (2*(f z.1-f z.2)-(g z.1-g z.2))])
  simp only [Pi.add_apply] at hh
  rw [integral_add ((hi f).const_mul 2) ((hi (f-g)).const_mul 2),
    integral_const_mul, integral_const_mul] at hh
  rw [heatBathEnergy_eq_edge n β hβ S g g.continuous,
    heatBathEnergy_eq_edge n β hβ S f f.continuous,
    heatBathEnergy_eq_edge n β hβ S (f-g) (f-g).continuous]
  simp only [ContinuousMap.sub_apply, Pi.sub_apply] at *
  linarith

/-- Source approximation is a genuine L2 error under the ground law.
Small cardinality of a field-dependent defect set is not this hypothesis. -/
theorem approximate_local_coercivity (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f g : C(Slice n, ℝ))
    (hg : WilsonLocalBlockCoercivity.Supported n S g) :
    variance n β hβ f ≤ 4*Real.exp (24*β*(S.card : ℝ))*heatBathEnergy n β hβ S f+
      (4*Real.exp (24*β*(S.card : ℝ))+2)*mass n β hβ (f-g) := by
  have hv := variance_approximation n β hβ f g
  have hg' := WilsonLocalBlockCoercivity.variance_le_heatBath n β hβ S g hg
  have he := heatBath_approximation n β hβ S f g
  have hm : variance n β hβ (f-g) ≤ mass n β hβ (f-g) := by
    rw [variance_formula, mass]
    exact sub_le_self _ (sq_nonneg _)
  have hr := (WilsonGroundVarianceBudget.heatBathEnergy_le_variance n β hβ S (f-g)).trans hm
  have hp := Real.exp_pos (24*β*(S.card : ℝ))
  change heatBathEnergy n β hβ S (f-g) ≤ _ at hr
  change heatBathEnergy n β hβ S g ≤ 2*heatBathEnergy n β hβ S f+
    2*heatBathEnergy n β hβ S (f-g) at he
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonBlockVarianceRemainder
