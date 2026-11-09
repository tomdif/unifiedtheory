/- The constructed Wilson block heat-bath Dirichlet form is exactly the
average of its actual conditional variances. No variance factorization or
mixing constant is assumed or established here. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundHeatBath
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonGroundHeatBathVariance
noncomputable section
open MeasureTheory ProbabilityTheory WilsonSlabOperator WilsonTimeSlab WilsonGroundHeatBath

/-- Two independent draws give twice the variance, with probability normalization explicit. -/
theorem iid_square_variance {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : Continuous f) :
    (1 / 2) * (∫ a, ∫ b, (f a - f b) ^ 2 ∂μ ∂μ) = variance f μ := by
  have hL : MemLp f 2 μ := hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi := hf.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hm : (∫ z : X × X, f z.1 - f z.2 ∂μ.prod μ) = 0 := by
    rw [integral_sub (hi.comp_fst μ) (hi.comp_snd μ), integral_fun_fst, integral_fun_snd]
    simp
  have hv := variance_add_prod hL hL.neg
  simp only [Pi.neg_apply, ← sub_eq_add_neg, variance_neg] at hv
  rw [variance_eq_integral (X := fun z : X × X => f z.1 - f z.2)
    ((hf.comp continuous_fst).sub
    (hf.comp continuous_snd)).measurable.aemeasurable, hm] at hv
  simp only [sub_zero] at hv
  have hc : Continuous (fun z : X × X => (f z.1 - f z.2) ^ 2) :=
    ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).pow 2
  rw [← integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  linarith

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

/-- The explicit edge density is the actual retained marginal mass times
 two independent draws from its normalized conditional law. -/
theorem conditional_pair_integral (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S)
    (F : Inside n S × Inside n S → ℝ) :
    (∫ a, ∫ b, edgeDensity n β hβ S (r, a, b) * F (a, b)
      ∂insideHaar n S ∂insideHaar n S) =
      fiberMass n β hβ S r *
        ∫ a, ∫ b, F (a, b) ∂conditionalLaw n β hβ S r ∂conditionalLaw n β hβ S r := by
  have hc : (∫ a, ∫ b, F (a, b)
      ∂conditionalLaw n β hβ S r ∂conditionalLaw n β hβ S r) =
      (∫ a, weight n β hβ S (r, a) *
        ((∫ b, weight n β hβ S (r, b) * F (a, b) ∂insideHaar n S) /
          fiberMass n β hβ S r) ∂insideHaar n S) / fiberMass n β hβ S r := by
    simp only [conditionalLaw_integral, conditionalDensity, div_mul_eq_mul_div,
      ← mul_div_assoc, integral_div]
  rw [hc, mul_div_cancel₀ _ (fiberMass_positive n β hβ S r).ne']
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  dsimp only
  have he (b : Inside n S) : edgeDensity n β hβ S (r, a, b) * F (a, b) =
      weight n β hβ S (r, a) * (weight n β hβ S (r, b) * F (a, b)) /
        fiberMass n β hβ S r := by unfold edgeDensity; ring
  simp_rw [he]
  rw [integral_div, integral_const_mul]
  ring

/-- An exact conditional-product representation of the actual reversible edge law. -/
theorem edge_integral_conditionals (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (F : Slice n × Slice n → ℝ) (hF : Continuous F) :
    (∫ z, F z ∂edgeLaw n β hβ S) =
      ∫ r, ∫ a, ∫ b, F (pairMap n S (r, a, b))
        ∂conditionalLaw n β hβ S r ∂conditionalLaw n β hβ S r ∂outsideLaw n β hβ S := by
  rw [edge_integral n β hβ S F hF, outsideLaw,
    LocalGibbsComparison.weighted_integral _ _ (fiberMass_continuous n β hβ S).measurable
      (fun r => (fiberMass_positive n β hβ S r).le)
      (by rw [fiberMass_integral]; norm_num), fiberMass_integral, div_one]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  exact conditional_pair_integral n β hβ S r (fun ab => F (pairMap n S (r, ab)))

/-- The block Dirichlet form is the average actual conditional variance,
with no replacement product ground law and no missing clock factor. -/
theorem heatBathEnergy_eq_conditional_variance (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (F : Slice n → ℝ) (hF : Continuous F) :
    heatBathEnergy n β hβ S F =
      ∫ r, variance (fun a => F (WilsonBlockMarginal.assemble S (r, a)))
        (conditionalLaw n β hβ S r) ∂outsideLaw n β hβ S := by
  rw [heatBathEnergy_eq_edge n β hβ S F hF,
    edge_integral_conditionals n β hβ S (fun z => (F z.1 - F z.2) ^ 2)
      (((hF.comp continuous_fst).sub (hF.comp continuous_snd)).pow 2), ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  letI := conditionalLaw_probability n β hβ S r
  exact iid_square_variance (conditionalLaw n β hβ S r)
    (fun a => F (WilsonBlockMarginal.assemble S (r, a)))
    (hF.comp ((WilsonBlockMarginal.assemble_continuous S).comp
      (continuous_const.prodMk continuous_id)))


/-- The same form is the mean-square residual of the actual conditional update. -/
theorem heatBathEnergy_eq_projection_residual (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (F : Slice n → ℝ) (hF : Continuous F) :
    heatBathEnergy n β hβ S F =
      ∫ U, (F U - ∫ V, F V ∂updateLaw n β hβ S U) ^ 2 ∂groundLaw n β hβ := by
  have hm : Continuous (fun U => ∫ V, F V ∂updateLaw n β hβ S U) :=
    update_joint_continuous n β hβ S (fun z => F z.2) (hF.comp continuous_snd)
  rw [heatBathEnergy_eq_conditional_variance n β hβ S F hF]
  calc
    _ = ∫ r, ∫ a, (F (WilsonBlockMarginal.assemble S (r, a)) -
        ∫ V, F V ∂updateLaw n β hβ S (WilsonBlockMarginal.assemble S (r, a))) ^ 2
          ∂conditionalLaw n β hβ S r ∂outsideLaw n β hβ S := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro r
      have hc : Continuous (fun a : Inside n S => F (WilsonBlockMarginal.assemble S (r, a))) :=
        hF.comp ((WilsonBlockMarginal.assemble_continuous S).comp
          (continuous_const.prodMk continuous_id))
      dsimp only
      rw [variance_eq_integral hc.measurable.aemeasurable]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a
      dsimp only
      rw [updateLaw_integral n β hβ S _ F hF]
      simp only [updateMap, outsideProjection_assemble]
    _ = _ := disintegration n β hβ S
      (fun U => (F U - ∫ V, F V ∂updateLaw n β hβ S U) ^ 2) ((hF.sub hm).pow 2)

end
end UnifiedTheory.Clay.YangMills.WilsonGroundHeatBathVariance
