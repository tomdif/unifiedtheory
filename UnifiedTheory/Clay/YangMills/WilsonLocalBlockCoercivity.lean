/- Full block updates control every observable supported in that block,
including physical defect observables. The explicit heat-bath constant
depends on beta and block size, never on exterior volume. -/
import UnifiedTheory.Clay.YangMills.CompactWeightedCenter
import UnifiedTheory.Clay.YangMills.WilsonGroundVarianceBudget
import UnifiedTheory.Clay.YangMills.WilsonHeatBathComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonLocalBlockCoercivity
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonHaarRefresh WilsonPhysicalVariance CompactDensityEntropy

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

/-- Support here means dependence on the listed link coordinates. -/
def Supported (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) : Prop :=
  ∀ u v : Slice n, (∀ e ∈ S, u e = v e) → f u = f v

omit [NeZero n] in
theorem supported_mono (S T : Finset (SpatialVertex n × Fin 3)) (hST : S ⊆ T)
    (f : C(Slice n, ℝ)) (hf : Supported n S f) : Supported n T f :=
  fun u v h => hf u v (fun e he => h e (hST he))

def reference (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) :
    C(Inside n S, ℝ) := fiber n S f 1

omit [NeZero n] in
theorem supported_fiber (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ))
    (hf : Supported n S f) (r : Outside n S) (a : Inside n S) :
    f (WilsonBlockMarginal.assemble S (r,a)) = reference n S f a := by
  apply hf
  intro e he
  simp only [WilsonBlockMarginal.assemble_inside S _ e he]

omit [NeZero n] in
theorem supported_update (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ))
    (hf : Supported n S f) (u : Slice n) (a : Inside n S) :
    f (updateMap n S u a) = reference n S f a :=
  supported_fiber n S f hf _ a

/-- Full Haar refresh sees all block coordinates, including defective ones. -/
theorem haar_decomposition (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) (hf : Supported n S f) :
    energy n β hβ S f = variance n β hβ f +
      ProbabilityTheory.variance (reference n S f) (insideHaar n S) +
        ((∫ u, f u ∂groundLaw n β hβ)-∫ a, reference n S f a ∂insideHaar n S)^2 := by
  letI := groundLaw_probability n β hβ
  unfold energy refreshAt
  simp_rw [supported_update n S f hf]
  rw [integral_integral_swap (f := fun u a => (f u-reference n S f a)^2)
    (continuous_integrable ((groundLaw n β hβ).prod (insideHaar n S)) _
      (((f.continuous.comp continuous_fst).sub
        ((reference n S f).continuous.comp continuous_snd)).pow 2))]
  exact CompactCrossVariance.cross_square_decomposition (groundLaw n β hβ) (insideHaar n S)
    f f.continuous (reference n S f) (reference n S f).continuous

theorem variance_le_haar (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) (hf : Supported n S f) :
    variance n β hβ f ≤ energy n β hβ S f := by
  rw [haar_decomposition n β hβ S f hf]
  have h := ProbabilityTheory.variance_nonneg (reference n S f) (insideHaar n S)
  nlinarith [sq_nonneg ((∫ u, f u ∂groundLaw n β hβ)-∫ a, reference n S f a ∂insideHaar n S)]

theorem weight_ratio (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (a b : Inside n S) :
    weight n β hβ S (r,a) ≤ Real.exp (24*β*(S.card : ℝ))*weight n β hβ S (r,b) := by
  have hh := WilsonGroundLocalComparison.ground_block n β hβ S
    (WilsonBlockMarginal.assemble S (r,a)) (WilsonBlockMarginal.assemble S (r,b)) (by
      intro e he
      simp only [WilsonBlockMarginal.assemble_outside S _ e he])
  have hs := sq_le_sq₀ (WilsonGroundLocalComparison.ground_pos n β hβ _).le
    (mul_pos (Real.exp_pos _) (WilsonGroundLocalComparison.ground_pos n β hβ _)).le |>.mpr hh
  have he : (Real.exp (12*β*(S.card : ℝ)))^2 = Real.exp (24*β*(S.card : ℝ)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [weight, mul_pow, he] using hs

theorem conditional_ratio (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (a b : Inside n S) :
    conditionalDensity n β hβ S r a ≤
      Real.exp (24*β*(S.card : ℝ))*conditionalDensity n β hβ S r b := by
  simpa only [conditionalDensity, mul_div_assoc] using
    div_le_div_of_nonneg_right (weight_ratio n β hβ S r a b) (fiberMass_positive n β hβ S r).le

/-- The reference center is independent of the exterior for a supported source. -/
theorem fiber_center_comparison (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ))
    (hf : Supported n S f) (r : Outside n S) :
    (∫ a, (f (WilsonBlockMarginal.assemble S (r,a))-
      ∫ b, reference n S f b ∂insideHaar n S)^2 ∂conditionalLaw n β hβ S r) ≤
      Real.exp (24*β*(S.card : ℝ))*
        ProbabilityTheory.variance (fiber n S f r) (conditionalLaw n β hβ S r) := by
  have hcont : Continuous (conditionalDensity n β hβ S r) :=
    ((weight_continuous n β hβ S).comp (continuous_const.prodMk continuous_id)).div_const _
  have hh := CompactWeightedCenter.center_comparison (insideHaar n S)
    (conditionalDensity n β hβ S r) (reference n S f) hcont (reference n S f).continuous
    (fun a => (conditionalDensity_positive n β hβ S r a).le)
    (Real.exp (24*β*(S.card : ℝ))) (Real.exp_pos _).le (conditional_ratio n β hβ S r)
    (fiberMean n β hβ S f r)
  rw [ProbabilityTheory.variance_eq_integral (fiber n S f r).continuous.measurable.aemeasurable,
    conditionalLaw_integral, conditionalLaw_integral]
  simp only [fiberMean, fiber, ContinuousMap.coe_mk, supported_fiber n S f hf] at *
  exact hh

/-- A genuine finite-block lower comparison. Its weak-coupling exponential
is explicit; this is not a global variance factorization. -/
theorem variance_le_heatBath (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) (hf : Supported n S f) :
    variance n β hβ f ≤ Real.exp (24*β*(S.card : ℝ))*heatBathEnergy n β hβ S f := by
  letI := groundLaw_probability n β hβ
  letI := outsideLaw_probability n β hβ S
  let m := ∫ a, reference n S f a ∂insideHaar n S
  let F : C(Slice n, ℝ) := ⟨fun u => (f u-m)^2, (f.continuous.sub continuous_const).pow 2⟩
  have hh := integral_mono
    (continuous_integrable (outsideLaw n β hβ S) _ (fiberMean_continuous n β hβ S F))
    ((continuous_integrable (outsideLaw n β hβ S) _ (fiberVariance_continuous n β hβ S f)).const_mul
      (Real.exp (24*β*(S.card : ℝ)))) (fiber_center_comparison n β hβ S f hf)
  change (∫ r, ∫ a, F (WilsonBlockMarginal.assemble S (r,a))
      ∂conditionalLaw n β hβ S r ∂outsideLaw n β hβ S) ≤ _ at hh
  rw [disintegration n β hβ S _ F.continuous, integral_const_mul] at hh
  simp only [fiber, ContinuousMap.coe_mk] at hh
  rw [← WilsonGroundHeatBathVariance.heatBathEnergy_eq_conditional_variance
    n β hβ S f f.continuous] at hh
  exact (CompactCrossVariance.variance_le_square (groundLaw n β hβ) f f.continuous m).trans hh

theorem heatBath_positive (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) (hf : Supported n S f)
    (u v : Slice n) (hne : f u ≠ f v) : 0 < heatBathEnergy n β hβ S f := by
  have hv := WilsonGroundVarianceBudget.variance_positive n β hβ f u v hne
  have hh := variance_le_heatBath n β hβ S f hf
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp (hv.trans_le hh)

theorem variance_le_transferEnergy (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) (hf : Supported n S f) :
    variance n β hβ f ≤ Real.exp (24*β*(S.card : ℝ))*
      (1+Real.exp (12*β*(S.card : ℝ)))^2*WilsonHeatBathComparison.transferEnergy n β hβ f := by
  calc
    _ ≤ Real.exp (24*β*(S.card : ℝ))*heatBathEnergy n β hβ S f :=
      variance_le_heatBath n β hβ S f hf
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (WilsonHeatBathComparison.heatBathEnergy_le_transferEnergy n β hβ S f) (Real.exp_pos _).le

end
end UnifiedTheory.Clay.YangMills.WilsonLocalBlockCoercivity
