/- Haar refresh of a true spatial block dominates its actual ground-law
conditional variance with coefficient one, at every nonnegative coupling.
This is a local comparison, not a global variance factorization. -/
import UnifiedTheory.Clay.YangMills.CompactCrossVariance
import UnifiedTheory.Clay.YangMills.WilsonGroundHeatBathVariance
import UnifiedTheory.Clay.YangMills.WilsonDissipationIteration

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonHaarRefresh
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open CompactDensityEntropy

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def fiber (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ))
    (r : Outside n S) : C(Inside n S, ℝ) :=
  ⟨fun a => f (WilsonBlockMarginal.assemble S (r, a)),
    f.continuous.comp ((WilsonBlockMarginal.assemble_continuous S).comp
      (continuous_const.prodMk continuous_id))⟩

def fiberMean (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (f : C(Slice n, ℝ)) (r : Outside n S) : ℝ :=
  ∫ a, fiber n S f r a ∂conditionalLaw n β hβ S r

theorem fiberMean_continuous (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) :
    Continuous (fiberMean n β hβ S f) := by
  have he : fiberMean n β hβ S f = fun r =>
      (∫ a, weight n β hβ S (r, a) * f (WilsonBlockMarginal.assemble S (r, a))
        ∂insideHaar n S) / fiberMass n β hβ S r := by
    funext r
    simp only [fiberMean, conditionalLaw_integral, conditionalDensity, fiber,
      ContinuousMap.coe_mk, div_mul_eq_mul_div, integral_div]
  rw [he]
  exact (GibbsMarginalTower.fiber_integral_continuous (insideHaar n S) _
    ((weight_continuous n β hβ S).mul
      (f.continuous.comp (WilsonBlockMarginal.assemble_continuous S)))).div
    (fiberMass_continuous n β hβ S) (fun r => (fiberMass_positive n β hβ S r).ne')

def refreshAt (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ))
    (U : Slice n) : ℝ :=
  ∫ b, (f U-f (updateMap n S U b))^2 ∂insideHaar n S

theorem refreshAt_continuous (S : Finset (SpatialVertex n × Fin 3))
    (f : C(Slice n, ℝ)) : Continuous (refreshAt n S f) :=
  GibbsMarginalTower.fiber_integral_continuous (insideHaar n S) _
    (((f.continuous.comp continuous_fst).sub
      (f.continuous.comp (updateMap_continuous n S))).pow 2)

def energy (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (f : C(Slice n, ℝ)) : ℝ := ∫ U, refreshAt n S f U ∂groundLaw n β hβ

theorem energy_nonneg (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (f : C(Slice n, ℝ)) : 0 ≤ energy n β hβ S f :=
  integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))

def remainderAt (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (f : C(Slice n, ℝ)) (r : Outside n S) : ℝ :=
  ∫ b, (fiberMean n β hβ S f r-fiber n S f r b)^2 ∂insideHaar n S

theorem remainderAt_nonneg (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) (r : Outside n S) :
    0 ≤ remainderAt n β hβ S f r := integral_nonneg (fun _ => sq_nonneg _)

theorem remainderAt_continuous (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) :
    Continuous (remainderAt n β hβ S f) :=
  GibbsMarginalTower.fiber_integral_continuous (insideHaar n S) _
    ((((fiberMean_continuous n β hβ S f).comp continuous_fst).sub
      (f.continuous.comp (WilsonBlockMarginal.assemble_continuous S))).pow 2)

theorem fiberVariance_continuous (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) :
    Continuous (fun r => ProbabilityTheory.variance (fiber n S f r)
      (conditionalLaw n β hβ S r)) := by
  have he (r : Outside n S) : ProbabilityTheory.variance (fiber n S f r)
      (conditionalLaw n β hβ S r) =
        fiberMean n β hβ S (f^2) r-(fiberMean n β hβ S f r)^2 := by
    letI := conditionalLaw_probability n β hβ S r
    exact CompactLikelihoodVariance.variance_formula _ _ (fiber n S f r).continuous
  simp_rw [he]
  exact (fiberMean_continuous n β hβ S (f^2)).sub
    ((fiberMean_continuous n β hβ S f).pow 2)

/-- The reference draw is independent only inside a fixed true exterior. -/
theorem conditional_decomposition (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) (r : Outside n S) :
    (∫ a, refreshAt n S f (WilsonBlockMarginal.assemble S (r, a))
      ∂conditionalLaw n β hβ S r) =
        ProbabilityTheory.variance (fiber n S f r) (conditionalLaw n β hβ S r) +
          remainderAt n β hβ S f r := by
  letI := conditionalLaw_probability n β hβ S r
  have he (a b : Inside n S) :
      updateMap n S (WilsonBlockMarginal.assemble S (r, a)) b =
        WilsonBlockMarginal.assemble S (r, b) := by
    unfold updateMap
    rw [WilsonGroundHeatBath.outsideProjection_assemble n S (r, a)]
  simp only [refreshAt, he]
  have hc : Continuous (fun z : Inside n S × Inside n S =>
      (fiber n S f r z.1-fiber n S f r z.2)^2) :=
    (((fiber n S f r).continuous.comp continuous_fst).sub
      ((fiber n S f r).continuous.comp continuous_snd)).pow 2
  change (∫ a, ∫ b, (fiber n S f r a-fiber n S f r b)^2
    ∂insideHaar n S ∂conditionalLaw n β hβ S r) = _
  rw [integral_integral_swap (f := fun a b => (fiber n S f r a-fiber n S f r b)^2)
    (continuous_integrable
    ((conditionalLaw n β hβ S r).prod (insideHaar n S)) _ hc)]
  exact CompactCrossVariance.cross_square (conditionalLaw n β hβ S r) (insideHaar n S)
    (fiber n S f r) (fiber n S f r).continuous (fiber n S f r) (fiber n S f r).continuous

/-- No density comparison or coupling-dependent constant is needed. -/
theorem energy_decomposition (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) :
    energy n β hβ S f = heatBathEnergy n β hβ S f +
      ∫ r, remainderAt n β hβ S f r ∂outsideLaw n β hβ S := by
  letI := outsideLaw_probability n β hβ S
  rw [energy, ← disintegration n β hβ S _ (refreshAt_continuous n S f)]
  simp_rw [conditional_decomposition n β hβ S f]
  rw [integral_add (continuous_integrable _ _ (fiberVariance_continuous n β hβ S f))
    (continuous_integrable _ _ (remainderAt_continuous n β hβ S f)),
    WilsonGroundHeatBathVariance.heatBathEnergy_eq_conditional_variance n β hβ S f f.continuous]
  rfl

theorem heatBathEnergy_le_energy (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) :
    heatBathEnergy n β hβ S f ≤ energy n β hβ S f := by
  rw [energy_decomposition]
  exact le_add_of_nonneg_right (integral_nonneg (remainderAt_nonneg n β hβ S f))

/-- Every block Haar refresh is an average over genuine block rotations. -/
def rotateBlock (S : Finset (SpatialVertex n × Fin 3)) (q : Inside n S)
    (U : Slice n) : Slice n := updateMap n S U (fun e => q e * U e.1)

omit [NeZero n] in
theorem refreshAt_rotations (S : Finset (SpatialVertex n × Fin 3))
    (f : C(Slice n, ℝ)) (U : Slice n) :
    refreshAt n S f U =
      ∫ q, (f U-f (rotateBlock n S q U))^2 ∂insideHaar n S := by
  haveI : (insideHaar n S).IsMulRightInvariant := by
    unfold insideHaar WilsonBlockMarginal.insideMeasure
    infer_instance
  exact (integral_mul_right_eq_self
    (fun b => (f U-f (updateMap n S U b))^2) (fun e : {e // e ∈ S} => U e.1)).symm

end
end UnifiedTheory.Clay.YangMills.WilsonHaarRefresh
