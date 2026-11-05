/- Exact block heat-bath resampling for the constructed Wilson ground law.
The density is the actual positive ground profile squared, split over true
spatial link coordinates. No locality or mixing assumption is introduced. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundLocalComparison
import UnifiedTheory.Clay.YangMills.WilsonBlockMarginal
import UnifiedTheory.Clay.YangMills.GroundStateDirichlet
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonGroundHeatBath
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab LocalGibbsComparison
open scoped ENNReal

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

abbrev Outside (S : Finset (SpatialVertex n × Fin 3)) :=
  WilsonBlockMarginal.Outside (G := Q) S
abbrev Inside (S : Finset (SpatialVertex n × Fin 3)) :=
  WilsonBlockMarginal.Inside (G := Q) S
abbrev outsideHaar (S : Finset (SpatialVertex n × Fin 3)) : Measure (Outside n S) :=
  WilsonBlockMarginal.outsideMeasure S (RegulatedGauge.compactHaar Q)
abbrev insideHaar (S : Finset (SpatialVertex n × Fin 3)) : Measure (Inside n S) :=
  WilsonBlockMarginal.insideMeasure S (RegulatedGauge.compactHaar Q)

def groundLaw (β : ℝ) (hβ : 0 ≤ β) : Measure (Slice n) :=
  GroundStateDirichlet.stationaryLaw (measure n) (WilsonGroundLocalComparison.ground n β hβ)

theorem groundLaw_probability (β : ℝ) (hβ : 0 ≤ β) : IsProbabilityMeasure (groundLaw n β hβ) :=
  GroundStateDirichlet.stationaryLaw_probability (measure n)
    (WilsonGroundLocalComparison.ground n β hβ)
    (WilsonGroundLocalComparison.ground n β hβ).continuous
    (WilsonGroundLocalComparison.ground_square_integral n β hβ)

def weight (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (z : Outside n S × Inside n S) : ℝ :=
  (WilsonGroundLocalComparison.ground n β hβ (WilsonBlockMarginal.assemble S z)) ^ 2

theorem weight_continuous (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3)) :
    Continuous (weight n β hβ S) :=
  ((WilsonGroundLocalComparison.ground n β hβ).continuous.comp
    (WilsonBlockMarginal.assemble_continuous S)).pow 2

theorem weight_positive (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (z : Outside n S × Inside n S) : 0 < weight n β hβ S z :=
  sq_pos_of_pos (WilsonGroundLocalComparison.ground_pos n β hβ _)

theorem weight_integral (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3)) :
    (∫ z, weight n β hβ S z ∂(outsideHaar n S).prod (insideHaar n S)) = 1 := by
  have hp : MeasurePreserving (WilsonBlockMarginal.assemble (G := Q) S)
      ((outsideHaar n S).prod (insideHaar n S)) (measure n) :=
    WilsonBlockMarginal.assemble_preserving S (RegulatedGauge.compactHaar Q)
  exact (hp.integral_comp (WilsonBlockMarginal.assemble S).measurableEmbedding
    (fun U => (WilsonGroundLocalComparison.ground n β hβ U) ^ 2)).trans
      (WilsonGroundLocalComparison.ground_square_integral n β hβ)

def fiberMass (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (r : Outside n S) : ℝ := ∫ a, weight n β hβ S (r, a) ∂insideHaar n S

theorem fiberMass_continuous (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3)) :
    Continuous (fiberMass n β hβ S) :=
  GibbsMarginalTower.fiber_integral_continuous (insideHaar n S) _ (weight_continuous n β hβ S)

theorem fiberMass_positive (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (r : Outside n S) : 0 < fiberMass n β hβ S r := by
  have hc : Continuous (fun a : Inside n S => weight n β hβ S (r, a)) :=
    (weight_continuous n β hβ S).comp (continuous_const.prodMk continuous_id)
  change 0 < ∫ a, weight n β hβ S (r, a) ∂insideHaar n S
  apply (integral_pos_iff_support_of_nonneg (fun a => (weight_positive n β hβ S (r, a)).le)
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mpr
  have hs : Function.support (fun a => weight n β hβ S (r, a)) = Set.univ := by
    ext a
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (weight_positive n β hβ S (r, a)).ne'
  simp [hs]

theorem fiberMass_integral (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3)) :
    (∫ r, fiberMass n β hβ S r ∂outsideHaar n S) = 1 := by
  unfold fiberMass
  rw [← integral_prod _ ((weight_continuous n β hβ S).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  exact weight_integral n β hβ S

def conditionalDensity (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (r : Outside n S) (a : Inside n S) : ℝ := weight n β hβ S (r, a) / fiberMass n β hβ S r

def conditionalLaw (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (r : Outside n S) : Measure (Inside n S) :=
  weightedLaw (insideHaar n S) (fun a => weight n β hβ S (r, a))

theorem conditionalLaw_probability (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) :
    IsProbabilityMeasure (conditionalLaw n β hβ S r) := by
  have hc : Continuous (fun a : Inside n S => weight n β hβ S (r, a)) :=
    (weight_continuous n β hβ S).comp (continuous_const.prodMk continuous_id)
  exact weightedLaw_probability _ _ hc.measurable
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun a => (weight_positive n β hβ S (r, a)).le) (fiberMass_positive n β hβ S r)

theorem conditionalDensity_positive (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (a : Inside n S) :
    0 < conditionalDensity n β hβ S r a :=
  div_pos (weight_positive n β hβ S (r, a)) (fiberMass_positive n β hβ S r)

theorem conditionalDensity_mass (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) :
    (∫ a, conditionalDensity n β hβ S r a ∂insideHaar n S) = 1 := by
  simp only [conditionalDensity, integral_div]
  exact div_self (fiberMass_positive n β hβ S r).ne'

theorem conditionalLaw_integral (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (F : Inside n S → ℝ) :
    (∫ a, F a ∂conditionalLaw n β hβ S r) =
      ∫ a, conditionalDensity n β hβ S r a * F a ∂insideHaar n S := by
  have hc : Continuous (fun a : Inside n S => weight n β hβ S (r, a)) :=
    (weight_continuous n β hβ S).comp (continuous_const.prodMk continuous_id)
  calc
    _ = (∫ a, weight n β hβ S (r, a) * F a ∂insideHaar n S) /
        fiberMass n β hβ S r :=
      weighted_integral _ _ hc.measurable (fun a => (weight_positive n β hβ S (r, a)).le)
        (fiberMass_positive n β hβ S r) F
    _ = _ := by simp only [conditionalDensity, div_mul_eq_mul_div, integral_div]

def splitLaw (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3)) :
    Measure (Outside n S × Inside n S) :=
  weightedLaw ((outsideHaar n S).prod (insideHaar n S)) (weight n β hβ S)

theorem groundLaw_eq_weightedLaw (β : ℝ) (hβ : 0 ≤ β) :
    groundLaw n β hβ = weightedLaw (measure n)
      (fun U => (WilsonGroundLocalComparison.ground n β hβ U) ^ 2) := by
  simp only [weightedLaw, WilsonGroundLocalComparison.ground_square_integral,
    ENNReal.ofReal_one, inv_one, one_smul]
  rfl

theorem assemble_ground_preserving (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) :
    MeasurePreserving (WilsonBlockMarginal.assemble (G := Q) S)
      (splitLaw n β hβ S) (groundLaw n β hβ) := by
  have hp : MeasurePreserving (WilsonBlockMarginal.assemble (G := Q) S)
      ((outsideHaar n S).prod (insideHaar n S)) (measure n) :=
    WilsonBlockMarginal.assemble_preserving S (RegulatedGauge.compactHaar Q)
  have hh := WilsonBlockMarginal.weightedLaw_preserving
    ((outsideHaar n S).prod (insideHaar n S)) (measure n)
    (WilsonBlockMarginal.assemble S) hp
    (fun U => (WilsonGroundLocalComparison.ground n β hβ U) ^ 2)
    ((WilsonGroundLocalComparison.ground n β hβ).continuous.pow 2).measurable
  rw [← groundLaw_eq_weightedLaw] at hh
  exact hh

theorem split_integral (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (F : Slice n → ℝ) :
    (∫ z, F (WilsonBlockMarginal.assemble S z) ∂splitLaw n β hβ S) =
      ∫ U, F U ∂groundLaw n β hβ :=
  (assemble_ground_preserving n β hβ S).integral_comp
    (WilsonBlockMarginal.assemble S).measurableEmbedding F


def outsideLaw (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3)) :
    Measure (Outside n S) := weightedLaw (outsideHaar n S) (fiberMass n β hβ S)

theorem outsideLaw_probability (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) : IsProbabilityMeasure (outsideLaw n β hβ S) :=
  weightedLaw_probability _ _ (fiberMass_continuous n β hβ S).measurable
    ((fiberMass_continuous n β hβ S).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (fun r => (fiberMass_positive n β hβ S r).le)
    (by rw [fiberMass_integral]; norm_num)

/-- Original ground-law expectations in the actual block product coordinates. -/
theorem ground_integral_coordinates (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (F : Slice n → ℝ) (hF : Continuous F) :
    (∫ U, F U ∂groundLaw n β hβ) =
      ∫ r, ∫ a, weight n β hβ S (r, a) * F (WilsonBlockMarginal.assemble S (r, a))
        ∂insideHaar n S ∂outsideHaar n S := by
  rw [← split_integral n β hβ S F]
  change (∫ z, F (WilsonBlockMarginal.assemble S z) ∂weightedLaw
    ((outsideHaar n S).prod (insideHaar n S)) (weight n β hβ S)) = _
  rw [weighted_integral _ _ (weight_continuous n β hβ S).measurable
    (fun z => (weight_positive n β hβ S z).le) (by rw [weight_integral]; norm_num),
    weight_integral, div_one]
  exact integral_prod _ (((weight_continuous n β hβ S).mul
    (hF.comp (WilsonBlockMarginal.assemble_continuous S))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

/-- The normalized conditional block law integrates to the original ground law. -/
theorem disintegration (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (F : Slice n → ℝ) (hF : Continuous F) :
    (∫ r, ∫ a, F (WilsonBlockMarginal.assemble S (r, a))
      ∂conditionalLaw n β hβ S r ∂outsideLaw n β hβ S) = ∫ U, F U ∂groundLaw n β hβ := by
  rw [outsideLaw, weighted_integral _ _ (fiberMass_continuous n β hβ S).measurable
    (fun r => (fiberMass_positive n β hβ S r).le)
    (by rw [fiberMass_integral]; norm_num), fiberMass_integral, div_one,
    ground_integral_coordinates n β hβ S F hF]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  dsimp only
  rw [conditionalLaw_integral n β hβ S r]
  simp only [conditionalDensity, div_mul_eq_mul_div, integral_div]
  exact mul_div_cancel₀ _ (fiberMass_positive n β hβ S r).ne'

abbrev Triple (S : Finset (SpatialVertex n × Fin 3)) := Outside n S × (Inside n S × Inside n S)

/-- Two conditional independent draws of the selected block at the same actual exterior. -/
def edgeDensity (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (z : Triple n S) : ℝ :=
  weight n β hβ S (z.1, z.2.1) * weight n β hβ S (z.1, z.2.2) /
    fiberMass n β hβ S z.1

theorem edgeDensity_continuous (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) : Continuous (edgeDensity n β hβ S) := by
  exact (((weight_continuous n β hβ S).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).mul
    ((weight_continuous n β hβ S).comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))).div
    ((fiberMass_continuous n β hβ S).comp continuous_fst)
    (fun z => (fiberMass_positive n β hβ S z.1).ne')

theorem edgeDensity_positive (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (z : Triple n S) :
    0 < edgeDensity n β hβ S z :=
  div_pos (mul_pos (weight_positive n β hβ S _) (weight_positive n β hβ S _))
    (fiberMass_positive n β hβ S z.1)

theorem edgeDensity_fiber_integral (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (a : Inside n S) :
    (∫ b, edgeDensity n β hβ S (r, a, b) ∂insideHaar n S) = weight n β hβ S (r, a) := by
  simp only [edgeDensity, integral_div, integral_const_mul]
  change weight n β hβ S (r, a) * fiberMass n β hβ S r / fiberMass n β hβ S r = _
  exact mul_div_cancel_right₀ _ (fiberMass_positive n β hβ S r).ne'

theorem edgeDensity_integral (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) :
    (∫ z, edgeDensity n β hβ S z
      ∂(outsideHaar n S).prod ((insideHaar n S).prod (insideHaar n S))) = 1 := by
  rw [integral_prod _ ((edgeDensity_continuous n β hβ S).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  have he (r : Outside n S) :
      (∫ z, edgeDensity n β hβ S (r, z) ∂(insideHaar n S).prod (insideHaar n S)) =
        fiberMass n β hβ S r := by
    have hc : Continuous (fun z : Inside n S × Inside n S => edgeDensity n β hβ S (r, z)) :=
      (edgeDensity_continuous n β hβ S).comp (continuous_const.prodMk continuous_id)
    rw [integral_prod _ (hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    simp only [edgeDensity_fiber_integral]
    rfl
  simp only [he]
  exact fiberMass_integral n β hβ S

def tripleLaw (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3)) : Measure (Triple n S) :=
  weightedLaw ((outsideHaar n S).prod ((insideHaar n S).prod (insideHaar n S)))
    (edgeDensity n β hβ S)

theorem tripleLaw_probability (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) : IsProbabilityMeasure (tripleLaw n β hβ S) :=
  weightedLaw_probability _ _ (edgeDensity_continuous n β hβ S).measurable
    ((edgeDensity_continuous n β hβ S).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (fun z => (edgeDensity_positive n β hβ S z).le)
    (by rw [edgeDensity_integral]; norm_num)

def pairMap (S : Finset (SpatialVertex n × Fin 3)) (z : Triple n S) : Slice n × Slice n :=
  (WilsonBlockMarginal.assemble S (z.1, z.2.1), WilsonBlockMarginal.assemble S (z.1, z.2.2))

omit [NeZero n] in
theorem pairMap_continuous (S : Finset (SpatialVertex n × Fin 3)) : Continuous (pairMap n S) :=
  ((WilsonBlockMarginal.assemble_continuous S).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
    ((WilsonBlockMarginal.assemble_continuous S).comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

def edgeLaw (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3)) :
    Measure (Slice n × Slice n) := (tripleLaw n β hβ S).map (pairMap n S)

theorem edgeLaw_probability (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) : IsProbabilityMeasure (edgeLaw n β hβ S) := by
  letI := tripleLaw_probability n β hβ S
  exact Measure.isProbabilityMeasure_map (pairMap_continuous n S).measurable.aemeasurable

/-- The actual heat-bath edge expectation is the explicit three-variable integral. -/
theorem edge_integral (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (F : Slice n × Slice n → ℝ) (hF : Continuous F) :
    (∫ z, F z ∂edgeLaw n β hβ S) =
      ∫ r, ∫ a, ∫ b, edgeDensity n β hβ S (r, a, b) * F (pairMap n S (r, a, b))
        ∂insideHaar n S ∂insideHaar n S ∂outsideHaar n S := by
  rw [edgeLaw, integral_map (pairMap_continuous n S).measurable.aemeasurable
    hF.aestronglyMeasurable]
  rw [tripleLaw, weighted_integral _ _ (edgeDensity_continuous n β hβ S).measurable
    (fun z => (edgeDensity_positive n β hβ S z).le)
    (by rw [edgeDensity_integral]; norm_num), edgeDensity_integral, div_one]
  have hc : Continuous (fun z : Triple n S =>
      edgeDensity n β hβ S z * F (pairMap n S z)) :=
    (edgeDensity_continuous n β hβ S).mul (hF.comp (pairMap_continuous n S))
  rw [integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  dsimp only
  exact integral_prod _ ((hc.comp (continuous_const.prodMk continuous_id))
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) )

theorem edge_first_integral (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (F : Slice n → ℝ) (hF : Continuous F) :
    (∫ z, F z.1 ∂edgeLaw n β hβ S) = ∫ U, F U ∂groundLaw n β hβ := by
  rw [edge_integral n β hβ S (fun z => F z.1) (hF.comp continuous_fst),
    ground_integral_coordinates n β hβ S F hF]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  change (∫ b, edgeDensity n β hβ S (r, a, b) *
    F (WilsonBlockMarginal.assemble S (r, a)) ∂insideHaar n S) = _
  rw [integral_mul_const, edgeDensity_fiber_integral]

omit [NeZero n] in
/-- The edge law is supported on pairs agreeing outside the resampled block. -/
theorem pairMap_outside (S : Finset (SpatialVertex n × Fin 3))
    (z : Triple n S) (e : SpatialVertex n × Fin 3) (he : e ∉ S) :
    (pairMap n S z).1 e = (pairMap n S z).2 e := by
  simp only [pairMap, WilsonBlockMarginal.assemble_outside S _ e he]

/-- The exact heat-bath Dirichlet form, with no supplied mixing estimate. -/
def heatBathEnergy (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (F : Slice n → ℝ) : ℝ :=
  (1 / 2) * ∫ r, ∫ a, ∫ b, edgeDensity n β hβ S (r, a, b) *
    (F (WilsonBlockMarginal.assemble S (r, a)) - F (WilsonBlockMarginal.assemble S (r, b))) ^ 2
      ∂insideHaar n S ∂insideHaar n S ∂outsideHaar n S

theorem heatBathEnergy_eq_edge (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (F : Slice n → ℝ) (hF : Continuous F) :
    heatBathEnergy n β hβ S F =
      (1 / 2) * ∫ z, (F z.1 - F z.2) ^ 2 ∂edgeLaw n β hβ S := by
  rw [edge_integral n β hβ S (fun z => (F z.1 - F z.2) ^ 2) (((hF.comp continuous_fst).sub
    (hF.comp continuous_snd)).pow 2)]
  rfl


/-- Swapping the two conditional draws preserves the exact joint density. -/
theorem edgeDensity_reflection (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (z : Triple n S) :
    edgeDensity n β hβ S (BoundaryReflectionGluing.reflection z) = edgeDensity n β hβ S z := by
  simp only [edgeDensity, BoundaryReflectionGluing.reflection, Prod.swap]
  ring

theorem tripleLaw_reflection (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) :
    MeasurePreserving BoundaryReflectionGluing.reflection
      (tripleLaw n β hβ S) (tripleLaw n β hβ S) := by
  unfold tripleLaw weightedLaw
  apply MeasurePreserving.smul_measure
  exact RegulatedGauge.preserves_withDensity
    (BoundaryReflectionGluing.reference_reflection (outsideHaar n S) (insideHaar n S)) _
    (edgeDensity_continuous n β hβ S).measurable.ennreal_ofReal
    (fun z => congrArg ENNReal.ofReal (edgeDensity_reflection n β hβ S z))

/-- The actual resampling edge law is reversible, as a measure equality. -/
theorem edgeLaw_reversible (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) :
    MeasurePreserving Prod.swap (edgeLaw n β hβ S) (edgeLaw n β hβ S) := by
  refine ⟨measurable_swap, ?_⟩
  rw [edgeLaw, Measure.map_map measurable_swap (pairMap_continuous n S).measurable]
  change (tripleLaw n β hβ S).map ((pairMap n S) ∘ BoundaryReflectionGluing.reflection) = _
  rw [← Measure.map_map (pairMap_continuous n S).measurable
    (BoundaryReflectionGluing.reference_reflection (outsideHaar n S) (insideHaar n S)).measurable,
    (tripleLaw_reflection n β hβ S).map_eq]

/-- The first marginal is the original constructed Wilson ground law. -/
theorem edge_first_marginal (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) :
    (edgeLaw n β hβ S).map Prod.fst = groundLaw n β hβ := by
  letI := edgeLaw_probability n β hβ S
  letI := groundLaw_probability n β hβ
  letI := Measure.isProbabilityMeasure_map (μ := edgeLaw n β hβ S) measurable_fst.aemeasurable
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro F
  rw [integral_map (f := fun x => F x) measurable_fst.aemeasurable
    F.continuous.aestronglyMeasurable]
  exact edge_first_integral n β hβ S F F.continuous

/-- Reversibility gives the same ground law as the second marginal: exact stationarity. -/
theorem edge_second_marginal (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) :
    (edgeLaw n β hβ S).map Prod.snd = groundLaw n β hβ := by
  calc
    _ = (edgeLaw n β hβ S).map (Prod.fst ∘ Prod.swap) := rfl
    _ = ((edgeLaw n β hβ S).map Prod.swap).map Prod.fst :=
      (Measure.map_map measurable_fst measurable_swap).symm
    _ = _ := by rw [(edgeLaw_reversible n β hβ S).map_eq, edge_first_marginal]

/-- Projection to the retained spatial links. -/
def outsideProjection (S : Finset (SpatialVertex n × Fin 3)) (U : Slice n) : Outside n S :=
  fun e => U e.1

omit [NeZero n] in
theorem outsideProjection_continuous (S : Finset (SpatialVertex n × Fin 3)) :
    Continuous (outsideProjection n S) := continuous_pi (fun e => continuous_apply e.1)

omit [NeZero n] in
theorem outsideProjection_assemble (S : Finset (SpatialVertex n × Fin 3))
    (z : Outside n S × Inside n S) :
    outsideProjection n S (WilsonBlockMarginal.assemble S z) = z.1 := by
  funext e
  exact WilsonBlockMarginal.assemble_outside S z e.1 e.2

/-- The retained law is the actual marginal of the constructed ground law. -/
theorem outsideLaw_eq_map (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) :
    outsideLaw n β hβ S = (groundLaw n β hβ).map (outsideProjection n S) := by
  letI := groundLaw_probability n β hβ
  letI := outsideLaw_probability n β hβ S
  letI := Measure.isProbabilityMeasure_map (μ := groundLaw n β hβ)
    (outsideProjection_continuous n S).measurable.aemeasurable
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro F
  rw [integral_map (f := fun x => F x)
    (outsideProjection_continuous n S).measurable.aemeasurable
    F.continuous.aestronglyMeasurable,
    ground_integral_coordinates n β hβ S (fun U => F (outsideProjection n S U))
      (F.continuous.comp (outsideProjection_continuous n S))]
  simp only [outsideProjection_assemble, integral_mul_const]
  exact weighted_integral (outsideHaar n S) (fiberMass n β hβ S)
    (fiberMass_continuous n β hβ S).measurable
    (fun r => (fiberMass_positive n β hβ S r).le)
    (by rw [fiberMass_integral]; norm_num) F |>.trans (by rw [fiberMass_integral, div_one]; rfl)

/-- A resampling retains the true outside coordinates and replaces only the selected block. -/
def updateMap (S : Finset (SpatialVertex n × Fin 3)) (U : Slice n) (a : Inside n S) : Slice n :=
  WilsonBlockMarginal.assemble S (outsideProjection n S U, a)

omit [NeZero n] in
theorem updateMap_continuous (S : Finset (SpatialVertex n × Fin 3)) :
    Continuous (fun z : Slice n × Inside n S => updateMap n S z.1 z.2) :=
  (WilsonBlockMarginal.assemble_continuous S).comp
    (((outsideProjection_continuous n S).comp continuous_fst).prodMk continuous_snd)

omit [NeZero n] in
theorem updateMap_outside (S : Finset (SpatialVertex n × Fin 3))
    (U : Slice n) (a : Inside n S) (e : SpatialVertex n × Fin 3) (he : e ∉ S) :
    updateMap n S U a e = U e := WilsonBlockMarginal.assemble_outside S _ e he

def updateLaw (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (U : Slice n) : Measure (Slice n) :=
  (conditionalLaw n β hβ S (outsideProjection n S U)).map (updateMap n S U)

theorem updateLaw_probability (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (U : Slice n) :
    IsProbabilityMeasure (updateLaw n β hβ S U) := by
  letI := conditionalLaw_probability n β hβ S (outsideProjection n S U)
  exact Measure.isProbabilityMeasure_map
    ((updateMap_continuous n S).comp
      (continuous_const.prodMk continuous_id)).measurable.aemeasurable

theorem updateLaw_integral (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (U : Slice n) (F : Slice n → ℝ) (hF : Continuous F) :
    (∫ V, F V ∂updateLaw n β hβ S U) =
      ∫ a, F (updateMap n S U a) ∂conditionalLaw n β hβ S (outsideProjection n S U) :=
  integral_map
    ((updateMap_continuous n S).comp
      (continuous_const.prodMk continuous_id)).measurable.aemeasurable
    hF.aestronglyMeasurable


/-- Exact pointwise conditional expectation formula for a joint continuous probe. -/
theorem update_joint_integral (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (F : Slice n × Slice n → ℝ)
    (hF : Continuous F) (U : Slice n) :
    (∫ V, F (U, V) ∂updateLaw n β hβ S U) =
      (∫ b, weight n β hβ S (outsideProjection n S U, b) * F (U, updateMap n S U b)
        ∂insideHaar n S) / fiberMass n β hβ S (outsideProjection n S U) := by
  rw [updateLaw_integral n β hβ S U (fun V => F (U, V))
    (hF.comp (continuous_const.prodMk continuous_id)), conditionalLaw_integral]
  simp only [conditionalDensity, div_mul_eq_mul_div, integral_div]

theorem update_joint_continuous (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (F : Slice n × Slice n → ℝ)
    (hF : Continuous F) :
    Continuous (fun U => ∫ V, F (U, V) ∂updateLaw n β hβ S U) := by
  have hc : Continuous (fun z : Slice n × Inside n S =>
      weight n β hβ S (outsideProjection n S z.1, z.2) * F (z.1, updateMap n S z.1 z.2)) :=
    ((weight_continuous n β hβ S).comp
      (((outsideProjection_continuous n S).comp continuous_fst).prodMk continuous_snd)).mul
      (hF.comp (continuous_fst.prodMk (updateMap_continuous n S)))
  have he : (fun U => ∫ V, F (U, V) ∂updateLaw n β hβ S U) =
      (fun U => (∫ b, weight n β hβ S (outsideProjection n S U, b) *
        F (U, updateMap n S U b) ∂insideHaar n S) /
          fiberMass n β hβ S (outsideProjection n S U)) :=
    funext (update_joint_integral n β hβ S F hF)
  rw [he]
  exact (GibbsMarginalTower.fiber_integral_continuous (insideHaar n S) _ hc).div
    ((fiberMass_continuous n β hβ S).comp (outsideProjection_continuous n S))
    (fun U => (fiberMass_positive n β hβ S _).ne')

/-- The reversible edge law is precisely one draw from the original ground law
followed by the constructed conditional resampling update. -/
theorem edge_integral_update (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (F : Slice n × Slice n → ℝ) (hF : Continuous F) :
    (∫ z, F z ∂edgeLaw n β hβ S) =
      ∫ U, ∫ V, F (U, V) ∂updateLaw n β hβ S U ∂groundLaw n β hβ := by
  rw [edge_integral n β hβ S F hF,
    ground_integral_coordinates n β hβ S _ (update_joint_continuous n β hβ S F hF)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  dsimp only
  rw [update_joint_integral n β hβ S F hF, outsideProjection_assemble]
  have he (b : Inside n S) :
      updateMap n S (WilsonBlockMarginal.assemble S (r, a)) b =
        WilsonBlockMarginal.assemble S (r, b) := by
    simp only [updateMap, outsideProjection_assemble]
  simp only [he]
  calc
    _ = ∫ b, weight n β hβ S (r, a) *
        (weight n β hβ S (r, b) * F (pairMap n S (r, a, b))) /
          fiberMass n β hβ S r ∂insideHaar n S := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun b => by unfold edgeDensity; ring)
    _ = _ := by
      rw [integral_div, integral_const_mul]
      simp only [pairMap]
      ring

/-- Exact stationarity of the actual conditional update, for every continuous observable. -/
theorem update_stationary (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (F : Slice n → ℝ) (hF : Continuous F) :
    (∫ U, ∫ V, F V ∂updateLaw n β hβ S U ∂groundLaw n β hβ) =
      ∫ U, F U ∂groundLaw n β hβ := by
  rw [← edge_integral_update n β hβ S (fun z => F z.2) (hF.comp continuous_snd)]
  rw [← edge_second_marginal n β hβ S]
  exact (integral_map (f := F) measurable_snd.aemeasurable hF.aestronglyMeasurable).symm

end
end UnifiedTheory.Clay.YangMills.WilsonGroundHeatBath
