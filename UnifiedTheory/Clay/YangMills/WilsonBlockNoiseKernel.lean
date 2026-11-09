/- The actual covariance removed by one independent Wilson block is a
positive semidefinite finite-stencil kernel. Its coefficients are deterministic
expectations under the original interacting law. This is not a finite-range
assertion about the full covariance or a repeated-scale renormalization bound. -/
import UnifiedTheory.Clay.YangMills.WilsonCrossCovariance
import UnifiedTheory.Clay.YangMills.WilsonIndependentVariance
import UnifiedTheory.Clay.YangMills.WilsonCellWeightLower
import UnifiedTheory.Clay.YangMills.WilsonSlabBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBlockNoiseKernel
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonBlockMarginal WilsonSingleLinkStaples

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (WilsonIndependentBlocks.Link n) := Classical.decEq _
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance lawProbability (β : ℝ) : IsProbabilityMeasure (wilsonLaw n Q character β 2) :=
  wilsonLaw_probability n Q character character_continuous β 2

/-- Basis source for one actual plaquette. -/
def basis (p : PlaquetteIndex n) (q : PlaquetteIndex n) : ℝ := if q = p then 1 else 0

def source (f : PlaquetteIndex n → ℝ) : Configuration (Vertex n) Q → ℝ :=
  WilsonBlockIntegration.source n Q character 2 f

def retained (β : ℝ) (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) :=
  WilsonCrossCovariance.retainedSource n Q character β 2 S f

def noise (β : ℝ) (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) :=
  WilsonCrossCovariance.removedSource n Q character β 2 S f

/-- Deterministic covariance coefficients of the fluctuation actually removed. -/
def coefficient (β : ℝ) (S : Finset (Edge (Vertex n))) (p q : PlaquetteIndex n) : ℝ :=
  ∫ U, noise n β S (basis n p) U * noise n β S (basis n q) U
    ∂wilsonLaw n Q character β 2

def bilinear (β : ℝ) (S : Finset (Edge (Vertex n))) (f g : PlaquetteIndex n → ℝ) : ℝ :=
  ∑ p, ∑ q, f p * g q * coefficient n β S p q

theorem source_continuous (f : PlaquetteIndex n → ℝ) : Continuous (source n f) :=
  WilsonBlockIntegration.source_continuous n Q character character_continuous 2 f

theorem retained_continuous (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) : Continuous (retained n β S f) :=
  WilsonCrossCovariance.retainedSource_continuous n Q character character_continuous β 2 S f

theorem noise_continuous (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) : Continuous (noise n β S f) :=
  (source_continuous n f).sub ((retained_continuous n β S f).comp
    (continuous_fst.comp (CompactGibbsBlockUpdate.assemble_symm_continuous S)))

theorem source_basis (p : PlaquetteIndex n) (U : Configuration (Vertex n) Q) :
    source n (basis n p) U = WilsonIndependentBlocks.plaquetteTerm n Q character 2 U p := by
  classical
  simp [source, basis, WilsonBlockIntegration.source, WilsonIndependentBlocks.plaquetteTerm]

theorem source_expansion (f : PlaquetteIndex n → ℝ) (U : Configuration (Vertex n) Q) :
    source n f U = ∑ p, f p * source n (basis n p) U := by
  simp_rw [source_basis]
  rfl

theorem retained_expansion (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) (r : Outside (G := Q) S) :
    retained n β S f r = ∑ p, f p * retained n β S (basis n p) r := by
  let A := splitAction n Q character β 2 S
  let ν := CompactGibbsContinuity.law (insideMeasure S (compactHaar Q)) (fun v => A (r, v))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability _ _
    ((splitAction_continuous n Q character character_continuous β 2 S).comp
      (continuous_const.prodMk continuous_id))
  have hr (g : PlaquetteIndex n → ℝ) : retained n β S g r =
      ∫ v, source n g (assemble S (r, v)) ∂ν :=
    GibbsMarginalTower.response_eq_expectation _ _ _
      (splitAction_continuous n Q character character_continuous β 2 S) r
  rw [hr]
  simp_rw [source_expansion n f]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul, ← hr]
  · intro p _
    have hc : Continuous (fun v => f p * source n (basis n p) (assemble S (r, v))) :=
      continuous_const.mul ((source_continuous n (basis n p)).comp
      ((assemble_continuous S).comp (continuous_const.prodMk continuous_id)))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem noise_expansion (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) (U : Configuration (Vertex n) Q) :
    noise n β S f U = ∑ p, f p * noise n β S (basis n p) U := by
  change source n f U - retained n β S f ((assemble S).symm U).1 =
    ∑ p, f p * (source n (basis n p) U - retained n β S (basis n p) ((assemble S).symm U).1)
  rw [source_expansion, retained_expansion]
  simp only [mul_sub, Finset.sum_sub_distrib]

theorem coefficient_symm (β : ℝ) (S : Finset (Edge (Vertex n))) (p q : PlaquetteIndex n) :
    coefficient n β S p q = coefficient n β S q p := by
  unfold coefficient
  congr 1
  funext U
  ring

/-- The entire finite matrix equals the Gram form of the actual combined removed sources. -/
theorem bilinear_eq_noise (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f g : PlaquetteIndex n → ℝ) :
    bilinear n β S f g = ∫ U, noise n β S f U * noise n β S g U
      ∂wilsonLaw n Q character β 2 := by
  let ν := wilsonLaw n Q character β 2
  have hi (p q : PlaquetteIndex n) : Integrable (fun U =>
      (f p * g q) * (noise n β S (basis n p) U * noise n β S (basis n q) U)) ν :=
    (continuous_const.mul ((noise_continuous n β S (basis n p)).mul
      (noise_continuous n β S (basis n q)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have he : (∫ U, ∑ p, ∑ q,
      (f p * g q) * (noise n β S (basis n p) U * noise n β S (basis n q) U) ∂ν) =
      ∑ p, ∑ q, f p * g q * coefficient n β S p q := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro p _
      rw [integral_finset_sum]
      · simp_rw [integral_const_mul]
        rfl
      · intro q _
        exact hi p q
    · intro p _
      exact integrable_finset_sum _ (fun q _ => hi p q)
  unfold bilinear
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with U
  rw [noise_expansion n β S f, noise_expansion n β S g, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Positive semidefiniteness is proved for every real plaquette-weight vector. -/
theorem positive_semidefinite (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) : 0 ≤ bilinear n β S f f := by
  rw [bilinear_eq_noise]
  exact integral_nonneg (fun _ => mul_self_nonneg _)


/-- Actual full-minus-retained covariance is exactly the removed-noise Gram form. -/
theorem covariance_sub_retained (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f g : PlaquetteIndex n → ℝ) :
    GibbsCrossCovariance.covariance (wilsonLaw n Q character β 2) (source n f) (source n g) -
      bilinear n β S f g =
    GibbsCrossCovariance.covariance (WilsonCrossCovariance.retainedLaw n Q character β 2 S)
      (retained n β S f) (retained n β S g) := by
  let μB := outsideMeasure S (compactHaar Q)
  let μX := insideMeasure S (compactHaar Q)
  let A := splitAction n Q character β 2 S
  let F := WilsonSeparatedSources.splitSource n Q character 2 S f
  let G := WilsonSeparatedSources.splitSource n Q character 2 S g
  have hA : Continuous A := splitAction_continuous n Q character character_continuous β 2 S
  have hF : Continuous F :=
    WilsonCrossCovariance.splitSource_continuous n Q character character_continuous 2 S f
  have hG : Continuous G :=
    WilsonCrossCovariance.splitSource_continuous n Q character character_continuous 2 S g
  have hc : GibbsCrossCovariance.covariance (wilsonLaw n Q character β 2)
      (source n f) (source n g) =
      GibbsCrossCovariance.covariance (CompactGibbsContinuity.law (μB.prod μX) A) F G := by
    unfold GibbsCrossCovariance.covariance
    rw [wilson_integral_split n Q character character_continuous β 2 S,
      wilson_integral_split n Q character character_continuous β 2 S,
      wilson_integral_split n Q character character_continuous β 2 S]
    rfl
  have hn : bilinear n β S f g =
      ∫ r, GibbsCrossCovariance.conditionalCovariance μX A F G r
        ∂GibbsMarginalTower.marginal μB μX A := by
    rw [bilinear_eq_noise, wilson_integral_split n Q character character_continuous β 2 S]
    simp only [noise, WilsonCrossCovariance.removedSource_assemble]
    have h := GibbsMarginalTower.response_expectation μB μX A
      (fun z => GibbsCrossCovariance.removed μX A F z * GibbsCrossCovariance.removed μX A G z)
      hA ((GibbsCrossCovariance.removed_continuous μX A F hA hF).mul
        (GibbsCrossCovariance.removed_continuous μX A G hA hG))
    simp_rw [GibbsCrossCovariance.conditional_removed_product μX A F G hA hF hG] at h
    exact h.symm
  rw [hc, hn]
  have h := GibbsCrossCovariance.total_covariance μB μX A F G hA hF hG
  change GibbsCrossCovariance.covariance (CompactGibbsContinuity.law (μB.prod μX) A) F G -
    (∫ r, GibbsCrossCovariance.conditionalCovariance μX A F G r
      ∂GibbsMarginalTower.marginal μB μX A) =
    GibbsCrossCovariance.covariance (GibbsMarginalTower.marginal μB μX A)
      (GibbsMarginalTower.response μX A F) (GibbsMarginalTower.response μX A G)
  linarith

theorem source_basis_bounds (p : PlaquetteIndex n) (U : Configuration (Vertex n) Q) :
    0 ≤ source n (basis n p) U ∧ source n (basis n p) U ≤ 4 := by
  rw [source_basis]
  exact WilsonSlabBounds.characterDefect_bounds
    (holonomy (Quiver.Symmetrify (Vertex n)) Q (orientedExtension (Vertex n) Q U) (loops n p))

/-- Conditional averaging keeps the genuine bounded plaquette range. -/
theorem retained_basis_bounds (β : ℝ) (S : Finset (Edge (Vertex n)))
    (p : PlaquetteIndex n) (r : Outside (G := Q) S) :
    0 ≤ retained n β S (basis n p) r ∧ retained n β S (basis n p) r ≤ 4 := by
  let A := splitAction n Q character β 2 S
  let ν := CompactGibbsContinuity.law (insideMeasure S (compactHaar Q)) (fun v => A (r, v))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability _ _
    ((splitAction_continuous n Q character character_continuous β 2 S).comp
      (continuous_const.prodMk continuous_id))
  have he : retained n β S (basis n p) r =
      ∫ v, source n (basis n p) (assemble S (r, v)) ∂ν :=
    GibbsMarginalTower.response_eq_expectation _ _ _
      (splitAction_continuous n Q character character_continuous β 2 S) r
  rw [he]
  constructor
  · exact integral_nonneg (fun v => (source_basis_bounds n p _).1)
  · have hi : Integrable (fun v => source n (basis n p) (assemble S (r, v))) ν := by
      have hc : Continuous (fun v => source n (basis n p) (assemble S (r, v))) :=
        (source_continuous n (basis n p)).comp
        ((assemble_continuous S).comp (continuous_const.prodMk continuous_id))
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h := integral_mono hi (integrable_const (4 : ℝ))
      (fun v => (source_basis_bounds n p (assemble S (r, v))).2)
    simpa only [integral_const, probReal_univ, one_smul] using h

theorem noise_basis_abs_le (β : ℝ) (S : Finset (Edge (Vertex n)))
    (p : PlaquetteIndex n) (U : Configuration (Vertex n) Q) :
    |noise n β S (basis n p) U| ≤ 4 := by
  have hs := source_basis_bounds n p U
  have hr := retained_basis_bounds n β S p ((assemble S).symm U).1
  change |source n (basis n p) U - retained n β S (basis n p) ((assemble S).symm U).1| ≤ 4
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Uniform coefficients, independent of volume, coupling and block cardinality. -/
theorem coefficient_abs_le (β : ℝ) (S : Finset (Edge (Vertex n)))
    (p q : PlaquetteIndex n) : |coefficient n β S p q| ≤ 16 := by
  have hi : Integrable (fun U =>
      |noise n β S (basis n p) U * noise n β S (basis n q) U|)
      (wilsonLaw n Q character β 2) :=
    (((noise_continuous n β S (basis n p)).mul
      (noise_continuous n β S (basis n q))).abs).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have h := integral_mono hi (integrable_const (16 : ℝ)) (fun U => by
    rw [abs_mul]
    have hh := mul_le_mul (noise_basis_abs_le n β S p U) (noise_basis_abs_le n β S q U)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    norm_num at hh ⊢
    exact hh)
  unfold coefficient
  apply (abs_integral_le_integral_abs).trans
  simpa only [integral_const, probReal_univ, one_smul] using h


/-- Sources separated on every selected link retain exactly their mixed form. -/
theorem bilinear_separated_zero (β : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (f g : PlaquetteIndex n → ℝ) (hsep : WilsonSeparatedSources.SeparatedOnBlock n S f g) :
    bilinear n β S f g = 0 := by
  rw [bilinear_eq_noise]
  exact WilsonCrossCovariance.removed_product_zero n Q character character_continuous
    β 2 S hS f g hsep

/-- A nonzero removed coefficient requires a selected link touching both plaquettes. -/
theorem coefficient_zero_of_no_shared (β : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (p q : PlaquetteIndex n)
    (hno : ∀ e ∈ S, ¬(p ∈ SingleLinkWilsonOscillation.affected n
        (WilsonIndependentBlocks.edgeCoord n e).1 (WilsonIndependentBlocks.edgeCoord n e).2 ∧
      q ∈ SingleLinkWilsonOscillation.affected n
        (WilsonIndependentBlocks.edgeCoord n e).1 (WilsonIndependentBlocks.edgeCoord n e).2)) :
    coefficient n β S p q = 0 := by
  have hsep : WilsonSeparatedSources.SeparatedOnBlock n S (basis n p) (basis n q) := by
    intro e he
    by_cases hp : p ∈ SingleLinkWilsonOscillation.affected n
        (WilsonIndependentBlocks.edgeCoord n e).1 (WilsonIndependentBlocks.edgeCoord n e).2
    · right
      intro r hr
      have hn : r ≠ q := by intro h; subst r; exact hno e he ⟨hp, hr⟩
      simp only [basis, if_neg hn]
    · left
      intro r hr
      have hn : r ≠ p := by intro h; subst r; exact hp hr
      simp only [basis, if_neg hn]
  exact WilsonCrossCovariance.removed_product_zero n Q character character_continuous
    β 2 S hS (basis n p) (basis n q) hsep

/-- A fixed-size geometric row stencil, containing all possibly removed pair coefficients. -/
def stencil (p : PlaquetteIndex n) : Finset (PlaquetteIndex n) :=
  (WilsonInfluenceGeometry.incidentLinks n p).biUnion
    (fun e => SingleLinkWilsonOscillation.affected n e.1 e.2)

theorem coefficient_zero_outside_stencil (β : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (p q : PlaquetteIndex n) (hq : q ∉ stencil n p) : coefficient n β S p q = 0 := by
  apply coefficient_zero_of_no_shared n β S hS p q
  intro e _ hpq
  apply hq
  exact Finset.mem_biUnion.mpr ⟨WilsonIndependentBlocks.edgeCoord n e,
    (WilsonInfluenceGeometry.mem_incidentLinks n p _).mpr
      ((WilsonInfluenceGeometry.affected_iff_incident n p _).mp hpq.1), hpq.2⟩

variable [Fact (1 < n)]

omit [NeZero n] in
/-- At most four incident links times six plaquettes per link. -/
theorem stencil_card (p : PlaquetteIndex n) : (stencil n p).card ≤ 24 := by
  have h := Finset.card_biUnion_le (s := WilsonInfluenceGeometry.incidentLinks n p)
    (t := fun e => SingleLinkWilsonOscillation.affected n e.1 e.2)
  change (stencil n p).card ≤ _ at h
  simp [affected_card_eq_six] at h
  have hc := WilsonInfluenceGeometry.incidentLinks_card_le n p
  omega

/-- A deterministic row budget for the actual removed covariance kernel. -/
theorem coefficient_row_budget (β : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (p : PlaquetteIndex n) : (∑ q, |coefficient n β S p q|) ≤ 384 := by
  classical
  have he : (∑ q ∈ stencil n p, |coefficient n β S p q|) =
      ∑ q, |coefficient n β S p q| := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro q _ hq
    rw [coefficient_zero_outside_stencil n β S hS p q hq, abs_zero]
  rw [← he]
  calc
    _ ≤ ∑ _q ∈ stencil n p, (16 : ℝ) :=
      Finset.sum_le_sum (fun q _ => coefficient_abs_le n β S p q)
    _ = ((stencil n p).card : ℝ) * 16 := by simp
    _ ≤ 384 := by
      have hc : ((stencil n p).card : ℝ) ≤ 24 := by exact_mod_cast stencil_card n p
      linarith

end
end UnifiedTheory.Clay.YangMills.WilsonBlockNoiseKernel
