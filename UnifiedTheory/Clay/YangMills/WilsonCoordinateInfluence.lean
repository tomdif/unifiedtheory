/-
Actual full-coordinate Wilson conditional influence, including repeated
period-two neighbors. Staple locality is derived from the actual plaquette
trace dictionary; only shared plaquettes contribute. The normalized conditional
laws obey the proved symmetric multiplicity majorant on both continuous tests
and every measurable event. No global mixing or physical transfer estimate is
assumed or claimed.
-/
import UnifiedTheory.Clay.YangMills.SU2WilsonConditionalInfluence
import UnifiedTheory.Clay.YangMills.SU2StarEnergy
import UnifiedTheory.Clay.YangMills.WilsonInfluenceGeometry
import UnifiedTheory.Clay.YangMills.ContinuousTestVariation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCoordinateInfluence
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples WilsonIndependentBlocks SingleLinkWilsonOscillation
open PeriodicPlaquetteReflection SU2StarEnergy SU2WilsonConditionalSource
open scoped Quaternion RealInnerProductSpace
variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (PlaquetteIndex n) := Classical.decEq _

omit [NeZero n] in
/-- The actual staple is determined by the links of its own plaquette. -/
theorem staple_congr_of_incident (a : Link n) (p : PlaquetteIndex n)
    (hp : p ∈ affected n a.1 a.2) (U V : Configuration (Vertex n) Q)
    (hUV : ∀ e : Edge (Vertex n), incident n p (edgeCoord n e) → U e = V e) :
    staple n Q U a.1 a.2 p = staple n Q V a.1 a.2 p := by
  classical
  have hi (q : Q) : inner ℝ (q : ℍ) (staple n Q U a.1 a.2 p : ℍ) =
      inner ℝ (q : ℍ) (staple n Q V a.1 a.2 p : ℍ) := by
    have hh := plaquette_congr n Q p (replaceLink n Q U a.1 a.2 q)
      (replaceLink n Q V a.1 a.2 q) (by
        intro e he
        by_cases h : e = selectedLink n a.1 a.2
        · subst e; simp [replaceLink]
        · unfold replaceLink
          rw [Function.update_of_ne h, Function.update_of_ne h]
          exact hUV e he)
    change holonomy _ Q _ (plaquette n p.1 p.2.1.1 p.2.1.2) =
      holonomy _ Q _ (plaquette n p.1 p.2.1.1 p.2.1.2) at hh
    rw [plaquette_holonomy_eq_product, plaquette_holonomy_eq_product] at hh
    have ht := congrArg (fun z : Q => (character z).re) hh
    dsimp only at ht
    rw [plaquette_character_replace n U a.1 a.2 q p hp,
      plaquette_character_replace n V a.1 a.2 q p hp] at ht
    linarith
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have h := hi (staple n Q U a.1 a.2 p)
  rw [real_inner_self_eq_norm_sq,
    CStarRing.norm_of_mem_unitary (staple n Q U a.1 a.2 p).property] at h
  have he := norm_sub_sq_real (staple n Q U a.1 a.2 p : ℍ)
    (staple n Q V a.1 a.2 p : ℍ)
  rw [CStarRing.norm_of_mem_unitary (staple n Q U a.1 a.2 p).property,
    CStarRing.norm_of_mem_unitary (staple n Q V a.1 a.2 p).property] at he
  nlinarith [norm_nonneg ((staple n Q U a.1 a.2 p : ℍ) -
    (staple n Q V a.1 a.2 p : ℍ))]

/-- Changing an exterior coordinate cannot change a staple of a nonincident plaquette. -/
theorem staple_eq_of_outside (a b : Link n) (p : PlaquetteIndex n)
    (hpa : p ∈ affected n a.1 a.2) (hpb : p ∉ affected n b.1 b.2)
    (U V : Configuration (Vertex n) Q)
    (hUV : ∀ e : Edge (Vertex n), e ≠ selectedLink n b.1 b.2 → U e = V e) :
    staple n Q U a.1 a.2 p = staple n Q V a.1 a.2 p := by
  apply staple_congr_of_incident n a p hpa U V
  intro e he
  apply hUV e
  intro hh
  subst e
  exact hpb (incident_affected n p b (by simpa only [edgeCoord_selected] using he))

/-- Only shared plaquettes contribute to the actual sum of changed unit staples. -/
theorem stapleSum_difference_bound (a b : Link n) (U V : Configuration (Vertex n) Q)
    (hUV : ∀ e : Edge (Vertex n), e ≠ selectedLink n b.1 b.2 → U e = V e) :
    ‖stapleSum n U a.1 a.2 - stapleSum n V a.1 a.2‖ ≤
      2 * ((affected n a.1 a.2 ∩ affected n b.1 b.2).card : ℝ) := by
  classical
  unfold stapleSum weightedStaple
  simp only [one_smul]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p ∈ affected n a.1 a.2,
        ((staple n Q U a.1 a.2 p : ℍ) - (staple n Q V a.1 a.2 p : ℍ))‖ ≤
        ∑ p ∈ affected n a.1 a.2,
          ‖(staple n Q U a.1 a.2 p : ℍ) - (staple n Q V a.1 a.2 p : ℍ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ affected n a.1 a.2, if p ∈ affected n b.1 b.2 then (2 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpb : p ∈ affected n b.1 b.2
      · rw [if_pos hpb]
        apply (norm_sub_le _ _).trans
        rw [CStarRing.norm_of_mem_unitary (staple n Q U a.1 a.2 p).property,
          CStarRing.norm_of_mem_unitary (staple n Q V a.1 a.2 p).property]
        norm_num
      · rw [if_neg hpb, staple_eq_of_outside n a b p hp hpb U V hUV]
        simp
    _ = 2 * ((affected n a.1 a.2 ∩ affected n b.1 b.2).card : ℝ) := by
      rw [← Finset.sum_filter]
      have he : (affected n a.1 a.2).filter (fun p => p ∈ affected n b.1 b.2) =
          affected n a.1 a.2 ∩ affected n b.1 b.2 := by ext p; simp
      rw [he]
      simp [mul_comm]

omit [Fact (1 < n)] in
/-- Exterior reconstruction preserves agreement away from a changed coordinate. -/
theorem exteriorConfig_agree_outside (a b : Link n) (U V : Configuration (Vertex n) Q)
    (hUV : ∀ e : Edge (Vertex n), e ≠ selectedLink n b.1 b.2 → U e = V e) :
    ∀ e : Edge (Vertex n), e ≠ selectedLink n b.1 b.2 →
      exteriorConfig n a.1 a.2 (exterior n a.1 a.2 U) e =
        exteriorConfig n a.1 a.2 (exterior n a.1 a.2 V) e := by
  intro e he
  unfold exteriorConfig
  by_cases hea : e = selectedLink n a.1 a.2
  · subst e
    rw [SingleCoordinateProduct.assemble_self, SingleCoordinateProduct.assemble_self]
  · rw [SingleCoordinateProduct.assemble_other _ _ hea,
      SingleCoordinateProduct.assemble_other _ _ hea]
    exact hUV e he

/-- The actual exterior staple field obeys the shared-plaquette norm estimate. -/
theorem stapleField_difference_intersection (a b : Link n)
    (U V : Configuration (Vertex n) Q)
    (hUV : ∀ e : Edge (Vertex n), e ≠ selectedLink n b.1 b.2 → U e = V e) :
    ‖stapleField n a.1 a.2 U - stapleField n a.1 a.2 V‖ ≤
      2 * ((affected n a.1 a.2 ∩ affected n b.1 b.2).card : ℝ) := by
  exact stapleSum_difference_bound n a b _ _ (exteriorConfig_agree_outside n a b U V hUV)

omit [NeZero n] [Fact (1 < n)] in
/-- The selected coordinate is absent from its own retained exterior. -/
theorem exterior_eq_of_agree_outside (a : Link n) (U V : Configuration (Vertex n) Q)
    (hUV : ∀ e : Edge (Vertex n), e ≠ selectedLink n a.1 a.2 → U e = V e) :
    exterior n a.1 a.2 U = exterior n a.1 a.2 V := by
  funext e
  exact hUV e.val e.property

/-- Changing one full Wilson coordinate changes the target staple field by at
most twice the actual number of shared plaquettes. The self-coordinate costs zero. -/
theorem stapleField_difference_bound (a b : Link n) (U V : Configuration (Vertex n) Q)
    (hUV : ∀ e : Edge (Vertex n), e ≠ selectedLink n b.1 b.2 → U e = V e) :
    ‖stapleField n a.1 a.2 U - stapleField n a.1 a.2 V‖ ≤
      2 * (WilsonInfluenceGeometry.multiplicity n a b : ℝ) := by
  classical
  by_cases hab : a = b
  · subst b
    unfold stapleField
    rw [exterior_eq_of_agree_outside n a U V hUV]
    simp
  · simpa only [WilsonInfluenceGeometry.multiplicity,
      WilsonInfluenceGeometry.sharedPlaquettes, if_neg hab] using
      stapleField_difference_intersection n a b U V hUV

/-- The proved symmetric lattice coefficient bounds the actual normalized
conditional distributions, tested against every continuous bounded observable. -/
theorem conditional_coordinate_influence (a b : Link n) (β : ℝ) (hβ : 0 ≤ β)
    (U V : Configuration (Vertex n) Q)
    (hUV : ∀ e : Edge (Vertex n), e ≠ selectedLink n b.1 b.2 → U e = V e)
    (G : Q → ℝ) (hG : Continuous G) (c d : ℝ) (hcd : c ≤ d)
    (hGb : ∀ q, G q ∈ Set.Icc c d) :
    |(∫ q, G q ∂conditionalLaw n a.1 a.2 β (exterior n a.1 a.2 U)) -
      (∫ q, G q ∂conditionalLaw n a.1 a.2 β (exterior n a.1 a.2 V))| ≤
        WilsonInfluenceGeometry.coefficient n β a b * (d - c) := by
  have h := SU2WilsonConditionalInfluence.conditional_expectation_difference n a.1 a.2 β
    (exterior n a.1 a.2 V) (exterior n a.1 a.2 U) hβ G hG c d hcd hGb
  have hn := stapleField_difference_bound n a b U V hUV
  have hm := mul_le_mul_of_nonneg_left hn (mul_nonneg hβ (sub_nonneg.mpr hcd))
  exact h.trans (by simpa only [WilsonInfluenceGeometry.coefficient, stapleField] using
    (by convert hm using 1; ring))

/-- The same bound for the repository's literal one-link replacement operation. -/
theorem conditional_replaceLink_influence (a b : Link n) (β : ℝ) (hβ : 0 ≤ β)
    (U : Configuration (Vertex n) Q) (v : Q)
    (G : Q → ℝ) (hG : Continuous G) (c d : ℝ) (hcd : c ≤ d)
    (hGb : ∀ q, G q ∈ Set.Icc c d) :
    |(∫ q, G q ∂conditionalLaw n a.1 a.2 β
        (exterior n a.1 a.2 (replaceLink n Q U b.1 b.2 v))) -
      (∫ q, G q ∂conditionalLaw n a.1 a.2 β (exterior n a.1 a.2 U))| ≤
        WilsonInfluenceGeometry.coefficient n β a b * (d - c) := by
  apply conditional_coordinate_influence n a b β hβ _ U _ G hG c d hcd hGb
  intro e he
  exact Function.update_of_ne he v U

omit [Fact (1 < n)] in
/-- Symmetry gives the matching column bound needed by a Hamming coupling. -/
theorem influence_column_bound (β : ℝ) (hβ : 0 ≤ β) (b : Link n) :
    ∑ a, WilsonInfluenceGeometry.coefficient n β a b ≤ 36 * β := by
  simp_rw [WilsonInfluenceGeometry.coefficient_symm n β _ b]
  exact WilsonInfluenceGeometry.coefficient_row_le n β hβ b

/-- Every measurable event obeys the actual Wilson coordinate-influence bound.
This is the probability total-variation convention `sup_E |mu(E) - nu(E)|`. -/
theorem conditional_event_influence (a b : Link n) (β : ℝ) (hβ : 0 ≤ β)
    (U V : Configuration (Vertex n) Q)
    (hUV : ∀ e : Edge (Vertex n), e ≠ selectedLink n b.1 b.2 → U e = V e)
    (s : Set Q) (hs : MeasurableSet s) :
    |(conditionalLaw n a.1 a.2 β (exterior n a.1 a.2 U)).real s -
      (conditionalLaw n a.1 a.2 β (exterior n a.1 a.2 V)).real s| ≤
        WilsonInfluenceGeometry.coefficient n β a b := by
  letI := conditionalLaw_probability n a.1 a.2 β (exterior n a.1 a.2 U)
  letI := conditionalLaw_probability n a.1 a.2 β (exterior n a.1 a.2 V)
  apply ContinuousTestVariation.measurable_event_abs_bound _ _ _
    (WilsonInfluenceGeometry.coefficient_nonneg n β hβ a b) _ s hs
  intro G hG hGb
  simpa using conditional_coordinate_influence n a b β hβ U V hUV G hG 0 1 (by norm_num) hGb

/-- The event bound also holds for a literal single-link replacement. -/
theorem conditional_replaceLink_event_influence (a b : Link n) (β : ℝ) (hβ : 0 ≤ β)
    (U : Configuration (Vertex n) Q) (v : Q) (s : Set Q) (hs : MeasurableSet s) :
    |(conditionalLaw n a.1 a.2 β
        (exterior n a.1 a.2 (replaceLink n Q U b.1 b.2 v))).real s -
      (conditionalLaw n a.1 a.2 β (exterior n a.1 a.2 U)).real s| ≤
        WilsonInfluenceGeometry.coefficient n β a b := by
  apply conditional_event_influence n a b β hβ _ U _ s hs
  intro e he
  exact Function.update_of_ne he v U

/-- The literal positive-link configuration associated with a Link-indexed state. -/
def toConfiguration (U : Link n → Q) : Configuration (Vertex n) Q :=
  fun e => U (edgeCoord n e)

/-- The actual one-site Wilson law in the Link indexing used by parallel product updates. -/
def coordinateLaw (β : ℝ) (U : Link n → Q) (a : Link n) : Measure Q :=
  conditionalLaw n a.1 a.2 β (exterior n a.1 a.2 (toConfiguration n U))

omit [Fact (1 < n)] in
theorem coordinateLaw_probability (β : ℝ) (U : Link n → Q) (a : Link n) :
    IsProbabilityMeasure (coordinateLaw n β U a) :=
  conditionalLaw_probability n a.1 a.2 β _

omit [NeZero n] [Fact (1 < n)] in
/-- Agreement away from a Link coordinate is agreement away from its actual edge. -/
theorem toConfiguration_agree_outside (b : Link n) (U V : Link n → Q)
    (hUV : ∀ c, c ≠ b → U c = V c) :
    ∀ e : Edge (Vertex n), e ≠ selectedLink n b.1 b.2 →
      toConfiguration n U e = toConfiguration n V e := by
  intro e he
  apply hUV (edgeCoord n e)
  intro hh
  apply he
  have hx := selected_edgeCoord n e
  rw [hh] at hx
  exact hx.symm

/-- The continuous-test influence estimate in literal product-state coordinates. -/
theorem coordinateLaw_influence (a b : Link n) (β : ℝ) (hβ : 0 ≤ β)
    (U V : Link n → Q) (hUV : ∀ c, c ≠ b → U c = V c)
    (G : Q → ℝ) (hG : Continuous G) (c d : ℝ) (hcd : c ≤ d)
    (hGb : ∀ q, G q ∈ Set.Icc c d) :
    |(∫ q, G q ∂coordinateLaw n β U a) - (∫ q, G q ∂coordinateLaw n β V a)| ≤
      WilsonInfluenceGeometry.coefficient n β a b * (d - c) :=
  conditional_coordinate_influence n a b β hβ _ _
    (toConfiguration_agree_outside n b U V hUV) G hG c d hcd hGb

/-- Actual total-variation control in the same coordinates as parallel product updates. -/
theorem coordinateLaw_event_influence (a b : Link n) (β : ℝ) (hβ : 0 ≤ β)
    (U V : Link n → Q) (hUV : ∀ c, c ≠ b → U c = V c)
    (s : Set Q) (hs : MeasurableSet s) :
    |(coordinateLaw n β U a).real s - (coordinateLaw n β V a).real s| ≤
      WilsonInfluenceGeometry.coefficient n β a b :=
  conditional_event_influence n a b β hβ _ _
    (toConfiguration_agree_outside n b U V hUV) s hs

end
end UnifiedTheory.Clay.YangMills.WilsonCoordinateInfluence
