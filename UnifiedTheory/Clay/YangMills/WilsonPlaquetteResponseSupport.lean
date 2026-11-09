/- Actual support of the normalized retained plaquette response after integrating
an independent Wilson block. Product-law cancellation is derived from the exact
Wilson action/source decomposition, not supplied as a locality hypothesis. -/
import UnifiedTheory.Clay.YangMills.WilsonInducedSupport
import UnifiedTheory.Clay.YangMills.SU2WilsonBlockApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonPlaquetteResponseSupport
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance WilsonMomentBounds
open WilsonIndependentBlocks WilsonInfluenceGeometry SingleLinkWilsonOscillation
open WilsonInducedSupport

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (PlaquetteIndex n) := Classical.decEq _

def delta (p : PlaquetteIndex n) (q : PlaquetteIndex n) : ℝ := if q = p then 1 else 0

/-- The same actual neighborhood, indexed by the retained-coordinate subtype. -/
def outsideSupport (S : Finset (Edge (Vertex n))) (p : PlaquetteIndex n) :
    Finset {e : Edge (Vertex n) // e ∉ S} :=
  (responseSupport n S p).subtype (fun e => e ∉ S)

omit [NeZero n] in
theorem mem_outsideSupport (S : Finset (Edge (Vertex n))) (p : PlaquetteIndex n)
    (e : {e : Edge (Vertex n) // e ∉ S}) :
    e ∈ outsideSupport n S p ↔ e.val ∈ responseSupport n S p := Finset.mem_subtype

theorem outsideSupport_card (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (p : PlaquetteIndex n) :
    (outsideSupport n S p).card ≤ 18 := by
  rw [outsideSupport, Finset.card_subtype]
  exact (Finset.card_filter_le _ _).trans (responseSupport_card n S hS p)

variable (G : Type*) [Group G]

theorem delta_source (χ : G → ℂ) (c : ℝ) (p : PlaquetteIndex n)
    (U : Configuration (Vertex n) G) :
    WilsonBlockIntegration.source n G χ c (delta n p) U = plaquetteTerm n G χ c U p := by
  simp [WilsonBlockIntegration.source, delta]

omit [NeZero n] in
theorem plaquette_remainder_subset (S : Finset (Edge (Vertex n))) (p : PlaquetteIndex n) :
    plaquetteEdges n p \ S ⊆ responseSupport n S p := by
  intro e he
  obtain ⟨hep, heS⟩ := Finset.mem_sdiff.mp he
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hep, heS⟩

omit [NeZero n] in
theorem touched_star_subset (S : Finset (Edge (Vertex n))) (p : PlaquetteIndex n)
    (e : Edge (Vertex n)) (he : e ∈ S) (hep : e ∈ plaquetteEdges n p) :
    retainedStar n S e ⊆ responseSupport n S p := by
  intro d hd
  obtain ⟨hde, hdS⟩ := Finset.mem_sdiff.mp hd
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨e, Finset.mem_inter.mpr ⟨hep, he⟩, hde⟩), hdS⟩

variable [MeasurableSpace G]

omit [NeZero n] in
theorem reference_eq_assemble (S : Finset (Edge (Vertex n)))
    (U : Configuration (Vertex n) G) :
    reference n G S U = WilsonBlockMarginal.assemble S ((fun e => U e.val), fun _ => 1) := by
  funext e
  by_cases he : e ∈ S
  · rw [WilsonBlockMarginal.assemble_inside S _ e he]
    simp only [reference, if_pos he]
  · rw [WilsonBlockMarginal.assemble_outside S _ e he]
    simp only [reference, if_neg he]

omit [NeZero n] [Group G] in
/-- Restriction to the genuine retained subtype preserves proved coordinate dependence. -/
theorem outside_dependsOn_of_lift (S D : Finset (Edge (Vertex n)))
    (hD : ∀ e ∈ D, e ∉ S) (F : WilsonBlockMarginal.Outside (G := G) S → ℝ)
    (hF : DependsOn (fun U : Configuration (Vertex n) G => F (fun e => U e.val))
      (D : Set _)) (q₀ : G) :
    DependsOn F (D.subtype (fun e => e ∉ S) : Set _) := by
  intro b b' hbb'
  let U := WilsonBlockMarginal.assemble S (b, fun _ => q₀)
  let V := WilsonBlockMarginal.assemble S (b', fun _ => q₀)
  have he (b : WilsonBlockMarginal.Outside (G := G) S) :
      (fun e : {e : Edge (Vertex n) // e ∉ S} =>
        WilsonBlockMarginal.assemble S (b, fun _ => q₀) e.val) = b := by
    funext e
    exact WilsonBlockMarginal.assemble_outside S _ e.val e.property
  have h := hF (x := U) (y := V) (by
    intro e hep
    have heS := hD e hep
    change WilsonBlockMarginal.assemble S (b, fun _ => q₀) e =
      WilsonBlockMarginal.assemble S (b', fun _ => q₀) e
    rw [WilsonBlockMarginal.assemble_outside S _ e heS,
      WilsonBlockMarginal.assemble_outside S _ e heS]
    exact hbb' ⟨e, heS⟩ (Finset.mem_subtype.mpr hep))
  simpa only [U, V, he] using h

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [BorelSpace G]

/-- The literal first-stage normalized conditional response, lifted to original coordinates. -/
def response (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n))) (p : PlaquetteIndex n)
    (U : Configuration (Vertex n) G) : ℝ :=
  GibbsMarginalTower.response (WilsonBlockMarginal.insideMeasure S (compactHaar G))
    (WilsonBlockMarginal.splitAction n G χ β c S)
    (fun z => plaquetteTerm n G χ c (WilsonBlockMarginal.assemble S z) p)
    (fun e => U e.val)

/-- Exact mean decomposition under the actual selected-subtype conditional Haar law. -/
theorem response_eq_sum (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (hS : Independent n (S.image (edgeCoord n)))
    (p : PlaquetteIndex n) (U : Configuration (Vertex n) G) :
    response n G χ β c S p U = plaquetteTerm n G χ c (reference n G S U) p +
      ∑ e : {e : Edge (Vertex n) // e ∈ S},
        ∫ q, (plaquetteTerm n G χ c (Function.update (reference n G S U) e.val q) p -
          plaquetteTerm n G χ c (reference n G S U) p)
          ∂CompactGibbsContinuity.law (compactHaar G) (fun q =>
            WilsonBlockIntegration.action n G χ β c
              (Function.update (reference n G S U) e.val q) -
              WilsonBlockIntegration.action n G χ β c (reference n G S U)) := by
  let b : WilsonBlockMarginal.Outside (G := G) S := fun e => U e.val
  let W := reference n G S U
  let A : {e : Edge (Vertex n) // e ∈ S} → G → ℝ := fun e q =>
    WilsonBlockIntegration.action n G χ β c (Function.update W e.val q) -
      WilsonBlockIntegration.action n G χ β c W
  let F : {e : Edge (Vertex n) // e ∈ S} → G → ℝ := fun e q =>
    plaquetteTerm n G χ c (Function.update W e.val q) p - plaquetteTerm n G χ c W p
  have he : W = WilsonBlockMarginal.assemble S (b, fun _ => 1) :=
    reference_eq_assemble n G S U
  have hA (e : {e : Edge (Vertex n) // e ∈ S}) : Continuous (A e) :=
    ((continuous_orientedWilsonAction _ G χ hχ (base n) (loops n) β c).comp
      (WilsonSeparatedSources.edge_update_continuous n G W e.val)).sub continuous_const
  have hP : Continuous (fun V => plaquetteTerm n G χ c V p) := by
    have heq : WilsonBlockIntegration.source n G χ c (delta n p) =
        (fun V => plaquetteTerm n G χ c V p) := funext (delta_source n G χ c p)
    rw [← heq]
    exact WilsonBlockIntegration.source_continuous n G χ hχ c (delta n p)
  have hF (e : {e : Edge (Vertex n) // e ∈ S}) : Continuous (F e) :=
    (hP.comp (WilsonSeparatedSources.edge_update_continuous n G W e.val)).sub continuous_const
  have hact (V : WilsonBlockMarginal.Inside (G := G) S) :
      WilsonBlockMarginal.splitAction n G χ β c S (b, V) =
        WilsonBlockIntegration.action n G χ β c W + ∑ e, A e (V e) := by
    dsimp only [A]
    rw [he]
    exact WilsonSeparatedSources.inside_action_sum n G χ β c S hS b V
  have hsrc (V : WilsonBlockMarginal.Inside (G := G) S) :
      plaquetteTerm n G χ c (WilsonBlockMarginal.assemble S (b, V)) p =
        plaquetteTerm n G χ c W p + ∑ e, F e (V e) := by
    have h := WilsonSeparatedSources.inside_source_sum n G χ c (delta n p) S hS b V
    simpa only [WilsonSeparatedSources.splitSource, delta_source, ← he] using h
  rw [response, GibbsMarginalTower.response_eq_expectation _ _ _
    (WilsonBlockMarginal.splitAction_continuous n G χ hχ β c S)]
  change (∫ V, plaquetteTerm n G χ c (WilsonBlockMarginal.assemble S (b, V)) p
    ∂CompactGibbsContinuity.law (WilsonBlockMarginal.insideMeasure S (compactHaar G))
      (fun V => WilsonBlockMarginal.splitAction n G χ β c S (b, V))) = _
  simp_rw [hact, hsrc]
  exact SU2WilsonBlockApproximation.affine_product_mean (compactHaar G) A F hA hF
    (WilsonBlockIntegration.action n G χ β c W) (plaquetteTerm n G χ c W p)

/-- First integration preserves a concrete finite dependency neighborhood for the true response. -/
theorem response_dependsOn (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (hS : Independent n (S.image (edgeCoord n)))
    (p : PlaquetteIndex n) :
    DependsOn (response n G χ β c S p) (responseSupport n S p : Set _) := by
  intro U V hUV
  rw [response_eq_sum n G χ hχ β c S hS p U, response_eq_sum n G χ hχ β c S hS p V]
  have hb : plaquetteTerm n G χ c (reference n G S U) p =
      plaquetteTerm n G χ c (reference n G S V) p :=
    plaquette_reference_dependsOn n G χ c S p
      (fun d hd => hUV d (plaquette_remainder_subset n S p hd))
  rw [hb]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases hep : e.val ∈ plaquetteEdges n p
  · have hs := touched_star_subset n S p e.val e.property hep
    have hA : (fun q =>
        WilsonBlockIntegration.action n G χ β c (Function.update (reference n G S U) e.val q) -
          WilsonBlockIntegration.action n G χ β c (reference n G S U)) =
        (fun q =>
        WilsonBlockIntegration.action n G χ β c (Function.update (reference n G S V) e.val q) -
          WilsonBlockIntegration.action n G χ β c (reference n G S V)) := by
      funext q
      exact increment_reference_dependsOn n G χ β c S e.val q (fun d hd => hUV d (hs hd))
    rw [hA]
    apply integral_congr_ae
    filter_upwards with q
    have hF := source_increment_reference_dependsOn n G χ c (delta n p) S e.val q
      (fun d hd => hUV d (hs hd))
    simpa only [delta_source, hb] using hF
  · have hU (q : G) := WilsonInducedSupport.term_update_unchanged n G χ c p e.val hep
      (reference n G S U) q
    have hV (q : G) := WilsonInducedSupport.term_update_unchanged n G χ c p e.val hep
      (reference n G S V) q
    simp_rw [hU, hV, hb, sub_self, integral_zero]

/-- Actual normalized first responses are local as functions of the genuine retained coordinates. -/
theorem outside_response_dependsOn (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (hS : Independent n (S.image (edgeCoord n)))
    (p : PlaquetteIndex n) :
    DependsOn
      (GibbsMarginalTower.response (WilsonBlockMarginal.insideMeasure S (compactHaar G))
        (WilsonBlockMarginal.splitAction n G χ β c S)
        (fun z => plaquetteTerm n G χ c (WilsonBlockMarginal.assemble S z) p))
      (outsideSupport n S p : Set _) := by
  apply outside_dependsOn_of_lift n G S (responseSupport n S p)
    (fun e he => (Finset.mem_sdiff.mp he).2) _ _ (1 : G)
  exact response_dependsOn n G χ hχ β c S hS p

omit [SecondCountableTopology G] in
/-- The lifted response is exactly the repo's two-split first response, on the same original law. -/
theorem firstResponse_eq_response (χ : G → ℂ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (p : PlaquetteIndex n)
    (z : WilsonBlockMarginal.Outside (G := G) T × WilsonBlockMarginal.Inside (G := G) T) :
    WilsonBlockMarginal.firstResponse n G χ β c S T (fun U => plaquetteTerm n G χ c U p) z =
      response n G χ β c S p
        (WilsonBlockMarginal.assemble S (WilsonBlockMarginal.assemble T z, fun _ => 1)) := by
  have hb : (fun e : {e : Edge (Vertex n) // e ∉ S} =>
      WilsonBlockMarginal.assemble S (WilsonBlockMarginal.assemble T z, fun _ => (1 : G)) e.val) =
      WilsonBlockMarginal.assemble T z := by
    funext e
    exact WilsonBlockMarginal.assemble_outside S _ e.val e.property
  unfold response WilsonBlockMarginal.firstResponse GibbsMarginalTower.response
    GibbsMarginalTower.fiberMass
  rw [hb]
  rfl

end
end UnifiedTheory.Clay.YangMills.WilsonPlaquetteResponseSupport
