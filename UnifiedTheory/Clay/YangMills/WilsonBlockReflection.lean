/- Exact reflection on selected and retained Wilson link coordinates.
The selected set must be reflection stable. No continuum positivity floor
or spatial decay estimate is assumed or proved. -/
import UnifiedTheory.Clay.YangMills.GibbsReflectionResponse
import UnifiedTheory.Clay.YangMills.WilsonCrossCovariance
import UnifiedTheory.Clay.YangMills.PeriodicPlaquetteReflection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBlockReflection
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 PeriodicTimeReflection
open PeriodicPlaquetteReflection WilsonBlockMarginal WilsonCrossCovariance
open WilsonSeparatedSources GibbsMarginalTower GibbsCrossCovariance

variable (n : ℕ) [NeZero n]
local instance : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance : DecidableEq (WilsonIndependentBlocks.Link n) := Classical.decEq _

def Stable (S : Finset (Edge (Vertex n))) : Prop :=
  ∀ e, edgeEquiv n e ∈ S ↔ e ∈ S

/-- A concrete nonempty independent block: all temporal links on one
periodic line through the spatial origin. -/
def timeLine : Finset (Edge (Vertex n)) :=
  (WilsonIndependentBlocks.parallelLine n (fun _ => 0) 0).image
    (fun a => WilsonUniformVariance.selectedLink n a.1 a.2)

theorem timeLine_coordinates :
    (timeLine n).image (WilsonIndependentBlocks.edgeCoord n) =
      WilsonIndependentBlocks.parallelLine n (fun _ => 0) 0 := by
  simp only [timeLine, Finset.image_image, Function.comp_def,
    WilsonIndependentBlocks.edgeCoord_selected, Finset.image_id']

theorem timeLine_independent :
    WilsonIndependentBlocks.Independent n
      ((timeLine n).image (WilsonIndependentBlocks.edgeCoord n)) := by
  rw [timeLine_coordinates]
  exact WilsonIndependentBlocks.parallelLine_independent n (fun _ => 0) 0

omit [NeZero n] in
theorem reflected_time_link (t : ZMod n) :
    edgeEquiv n (WilsonUniformVariance.selectedLink n
      (Function.update (fun _ => 0) 0 t) 0) =
      WilsonUniformVariance.selectedLink n
        (Function.update (fun _ => 0) 0 (-t - 1)) 0 := by
  apply (edgeCoordinates n).injective
  change reflectIndex n (Function.update (fun _ => 0) 0 t, 0) =
    (Function.update (fun _ => 0) 0 (-t - 1), 0)
  apply Prod.ext
  · funext j
    by_cases hj : j = 0
    · subst j
      simp [reflectIndex, reflectVertex, step]
      ring
    · simp [reflectIndex, reflectVertex, step, hj]
  · rfl

theorem timeLine_reflected_mem (e : Edge (Vertex n)) (he : e ∈ timeLine n) :
    edgeEquiv n e ∈ timeLine n := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  have ha' : ∃ t : ZMod n, (Function.update (fun _ : Fin 4 => 0) 0 t, 0) = a := by
    simpa only [WilsonIndependentBlocks.parallelLine, Finset.mem_image,
      Finset.mem_univ, true_and] using ha
  obtain ⟨t, rfl⟩ := ha'
  rw [reflected_time_link]
  apply Finset.mem_image.mpr
  refine ⟨(Function.update (fun _ => 0) 0 (-t - 1), 0), ?_, rfl⟩
  simp only [WilsonIndependentBlocks.parallelLine, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact ⟨-t - 1, rfl⟩

theorem timeLine_stable : Stable n (timeLine n) := by
  intro e
  constructor
  · intro he
    have hh := timeLine_reflected_mem n _ he
    rw [edgeEquiv_involutive n e] at hh
    exact hh
  · exact timeLine_reflected_mem n e

theorem timeLine_card : (timeLine n).card = n := by
  have hinj : Function.Injective
      (fun a : WilsonIndependentBlocks.Link n =>
        WilsonUniformVariance.selectedLink n a.1 a.2) := by
    intro a b h
    have h' := congrArg (WilsonIndependentBlocks.edgeCoord n) h
    simpa only [WilsonIndependentBlocks.edgeCoord_selected] using h'
  rw [timeLine, Finset.card_image_of_injective _ hinj]
  exact WilsonIndependentBlocks.parallelLine_card n (fun _ => 0) 0

def reflectedWeights (f : PlaquetteIndex n → ℝ) : PlaquetteIndex n → ℝ :=
  fun p => f (reflectPlaquette n p)

omit [NeZero n] in
theorem affected_reflected_time (x : Vertex n) (p : PlaquetteIndex n)
    (hp : p ∈ SingleLinkWilsonOscillation.affected n x 0) :
    (reflectPlaquette n p).1 0 = -x 0 - 1 := by
  have ht := WilsonIndependentBlocks.affected_preserves_parallel_coordinate n x 0 p hp
  have hplane := ((WilsonIndependentBlocks.mem_affected_iff n x 0 p).mp hp).1
  have hfirst : p.2.1.1 = 0 := by
    have he : p.2.1.1 = 0 ∨ p.2.1.2 = 0 := by
      simpa [SingleLinkWilsonOscillation.planes] using hplane
    rcases he with he | he
    · exact he
    · have hlt := p.2.2
      rw [he] at hlt
      exact False.elim ((not_lt_of_ge (Fin.zero_le _)) hlt)
  simp [reflectPlaquette, reflectIndex, hfirst, reflectVertex, step, ht]
  ring

/-- Time support separated from its shifted reflection supplies the actual
affected-plaquette separation for this nonempty independent block. -/
theorem timeLine_separated (T : Set (ZMod n)) (f : PlaquetteIndex n → ℝ)
    (hf : ∀ p, p.1 0 ∉ T → f p = 0)
    (hT : ∀ t ∈ T, -t - 1 ∉ T) :
    SeparatedOnBlock n (timeLine n) (reflectedWeights n f) f := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  have ha' : ∃ t : ZMod n, (Function.update (fun _ : Fin 4 => 0) 0 t, 0) = a := by
    simpa only [WilsonIndependentBlocks.parallelLine, Finset.mem_image,
      Finset.mem_univ, true_and] using ha
  obtain ⟨t, rfl⟩ := ha'
  by_cases ht : t ∈ T
  · left
    intro p hp
    apply hf
    have heq := affected_reflected_time n (Function.update (fun _ => 0) 0 t) p hp
    simpa [heq] using hT t ht
  · right
    intro p hp
    apply hf
    have heq := WilsonIndependentBlocks.affected_preserves_parallel_coordinate n
      (Function.update (fun _ => 0) 0 t) 0 p hp
    simpa [heq] using ht

section Part
variable (P : Edge (Vertex n) → Prop) (hP : ∀ e, P (edgeEquiv n e) ↔ P e)

def partIndex : {e : Edge (Vertex n) // P e} ≃ {e : Edge (Vertex n) // P e} where
  toFun e := ⟨edgeEquiv n e.1, (hP e.1).mpr e.2⟩
  invFun e := ⟨edgeEquiv n e.1, (hP e.1).mpr e.2⟩
  left_inv e := Subtype.ext (edgeEquiv_involutive n e.1)
  right_inv e := Subtype.ext (edgeEquiv_involutive n e.1)

variable (G : Type*) [Group G]

def partReflection (U : {e : Edge (Vertex n) // P e} → G) :
    {e : Edge (Vertex n) // P e} → G :=
  fun e => if e.1.2.2.val = 0 then (U (partIndex n P hP e))⁻¹ else U (partIndex n P hP e)

omit [NeZero n] in
theorem partReflection_involutive : Function.Involutive (partReflection n P hP G) := by
  intro U
  funext e
  have hdir : (partIndex n P hP e).1.2.2.val = e.1.2.2.val := rfl
  have hii : partIndex n P hP (partIndex n P hP e) = e :=
    Subtype.ext (edgeEquiv_involutive n e.1)
  by_cases he : e.1.2.2.val = 0 <;> simp [partReflection, hdir, hii, he]

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [NeZero n] in
theorem partReflection_continuous : Continuous (partReflection n P hP G) := by
  apply continuous_pi
  intro e
  by_cases he : e.1.2.2.val = 0
  · simpa only [partReflection, he, if_true] using (continuous_apply (partIndex n P hP e)).inv
  · simpa only [partReflection, he, if_false] using continuous_apply (partIndex n P hP e)

variable [MeasurableSpace G] [BorelSpace G]

omit [NeZero n] in
theorem partReflection_measurable : Measurable (partReflection n P hP G) := by
  apply measurable_pi_lambda
  intro e
  by_cases he : e.1.2.2.val = 0
  · simpa only [partReflection, he, if_true] using
      (measurable_pi_apply (partIndex n P hP e)).inv
  · simpa only [partReflection, he, if_false] using
      measurable_pi_apply (partIndex n P hP e)

def partReflectionEquiv :
    ({e : Edge (Vertex n) // P e} → G) ≃ᵐ ({e : Edge (Vertex n) // P e} → G) :=
  MeasurableEquiv.ofInvolutive (partReflection n P hP G)
    (partReflection_involutive n P hP G) (partReflection_measurable n P hP G)

variable [CompactSpace G] [SecondCountableTopology G] [DecidablePred P]

theorem partReflection_preserving :
    MeasurePreserving (partReflectionEquiv n P hP G)
      (Measure.pi (fun _ : {e : Edge (Vertex n) // P e} => compactHaar G))
      (Measure.pi (fun _ : {e : Edge (Vertex n) // P e} => compactHaar G)) := by
  have hp : MeasurePreserving
      (fun U : {e : Edge (Vertex n) // P e} → G => U ∘ partIndex n P hP)
      (Measure.pi (fun _ : {e : Edge (Vertex n) // P e} => compactHaar G))
      (Measure.pi (fun _ : {e : Edge (Vertex n) // P e} => compactHaar G)) := by
    have h := measurePreserving_piCongrLeft
      (fun _ : {e : Edge (Vertex n) // P e} => compactHaar G) (partIndex n P hP).symm
    convert h using 1
    funext U e
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have hi : MeasurePreserving
      (fun U : {e : Edge (Vertex n) // P e} → G =>
        fun e => if e.1.2.2.val = 0 then (U e)⁻¹ else U e)
      (Measure.pi (fun _ : {e : Edge (Vertex n) // P e} => compactHaar G))
      (Measure.pi (fun _ : {e : Edge (Vertex n) // P e} => compactHaar G)) := by
    refine measurePreserving_pi
      (fun _ : {e : Edge (Vertex n) // P e} => compactHaar G)
      (fun _ : {e : Edge (Vertex n) // P e} => compactHaar G)
      (f := fun e u => if e.1.2.2.val = 0 then u⁻¹ else u) ?_
    intro e
    by_cases he : e.1.2.2.val = 0
    · simpa only [he, if_true] using compactHaar_preserves_inv G
    · simpa only [he, if_false] using MeasurePreserving.id (compactHaar G)
  exact hi.comp hp
end Part

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (S : Finset (Edge (Vertex n))) (hS : Stable n S)

def outsideReflection : Outside (G := G) S ≃ᵐ Outside (G := G) S :=
  partReflectionEquiv n (fun e => e ∉ S) (fun e => not_congr (hS e)) G

def insideReflection : Inside (G := G) S ≃ᵐ Inside (G := G) S :=
  partReflectionEquiv n (fun e => e ∈ S) hS G

theorem insideReflection_preserving :
    MeasurePreserving (insideReflection n G S hS)
      (insideMeasure S (compactHaar G)) (insideMeasure S (compactHaar G)) :=
  by
    have he : Finset.Subtype.fintype S = Subtype.fintype (fun e : Edge (Vertex n) => e ∈ S) :=
      Subsingleton.elim _ _
    simpa only [insideReflection, insideMeasure, he] using
      partReflection_preserving n (fun e => e ∈ S) hS G

theorem outsideReflection_preserving :
    MeasurePreserving (outsideReflection n G S hS)
      (outsideMeasure S (compactHaar G)) (outsideMeasure S (compactHaar G)) :=
  partReflection_preserving n (fun e => e ∉ S) (fun e => not_congr (hS e)) G

omit [NeZero n] [CompactSpace G] [SecondCountableTopology G] in
theorem assemble_reflection (b : Outside (G := G) S) (x : Inside (G := G) S) :
    assemble S (outsideReflection n G S hS b, insideReflection n G S hS x) =
      reflectConfiguration n G (assemble S (b, x)) := by
  funext e
  by_cases he : e ∈ S
  · have hr := (hS e).mpr he
    rw [assemble_inside S _ e he]
    change (if e.2.2.val = 0 then (x ⟨edgeEquiv n e, hr⟩)⁻¹ else x ⟨edgeEquiv n e, hr⟩) = _
    simp only [reflectConfiguration, assemble_inside S (b, x) (edgeEquiv n e) hr]
  · have hr : edgeEquiv n e ∉ S := fun h => he ((hS e).mp h)
    rw [assemble_outside S _ e he]
    change (if e.2.2.val = 0 then (b ⟨edgeEquiv n e, hr⟩)⁻¹ else b ⟨edgeEquiv n e, hr⟩) = _
    simp only [reflectConfiguration, assemble_outside S (b, x) (edgeEquiv n e) hr]

omit [CompactSpace G] [SecondCountableTopology G] in
theorem splitAction_reflection (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (b : Outside (G := G) S) (x : Inside (G := G) S) :
    splitAction n G χ β c S (outsideReflection n G S hS b, insideReflection n G S hS x) =
      splitAction n G χ β c S (b, x) := by
  unfold splitAction
  rw [assemble_reflection n G S hS]
  exact wilsonAction_reflection n G χ hχ hinv β c _

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem source_reflection (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (c : ℝ) (f : PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) G) :
    WilsonBlockIntegration.source n G χ c f (reflectConfiguration n G U) =
      WilsonBlockIntegration.source n G χ c (reflectedWeights n f) U := by
  have hlo (V : Configuration (Vertex n) G) (p : PlaquetteIndex n) :
      WilsonMomentBounds.loopObservable (Vertex n) G χ (loops n p) V =
        χ (plaquetteProduct n G V p.1 p.2.1.1 p.2.1.2) :=
    congrArg χ (plaquette_holonomy_eq_product n G V p.1 p.2.1.1 p.2.1.2)
  unfold WilsonBlockIntegration.source WilsonIndependentBlocks.plaquetteTerm
  simp only [hlo]
  simp_rw [reflected_plaquette_character n G χ hχ hinv U]
  have h := Equiv.sum_comp (plaquetteEquiv n)
    (fun p => f (reflectPlaquette n p) *
      (c - (χ (plaquetteProduct n G U p.1 p.2.1.1 p.2.1.2)).re))
  have hp (p : PlaquetteIndex n) : reflectPlaquette n (reflectPlaquette n p) = p :=
    reflectPlaquette_involutive n p
  simpa only [plaquetteEquiv, Function.Involutive.coe_toPerm,
    hp, reflectedWeights] using h

omit [CompactSpace G] [SecondCountableTopology G] in
theorem splitSource_reflection (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (c : ℝ) (f : PlaquetteIndex n → ℝ)
    (b : Outside (G := G) S) (x : Inside (G := G) S) :
    splitSource n G χ c S f (outsideReflection n G S hS b, insideReflection n G S hS x) =
      splitSource n G χ c S (reflectedWeights n f) (b, x) := by
  unfold splitSource
  rw [assemble_reflection n G S hS]
  exact source_reflection n G χ hχ hinv c f _

/-- Conditional expectation commutes with the actual reflected retained
coordinates. This identity is proved from Haar transport and Wilson symmetry. -/
theorem retainedSource_reflection (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ) (f : PlaquetteIndex n → ℝ)
    (b : Outside (G := G) S) :
    retainedSource n G χ β c S f (outsideReflection n G S hS b) =
      retainedSource n G χ β c S (reflectedWeights n f) b := by
  unfold retainedSource
  rw [GibbsReflectionResponse.response_reflection _ (outsideReflection n G S hS)
    (insideReflection n G S hS) (insideReflection_preserving n G S hS)
    _ (splitAction_reflection n G S hS χ hχ hinv β c)]
  congr 1
  funext p
  exact splitSource_reflection n G S hS χ hχ hinv c f p.1 p.2

omit [NeZero n] [CompactSpace G] [SecondCountableTopology G] in
theorem split_reflection (U : Configuration (Vertex n) G) :
    (assemble S).symm (reflectConfiguration n G U) =
      (outsideReflection n G S hS ((assemble S).symm U).1,
        insideReflection n G S hS ((assemble S).symm U).2) := by
  apply (assemble S).injective
  rw [MeasurableEquiv.apply_symm_apply, assemble_reflection n G S hS,
    MeasurableEquiv.apply_symm_apply]

include hS in
theorem removedSource_reflection (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ) (f : PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) G) :
    removedSource n G χ β c S f (reflectConfiguration n G U) =
      removedSource n G χ β c S (reflectedWeights n f) U := by
  unfold removedSource
  rw [source_reflection n G χ hχ hinv, split_reflection n G S hS]
  rw [retainedSource_reflection n G S hS χ hχ hinv]

theorem reflected_product_preserved (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (hi : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (f g : PlaquetteIndex n → ℝ) (hsep : SeparatedOnBlock n S (reflectedWeights n f) g) :
    (∫ U, WilsonBlockIntegration.source n G χ c f (reflectConfiguration n G U) *
      WilsonBlockIntegration.source n G χ c g U ∂wilsonLaw n G χ β c) =
      ∫ b, retainedSource n G χ β c S f (outsideReflection n G S hS b) *
        retainedSource n G χ β c S g b ∂retainedLaw n G χ β c S := by
  simp only [source_reflection n G χ hχ hinv,
    retainedSource_reflection n G S hS χ hχ hinv]
  exact source_product_preserved n G χ hcχ β c S hi _ g hsep

include hS in
/-- Exact zero reflected pairing in the original interacting Wilson law.
Positive-half support membership is a separate condition for OS quotient use. -/
theorem removed_reflected_zero (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (hi : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (f g : PlaquetteIndex n → ℝ) (hsep : SeparatedOnBlock n S (reflectedWeights n f) g) :
    (∫ U, removedSource n G χ β c S f (reflectConfiguration n G U) *
      removedSource n G χ β c S g U ∂wilsonLaw n G χ β c) = 0 := by
  simp only [removedSource_reflection n G S hS χ hχ hinv]
  exact WilsonCrossCovariance.removed_product_zero n G χ hcχ β c S hi _ g hsep

theorem timeLine_removed_reflected_zero (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (T : Set (ZMod n)) (f : PlaquetteIndex n → ℝ)
    (hf : ∀ p, p.1 0 ∉ T → f p = 0) (hT : ∀ t ∈ T, -t - 1 ∉ T) :
    (∫ U, removedSource n G χ β c (timeLine n) f (reflectConfiguration n G U) *
      removedSource n G χ β c (timeLine n) f U ∂wilsonLaw n G χ β c) = 0 :=
  removed_reflected_zero n G (timeLine n) (timeLine_stable n) χ hcχ hχ hinv β c
    (timeLine_independent n) f f (timeLine_separated n T f hf hT)

end
end UnifiedTheory.Clay.YangMills.WilsonBlockReflection
