/- Exact finite-coordinate splits for actual Wilson Gibbs measures. These
splits allow correlated retained links and do not assert a Wilson-form
closure of the effective action. -/
import UnifiedTheory.Clay.YangMills.WilsonBlockIntegration
import UnifiedTheory.Clay.YangMills.GibbsCoordinateTransport
import UnifiedTheory.Clay.YangMills.GibbsReflectionTransport
import UnifiedTheory.Clay.YangMills.GibbsMarginalTower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBlockMarginal
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 GibbsCoordinateTransport

section Coordinates
variable {I G : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace G]

abbrev Outside (S : Finset I) := {i : I // i ∉ S} → G
abbrev Inside (S : Finset I) := {i : I // i ∈ S} → G

abbrev outsideMeasure (S : Finset I) (μ : Measure G) : Measure (Outside (G := G) S) :=
  Measure.pi (fun _ : {i : I // i ∉ S} => μ)

abbrev insideMeasure (S : Finset I) (μ : Measure G) : Measure (Inside (G := G) S) :=
  Measure.pi (fun _ : {i : I // i ∈ S} => μ)

def assemble (S : Finset I) : Outside (G := G) S × Inside (G := G) S ≃ᵐ (I → G) :=
  (MeasurableEquiv.prodComm : Outside (G := G) S × Inside (G := G) S ≃ᵐ
    Inside (G := G) S × Outside (G := G) S).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => G) (fun i => i ∈ S)).symm

omit [Fintype I] in
@[simp] theorem assemble_inside (S : Finset I) (z : Outside (G := G) S × Inside (G := G) S)
    (i : I) (hi : i ∈ S) : assemble S z i = z.2 ⟨i, hi⟩ := by
  simp [assemble, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.prodComm, hi]

omit [Fintype I] in
@[simp] theorem assemble_outside (S : Finset I) (z : Outside (G := G) S × Inside (G := G) S)
    (i : I) (hi : i ∉ S) : assemble S z i = z.1 ⟨i, hi⟩ := by
  simp [assemble, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.prodComm, hi]

omit [Fintype I] in
theorem assemble_continuous [TopologicalSpace G] (S : Finset I) :
    Continuous (assemble (G := G) S) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ S
  · simpa only [assemble_inside S _ i hi] using
      ((continuous_apply (⟨i, hi⟩ : {i : I // i ∈ S})).comp continuous_snd :
        Continuous (fun z : Outside (G := G) S × Inside (G := G) S => z.2 ⟨i, hi⟩))
  · simpa only [assemble_outside S _ i hi] using
      ((continuous_apply (⟨i, hi⟩ : {i : I // i ∉ S})).comp continuous_fst :
        Continuous (fun z : Outside (G := G) S × Inside (G := G) S => z.1 ⟨i, hi⟩))

theorem assemble_preserving (S : Finset I) (μ : Measure G) [SigmaFinite μ] :
    MeasurePreserving (assemble S)
      ((Measure.pi (fun _ : {i : I // i ∉ S} => μ)).prod
        (Measure.pi (fun _ : {i : I // i ∈ S} => μ)))
      (Measure.pi (fun _ : I => μ)) := by
  exact ((measurePreserving_piEquivPiSubtypeProd (fun _ : I => μ) (fun i => i ∈ S)).symm
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => G) (fun i => i ∈ S))).comp
    (by
      have he : (Finset.Subtype.fintype S) = (Subtype.fintype (fun i : I => i ∈ S)) :=
        Subsingleton.elim _ _
      simpa only [MeasurableEquiv.prodComm, he] using
        (Measure.measurePreserving_swap (μ := Measure.pi (fun _ : {i : I // i ∉ S} => μ))
          (ν := Measure.pi (fun _ : {i : I // i ∈ S} => μ))))

/-- Two actual successive eliminations. The second block is a subset of
the retained first-stage coordinates; no conditional independence is needed. -/
def assembleTwo (S : Finset I) (T : Finset {i : I // i ∉ S}) :
    (Outside (G := G) T × Inside (G := G) T) × Inside (G := G) S ≃ᵐ (I → G) :=
  ((assemble T).prodCongr (MeasurableEquiv.refl _)).trans (assemble S)

omit [Fintype I] in
theorem assembleTwo_apply (S : Finset I) (T : Finset {i : I // i ∉ S})
    (z : (Outside (G := G) T × Inside (G := G) T) × Inside (G := G) S) :
    assembleTwo S T z = assemble S (assemble T z.1, z.2) := rfl

omit [Fintype I] in
theorem assembleTwo_continuous [TopologicalSpace G] (S : Finset I)
    (T : Finset {i : I // i ∉ S}) : Continuous (assembleTwo (G := G) S T) := by
  exact (assemble_continuous S).comp
    (((assemble_continuous T).comp continuous_fst).prodMk continuous_snd)

theorem assembleTwo_preserving (S : Finset I) (T : Finset {i : I // i ∉ S})
    (μ : Measure G) [SigmaFinite μ] :
    MeasurePreserving (assembleTwo S T)
      (((Measure.pi (fun _ : {i : {i : I // i ∉ S} // i ∉ T} => μ)).prod
        (Measure.pi (fun _ : {i : {i : I // i ∉ S} // i ∈ T} => μ))).prod
        (Measure.pi (fun _ : {i : I // i ∈ S} => μ)))
      (Measure.pi (fun _ : I => μ)) := by
  exact (assemble_preserving S μ).comp
    ((assemble_preserving T μ).prod (MeasurePreserving.id _))
end Coordinates

theorem weightedLaw_preserving {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (w : Y → ℝ) (hw : Measurable w) :
    MeasurePreserving e (LocalGibbsComparison.weightedLaw μ (w ∘ e))
      (LocalGibbsComparison.weightedLaw ν w) := by
  unfold LocalGibbsComparison.weightedLaw
  have hp := he.integral_comp e.measurableEmbedding w
  change (∫ x, (w ∘ e) x ∂μ) = ∫ y, w y ∂ν at hp
  rw [hp]
  exact (GibbsReflectionTransport.withDensity_transport he
    (fun y => ENNReal.ofReal (w y)) hw.ennreal_ofReal).smul_measure _

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance : DecidableEq (Edge (Vertex n)) := Classical.decEq _

def splitAction (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (z : Outside (G := G) S × Inside (G := G) S) : ℝ :=
  WilsonBlockIntegration.action n G χ β c (assemble S z)

omit [CompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
theorem splitAction_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) : Continuous (splitAction n G χ β c S) :=
  (continuous_orientedWilsonAction _ G χ hχ (base n) (loops n) β c).comp
    (assemble_continuous S)

/-- The original periodic Wilson probability is transported exactly to
the block coordinates, including its actual interacting Gibbs density. -/
theorem wilson_integral_split (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (F : Configuration (Vertex n) G → ℝ) :
    (∫ U, F U ∂wilsonLaw n G χ β c) =
      ∫ z, F (assemble S z) ∂CompactGibbsContinuity.law
        ((Measure.pi (fun _ : {e : Edge (Vertex n) // e ∉ S} => compactHaar G)).prod
          (Measure.pi (fun _ : {e : Edge (Vertex n) // e ∈ S} => compactHaar G)))
        (splitAction n G χ β c S) := by
  change (∫ U, F U ∂gibbsMeasure _ G
    (orientedWilsonAction _ G χ (base n) (loops n) β c)) = _
  rw [gibbs_eq_weightedLaw _ G _
    (continuous_orientedWilsonAction _ G χ hχ (base n) (loops n) β c)]
  symm
  exact weighted_integral_transport _ _ (assemble S) (assemble_preserving S (compactHaar G))
    (fun U => Real.exp (-WilsonBlockIntegration.action n G χ β c U))
    (Real.continuous_exp.comp
      (continuous_orientedWilsonAction _ G χ hχ (base n) (loops n) β c).neg).measurable
    (fun U => (Real.exp_pos _).le)
    (CompactGibbsContinuity.partition_positive _ _
      (continuous_orientedWilsonAction _ G χ hχ (base n) (loops n) β c)) F

def splitActionTwo (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (z : (Outside (G := G) T × Inside (G := G) T) × Inside (G := G) S) : ℝ :=
  WilsonBlockIntegration.action n G χ β c (assembleTwo S T z)

omit [CompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
theorem splitActionTwo_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S}) :
    Continuous (splitActionTwo n G χ β c S T) :=
  (continuous_orientedWilsonAction _ G χ hχ (base n) (loops n) β c).comp
    (assembleTwo_continuous S T)

theorem wilson_integral_split_two (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F : Configuration (Vertex n) G → ℝ) :
    (∫ U, F U ∂wilsonLaw n G χ β c) =
      ∫ z, F (assembleTwo S T z) ∂CompactGibbsContinuity.law
        (((Measure.pi
          (fun _ : {e : {e : Edge (Vertex n) // e ∉ S} // e ∉ T} => compactHaar G)).prod
          (Measure.pi
            (fun _ : {e : {e : Edge (Vertex n) // e ∉ S} // e ∈ T} => compactHaar G))).prod
          (Measure.pi (fun _ : {e : Edge (Vertex n) // e ∈ S} => compactHaar G)))
        (splitActionTwo n G χ β c S T) := by
  change (∫ U, F U ∂gibbsMeasure _ G
    (orientedWilsonAction _ G χ (base n) (loops n) β c)) = _
  rw [gibbs_eq_weightedLaw _ G _
    (continuous_orientedWilsonAction _ G χ hχ (base n) (loops n) β c)]
  symm
  exact weighted_integral_transport _ _ (assembleTwo S T)
    (assembleTwo_preserving S T (compactHaar G))
    (fun U => Real.exp (-WilsonBlockIntegration.action n G χ β c U))
    (Real.continuous_exp.comp
      (continuous_orientedWilsonAction _ G χ hχ (base n) (loops n) β c).neg).measurable
    (fun U => (Real.exp_pos _).le)
    (CompactGibbsContinuity.partition_positive _ _
      (continuous_orientedWilsonAction _ G χ hχ (base n) (loops n) β c)) F

/-- Exact transport of the probability measure itself, so every measurable
retained event uses the actual Wilson marginal, not a comparison law. -/
theorem wilson_coordinates_two_preserving (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S}) :
    MeasurePreserving (assembleTwo (G := G) S T).symm (wilsonLaw n G χ β c)
      (CompactGibbsContinuity.law
        (((outsideMeasure T (compactHaar G)).prod (insideMeasure T (compactHaar G))).prod
          (insideMeasure S (compactHaar G))) (splitActionTwo n G χ β c S T)) := by
  have h := weightedLaw_preserving _ _ (assembleTwo (G := G) S T)
    (assembleTwo_preserving S T (compactHaar G))
    (fun U => Real.exp (-WilsonBlockIntegration.action n G χ β c U))
    (Real.continuous_exp.comp
      (continuous_orientedWilsonAction _ G χ hχ (base n) (loops n) β c).neg).measurable
  have hg := gibbs_eq_weightedLaw (Vertex n) G
    (orientedWilsonAction _ G χ (base n) (loops n) β c)
    (continuous_orientedWilsonAction _ G χ hχ (base n) (loops n) β c)
  change wilsonLaw n G χ β c = LocalGibbsComparison.weightedLaw
    (Measure.pi (fun _ : Edge (Vertex n) => compactHaar G))
    (fun U => Real.exp (-WilsonBlockIntegration.action n G χ β c U)) at hg
  rw [← hg] at h
  exact h.symm (assembleTwo S T)

def firstResponse (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (F : Configuration (Vertex n) G → ℝ) :
    Outside (G := G) T × Inside (G := G) T → ℝ :=
  GibbsMarginalTower.response (insideMeasure S (compactHaar G))
    (splitActionTwo n G χ β c S T) (F ∘ assembleTwo S T)

def firstMarginal (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) :
    Measure (Outside (G := G) T × Inside (G := G) T) :=
  GibbsMarginalTower.marginal
    ((outsideMeasure T (compactHaar G)).prod (insideMeasure T (compactHaar G)))
    (insideMeasure S (compactHaar G)) (splitActionTwo n G χ β c S T)

def retainedAction (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) :
    Outside (G := G) T × Inside (G := G) T → ℝ :=
  GibbsMarginalTower.effectiveAction (insideMeasure S (compactHaar G))
    (splitActionTwo n G χ β c S T)

def secondResponse (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (H : Outside (G := G) T × Inside (G := G) T → ℝ) : Outside (G := G) T → ℝ :=
  GibbsMarginalTower.response (insideMeasure T (compactHaar G))
    (retainedAction n G χ β c S T) H

def secondMarginal (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) : Measure (Outside (G := G) T) :=
  GibbsMarginalTower.marginal (outsideMeasure T (compactHaar G))
    (insideMeasure T (compactHaar G)) (retainedAction n G χ β c S T)

theorem firstMarginal_eq_map (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S}) :
    firstMarginal n G χ β c S T =
      (wilsonLaw n G χ β c).map (fun U => ((assembleTwo (G := G) S T).symm U).1) := by
  unfold firstMarginal GibbsMarginalTower.marginal
  rw [← (wilson_coordinates_two_preserving n G χ hχ β c S T).map_eq,
    Measure.map_map measurable_fst (assembleTwo S T).symm.measurable]
  rfl

theorem secondMarginal_eq_map (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S}) :
    secondMarginal n G χ β c S T =
      (wilsonLaw n G χ β c).map (fun U => ((assembleTwo (G := G) S T).symm U).1.1) := by
  unfold secondMarginal retainedAction
  have hm : Measurable (fun p :
      (Outside (G := G) T × Inside (G := G) T) × Inside (G := G) S => p.1.1) :=
    measurable_fst.comp measurable_fst
  rw [GibbsMarginalTower.marginal_tower _ _ _ _
    (splitActionTwo_continuous n G χ hχ β c S T),
    ← (wilson_coordinates_two_preserving n G χ hχ β c S T).map_eq,
    Measure.map_map hm (assembleTwo S T).symm.measurable]
  rfl

/-- The first-stage error and the same vacuum constant survive a second
exact integration with contraction constant one, even for correlated blocks. -/
theorem wilson_nested_residual_bound (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F : Configuration (Vertex n) G → ℝ) (hF : Continuous F)
    (H : Outside (G := G) T × Inside (G := G) T → ℝ) (hH : Continuous H) (v : ℝ) :
    (∫ z, (secondResponse n G χ β c S T (firstResponse n G χ β c S T F) z-v-
        secondResponse n G χ β c S T H z)^2 ∂secondMarginal n G χ β c S T) ≤
      ∫ p, (firstResponse n G χ β c S T F p-v-H p)^2 ∂firstMarginal n G χ β c S T :=
  GibbsMarginalTower.nested_residual_l2_bound _ _ _ _ _
    (splitActionTwo_continuous n G χ hχ β c S T)
    (hF.comp (assembleTwo_continuous S T)) H hH v

theorem wilson_nested_error_bound (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F : Configuration (Vertex n) G → ℝ) (hF : Continuous F)
    (H : Outside (G := G) T × Inside (G := G) T → ℝ) (hH : Continuous H) (v : ℝ) :
    (∫ z, (secondResponse n G χ β c S T (firstResponse n G χ β c S T F) z-v-
        secondResponse n G χ β c S T H z)^2 ∂secondMarginal n G χ β c S T) ≤
      ∫ U, (F U-v-H ((assembleTwo (G := G) S T).symm U).1)^2
        ∂wilsonLaw n G χ β c := by
  rw [wilson_integral_split_two n G χ hχ β c S T]
  simp only [MeasurableEquiv.symm_apply_apply]
  exact GibbsMarginalTower.nested_error_l2_bound _ _ _ _ _
    (splitActionTwo_continuous n G χ hχ β c S T)
    (hF.comp (assembleTwo_continuous S T)) H hH v

/-- The actual original Wilson centered square splits into eliminated
fluctuations and retained fluctuations. Neither term is silently discarded. -/
theorem wilson_centered_square_decomposition (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F : Configuration (Vertex n) G → ℝ) (hF : Continuous F) (v : ℝ) :
    (∫ U, (F U-v)^2 ∂wilsonLaw n G χ β c) =
      (∫ U, (F U-firstResponse n G χ β c S T F
        ((assembleTwo (G := G) S T).symm U).1)^2 ∂wilsonLaw n G χ β c)+
      ∫ p, (firstResponse n G χ β c S T F p-v)^2 ∂firstMarginal n G χ β c S T := by
  rw [wilson_integral_split_two n G χ hχ β c S T,
    wilson_integral_split_two n G χ hχ β c S T]
  simp only [MeasurableEquiv.symm_apply_apply]
  exact GibbsMarginalTower.centered_square_identity _ _ _ _
    (splitActionTwo_continuous n G χ hχ β c S T)
    (hF.comp (assembleTwo_continuous S T)) v

end
end UnifiedTheory.Clay.YangMills.WilsonBlockMarginal
