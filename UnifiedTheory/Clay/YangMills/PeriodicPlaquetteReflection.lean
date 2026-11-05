/- Exact transformation of actual periodic lattice plaquettes under site-time
reflection. Temporal plaquettes become conjugates of inverse plaquettes;
spatial plaquettes retain their orientation. This proves action/measure symmetry,
not by itself reflection positivity. -/
import UnifiedTheory.Clay.YangMills.PeriodicTimeReflection
import UnifiedTheory.Clay.YangMills.UnitaryCharacterObservables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PeriodicPlaquetteReflection
noncomputable section
open PeriodicLattice4 PeriodicTimeReflection RegulatedGauge MeasureTheory

variable (N : ℕ) (G : Type*) [Group G]

def plaquetteProduct (U : Configuration (Vertex N) G) (x : Vertex N) (μ ν : Fin 4) : G :=
  linkValue N G U x μ * linkValue N G U (step N x μ) ν *
    (linkValue N G U (step N x ν) μ)⁻¹ * (linkValue N G U x ν)⁻¹

theorem plaquette_holonomy_eq_product (U : Configuration (Vertex N) G)
    (x : Vertex N) (μ ν : Fin 4) :
    holonomy (Quiver.Symmetrify (Vertex N)) G (orientedExtension (Vertex N) G U)
      (plaquette N x μ ν) = plaquetteProduct N G U x μ ν := by
  simp [plaquette, holonomy, link, orientedExtension, plaquetteProduct, linkValue, forward]
  exact congrArg U ((edgeCoordinates N).injective rfl)

theorem reflected_spatial_plaquette (U : Configuration (Vertex N) G)
    (x : Vertex N) (μ ν : Fin 4) (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    plaquetteProduct N G (reflectConfiguration N G U) x μ ν =
      plaquetteProduct N G U (reflectVertex N x) μ ν := by
  simp only [plaquetteProduct, reflect_link_spatial N G U _ μ hμ,
    reflect_link_spatial N G U _ ν hν, reflectVertex_step_spatial N x μ hμ,
    reflectVertex_step_spatial N x ν hν]

theorem reflected_time_spatial_corner (x : Vertex N) (ν : Fin 4) (hν : ν ≠ 0) :
    reflectVertex N (step N (step N x ν) 0) =
      step N (reflectVertex N (step N x 0)) ν := by
  rw [step_comm N x ν 0, reflectVertex_step_spatial N (step N x 0) ν hν]

/-- The conjugating temporal link is retained explicitly; no commutativity is used. -/
theorem reflected_temporal_plaquette (U : Configuration (Vertex N) G)
    (x : Vertex N) (ν : Fin 4) (hν : ν ≠ 0) :
    plaquetteProduct N G (reflectConfiguration N G U) x 0 ν =
      (linkValue N G U (reflectVertex N (step N x 0)) 0)⁻¹ *
        (plaquetteProduct N G U (reflectVertex N (step N x 0)) 0 ν)⁻¹ *
        linkValue N G U (reflectVertex N (step N x 0)) 0 := by
  simp only [plaquetteProduct, reflect_link_time, reflect_link_spatial N G U _ ν hν,
    reflected_time_spatial_corner N x ν hν, reflectVertex_step_time]
  group

def reflectPlaquette (p : PlaquetteIndex N) : PlaquetteIndex N :=
  ((reflectIndex N (p.1, p.2.1.1)).1, p.2)

theorem reflectPlaquette_involutive : Function.Involutive (reflectPlaquette N) := by
  rintro ⟨x, μν⟩
  have h := congrArg Prod.fst (reflectIndex_involutive N (x, μν.1.1))
  exact Prod.ext h rfl

def plaquetteEquiv : PlaquetteIndex N ≃ PlaquetteIndex N :=
  (reflectPlaquette_involutive N).toPerm

theorem reflected_plaquette_character (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (U : Configuration (Vertex N) G)
    (p : PlaquetteIndex N) :
    (χ (plaquetteProduct N G (reflectConfiguration N G U) p.1 p.2.1.1 p.2.1.2)).re =
      (χ (plaquetteProduct N G U (reflectPlaquette N p).1 p.2.1.1 p.2.1.2)).re := by
  rcases p with ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩
  have hν : ν ≠ 0 := by intro h; subst ν; exact (not_lt_of_ge (Fin.zero_le μ)) hμν
  by_cases hμ : μ = 0
  · subst μ
    simp only [reflectPlaquette, reflectIndex, ↓reduceIte]
    rw [reflected_temporal_plaquette N G U x ν hν]
    have hc := hχ (linkValue N G U (reflectVertex N (step N x 0)) 0)⁻¹
      (plaquetteProduct N G U (reflectVertex N (step N x 0)) 0 ν)⁻¹
    simp only [inv_inv] at hc
    rw [hc, hinv]
  · simp only [reflectPlaquette, reflectIndex, if_neg hμ]
    rw [reflected_spatial_plaquette N G U x μ ν hμ hν]

variable [NeZero N]

theorem wilsonAction_reflection (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ) (U : Configuration (Vertex N) G) :
    orientedWilsonAction (Vertex N) G χ (base N) (loops N) β c (reflectConfiguration N G U) =
      orientedWilsonAction (Vertex N) G χ (base N) (loops N) β c U := by
  change β * ∑ p : PlaquetteIndex N, (c - (χ (holonomy (Quiver.Symmetrify (Vertex N)) G
    (orientedExtension (Vertex N) G (reflectConfiguration N G U))
    (plaquette N p.1 p.2.1.1 p.2.1.2))).re) =
      β * ∑ p : PlaquetteIndex N, (c - (χ (holonomy (Quiver.Symmetrify (Vertex N)) G
        (orientedExtension (Vertex N) G U) (plaquette N p.1 p.2.1.1 p.2.1.2))).re)
  simp only [plaquette_holonomy_eq_product]
  simp_rw [reflected_plaquette_character N G χ hχ hinv U]
  congr 1
  exact (Equiv.sum_comp (plaquetteEquiv N)
    (fun p => c - (χ (plaquetteProduct N G U p.1 p.2.1.1 p.2.1.2)).re))

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem unitaryCharacter_inverse_re (ρ : G →* Matrix.unitaryGroup d ℂ) (g : G) :
    (WilsonCrossingKernel.unitaryCharacter ρ g⁻¹).re =
      (WilsonCrossingKernel.unitaryCharacter ρ g).re := by
  simp only [WilsonCrossingKernel.unitaryCharacter, map_inv, Matrix.UnitaryGroup.inv_val,
    Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The reflected link transformation preserves the actual finite periodic Wilson law. -/
theorem wilsonLaw_preserves_reflection (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ) :
    MeasurePreserving (reflectConfiguration N G) (wilsonLaw N G χ β c) (wilsonLaw N G χ β c) := by
  apply MeasurePreserving.smul_measure
  apply preserves_withDensity (reference_preserves_reflection N G) _
    (Real.continuous_exp.comp
      (continuous_orientedWilsonAction (Vertex N) G χ hcχ (base N) (loops N) β c).neg).measurable.ennreal_ofReal
  intro U
  change ENNReal.ofReal (Real.exp (-orientedWilsonAction (Vertex N) G χ (base N) (loops N) β c
    (reflectConfiguration N G U))) = _
  rw [wilsonAction_reflection N G χ hχ hinv]
  rfl

end
end UnifiedTheory.Clay.YangMills.PeriodicPlaquetteReflection
