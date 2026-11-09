/- Volume-uniform plaquette fluctuations for the actual periodic Wilson law
at bounded coupling. The coordinate split and the local action comparison are
proved. The conservative exponent is independent of lattice volume but decays
when the coupling bound grows; this does not prove continuum weak-coupling
nontriviality. -/
import UnifiedTheory.Clay.YangMills.GibbsCoordinateTransport
import UnifiedTheory.Clay.YangMills.LocalHaarGibbsVariance
import UnifiedTheory.Clay.YangMills.WilsonLocalOscillation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonUniformVariance
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonMomentBounds
open SingleCoordinateProduct GibbsCoordinateTransport LocalGibbsComparison
open HaarCenteredFluctuation LocalHaarGibbsVariance

variable (n : ℕ) [NeZero n] [Fact (1 < n)] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
local instance : DecidableEq (Edge (Vertex n)) := Classical.decEq _

def selectedLink (x : Vertex n) (μ : Fin 4) : Edge (Vertex n) :=
  ⟨x, step n x μ, forward n x μ⟩

abbrev Exterior (x : Vertex n) (μ : Fin 4) := Outside (G := G) (selectedLink n x μ)

def exteriorMeasure (x : Vertex n) (μ : Fin 4) : Measure (Exterior n G x μ) :=
  Measure.pi (fun _ => compactHaar G)

instance exterior_probability (x : Vertex n) (μ : Fin 4) :
    IsProbabilityMeasure (exteriorMeasure n G x μ) := by unfold exteriorMeasure; infer_instance

def residualHolonomy (x : Vertex n) (μ ν : Fin 4) (r : Exterior n G x μ) : G :=
  holonomy (Quiver.Symmetrify (Vertex n)) G
    (orientedExtension (Vertex n) G (assemble (selectedLink n x μ) (r, 1))) (plaquette n x μ ν)

theorem residualHolonomy_continuous (x : Vertex n) (μ ν : Fin 4) :
    Continuous (residualHolonomy n G x μ ν) :=
  (continuous_holonomy (Quiver.Symmetrify (Vertex n)) G _).comp
    ((continuous_orientedExtension (Vertex n) G).comp
      ((assemble_continuous _).comp (continuous_id.prodMk continuous_const)))

theorem plaquette_split (x : Vertex n) (μ ν : Fin 4) (hμν : μ ≠ ν)
    (r : Exterior n G x μ) (g : G) :
    holonomy (Quiver.Symmetrify (Vertex n)) G
      (orientedExtension (Vertex n) G (assemble (selectedLink n x μ) (r, g))) (plaquette n x μ ν) =
      g * residualHolonomy n G x μ ν r := by
  have hμ := PeriodicPlaquetteNontriviality.step_ne n x μ
  have hν := PeriodicPlaquetteNontriviality.step_ne n x ν
  have h2 : (⟨step n x μ, step n (step n x μ) ν, forward n (step n x μ) ν⟩ : Edge (Vertex n)) ≠
      selectedLink n x μ := fun he => hμ (congrArg Sigma.fst he)
  have h3 : (⟨step n x ν, step n (step n x μ) ν, ⟨μ, step_comm n x ν μ⟩⟩ : Edge (Vertex n)) ≠
      selectedLink n x μ := fun he => hν (congrArg Sigma.fst he)
  have h4 : (⟨x, step n x ν, forward n x ν⟩ : Edge (Vertex n)) ≠ selectedLink n x μ := by
    intro he
    exact hμν (congrArg (fun e : Edge (Vertex n) => e.2.2.val) he).symm
  change _ = g * holonomy (Quiver.Symmetrify (Vertex n)) G
    (orientedExtension (Vertex n) G (assemble (selectedLink n x μ) (r, 1))) (plaquette n x μ ν)
  simp only [plaquette, holonomy, orientedExtension, link]
  change 1 * assemble (selectedLink n x μ) (r, g) (selectedLink n x μ) * _ * _ * _ =
    g * (1 * assemble (selectedLink n x μ) (r, 1) (selectedLink n x μ) * _ * _ * _)
  simp only [assemble_self, assemble_other _ _ h2, assemble_other _ _ h3, assemble_other _ _ h4,
    one_mul, mul_assoc]

def exteriorAction (χ : G → ℂ) (β c : ℝ) (x : Vertex n) (μ : Fin 4)
    (r : Exterior n G x μ) : ℝ :=
  orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c (assemble (selectedLink n x μ) (r, 1))

def localAction (χ : G → ℂ) (β c : ℝ) (x : Vertex n) (μ : Fin 4)
    (z : Exterior n G x μ × G) : ℝ :=
  orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c (assemble (selectedLink n x μ) z) -
    exteriorAction n G χ β c x μ z.1

theorem exteriorAction_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (x : Vertex n) (μ : Fin 4) : Continuous (exteriorAction n G χ β c x μ) :=
  (continuous_orientedWilsonAction _ G χ hχ _ _ β c).comp
    ((assemble_continuous _).comp (continuous_id.prodMk continuous_const))

theorem localAction_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (x : Vertex n) (μ : Fin 4) : Continuous (localAction n G χ β c x μ) :=
  ((continuous_orientedWilsonAction _ G χ hχ _ _ β c).comp (assemble_continuous _)).sub
    ((exteriorAction_continuous n G χ hχ β c x μ).comp continuous_fst)

theorem localAction_bound (χ : G → ℂ) (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (x : Vertex n) (μ : Fin 4) (z : Exterior n G x μ × G) :
    |localAction n G χ β c x μ z| ≤ 60 * |β| * B := by
  apply WilsonLocalOscillation.action_oscillation n G χ B hB hχ β c x
  intro e he
  have hne : e ≠ selectedLink n x μ := fun h => he (congrArg Sigma.fst h)
  rw [assemble_other _ _ hne, assemble_other _ _ hne]

theorem centered_lower (χ : G → ℂ) (hcχ : Continuous χ) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ) (x : Vertex n) (μ ν : Fin 4) (hμν : μ ≠ ν) (m : ℂ) :
    Real.exp (-120 * |β| * B) * haarFluctuation G χ ≤
      ∫ U, ‖loopObservable (Vertex n) G χ (plaquette n x μ ν) U - m‖ ^ 2
        ∂wilsonLaw n G χ β c := by
  let S := exteriorAction n G χ β c x μ
  let L := localAction n G χ β c x μ
  have he := LocalHaarGibbsVariance.centered_lower G (exteriorMeasure n G x μ)
    S (exteriorAction_continuous n G χ hcχ β c x μ)
    L (localAction_continuous n G χ hcχ β c x μ) (60 * |β| * B)
    (localAction_bound n G χ B hB hχ β c x μ) χ hcχ
    (fun _ => 1) (residualHolonomy n G x μ ν) continuous_const
    (residualHolonomy_continuous n G x μ ν) m
  have hw : (fun z : Exterior n G x μ × G => Real.exp
      (-orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c
        (assemble (selectedLink n x μ) z))) =
      localWeight (fun r => Real.exp (-S r)) (fun z => Real.exp (-L z)) := by
    funext z
    rw [localWeight, ← Real.exp_add]
    congr 1
    dsimp [S, L, localAction]
    ring
  have hf (z : Exterior n G x μ × G) :
      loopObservable (Vertex n) G χ (plaquette n x μ ν) (assemble (selectedLink n x μ) z) =
        observable G χ (fun _ => 1) (residualHolonomy n G x μ ν) z := by
    rcases z with ⟨r, g⟩
    simp only [loopObservable, wilson, plaquette_split n G x μ ν hμν,
      observable, one_mul]
  change _ ≤ ∫ U, _ ∂gibbsMeasure (Vertex n) G
    (orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c)
  rw [gibbs_integral_split (Vertex n) G _
    (continuous_orientedWilsonAction _ G χ hcχ _ _ β c) (selectedLink n x μ)]
  rw [hw]
  simp_rw [hf]
  convert he using 1 <;> ring

theorem bounded_coupling_variance_lower (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (betaMax β c : ℝ) (hbeta : |β| ≤ betaMax) (x : Vertex n)
    (μ ν : Fin 4) (hμν : μ ≠ ν) :
    Real.exp (-120 * betaMax * B) * haarFluctuation G χ ≤
      ∫ U, ‖loopObservable (Vertex n) G χ (plaquette n x μ ν) U -
        ∫ W, loopObservable (Vertex n) G χ (plaquette n x μ ν) W ∂wilsonLaw n G χ β c‖ ^ 2
        ∂wilsonLaw n G χ β c := by
  apply le_trans _ (centered_lower n G χ hcχ B hB hχ β c x μ ν hμν _)
  apply mul_le_mul_of_nonneg_right _ (ProbabilityTheory.variance_nonneg _ _)
  apply Real.exp_le_exp.mpr
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonUniformVariance
