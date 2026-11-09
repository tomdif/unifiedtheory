/- Nontrivial plaquette fluctuations for the constructed finite Wilson law.
A single independent link realizes every group element as plaquette holonomy.
Strict variance is finite-volume only; its regulator-uniform survival is open. -/
import UnifiedTheory.Clay.YangMills.WilsonMomentBounds
import UnifiedTheory.Clay.YangMills.GibbsFullSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PeriodicPlaquetteNontriviality
noncomputable section
open RegulatedGauge PeriodicLattice4 WilsonMomentBounds GibbsFullSupport MeasureTheory

variable (n : ℕ) [NeZero n] [Fact (1 < n)] (G : Type*) [Group G]

def singleLink (x : Vertex n) (μ : Fin 4) (g : G) : Configuration (Vertex n) G :=
  fun e => if e.1 = x ∧ e.2.2.val = μ then g else 1

omit [NeZero n] in
theorem step_ne (x : Vertex n) (μ : Fin 4) : step n x μ ≠ x := by
  intro he
  have h := congrArg (fun z : Vertex n => z μ) he
  change x μ + (Pi.single μ (1 : ZMod n) : Vertex n) μ = x μ at h
  have hz : (1 : ZMod n) = 0 := by simpa only [Pi.single_eq_same, add_eq_left] using h
  exact one_ne_zero hz

/-- No commuting gauge-group hypothesis: the other three links are identities. -/
theorem plaquette_singleLink (x : Vertex n) (μ ν : Fin 4) (hμν : μ ≠ ν) (g : G) :
    holonomy (Quiver.Symmetrify (Vertex n)) G
      (orientedExtension (Vertex n) G (singleLink n G x μ g)) (plaquette n x μ ν) = g := by
  have hμ := step_ne n x μ
  have hν := step_ne n x ν
  simp [plaquette, holonomy, link, orientedExtension, singleLink, forward,
    hμ, hν, hμν.symm]

theorem plaquette_holonomy_surjective (x : Vertex n) (μ ν : Fin 4) (hμν : μ ≠ ν) :
    Function.Surjective (fun U : Configuration (Vertex n) G =>
      holonomy (Quiver.Symmetrify (Vertex n)) G
        (orientedExtension (Vertex n) G U) (plaquette n x μ ν)) :=
  fun g => ⟨singleLink n G x μ g, plaquette_singleLink n G x μ ν hμν g⟩

theorem loopObservable_singleLink (χ : G → ℂ) (x : Vertex n)
    (μ ν : Fin 4) (hμν : μ ≠ ν) (g : G) :
    loopObservable (Vertex n) G χ (plaquette n x μ ν) (singleLink n G x μ g) = χ g := by
  unfold loopObservable wilson
  rw [plaquette_singleLink n G x μ ν hμν]

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Every nonconstant continuous plaquette observable has a strictly positive
connected variance under the actual finite periodic Wilson law, for any coupling. -/
theorem plaquette_variance_pos (χ : G → ℂ) (hχ : Continuous χ)
    (g h : G) (hne : χ g ≠ χ h) (β c : ℝ)
    (x : Vertex n) (μ ν : Fin 4) (hμν : μ ≠ ν) :
    0 < ∫ U, ‖loopObservable (Vertex n) G χ (plaquette n x μ ν) U -
      ∫ W, loopObservable (Vertex n) G χ (plaquette n x μ ν) W
        ∂wilsonLaw n G χ β c‖ ^ 2 ∂wilsonLaw n G χ β c := by
  exact variance_pos (Vertex n) G _
    (continuous_orientedWilsonAction (Vertex n) G χ hχ (base n) (loops n) β c)
    _ (loopObservable_continuous (Vertex n) G χ hχ (plaquette n x μ ν))
    (singleLink n G x μ g) (singleLink n G x μ h)
    (by simpa only [loopObservable_singleLink n G χ x μ ν hμν] using hne)

end
end UnifiedTheory.Clay.YangMills.PeriodicPlaquetteNontriviality
