/- The actual periodic Wilson covariance theorem applied to genuine
finite plaquette sources, with their coordinate support derived from the action. -/
import UnifiedTheory.Clay.YangMills.WilsonLocalClustering

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSourceClustering
noncomputable section
open MeasureTheory WilsonParallelContraction WilsonParallelPoincare
open WilsonIndependentBlocks WilsonSupportPropagation

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- The original Wilson plaquette source as a continuous observable. -/
def observable (f : PeriodicLattice4.PlaquetteIndex n → ℝ) :
    C(RegulatedGauge.Configuration (PeriodicLattice4.Vertex n) Q, ℝ) :=
  ⟨WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f,
    WilsonBlockIntegration.source_continuous n Q WilsonSingleLinkStaples.character
      WilsonSingleLinkStaples.character_continuous 2 f⟩

theorem observable_dependsOn (f : PeriodicLattice4.PlaquetteIndex n → ℝ)
    (S : Finset (PeriodicLattice4.PlaquetteIndex n)) (hf : ∀ p, p ∉ S → f p = 0) :
    DependsOn (pullback n (observable n f) : State n → ℝ)
      (plaquetteSupport n S : Set (Link n)) := by
  have he : (pullback n (observable n f) : State n → ℝ) =
      fun U => WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f
        (WilsonCoordinateInfluence.toConfiguration n U) := by
    funext U
    change WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f
      (WilsonCoordinateLaw.configEquiv n U) = _
    rw [WilsonCoordinateLaw.configEquiv_eq_toConfiguration]
  rw [he]
  exact source_dependsOn n f S hf

variable [Fact (1 < n)]

/-- No support hypothesis on a black-box observable remains: the coefficient
supports of the two actual plaquette sources determine the geometric separation. -/
theorem original_source_covariance_decay (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (f g : PeriodicLattice4.PlaquetteIndex n → ℝ)
    (S T : Finset (PeriodicLattice4.PlaquetteIndex n))
    (hf : ∀ p, p ∉ S → f p = 0) (hg : ∀ p, p ∉ T → g p = 0)
    (d : ℕ) (hsep : ∀ j, j < d →
      Disjoint (neighborhood n (plaquetteSupport n S) j) (plaquetteSupport n T)) :
    let ρ := PeriodicLattice4.wilsonLaw n Q WilsonSingleLinkStaples.character β 2
    let F := observable n f
    let G := observable n g
    |∫ U, (F U - ∫ V, F V ∂ρ) * (G U - ∫ V, G V ∂ρ) ∂ρ| ≤
      rate β ^ d * Real.sqrt (∫ U, (F U - ∫ V, F V ∂ρ)^2 ∂ρ) *
        Real.sqrt (∫ U, (G U - ∫ V, G V ∂ρ)^2 ∂ρ) :=
  WilsonLocalClustering.original_wilson_covariance_decay n β hβ heven
    (observable n f) (observable n g) (plaquetteSupport n S) (plaquetteSupport n T)
    (observable_dependsOn n f S hf) (observable_dependsOn n g T hg) d hsep

end
end UnifiedTheory.Clay.YangMills.WilsonSourceClustering
