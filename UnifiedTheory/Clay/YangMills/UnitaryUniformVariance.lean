/- A strictly positive volume-uniform connected plaquette variance for a
nontrivial continuous unitary character at bounded coupling. The explicit
floor decays with the coupling bound; no weak-coupling continuum claim follows. -/
import UnifiedTheory.Clay.YangMills.WilsonUniformVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.UnitaryUniformVariance
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonMomentBounds WilsonCrossingKernel
open UnitaryCharacterObservables HaarCenteredFluctuation

variable {d G : Type*} [Fintype d] [DecidableEq d] [Group G]

theorem character_real_part_ne_at_one (ρ : G →* Matrix.unitaryGroup d ℂ)
    (g : G) (hg : ρ g ≠ 1) : (unitaryCharacter ρ g).re ≠ (unitaryCharacter ρ 1).re := by
  intro he
  have hr : (unitaryCharacter ρ g).re = (Fintype.card d : ℝ) := by
    simpa only [unitaryCharacter_one, Complex.natCast_re] using he
  have hn : ‖unitaryCharacter ρ g‖ = (Fintype.card d : ℝ) :=
    le_antisymm (unitary_trace_bound (ρ g)) (by rw [← hr]; exact Complex.re_le_norm _)
  have hi : (unitaryCharacter ρ g).im = 0 := Complex.abs_re_eq_norm.mp (by
    rw [hr, hn, abs_of_nonneg (Nat.cast_nonneg _)])
  apply unitaryCharacter_ne_at_one ρ g hg
  apply Complex.ext
  · exact he
  · simpa only [unitaryCharacter_one, Complex.natCast_im] using hi

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def varianceFloor (ρ : G →* Matrix.unitaryGroup d ℂ) (betaMax : ℝ) : ℝ :=
  Real.exp (-120 * betaMax * (Fintype.card d : ℝ)) * haarFluctuation G (unitaryCharacter ρ)

theorem varianceFloor_pos (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (g : G) (hg : ρ g ≠ 1) (betaMax : ℝ) : 0 < varianceFloor ρ betaMax :=
  mul_pos (Real.exp_pos _) (haarFluctuation_pos G _ (unitaryCharacter_continuous ρ hρ)
    g 1 (character_real_part_ne_at_one ρ g hg))

theorem bounded_coupling_plaquette_variance (n : ℕ) [NeZero n] [Fact (1 < n)]
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (betaMax β c : ℝ) (hbeta : |β| ≤ betaMax) (x : Vertex n)
    (μ ν : Fin 4) (hμν : μ ≠ ν) :
    varianceFloor ρ betaMax ≤
      ∫ U, ‖loopObservable (Vertex n) G (unitaryCharacter ρ) (plaquette n x μ ν) U -
        ∫ W, loopObservable (Vertex n) G (unitaryCharacter ρ) (plaquette n x μ ν) W
          ∂wilsonLaw n G (unitaryCharacter ρ) β c‖ ^ 2
        ∂wilsonLaw n G (unitaryCharacter ρ) β c :=
  WilsonUniformVariance.bounded_coupling_variance_lower n G (unitaryCharacter ρ)
    (unitaryCharacter_continuous ρ hρ) (Fintype.card d : ℝ) (Nat.cast_nonneg _)
    (fun g => unitary_trace_bound (ρ g)) betaMax β c hbeta x μ ν hμν

theorem exists_uniform_positive_floor (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (g : G) (hg : ρ g ≠ 1) (betaMax : ℝ) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (n : ℕ) [NeZero n] [Fact (1 < n)]
      (β c : ℝ), |β| ≤ betaMax → ∀ (x : Vertex n) (μ ν : Fin 4), μ ≠ ν →
        eta ≤ ∫ U, ‖loopObservable (Vertex n) G (unitaryCharacter ρ) (plaquette n x μ ν) U -
          ∫ W, loopObservable (Vertex n) G (unitaryCharacter ρ) (plaquette n x μ ν) W
            ∂wilsonLaw n G (unitaryCharacter ρ) β c‖ ^ 2
          ∂wilsonLaw n G (unitaryCharacter ρ) β c :=
  ⟨varianceFloor ρ betaMax, varianceFloor_pos ρ hρ g hg betaMax,
    fun n _ _ β c hbeta x μ ν hμν => bounded_coupling_plaquette_variance n ρ hρ
      betaMax β c hbeta x μ ν hμν⟩

end
end UnifiedTheory.Clay.YangMills.UnitaryUniformVariance
