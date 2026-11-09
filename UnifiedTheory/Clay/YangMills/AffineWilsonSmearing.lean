/- Identity subtraction and multiplicative rescaling of the actual smeared
plaquette character. The Wilson probability law is kept fixed: changing the
observable does not silently change the lattice action. -/
import UnifiedTheory.Clay.YangMills.WilsonSmearedObservable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.AffineWilsonSmearing
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 FiniteCellSmearing

section FiniteCells
variable {E I Z : Type*} [MeasurableSpace E] [Fintype I] [DecidableEq I]
  [MeasurableSpace I] [MeasurableSingletonClass I]
  (μ : Measure E) (s : E → I) (hs : Measurable s)
include hs

theorem coefficient_sum (f : E → ℂ) (hf : Integrable f μ) :
    (∑ q, coefficient μ s q f) = ∫ x, f x ∂μ := by
  simpa only [one_mul] using (integral_decomposition μ s hs (fun _ => 1) f hf).symm

theorem observable_affine (F : I → Z → ℂ) (f : E → ℂ) (hf : Integrable f μ)
    (center scale : ℂ) (z : Z) :
    observable μ s (fun q z => scale * (F q z - center)) f z =
      scale * (observable μ s F f z - center * ∫ x, f x ∂μ) := by
  rw [← coefficient_sum μ s hs f hf]
  unfold observable
  calc
    _ = ∑ q, (scale * (coefficient μ s q f * F q z) -
        (scale * center) * coefficient μ s q f) := by
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
end FiniteCells

def affineCharacter {G : Type*} (χ : G → ℂ) (center scale : ℂ) : G → ℂ :=
  fun g => scale * (χ g - center)

variable (G : Type*) [Group G] (N : ℕ) [NeZero N]

theorem affine_word_one (χ : G → ℂ) (center scale : ℂ)
    (q : Fin 1 → PlaquetteIndex N) (U : RegulatedGauge.Configuration (Vertex N) G) :
    WilsonSmearedObservable.word G N (affineCharacter χ center scale) 1 q U =
      scale * (WilsonSmearedObservable.word G N χ 1 q U - center) := by
  simp only [WilsonSmearedObservable.word, Fin.prod_univ_one,
    WilsonMomentBounds.loopObservable, RegulatedGauge.wilson, affineCharacter]

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The subtraction is the identity smeared against the same test, with its
actual coefficient equal to the test integral. -/
theorem affine_smearing (a : ℝ) (plane : Plane) (χ : G → ℂ) (center scale : ℂ)
    (f : CorrelationTest 1) (U : RegulatedGauge.Configuration (Vertex N) G) :
    WilsonSmearedObservable.observable G N a plane (affineCharacter χ center scale) 1 f U =
      scale * (WilsonSmearedObservable.observable G N a plane χ 1 f U - center * ∫ x, f x) := by
  unfold WilsonSmearedObservable.observable
  have he : WilsonSmearedObservable.word G N (affineCharacter χ center scale) 1 =
      fun q U => scale * (WilsonSmearedObservable.word G N χ 1 q U - center) :=
    funext (fun q => funext (fun U => affine_word_one G N χ center scale q U))
  rw [he]
  exact observable_affine volume _
    (PeriodicCellSampling.sampleConfiguration_measurable 1 N a plane)
    (WilsonSmearedObservable.word G N χ 1) f f.integrable center scale U

/-- Finite-law expectations are shifted/rescaled with the observable while
the specified original Wilson law, including its coupling, is unchanged. -/
theorem affine_mean (a : ℝ) (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (actionCharacter : G → ℂ) (haction : Continuous actionCharacter) (beta offset : ℝ)
    (center scale : ℂ) (f : CorrelationTest 1) :
    (∫ U, WilsonSmearedObservable.observable G N a plane (affineCharacter χ center scale) 1 f U
      ∂wilsonLaw N G actionCharacter beta offset) =
      scale * ((∫ U, WilsonSmearedObservable.observable G N a plane χ 1 f U
        ∂wilsonLaw N G actionCharacter beta offset) - center * ∫ x, f x) := by
  letI := wilsonLaw_probability N G actionCharacter haction beta offset
  simp_rw [affine_smearing]
  rw [integral_const_mul, integral_sub]
  · simp only [integral_const, probReal_univ, one_smul]
  · exact (WilsonSmearedObservable.observable_continuous G N a plane χ hcχ 1 f).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact integrable_const _

/-- Centering removes every identity subtraction exactly; only the
multiplicative renormalization acts on the fluctuating observable. -/
theorem affine_centered (a : ℝ) (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (actionCharacter : G → ℂ) (haction : Continuous actionCharacter) (beta offset : ℝ)
    (center scale : ℂ) (f : CorrelationTest 1)
    (U : RegulatedGauge.Configuration (Vertex N) G) :
    WilsonSmearedObservable.observable G N a plane (affineCharacter χ center scale) 1 f U -
      (∫ V, WilsonSmearedObservable.observable G N a plane (affineCharacter χ center scale) 1 f V
        ∂wilsonLaw N G actionCharacter beta offset) =
      scale * (WilsonSmearedObservable.observable G N a plane χ 1 f U -
        ∫ V, WilsonSmearedObservable.observable G N a plane χ 1 f V
          ∂wilsonLaw N G actionCharacter beta offset) := by
  rw [affine_smearing, affine_mean G N a plane χ hcχ actionCharacter haction]
  ring

end
end UnifiedTheory.Clay.YangMills.AffineWilsonSmearing
