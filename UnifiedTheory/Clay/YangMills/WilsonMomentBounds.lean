/- Uniform bare Wilson-loop moment bounds for the actual finite-regulator laws.
The bound depends only on the fixed continuous class function, not the lattice
size or coupling. It is not a bound for renormalized continuum local fields. -/
import UnifiedTheory.Clay.YangMills.PeriodicLattice4
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonMomentBounds
noncomputable section
open MeasureTheory RegulatedGauge

section Probability
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  {ι : Type*}

def moment (s : Finset ι) (F : ι → X → ℂ) : ℂ := ∫ x, ∏ i ∈ s, F i x ∂μ

theorem moment_bound (s : Finset ι) (F : ι → X → ℂ) (B : ℝ)
    (_hB : 0 ≤ B) (hF : ∀ i ∈ s, ∀ x, ‖F i x‖ ≤ B) :
    ‖moment μ s F‖ ≤ B ^ s.card := by
  have hb : ∀ x, ‖∏ i ∈ s, F i x‖ ≤ B ^ s.card := by
    intro x
    rw [norm_prod]
    exact (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i hi => hF i hi x)).trans
      (by simp)
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)

theorem moment_empty (F : ι → X → ℂ) : moment μ ∅ F = 1 := by
  simp [moment]

variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]

theorem moment_integrable (s : Finset ι) (F : ι → X → ℂ)
    (hF : ∀ i, Continuous (F i)) : Integrable (fun x => ∏ i ∈ s, F i x) μ :=
  (continuous_finset_prod s (fun i _ => hF i)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Ordinary measure positivity. This does not assert time-reflection positivity. -/
theorem square_expectation_nonneg (F : X → ℂ) (hF : Continuous F) :
    0 ≤ (∫ x, star (F x) * F x ∂μ).re := by
  have hc : Continuous (fun x => star (F x) * F x) := hF.star.mul hF
  have hi := hc.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  change 0 ≤ RCLike.re (∫ x, star (F x) * F x ∂μ)
  rw [← integral_re hi]
  apply integral_nonneg
  intro x
  change 0 ≤ (star (F x) * F x).re
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (F x).re, sq_nonneg (F x).im]
end Probability

variable (V : Type*) [Quiver V] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

def loopObservable (χ : G → ℂ) {a : Quiver.Symmetrify V} (p : Quiver.Path a a)
    (U : Configuration V G) : ℂ :=
  wilson (Quiver.Symmetrify V) G χ (orientedExtension V G U) p

theorem loopObservable_continuous (χ : G → ℂ) (hχ : Continuous χ)
    {a : Quiver.Symmetrify V} (p : Quiver.Path a a) : Continuous (loopObservable V G χ p) :=
  (continuous_wilson (Quiver.Symmetrify V) G χ hχ p).comp (continuous_orientedExtension V G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem loopObservable_bound (χ : G → ℂ) (B : ℝ) (hχ : ∀ g, ‖χ g‖ ≤ B)
    {a : Quiver.Symmetrify V} (p : Quiver.Path a a) (U : Configuration V G) :
    ‖loopObservable V G χ p U‖ ≤ B := hχ _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem loopObservable_gauge (χ : G → ℂ) (hχ : ClassFunction G χ)
    {a : Quiver.Symmetrify V} (p : Quiver.Path a a)
    (g : GaugeTransformation V G) (U : Configuration V G) :
    loopObservable V G χ p (gauge V G g U) = loopObservable V G χ p U := by
  unfold loopObservable
  rw [orientedExtension_gauge, wilson_gauge _ _ χ hχ]

variable [CompactSpace G]

omit [Group G] [IsTopologicalGroup G] in
theorem character_bound_exists (χ : G → ℂ) (hχ : Continuous χ) :
    ∃ B : ℝ, 0 < B ∧ ∀ g, ‖χ g‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := (isCompact_range hχ).isBounded.exists_pos_norm_le
  exact ⟨B, hB, fun g => hb _ ⟨g, rfl⟩⟩

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [Fintype (Edge V)] {P : Type*} [Fintype P]

theorem gibbs_moment_bound (S : Configuration V G → ℝ) (hS : Continuous S)
    (χ : G → ℂ) (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    {ι : Type*} (s : Finset ι) (base : ι → Quiver.Symmetrify V)
    (loops : ∀ i, Quiver.Path (base i) (base i)) :
    ‖moment (gibbsMeasure V G S) s (fun i => loopObservable V G χ (loops i))‖ ≤ B ^ s.card := by
  letI := gibbsMeasure_probability V G S hS
  exact moment_bound _ s _ B hB (fun i _ U => loopObservable_bound V G χ B hχ (loops i) U)

theorem wilson_moment_bound (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (base : P → Quiver.Symmetrify V) (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ)
    {ι : Type*} (s : Finset ι) (obsBase : ι → Quiver.Symmetrify V)
    (obsLoops : ∀ i, Quiver.Path (obsBase i) (obsBase i)) :
    ‖moment (orientedWilsonMeasure V G χ base loops β c) s
      (fun i => loopObservable V G χ (obsLoops i))‖ ≤ B ^ s.card :=
  gibbs_moment_bound V G _ (continuous_orientedWilsonAction V G χ hcχ base loops β c)
    χ B hB hχ s obsBase obsLoops

/-- One bound works at every period, every real coupling, every finite family
of oriented Wilson loops and every moment order. -/
theorem periodic_uniform_moments (χ : G → ℂ) (hχ : Continuous χ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) [NeZero n] (β c : ℝ) (m : ℕ)
      (base : Fin m → Quiver.Symmetrify (PeriodicLattice4.Vertex n))
      (loops : ∀ i, Quiver.Path (base i) (base i)),
      ‖moment (PeriodicLattice4.wilsonLaw n G χ β c) Finset.univ
        (fun i => loopObservable (PeriodicLattice4.Vertex n) G χ (loops i))‖ ≤ B ^ m := by
  obtain ⟨B, hB, hb⟩ := character_bound_exists G χ hχ
  refine ⟨B, hB, ?_⟩
  intro n hn β c m base loops
  simpa only [Finset.card_univ, Fintype.card_fin] using
    wilson_moment_bound (PeriodicLattice4.Vertex n) G χ hχ B hB.le hb
      (PeriodicLattice4.base n) (PeriodicLattice4.loops n) β c Finset.univ base loops

end
end UnifiedTheory.Clay.YangMills.WilsonMomentBounds
