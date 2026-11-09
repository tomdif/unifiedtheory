/- The actual site-reflected Wilson Gram kernel, with its null quotient and
Hilbert completion. Positivity is derived from the periodic lattice theorem.
Countable limits below retain this reflected form, but construct no dynamics. -/
import UnifiedTheory.Clay.YangMills.PeriodicSiteReflection
import UnifiedTheory.Clay.YangMills.ConnectedGramLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ReflectedWilsonKernel
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 PeriodicHalfSplit
open PeriodicTimeReflection PeriodicSiteReflection CountableCorrelationCompactness
open PositiveKernelForm KernelHilbertCompletion

variable {ι : Type*} (n : ℕ) [NeZero n]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem continuous_reflection : Continuous (reflectConfiguration (2 * n) G) := by
  apply continuous_pi
  intro e
  change Continuous (fun U : Configuration (Vertex (2 * n)) G => if e.2.2.val = 0 then
    (U (edgeEquiv (2 * n) e))⁻¹ else U (edgeEquiv (2 * n) e))
  split_ifs
  · exact (continuous_apply _).inv
  · exact continuous_apply _

theorem continuous_observable
    (f : BoundaryConfiguration n G × HalfConfiguration n G → ℂ) (hf : Continuous f) :
    Continuous (observable n G f) := by
  change Continuous (fun U => f ((splitConfiguration n G U).1,
    (splitConfiguration n G U).2.2))
  exact hf.comp ((continuous_splitConfiguration n G).fst.prodMk
    (continuous_splitConfiguration n G).snd.snd)

def positiveObservable
    (f : BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (U : Configuration (Vertex (2 * n)) G) : ℂ :=
  f ((splitConfiguration n G U).1, (splitConfiguration n G U).2.1)

theorem positiveObservable_eq_reflected
    (f : BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (U : Configuration (Vertex (2 * n)) G) :
    positiveObservable n G f U = observable n G f (reflectConfiguration (2 * n) G U) := by
  change _ = f ((splitConfiguration n G (reflectConfiguration (2 * n) G U)).1,
    (splitConfiguration n G (reflectConfiguration (2 * n) G U)).2.2)
  rw [split_reflection]
  rfl

theorem positive_reflection_positive (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (f : BoundaryConfiguration n G × HalfConfiguration n G → ℂ) (hf : Continuous f) :
    0 ≤ (∫ U, star (positiveObservable n G f (reflectConfiguration (2 * n) G U)) *
      positiveObservable n G f U ∂wilsonLaw (2 * n) G χ β c).re ∧
    (∫ U, star (positiveObservable n G f (reflectConfiguration (2 * n) G U)) *
      positiveObservable n G f U ∂wilsonLaw (2 * n) G χ β c).im = 0 := by
  have h := reflection_positive n G χ hcχ hχ hinv β c f hf
  have ht (U : Configuration (Vertex (2 * n)) G) :
      reflectConfiguration (2 * n) G (reflectConfiguration (2 * n) G U) = U :=
    reflectConfiguration_involutive (2 * n) G U
  have he : (∫ U, star (positiveObservable n G f (reflectConfiguration (2 * n) G U)) *
      positiveObservable n G f U ∂wilsonLaw (2 * n) G χ β c) =
      star (∫ U, star (observable n G f (reflectConfiguration (2 * n) G U)) *
        observable n G f U ∂wilsonLaw (2 * n) G χ β c) := by
    simp_rw [positiveObservable_eq_reflected, ht]
    simp only [Complex.star_def, ← integral_conj, map_mul, Complex.conj_conj, mul_comm]
  rw [he]
  simpa only [Complex.star_def, Complex.conj_re, Complex.conj_im, neg_eq_zero] using h

def kernel (χ : G → ℂ) (β c : ℝ)
    (F : ι → BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (p : ι × ι) : ℂ :=
  ∫ U, star (observable n G (F p.1) (reflectConfiguration (2 * n) G U)) *
    observable n G (F p.2) U ∂wilsonLaw (2 * n) G χ β c

def combination (F : ι → BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (m : ℕ) (index : Fin m → ι) (a : Fin m → ℂ)
    (z : BoundaryConfiguration n G × HalfConfiguration n G) : ℂ :=
  ∑ j, a j * F (index j) z

theorem gram_as_reflected_square (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)
    (F : ι → BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (hF : ∀ i, Continuous (F i)) (m : ℕ) (index : Fin m → ι) (a : Fin m → ℂ) :
    gramValue (fun i j => (i, j)) (kernel n G χ β c F) m index a =
      ∫ U, star (observable n G (combination n G F m index a)
        (reflectConfiguration (2 * n) G U)) *
        observable n G (combination n G F m index a) U ∂wilsonLaw (2 * n) G χ β c := by
  letI := wilsonLaw_probability (2 * n) G χ hcχ β c
  have hpoly (U : Configuration (Vertex (2 * n)) G) :
      star (observable n G (combination n G F m index a)
        (reflectConfiguration (2 * n) G U)) *
        observable n G (combination n G F m index a) U =
      ∑ i, ∑ j, (star (a i) * a j) *
        (star (observable n G (F (index i)) (reflectConfiguration (2 * n) G U)) *
          observable n G (F (index j)) U) := by
    simp only [combination, observable, BoundaryReflectionGluing.halfObservable,
      star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (i j : Fin m) : Integrable (fun U => (star (a i) * a j) *
      (star (observable n G (F (index i)) (reflectConfiguration (2 * n) G U)) *
        observable n G (F (index j)) U)) (wilsonLaw (2 * n) G χ β c) :=
    (continuous_const.mul (((continuous_observable n G _ (hF (index i))).comp
      (continuous_reflection n G)).star.mul
        (continuous_observable n G _ (hF (index j))))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  simp_rw [hpoly]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hi _ j), integral_const_mul]
  rfl

theorem kernel_positive (χ : G → ℂ) (hcχ : Continuous χ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (F : ι → BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (hF : ∀ i, Continuous (F i)) :
    GramPositive (fun i j => (i, j)) (kernel n G χ β c F) := by
  intro m index a
  rw [gram_as_reflected_square n G χ hcχ β c F hF]
  have hc : Continuous (combination n G F m index a) :=
    continuous_finset_sum _ (fun j _ => continuous_const.mul (hF (index j)))
  exact (reflection_positive n G χ hcχ hχ hinv β c _ hc).symm

def positiveKernel (χ : G → ℂ) (hcχ : Continuous χ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (F : ι → BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (hF : ∀ i, Continuous (F i)) : PositiveKernel ι :=
  ⟨kernel n G χ β c F, kernel_positive n G χ hcχ hχ hinv β c F hF⟩

theorem kernel_normalized (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)
    (F : ι → BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (u : ι) (hu : ∀ z, F u z = 1) : kernel n G χ β c F (u, u) = 1 := by
  letI := wilsonLaw_probability (2 * n) G χ hcχ β c
  simp [kernel, observable, BoundaryReflectionGluing.halfObservable, hu]

theorem vacuum_normalized (χ : G → ℂ) (hcχ : Continuous χ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (F : ι → BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (hF : ∀ i, Continuous (F i)) (u : ι) (hu : ∀ z, F u z = 1) :
    ‖vacuum (positiveKernel n G χ hcχ hχ hinv β c F hF) u‖ = 1 :=
  vacuum_norm _ u (kernel_normalized n G χ hcχ β c F u hu)

theorem canonical_reflected_inner (χ : G → ℂ) (hcχ : Continuous χ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (F : ι → BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (hF : ∀ i, Continuous (F i)) (i j : ι) :
    inner ℂ (canonical (positiveKernel n G χ hcχ hχ hinv β c F hF) i)
      (canonical (positiveKernel n G χ hcχ hχ hinv β c F hF) j) =
      kernel n G χ β c F (i, j) := canonical_inner _ i j

theorem kernel_bound (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)
    (F : ι → BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (hb : ∀ i z, ‖F i z‖ ≤ B i) (p : ι × ι) :
    ‖kernel n G χ β c F p‖ ≤ B p.1 * B p.2 := by
  letI := wilsonLaw_probability (2 * n) G χ hcχ β c
  have he (U : Configuration (Vertex (2 * n)) G) :
      ‖star (observable n G (F p.1) (reflectConfiguration (2 * n) G U)) *
        observable n G (F p.2) U‖ ≤ B p.1 * B p.2 := by
    rw [norm_mul, norm_star]
    exact mul_le_mul (hb p.1 _) (hb p.2 _) (norm_nonneg _) (hB p.1)
  simpa only [kernel, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const
      (μ := wilsonLaw (2 * n) G χ β c) (Filter.Eventually.of_forall he)

variable [Countable ι]

/-- Common countable limits of actual reflected Wilson kernels. No continuum
scaling, locality, or time-translation action is supplied by this extraction. -/
theorem exists_normalized_reflected_limit
    (period : ℕ → ℕ) [∀ k, NeZero (period k)] (beta offset : ℕ → ℝ)
    (χ : G → ℂ) (hcχ : Continuous χ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (F : ∀ k, ι → BoundaryConfiguration (period k) G × HalfConfiguration (period k) G → ℂ)
    (hF : ∀ k i, Continuous (F k i))
    (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (hb : ∀ k i z, ‖F k i z‖ ≤ B i)
    (u : ι) (hu : ∀ k z, F k u z = 1) :
    ∃ (K : PositiveKernel ι) (phi : ℕ → ℕ), StrictMono phi ∧
      CoordinateConvergence
        (fun k => kernel (period (phi k)) G χ (beta (phi k)) (offset (phi k)) (F (phi k)))
        K.value ∧ (∀ p, ‖K.value p‖ ≤ B p.1 * B p.2) ∧ K.value (u, u) = 1 := by
  obtain ⟨w, phi, hphi, hc, hw, hp, hn⟩ := exists_positive_normalized_limit
    (fun k => kernel (period k) G χ (beta k) (offset k) (F k))
    (fun p => B p.1 * B p.2)
    (fun k p => kernel_bound (period k) G χ hcχ (beta k) (offset k) (F k) B hB (hb k) p)
    (fun i j => (i, j))
    (fun k => kernel_positive (period k) G χ hcχ hχ hinv (beta k) (offset k) (F k) (hF k))
    (u, u) (fun k => kernel_normalized (period k) G χ hcχ (beta k) (offset k) (F k) u (hu k))
  exact ⟨⟨w, hp⟩, phi, hphi, hc, hw, hn⟩

end
end UnifiedTheory.Clay.YangMills.ReflectedWilsonKernel
