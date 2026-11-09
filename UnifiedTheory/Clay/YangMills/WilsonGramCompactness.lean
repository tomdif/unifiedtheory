/- A positive normalized limiting Gram kernel of actual bounded Wilson-loop
products. Positivity comes from integration of squared absolute values under
finite Wilson probability laws; it is not assumed or confused with reflection
positivity. Connected nontriviality and renormalized local fields remain open. -/
import UnifiedTheory.Clay.YangMills.ProbabilityGramCompactness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonGramCompactness
noncomputable section
open CountableCorrelationCompactness WilsonMomentBounds ProbabilityGramCompactness

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {ι : Type*} [Countable ι]
variable (period : ℕ → ℕ) [∀ k, NeZero (period k)] (beta offset : ℕ → ℝ)
  (χ : G → ℂ) (order : ι → ℕ)
  (base : ∀ k i, Fin (order i) → Quiver.Symmetrify (PeriodicLattice4.Vertex (period k)))
  (loops : ∀ k i j, Quiver.Path (base k i j) (base k i j))

def wordProduct (k : ℕ) (i : ι) (U : RegulatedGauge.Configuration (PeriodicLattice4.Vertex (period k)) G) : ℂ :=
  ∏ j, loopObservable (PeriodicLattice4.Vertex (period k)) G χ (loops k i j) U

theorem wordProduct_continuous (hχ : Continuous χ) (k : ℕ) (i : ι) :
    Continuous (wordProduct G period χ order base loops k i) :=
  continuous_finset_prod _ (fun j _ => loopObservable_continuous _ G χ hχ (loops k i j))

theorem wordProduct_bound (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (k : ℕ) (i : ι) (U : RegulatedGauge.Configuration (PeriodicLattice4.Vertex (period k)) G) :
    ‖wordProduct G period χ order base loops k i U‖ ≤ B ^ order i := by
  unfold wordProduct
  rw [norm_prod]
  exact (Finset.prod_le_prod (fun j _ => norm_nonneg _)
    (fun j _ => loopObservable_bound _ G χ B hχ (loops k i j) U)).trans
      (by simp)

def gramCorrelation (k : ℕ) : ι × ι → ℂ :=
  kernel (PeriodicLattice4.wilsonLaw (period k) G χ (beta k) (offset k))
    (wordProduct G period χ order base loops k)

theorem exists_positive_wilson_gram_limit (hχ : Continuous χ) :
    ∃ (B : ℝ) (w : ι × ι → ℂ) (phi : ℕ → ℕ), 0 < B ∧ StrictMono phi ∧
      CoordinateConvergence (gramCorrelation G period beta offset χ order base loops ∘ phi) w ∧
      (∀ i, ‖w i‖ ≤ B ^ (order i.1 + order i.2)) ∧
      GramPositive (fun i j => (i, j)) w := by
  obtain ⟨B, hB, hb⟩ := character_bound_exists G χ hχ
  letI : ∀ k, MeasureTheory.IsProbabilityMeasure
      (PeriodicLattice4.wilsonLaw (period k) G χ (beta k) (offset k)) :=
    fun k => PeriodicLattice4.wilsonLaw_probability (period k) G χ hχ (beta k) (offset k)
  obtain ⟨w, phi, hphi, hc, hw, hp⟩ := exists_positive_kernel_limit
    (fun k => PeriodicLattice4.wilsonLaw (period k) G χ (beta k) (offset k))
    (wordProduct G period χ order base loops) (wordProduct_continuous G period χ order base loops hχ)
    (fun i => B ^ order i) (fun i => pow_nonneg hB.le _)
    (wordProduct_bound G period χ order base loops B hB.le hb)
  exact ⟨B, w, phi, hB, hphi, hc, fun i => by simpa only [pow_add] using hw i, hp⟩

theorem exists_normalized_positive_wilson_gram_limit (hχ : Continuous χ)
    (unitIndex : ι) (hunit : order unitIndex = 0) :
    ∃ (B : ℝ) (w : ι × ι → ℂ) (phi : ℕ → ℕ), 0 < B ∧ StrictMono phi ∧
      CoordinateConvergence (gramCorrelation G period beta offset χ order base loops ∘ phi) w ∧
      (∀ i, ‖w i‖ ≤ B ^ (order i.1 + order i.2)) ∧
      GramPositive (fun i j => (i, j)) w ∧ w (unitIndex, unitIndex) = 1 := by
  obtain ⟨B, hB, hb⟩ := character_bound_exists G χ hχ
  letI : ∀ k, MeasureTheory.IsProbabilityMeasure
      (PeriodicLattice4.wilsonLaw (period k) G χ (beta k) (offset k)) :=
    fun k => PeriodicLattice4.wilsonLaw_probability (period k) G χ hχ (beta k) (offset k)
  have hn (k : ℕ) (U : RegulatedGauge.Configuration (PeriodicLattice4.Vertex (period k)) G) :
      wordProduct G period χ order base loops k unitIndex U = 1 := by
    have hz : IsEmpty (Fin (order unitIndex)) := by rw [hunit]; infer_instance
    letI := hz
    simp [wordProduct]
  obtain ⟨w, phi, hphi, hc, hw, hp, hnorm⟩ := exists_normalized_positive_kernel_limit
    (fun k => PeriodicLattice4.wilsonLaw (period k) G χ (beta k) (offset k))
    (wordProduct G period χ order base loops) (wordProduct_continuous G period χ order base loops hχ)
    (fun i => B ^ order i) (fun i => pow_nonneg hB.le _)
    (wordProduct_bound G period χ order base loops B hB.le hb) unitIndex hn
  exact ⟨B, w, phi, hB, hphi, hc, fun i => by simpa only [pow_add] using hw i, hp, hnorm⟩

end
end UnifiedTheory.Clay.YangMills.WilsonGramCompactness
