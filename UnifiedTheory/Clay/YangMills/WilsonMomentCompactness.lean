/- A common convergent subsequence for countably many bare loop moments
of the actual periodic four-dimensional Wilson laws. No renormalized local
field limit, reflection positivity, or surviving mass gap is asserted. -/
import UnifiedTheory.Clay.YangMills.CountableCorrelationCompactness
import UnifiedTheory.Clay.YangMills.WilsonMomentBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonMomentCompactness
noncomputable section
open CountableCorrelationCompactness WilsonMomentBounds

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {ι : Type*} [Countable ι]

variable (period : ℕ → ℕ) [∀ k, NeZero (period k)] (beta offset : ℕ → ℝ)
  (χ : G → ℂ) (order : ι → ℕ)
  (base : ∀ k i, Fin (order i) → Quiver.Symmetrify (PeriodicLattice4.Vertex (period k)))
  (loops : ∀ k i j, Quiver.Path (base k i j) (base k i j))

def correlation (k : ℕ) (i : ι) : ℂ :=
  moment (PeriodicLattice4.wilsonLaw (period k) G χ (beta k) (offset k)) Finset.univ
    (fun j => loopObservable (PeriodicLattice4.Vertex (period k)) G χ (loops k i j))

theorem exists_bare_moment_subsequence (hχ : Continuous χ) :
    ∃ (B : ℝ) (w : ι → ℂ) (phi : ℕ → ℕ), 0 < B ∧ StrictMono phi ∧
      CoordinateConvergence (correlation G period beta offset χ order base loops ∘ phi) w ∧
      ∀ i, ‖w i‖ ≤ B ^ order i := by
  obtain ⟨B, hB, hb⟩ := periodic_uniform_moments G χ hχ
  obtain ⟨w, phi, hphi, hc, hw⟩ := exists_common_subsequence
    (correlation G period beta offset χ order base loops) (fun i => B ^ order i)
    (fun k i => hb (period k) (beta k) (offset k) (order i) (base k i) (loops k i))
  exact ⟨B, w, phi, hB, hphi, hc, hw⟩

theorem empty_moment (hχ : Continuous χ) (i : ι) (hi : order i = 0) (k : ℕ) :
    correlation G period beta offset χ order base loops k i = 1 := by
  letI := PeriodicLattice4.wilsonLaw_probability (period k) G χ hχ (beta k) (offset k)
  have hz : IsEmpty (Fin (order i)) := by rw [hi]; infer_instance
  letI := hz
  simp [correlation, moment]

theorem exists_normalized_bare_moment_subsequence (hχ : Continuous χ)
    (unitIndex : ι) (hunit : order unitIndex = 0) :
    ∃ (B : ℝ) (w : ι → ℂ) (phi : ℕ → ℕ), 0 < B ∧ StrictMono phi ∧
      CoordinateConvergence (correlation G period beta offset χ order base loops ∘ phi) w ∧
      (∀ i, ‖w i‖ ≤ B ^ order i) ∧ w unitIndex = 1 := by
  obtain ⟨B, w, phi, hB, hphi, hc, hw⟩ :=
    exists_bare_moment_subsequence G period beta offset χ order base loops hχ
  refine ⟨B, w, phi, hB, hphi, hc, hw, ?_⟩
  exact normalization_survives _ _ hc unitIndex
    (fun k => empty_moment G period beta offset χ order base loops hχ unitIndex hunit (phi k))

end
end UnifiedTheory.Clay.YangMills.WilsonMomentCompactness
