/- Two genuine successive Wilson eliminations. The first block is integrated
under the original Wilson law; the second is integrated under its exact induced
action. No independence, Wilson-form closure, or small evolved covariance is
assumed. All mixed covariance terms and the final retained term remain explicit. -/
import UnifiedTheory.Clay.YangMills.GibbsSuccessiveCovariance
import UnifiedTheory.Clay.YangMills.WilsonBlockMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSuccessiveCovariance
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonBlockMarginal
open GibbsMarginalTower GibbsCrossCovariance

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The first fluctuation, evaluated on the actual original configuration. -/
def firstNoise (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F : Configuration (Vertex n) G → ℝ) (U : Configuration (Vertex n) G) : ℝ :=
  F U - firstResponse n G χ β c S T F ((assembleTwo S T).symm U).1

/-- The second fluctuation belongs to the actual retained first-stage coordinates. -/
def secondNoise (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F : Configuration (Vertex n) G → ℝ) (z : Outside (G := G) T × Inside (G := G) T) : ℝ :=
  firstResponse n G χ β c S T F z -
    secondResponse n G χ β c S T (firstResponse n G χ β c S T F) z.1

/-- The first Gram is taken under the original interacting Wilson law. -/
def firstGram (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F H : Configuration (Vertex n) G → ℝ) : ℝ :=
  ∫ U, firstNoise n G χ β c S T F U * firstNoise n G χ β c S T H U
    ∂wilsonLaw n G χ β c

/-- The next Gram is taken under the genuine first marginal, with its induced interactions. -/
def secondGram (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F H : Configuration (Vertex n) G → ℝ) : ℝ :=
  ∫ z, secondNoise n G χ β c S T F z * secondNoise n G χ β c S T H z
    ∂firstMarginal n G χ β c S T

/-- The actual fluctuation removed by both integrations. -/
def jointNoise (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F : Configuration (Vertex n) G → ℝ) (U : Configuration (Vertex n) G) : ℝ :=
  F U - secondResponse n G χ β c S T (firstResponse n G χ β c S T F)
    ((assembleTwo S T).symm U).1.1

omit [SecondCountableTopology G] in
theorem firstNoise_assemble (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (F : Configuration (Vertex n) G → ℝ)
    (z : (Outside (G := G) T × Inside (G := G) T) × Inside (G := G) S) :
    firstNoise n G χ β c S T F (assembleTwo S T z) =
      removed (insideMeasure S (compactHaar G)) (splitActionTwo n G χ β c S T)
        (F ∘ assembleTwo S T) z := by
  simp only [firstNoise, MeasurableEquiv.symm_apply_apply]
  rfl

theorem firstGram_eq_generic (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F H : Configuration (Vertex n) G → ℝ) :
    firstGram n G χ β c S T F H =
      GibbsSuccessiveCovariance.gram
        ((outsideMeasure T (compactHaar G)).prod (insideMeasure T (compactHaar G)))
        (insideMeasure S (compactHaar G)) (splitActionTwo n G χ β c S T)
        (F ∘ assembleTwo S T) (H ∘ assembleTwo S T) := by
  unfold firstGram
  rw [wilson_integral_split_two n G χ hχ β c S T]
  simp only [firstNoise_assemble]
  rfl

theorem secondGram_eq_generic (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F H : Configuration (Vertex n) G → ℝ) :
    secondGram n G χ β c S T F H =
      GibbsSuccessiveCovariance.secondGram (outsideMeasure T (compactHaar G))
        (insideMeasure T (compactHaar G)) (insideMeasure S (compactHaar G))
        (splitActionTwo n G χ β c S T) (F ∘ assembleTwo S T) (H ∘ assembleTwo S T) := by
  unfold secondGram firstMarginal
  rw [marginal_eq_effectiveLaw _ _ _ (splitActionTwo_continuous n G χ hχ β c S T)]
  rfl

theorem covariance_coordinates (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F H : Configuration (Vertex n) G → ℝ) :
    covariance (wilsonLaw n G χ β c) F H =
      covariance (CompactGibbsContinuity.law
        (((outsideMeasure T (compactHaar G)).prod (insideMeasure T (compactHaar G))).prod
          (insideMeasure S (compactHaar G))) (splitActionTwo n G χ β c S T))
        (F ∘ assembleTwo S T) (H ∘ assembleTwo S T) := by
  unfold covariance
  rw [wilson_integral_split_two n G χ hχ β c S T,
    wilson_integral_split_two n G χ hχ β c S T,
    wilson_integral_split_two n G χ hχ β c S T]
  rfl

/-- Exact mixed covariance decomposition under the original Wilson law and its true marginals. -/
theorem covariance_decomposition (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F H : Configuration (Vertex n) G → ℝ) (hF : Continuous F) (hH : Continuous H) :
    covariance (wilsonLaw n G χ β c) F H =
      firstGram n G χ β c S T F H + secondGram n G χ β c S T F H +
      covariance (secondMarginal n G χ β c S T)
        (secondResponse n G χ β c S T (firstResponse n G χ β c S T F))
        (secondResponse n G χ β c S T (firstResponse n G χ β c S T H)) := by
  rw [covariance_coordinates n G χ hχ β c S T,
    firstGram_eq_generic n G χ hχ β c S T, secondGram_eq_generic n G χ hχ β c S T]
  exact GibbsSuccessiveCovariance.successive_covariance _ _ _ _ _ _
    (splitActionTwo_continuous n G χ hχ β c S T)
    (hF.comp (assembleTwo_continuous S T)) (hH.comp (assembleTwo_continuous S T))

/-- Different-stage fluctuations are orthogonal under the original law. -/
theorem successive_orthogonal (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F H : Configuration (Vertex n) G → ℝ) (hF : Continuous F) (hH : Continuous H) :
    (∫ U, firstNoise n G χ β c S T F U *
      secondNoise n G χ β c S T H ((assembleTwo S T).symm U).1
      ∂wilsonLaw n G χ β c) = 0 := by
  rw [wilson_integral_split_two n G χ hχ β c S T]
  simp only [firstNoise_assemble, MeasurableEquiv.symm_apply_apply]
  exact GibbsSuccessiveCovariance.successive_noise_orthogonal _ _ _ _ _ _
    (splitActionTwo_continuous n G χ hχ β c S T)
    (hF.comp (assembleTwo_continuous S T)) (hH.comp (assembleTwo_continuous S T))

/-- Both actual noise budgets add without double counting the original fluctuation. -/
theorem joint_noise_gram (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F H : Configuration (Vertex n) G → ℝ) (hF : Continuous F) (hH : Continuous H) :
    (∫ U, jointNoise n G χ β c S T F U * jointNoise n G χ β c S T H U
      ∂wilsonLaw n G χ β c) =
      firstGram n G χ β c S T F H + secondGram n G χ β c S T F H := by
  rw [wilson_integral_split_two n G χ hχ β c S T,
    firstGram_eq_generic n G χ hχ β c S T, secondGram_eq_generic n G χ hχ β c S T]
  simp only [jointNoise, MeasurableEquiv.symm_apply_apply]
  exact GibbsSuccessiveCovariance.joint_noise_gram _ _ _ _ _ _
    (splitActionTwo_continuous n G χ hχ β c S T)
    (hF.comp (assembleTwo_continuous S T)) (hH.comp (assembleTwo_continuous S T))

/-- The positive cumulative loss is bounded by the original variance,
with no desired bound supplied. -/
theorem cumulative_variance_budget (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F : Configuration (Vertex n) G → ℝ) (hF : Continuous F) :
    0 ≤ firstGram n G χ β c S T F F + secondGram n G χ β c S T F F ∧
    firstGram n G χ β c S T F F + secondGram n G χ β c S T F F ≤
      covariance (wilsonLaw n G χ β c) F F := by
  rw [firstGram_eq_generic n G χ hχ β c S T, secondGram_eq_generic n G χ hχ β c S T,
    covariance_coordinates n G χ hχ β c S T]
  exact GibbsSuccessiveCovariance.cumulative_variance_budget _ _ _ _ _
    (splitActionTwo_continuous n G χ hχ β c S T) (hF.comp (assembleTwo_continuous S T))

/-- Nonexpansion for the actual twice retained source, without claiming a uniform variance bound. -/
theorem retained_variance_bounds (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (F : Configuration (Vertex n) G → ℝ) (hF : Continuous F) :
    0 ≤ covariance (secondMarginal n G χ β c S T)
      (secondResponse n G χ β c S T (firstResponse n G χ β c S T F))
      (secondResponse n G χ β c S T (firstResponse n G χ β c S T F)) ∧
    covariance (secondMarginal n G χ β c S T)
      (secondResponse n G χ β c S T (firstResponse n G χ β c S T F))
      (secondResponse n G χ β c S T (firstResponse n G χ β c S T F)) ≤
        covariance (wilsonLaw n G χ β c) F F := by
  rw [covariance_coordinates n G χ hχ β c S T]
  exact GibbsSuccessiveCovariance.final_variance_bounds _ _ _ _ _
    (splitActionTwo_continuous n G χ hχ β c S T) (hF.comp (assembleTwo_continuous S T))

omit [SecondCountableTopology G] in
/-- Both individual removed forms have nonnegative diagonals under their actual laws. -/
theorem removed_forms_nonneg (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (F : Configuration (Vertex n) G → ℝ) :
    0 ≤ firstGram n G χ β c S T F F ∧ 0 ≤ secondGram n G χ β c S T F F :=
  ⟨integral_nonneg (fun _ => mul_self_nonneg _),
    integral_nonneg (fun _ => mul_self_nonneg _)⟩

/-- A final-coordinate source has exactly the same covariance after both Wilson integrations.
No blanket strict contraction on all sources follows from elimination alone. -/
theorem retained_exact_boundary (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (H J : Outside (G := G) T → ℝ) (hH : Continuous H) (hJ : Continuous J) :
    covariance (wilsonLaw n G χ β c)
      (fun U => H ((assembleTwo (G := G) S T).symm U).1.1)
      (fun U => J ((assembleTwo (G := G) S T).symm U).1.1) =
      covariance (secondMarginal n G χ β c S T) H J := by
  rw [covariance_coordinates n G χ hχ β c S T]
  have he (L : Outside (G := G) T → ℝ) :
      (fun U => L ((assembleTwo (G := G) S T).symm U).1.1) ∘ assembleTwo S T =
      fun z => L z.1.1 := by
    funext z
    simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  rw [he H, he J]
  exact GibbsSuccessiveCovariance.retained_exact_boundary
    (outsideMeasure T (compactHaar G)) (insideMeasure T (compactHaar G))
    (insideMeasure S (compactHaar G)) (splitActionTwo n G χ β c S T)
    (splitActionTwo_continuous n G χ hχ β c S T) H J hH hJ

end
end UnifiedTheory.Clay.YangMills.WilsonSuccessiveCovariance
