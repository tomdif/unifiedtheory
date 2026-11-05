/- The actual next-stage Wilson noise has a deterministic bounded covariance
matrix under the true first induced law. Its coefficient bound is uniform in
coupling and both eliminated blocks; locality requires separate geometric control. -/
import UnifiedTheory.Clay.YangMills.GibbsBoundedResponse
import UnifiedTheory.Clay.YangMills.WilsonSuccessiveCovariance
import UnifiedTheory.Clay.YangMills.WilsonBlockNoiseKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSuccessiveNoiseKernel
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonBlockMarginal
open WilsonSingleLinkStaples WilsonBlockNoiseKernel GibbsMarginalTower

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

def first (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f : PlaquetteIndex n → ℝ) :=
  firstResponse n Q character β 2 S T (source n f)

def next (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f : PlaquetteIndex n → ℝ) :=
  secondResponse n Q character β 2 S T (first n β S T f)

def noise (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f : PlaquetteIndex n → ℝ)
    (r : Outside (G := Q) T × Inside (G := Q) T) : ℝ :=
  first n β S T f r - next n β S T f r.1

/-- This coefficient is computed under the actual first induced Wilson measure. -/
def coefficient (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (p q : PlaquetteIndex n) : ℝ :=
  ∫ r, noise n β S T (basis n p) r * noise n β S T (basis n q) r
    ∂firstMarginal n Q character β 2 S T

def bilinear (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f g : PlaquetteIndex n → ℝ) : ℝ :=
  ∑ p, ∑ q, f p * g q * coefficient n β S T p q

theorem first_continuous (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f : PlaquetteIndex n → ℝ) :
    Continuous (first n β S T f) :=
  response_continuous _ _ _ (splitActionTwo_continuous n Q character character_continuous β 2 S T)
    ((source_continuous n f).comp (assembleTwo_continuous S T))

theorem next_continuous (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f : PlaquetteIndex n → ℝ) :
    Continuous (next n β S T f) :=
  response_continuous _ _ _
    (effectiveAction_continuous _ _
      (splitActionTwo_continuous n Q character character_continuous β 2 S T))
    (first_continuous n β S T f)

theorem noise_continuous (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f : PlaquetteIndex n → ℝ) :
    Continuous (noise n β S T f) :=
  (first_continuous n β S T f).sub ((next_continuous n β S T f).comp continuous_fst)

/-- Actual first conditional averaging retains the original plaquette interval. -/
theorem first_basis_bounds (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (p : PlaquetteIndex n)
    (r : Outside (G := Q) T × Inside (G := Q) T) : first n β S T (basis n p) r ∈ Set.Icc 0 4 :=
  GibbsBoundedResponse.response_bounds _ _ _
    (splitActionTwo_continuous n Q character character_continuous β 2 S T)
    ((source_continuous n (basis n p)).comp (assembleTwo_continuous S T)) 0 4
    (fun z => source_basis_bounds n p (assembleTwo S T z)) r

/-- The interval survives the second averaging under the actual induced interaction. -/
theorem next_basis_bounds (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (p : PlaquetteIndex n)
    (r : Outside (G := Q) T) : next n β S T (basis n p) r ∈ Set.Icc 0 4 :=
  GibbsBoundedResponse.response_bounds _ _ _
    (effectiveAction_continuous _ _
      (splitActionTwo_continuous n Q character character_continuous β 2 S T))
    (first_continuous n β S T (basis n p)) 0 4 (first_basis_bounds n β S T p) r

theorem coefficient_eq_secondGram (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (p q : PlaquetteIndex n) :
    coefficient n β S T p q = WilsonSuccessiveCovariance.secondGram n Q character β 2 S T
      (source n (basis n p)) (source n (basis n q)) := rfl

/-- The coefficient is exactly the averaged conditional covariance at the induced stage. -/
theorem coefficient_eq_conditional (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (p q : PlaquetteIndex n) :
    coefficient n β S T p q =
      ∫ r, GibbsCrossCovariance.conditionalCovariance (insideMeasure T (compactHaar Q))
        (retainedAction n Q character β 2 S T)
        (first n β S T (basis n p)) (first n β S T (basis n q)) r
        ∂secondMarginal n Q character β 2 S T := by
  rw [coefficient_eq_secondGram,
    WilsonSuccessiveCovariance.secondGram_eq_generic n Q character character_continuous β 2 S T]
  exact GibbsSuccessiveCovariance.gram_eq_conditional
    (outsideMeasure T (compactHaar Q)) (insideMeasure T (compactHaar Q))
    (retainedAction n Q character β 2 S T)
    (first n β S T (basis n p)) (first n β S T (basis n q))
    (effectiveAction_continuous _ _
      (splitActionTwo_continuous n Q character character_continuous β 2 S T))
    (first_continuous n β S T (basis n p)) (first_continuous n β S T (basis n q))

/-- An exact conditional product identity suffices to remove the actual next-stage entry. -/
theorem coefficient_zero_of_conditional (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (p q : PlaquetteIndex n)
    (hzero : ∀ r, GibbsCrossCovariance.conditionalCovariance (insideMeasure T (compactHaar Q))
      (retainedAction n Q character β 2 S T)
      (first n β S T (basis n p)) (first n β S T (basis n q)) r = 0) :
    coefficient n β S T p q = 0 := by
  rw [coefficient_eq_conditional]
  simp only [hzero, integral_zero]

/-- The next-stage coefficients have the sharp bounded-interval constant four.
No independence or supplied density comparison is needed for this amplitude bound. -/
theorem coefficient_abs_le (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (p q : PlaquetteIndex n) :
    |coefficient n β S T p q| ≤ 4 := by
  rw [coefficient_eq_secondGram,
    WilsonSuccessiveCovariance.secondGram_eq_generic n Q character character_continuous β 2 S T]
  have h := GibbsBoundedResponse.gram_abs_le (outsideMeasure T (compactHaar Q))
    (insideMeasure T (compactHaar Q)) (retainedAction n Q character β 2 S T)
    (first n β S T (basis n p)) (first n β S T (basis n q))
    (effectiveAction_continuous _ _
      (splitActionTwo_continuous n Q character character_continuous β 2 S T))
    (first_continuous n β S T (basis n p)) (first_continuous n β S T (basis n q))
    0 4 0 4 (by norm_num) (by norm_num)
    (first_basis_bounds n β S T p) (first_basis_bounds n β S T q)
  norm_num at h
  exact h

theorem coefficient_symm (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (p q : PlaquetteIndex n) :
    coefficient n β S T p q = coefficient n β S T q p := by
  unfold coefficient
  apply integral_congr_ae
  filter_upwards with r
  ring

/-- Every original finite coefficient expansion survives the first true averaging. -/
theorem first_expansion (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f : PlaquetteIndex n → ℝ)
    (r : Outside (G := Q) T × Inside (G := Q) T) :
    first n β S T f r = ∑ p, f p * first n β S T (basis n p) r := by
  let A := splitActionTwo n Q character β 2 S T
  have hA : Continuous A := splitActionTwo_continuous n Q character character_continuous β 2 S T
  have he : (source n f ∘ assembleTwo S T) =
      fun z => ∑ p, f p * source n (basis n p) (assembleTwo S T z) := by
    funext z
    exact source_expansion n f _
  change response (insideMeasure S (compactHaar Q)) A _ r = _
  rw [he, GibbsBoundedResponse.response_sum _ Finset.univ A
    (fun p z => f p * source n (basis n p) (assembleTwo S T z)) hA
    (fun p => continuous_const.mul
      ((source_continuous n (basis n p)).comp (assembleTwo_continuous S T)))]
  simp only [GibbsBoundedResponse.response_const_mul _ A _ hA]
  rfl

/-- The same expansion survives the second averaging without reusing the original law. -/
theorem next_expansion (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f : PlaquetteIndex n → ℝ)
    (r : Outside (G := Q) T) :
    next n β S T f r = ∑ p, f p * next n β S T (basis n p) r := by
  let A := retainedAction n Q character β 2 S T
  have hA : Continuous A := effectiveAction_continuous _ _
    (splitActionTwo_continuous n Q character character_continuous β 2 S T)
  have he : first n β S T f = fun z => ∑ p, f p * first n β S T (basis n p) z :=
    funext (first_expansion n β S T f)
  change response (insideMeasure T (compactHaar Q)) A _ r = _
  rw [he, GibbsBoundedResponse.response_sum _ Finset.univ A
    (fun p z => f p * first n β S T (basis n p) z) hA
    (fun p => continuous_const.mul (first_continuous n β S T (basis n p)))]
  simp only [GibbsBoundedResponse.response_const_mul _ A _ hA]
  rfl

theorem noise_expansion (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f : PlaquetteIndex n → ℝ)
    (r : Outside (G := Q) T × Inside (G := Q) T) :
    noise n β S T f r = ∑ p, f p * noise n β S T (basis n p) r := by
  unfold noise
  rw [first_expansion, next_expansion]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- The finite next-stage matrix is exactly the Gram form of the actual combined noise. -/
theorem bilinear_eq_noise (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f g : PlaquetteIndex n → ℝ) :
    bilinear n β S T f g = ∫ r, noise n β S T f r * noise n β S T g r
      ∂firstMarginal n Q character β 2 S T := by
  let ν := firstMarginal n Q character β 2 S T
  letI : IsProbabilityMeasure ν := marginal_probability _ _ _
    (splitActionTwo_continuous n Q character character_continuous β 2 S T)
  have hi (p q : PlaquetteIndex n) : Integrable (fun r =>
      (f p * g q) * (noise n β S T (basis n p) r * noise n β S T (basis n q) r)) ν :=
    (continuous_const.mul ((noise_continuous n β S T (basis n p)).mul
      (noise_continuous n β S T (basis n q)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have he : (∫ r, ∑ p, ∑ q,
      (f p * g q) * (noise n β S T (basis n p) r * noise n β S T (basis n q) r) ∂ν) =
      ∑ p, ∑ q, f p * g q * coefficient n β S T p q := by
    rw [integral_finset_sum _ (fun p _ => integrable_finset_sum _ (fun q _ => hi p q))]
    simp_rw [integral_finset_sum _ (fun q _ => hi _ q), integral_const_mul]
    rfl
  unfold bilinear
  rw [← he]
  apply integral_congr_ae
  filter_upwards with r
  rw [noise_expansion n β S T f, noise_expansion n β S T g, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem bilinear_eq_secondGram (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f g : PlaquetteIndex n → ℝ) :
    bilinear n β S T f g =
      WilsonSuccessiveCovariance.secondGram n Q character β 2 S T (source n f) (source n g) :=
  bilinear_eq_noise n β S T f g

theorem positive_semidefinite (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f : PlaquetteIndex n → ℝ) :
    0 ≤ bilinear n β S T f f := by
  rw [bilinear_eq_noise]
  exact integral_nonneg (fun _ => mul_self_nonneg _)

/-- The actual second covariance matrix subtracts from the true first covariance. -/
theorem covariance_sub_next (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f g : PlaquetteIndex n → ℝ) :
    GibbsCrossCovariance.covariance (firstMarginal n Q character β 2 S T)
      (first n β S T f) (first n β S T g) - bilinear n β S T f g =
      GibbsCrossCovariance.covariance (secondMarginal n Q character β 2 S T)
        (next n β S T f) (next n β S T g) := by
  rw [bilinear_eq_secondGram,
    WilsonSuccessiveCovariance.secondGram_eq_generic n Q character character_continuous β 2 S T]
  have h := GibbsSuccessiveCovariance.covariance_decomposition (outsideMeasure T (compactHaar Q))
    (insideMeasure T (compactHaar Q)) (retainedAction n Q character β 2 S T)
    (first n β S T f) (first n β S T g)
    (effectiveAction_continuous _ _
      (splitActionTwo_continuous n Q character character_continuous β 2 S T))
    (first_continuous n β S T f) (first_continuous n β S T g)
  have hl := GibbsMarginalTower.marginal_eq_effectiveLaw
    ((outsideMeasure T (compactHaar Q)).prod (insideMeasure T (compactHaar Q)))
    (insideMeasure S (compactHaar Q)) (splitActionTwo n Q character β 2 S T)
    (splitActionTwo_continuous n Q character character_continuous β 2 S T)
  change firstMarginal n Q character β 2 S T =
    CompactGibbsContinuity.law
      ((outsideMeasure T (compactHaar Q)).prod (insideMeasure T (compactHaar Q)))
      (retainedAction n Q character β 2 S T) at hl
  rw [hl]
  change GibbsCrossCovariance.covariance _ _ _ - GibbsSuccessiveCovariance.gram _ _ _ _ _ = _
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

end
end UnifiedTheory.Clay.YangMills.WilsonSuccessiveNoiseKernel
