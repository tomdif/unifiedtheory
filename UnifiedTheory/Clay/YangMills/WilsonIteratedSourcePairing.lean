/- Exact source and physical-cell identities at every genuine elimination depth.
The source is transported through each actual induced law. Finite telescoping
and cell interpolation do not assert uniform control of the retained covariance. -/
import UnifiedTheory.Clay.YangMills.WilsonIteratedNoiseKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonIteratedSourcePairing
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 LocalFields FiniteCellSmearing
open WilsonSingleLinkStaples WilsonBlockNoiseKernel WilsonIteratedNoiseKernel

local instance complexRealNormedSpace : NormedSpace ℝ ℂ :=
  InnerProductSpace.toNormedSpace

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- Linearity survives every actual induced conditional expectation. -/
theorem response_expansion (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) (j : ℕ) (U : Configuration (Vertex n) Q) :
    response n β T f j U = ∑ p, f p * response n β T (basis n p) j U := by
  induction j generalizing U with
  | zero => exact source_expansion n f U
  | succ j ih =>
    let A := GibbsCoordinateTower.action (compactHaar Q) T (WilsonFactorTower.initialAction n β) j
    let S := T j
    let J := CompactGibbsBlockUpdate.join (G := Q) S
    let B := A.comp J
    have he : ((response n β T f j).comp J : _ → ℝ) =
        fun z => ∑ p, f p * response n β T (basis n p) j (J z) := by
      funext z
      exact ih (J z)
    change GibbsMarginalTower.response (WilsonBlockMarginal.insideMeasure S (compactHaar Q))
      B ((response n β T f j).comp J) _ = _
    rw [he, GibbsBoundedResponse.response_sum _ Finset.univ B
      (fun p z => f p * response n β T (basis n p) j (J z)) B.continuous
      (fun p => continuous_const.mul ((response n β T (basis n p) j).continuous.comp J.continuous))]
    simp only [GibbsBoundedResponse.response_const_mul _ B _ B.continuous]
    rfl

/-- Every stage's centered removed source has the original finite basis expansion. -/
theorem noise_expansion (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) (j : ℕ) (U : Configuration (Vertex n) Q) :
    noise n β T f j U = ∑ p, f p * noise n β T (basis n p) j U := by
  change response n β T f j U - response n β T f (j + 1) U = _
  rw [response_expansion, response_expansion]
  simp only [WilsonIteratedNoiseKernel.noise, ContinuousMap.sub_apply, mul_sub,
    Finset.sum_sub_distrib]

/-- The finite matrix equals the Gram under the actual stage law. -/
theorem bilinear_eq_noise (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (j : ℕ) (f g : PlaquetteIndex n → ℝ) :
    bilinear n β T j f g = ∫ U, noise n β T f j U * noise n β T g j U ∂law n β T j := by
  let ν := law n β T j
  letI : IsProbabilityMeasure ν := GibbsCoordinateTower.lawProbability _ _ _ _
  have hi (p q : PlaquetteIndex n) : Integrable (fun U =>
      (f p * g q) * (noise n β T (basis n p) j U * noise n β T (basis n q) j U)) ν :=
    (continuous_const.mul ((noise n β T (basis n p) j).continuous.mul
      (noise n β T (basis n q) j).continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have he : (∫ U, ∑ p, ∑ q,
      (f p * g q) * (noise n β T (basis n p) j U * noise n β T (basis n q) j U) ∂ν) =
      ∑ p, ∑ q, f p * g q * coefficient n β T j p q := by
    rw [integral_finset_sum _ (fun p _ => integrable_finset_sum _ (fun q _ => hi p q))]
    simp_rw [integral_finset_sum _ (fun q _ => hi _ q), integral_const_mul]
    rfl
  unfold WilsonIteratedNoiseKernel.bilinear
  rw [← he]
  apply integral_congr_ae
  filter_upwards with U
  rw [noise_expansion n β T f, noise_expansion n β T g, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The coefficient is not a substituted original-law form: it is the actual tower removal. -/
theorem bilinear_eq_removedGram (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (j : ℕ) (f g : PlaquetteIndex n → ℝ) :
    bilinear n β T j f g = GibbsCoordinateTower.coefficient (compactHaar Q) T
      (WilsonFactorTower.initialAction n β) (sourceMap n f) (sourceMap n g) j :=
  bilinear_eq_noise n β T j f g

theorem positive_semidefinite (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (j : ℕ) (f : PlaquetteIndex n → ℝ) : 0 ≤ bilinear n β T j f f := by
  rw [bilinear_eq_noise]
  exact integral_nonneg (fun _ => mul_self_nonneg _)

/-- Exact finite-depth decomposition for every original weighted source. -/
theorem covariance_telescope (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (N : ℕ) (f g : PlaquetteIndex n → ℝ) :
    GibbsCrossCovariance.covariance (wilsonLaw n Q character β 2) (source n f) (source n g) =
      (∑ j ∈ Finset.range N, bilinear n β T j f g) +
      GibbsCrossCovariance.covariance (law n β T N) (response n β T f N) (response n β T g N) := by
  have h := GibbsCoordinateTower.covariance_telescope (compactHaar Q) T
    (WilsonFactorTower.initialAction n β) (sourceMap n f) (sourceMap n g) N
  change GibbsCrossCovariance.covariance
    (CompactGibbsContinuity.law (Measure.pi (fun _ : Edge (Vertex n) => compactHaar Q))
      (WilsonFactorTower.initialAction n β)) (source n f) (source n g) = _ at h
  rw [WilsonFactorTower.initial_law] at h
  simp_rw [bilinear_eq_removedGram]
  exact h

theorem tensor_expansion (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (j : ℕ)
    (plane plane' : Plane) (f g : TestFunction) (z : Spacetime × Spacetime) :
    (kernel n β a T j plane plane' z.1 z.2 : ℂ) * (f z.1 * g z.2) =
      ∑ p, ∑ q, (((a ^ 8)⁻¹ * coefficient n β T j p q : ℝ) : ℂ) *
        (cellFunction (PeriodicCellSampling.sample n a plane) p f z.1 *
          cellFunction (PeriodicCellSampling.sample n a plane') q g z.2) := by
  classical
  simp [cellFunction, mul_ite, ite_mul, kernel, eq_comm]

theorem tensor_summand_integrable (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (j : ℕ)
    (plane plane' : Plane) (f g : TestFunction) (p q : PlaquetteIndex n) :
    Integrable (fun z : Spacetime × Spacetime =>
      (((a ^ 8)⁻¹ * coefficient n β T j p q : ℝ) : ℂ) *
        (cellFunction (PeriodicCellSampling.sample n a plane) p f z.1 *
          cellFunction (PeriodicCellSampling.sample n a plane') q g z.2)) := by
  have hf := cellFunction_integrable volume (PeriodicCellSampling.sample n a plane)
    (PeriodicCellSampling.sample_measurable n a plane) p f f.integrable
  have hg := cellFunction_integrable volume (PeriodicCellSampling.sample n a plane')
    (PeriodicCellSampling.sample_measurable n a plane') q g g.integrable
  exact (hf.mul_prod hg).const_mul _

/-- The physical kernel times a tensor Schwartz test is genuinely integrable. -/
theorem tensor_integrable (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (j : ℕ)
    (plane plane' : Plane) (f g : TestFunction) :
    Integrable (fun z : Spacetime × Spacetime =>
      (kernel n β a T j plane plane' z.1 z.2 : ℂ) *
        (f z.1 * g z.2)) := by
  simp_rw [tensor_expansion n β a T j plane plane' f g]
  exact integrable_finset_sum _ (fun p _ => integrable_finset_sum _
    (fun q _ => tensor_summand_integrable n β a T j plane plane' f g p q))

/-- An exact finite-cell disintegration, before any asymptotic or contact expansion. -/
theorem tensor_pairing (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (j : ℕ)
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    (∫ z : Spacetime × Spacetime,
      (kernel n β a T j plane plane' z.1 z.2 : ℂ) * (f z.1 * g z.2)) =
      (((a ^ 8)⁻¹ * bilinear n β T j (WilsonPhysicalCellWeights.weight n a plane f)
        (WilsonPhysicalCellWeights.weight n a plane' g) : ℝ) : ℂ) := by
  simp_rw [tensor_expansion n β a T j plane plane' f g]
  rw [integral_finset_sum _ (fun p _ => integrable_finset_sum _
    (fun q _ => tensor_summand_integrable n β a T j plane plane' f g p q))]
  simp_rw [integral_finset_sum _
    (fun q _ => tensor_summand_integrable n β a T j plane plane' f g _ q)]
  have hp (p q : PlaquetteIndex n) :
      (∫ z : Spacetime × Spacetime,
        cellFunction (PeriodicCellSampling.sample n a plane) p f z.1 *
          cellFunction (PeriodicCellSampling.sample n a plane') q g z.2) =
      (∫ x, cellFunction (PeriodicCellSampling.sample n a plane) p f x) *
        ∫ y, cellFunction (PeriodicCellSampling.sample n a plane') q g y := by
    have hi := cellFunction_integrable volume (PeriodicCellSampling.sample n a plane)
      (PeriodicCellSampling.sample_measurable n a plane) p f f.integrable
    have hj := cellFunction_integrable volume (PeriodicCellSampling.sample n a plane')
      (PeriodicCellSampling.sample_measurable n a plane') q g g.integrable
    change (∫ z : Spacetime × Spacetime,
      cellFunction (PeriodicCellSampling.sample n a plane) p f z.1 *
        cellFunction (PeriodicCellSampling.sample n a plane') q g z.2 ∂volume.prod volume) = _
    rw [integral_prod _ (hi.mul_prod hj)]
    simp_rw [integral_const_mul, integral_mul_const]
  simp_rw [integral_const_mul, hp]
  change (∑ p, ∑ q, (((a ^ 8)⁻¹ * coefficient n β T j p q : ℝ) : ℂ) *
    (FiniteCellSmearing.coefficient volume (PeriodicCellSampling.sample n a plane) p f *
      FiniteCellSmearing.coefficient volume (PeriodicCellSampling.sample n a plane') q g)) = _
  simp_rw [WilsonPhysicalSecondMoment.coefficient_real n a plane f hf,
    WilsonPhysicalSecondMoment.coefficient_real n a plane' g hg]
  unfold WilsonIteratedNoiseKernel.bilinear
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring


/-- Physical rescaling and every finite removed stage agree exactly with the actual Wilson tower. -/
theorem physical_covariance_sub_sum (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (N : ℕ) (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    let wf := WilsonPhysicalCellWeights.weight n a plane f
    let wg := WilsonPhysicalCellWeights.weight n a plane' g
    (((a ^ 8)⁻¹ * GibbsCrossCovariance.covariance (wilsonLaw n Q character β 2)
      (source n wf) (source n wg) : ℝ) : ℂ) -
      (∑ j ∈ Finset.range N, ∫ z : Spacetime × Spacetime,
        (kernel n β a T j plane plane' z.1 z.2 : ℂ) * (f z.1 * g z.2)) =
      (((a ^ 8)⁻¹ * GibbsCrossCovariance.covariance (law n β T N)
        (response n β T wf N) (response n β T wg N) : ℝ) : ℂ) := by
  dsimp only
  simp_rw [tensor_pairing n β a T _ plane plane' f g hf hg]
  have h := covariance_telescope n β T N (WilsonPhysicalCellWeights.weight n a plane f)
    (WilsonPhysicalCellWeights.weight n a plane' g)
  rw [h, mul_add, Finset.mul_sum]
  push_cast
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonIteratedSourcePairing
