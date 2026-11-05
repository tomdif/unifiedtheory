/- The physical sampled noise pairing is exactly the true finite-cell source
covariance removed by the block. The tensor tests are ordinary physical Schwartz
smears; no new measure or continuum identification is supplied. -/
import UnifiedTheory.Clay.YangMills.WilsonCompactContactSubtraction
import UnifiedTheory.Clay.YangMills.WilsonPhysicalSecondMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonNoiseCellPairing
noncomputable section
open MeasureTheory RegulatedGauge LocalFields PeriodicLattice4
open WilsonSingleLinkStaples FiniteCellSmearing WilsonBlockNoiseKernel

local instance complexRealNormedSpace : NormedSpace ℝ ℂ :=
  InnerProductSpace.toNormedSpace

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (WilsonIndependentBlocks.Link n) := Classical.decEq _

theorem tensor_expansion (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (f g : TestFunction) (z : Spacetime × Spacetime) :
    (WilsonNoisePhysicalSupport.kernel n β a S plane plane' z.1 z.2 : ℂ) * (f z.1 * g z.2) =
      ∑ p, ∑ q, (((a ^ 8)⁻¹ * coefficient n β S p q : ℝ) : ℂ) *
        (cellFunction (PeriodicCellSampling.sample n a plane) p f z.1 *
          cellFunction (PeriodicCellSampling.sample n a plane') q g z.2) := by
  classical
  simp [cellFunction, mul_ite, ite_mul, WilsonNoisePhysicalSupport.kernel, eq_comm]

theorem tensor_summand_integrable (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (f g : TestFunction) (p q : PlaquetteIndex n) :
    Integrable (fun z : Spacetime × Spacetime =>
      (((a ^ 8)⁻¹ * coefficient n β S p q : ℝ) : ℂ) *
        (cellFunction (PeriodicCellSampling.sample n a plane) p f z.1 *
          cellFunction (PeriodicCellSampling.sample n a plane') q g z.2)) := by
  have hf := cellFunction_integrable volume (PeriodicCellSampling.sample n a plane)
    (PeriodicCellSampling.sample_measurable n a plane) p f f.integrable
  have hg := cellFunction_integrable volume (PeriodicCellSampling.sample n a plane')
    (PeriodicCellSampling.sample_measurable n a plane') q g g.integrable
  exact (hf.mul_prod hg).const_mul _

/-- The physical kernel times a tensor Schwartz test is genuinely integrable. -/
theorem tensor_integrable (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (f g : TestFunction) :
    Integrable (fun z : Spacetime × Spacetime =>
      (WilsonNoisePhysicalSupport.kernel n β a S plane plane' z.1 z.2 : ℂ) *
        (f z.1 * g z.2)) := by
  simp_rw [tensor_expansion n β a S plane plane' f g]
  exact integrable_finset_sum _ (fun p _ => integrable_finset_sum _
    (fun q _ => tensor_summand_integrable n β a S plane plane' f g p q))

/-- An exact finite-cell disintegration, before any asymptotic or contact expansion. -/
theorem tensor_pairing (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    (∫ z : Spacetime × Spacetime,
      (WilsonNoisePhysicalSupport.kernel n β a S plane plane' z.1 z.2 : ℂ) * (f z.1 * g z.2)) =
      (((a ^ 8)⁻¹ * bilinear n β S (WilsonPhysicalCellWeights.weight n a plane f)
        (WilsonPhysicalCellWeights.weight n a plane' g) : ℝ) : ℂ) := by
  simp_rw [tensor_expansion n β a S plane plane' f g]
  rw [integral_finset_sum _ (fun p _ => integrable_finset_sum _
    (fun q _ => tensor_summand_integrable n β a S plane plane' f g p q))]
  simp_rw [integral_finset_sum _
    (fun q _ => tensor_summand_integrable n β a S plane plane' f g _ q)]
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
  change (∑ p, ∑ q, (((a ^ 8)⁻¹ * coefficient n β S p q : ℝ) : ℂ) *
    (FiniteCellSmearing.coefficient volume (PeriodicCellSampling.sample n a plane) p f *
      FiniteCellSmearing.coefficient volume (PeriodicCellSampling.sample n a plane') q g)) = _
  simp_rw [WilsonPhysicalSecondMoment.coefficient_real n a plane f hf,
    WilsonPhysicalSecondMoment.coefficient_real n a plane' g hg]
  unfold bilinear
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The physical pairing is the actual original-minus-retained smeared covariance. -/
theorem tensor_covariance_pairing (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    let wf := WilsonPhysicalCellWeights.weight n a plane f
    let wg := WilsonPhysicalCellWeights.weight n a plane' g
    (∫ z : Spacetime × Spacetime,
      (WilsonNoisePhysicalSupport.kernel n β a S plane plane' z.1 z.2 : ℂ) * (f z.1 * g z.2)) =
      (((a ^ 8)⁻¹ *
        (GibbsCrossCovariance.covariance (wilsonLaw n Q character β 2) (source n wf) (source n wg) -
          GibbsCrossCovariance.covariance (WilsonCrossCovariance.retainedLaw n Q character β 2 S)
            (retained n β S wf) (retained n β S wg)) : ℝ) : ℂ) := by
  dsimp only
  rw [tensor_pairing n β a S plane plane' f g hf hg]
  congr 1
  congr 1
  have h := covariance_sub_retained n β S (WilsonPhysicalCellWeights.weight n a plane f)
    (WilsonPhysicalCellWeights.weight n a plane' g)
  linarith

/-- The actual removed smooth-source covariance admits the constructed local
contact subtraction with a proved O(a) error on compact physical supports. -/
theorem tensor_contact_bound (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0)
    (hfs : ∀ x, f x ≠ 0 → ‖x‖ ≤ R) (hgs : ∀ x, g x ≠ 0 → ‖x‖ ≤ R)
    (ha : 0 < a) (hperiod : 2 * R + 2 * a < (n : ℝ) * a) :
    ‖(((a ^ 8)⁻¹ * bilinear n β S (WilsonPhysicalCellWeights.weight n a plane f)
        (WilsonPhysicalCellWeights.weight n a plane' g) : ℝ) : ℂ) -
      WilsonCompactContactSubtraction.contact4 n β a R S plane plane'
        (SchwartzProductTensor.tensor f g)‖ ≤
      (WilsonNoiseTubeMass.massConstant R * 4 ^ 5 / 24) *
        SchwartzMap.seminorm ℝ 0 5 (SchwartzProductTensor.tensor f g) * a := by
  have hs (z : Spacetime × Spacetime) (hz : SchwartzProductTensor.tensor f g z ≠ 0) :
      ‖z.1‖ ≤ R ∧ ‖z.2‖ ≤ R := by
    change f z.1 * g z.2 ≠ 0 at hz
    exact ⟨hfs z.1 (left_ne_zero_of_mul hz), hgs z.2 (right_ne_zero_of_mul hz)⟩
  have h := WilsonCompactContactSubtraction.compact_subtraction_bound n β a R S hS
    plane plane' (SchwartzProductTensor.tensor f g) hs ha hperiod
  change ‖(∫ z : Spacetime × Spacetime,
    (WilsonNoisePhysicalSupport.kernel n β a S plane plane' z.1 z.2 : ℂ) * (f z.1 * g z.2)) -
      WilsonCompactContactSubtraction.contact4 n β a R S plane plane'
        (SchwartzProductTensor.tensor f g)‖ ≤ _ at h
  rw [tensor_pairing n β a S plane plane' f g hf hg] at h
  exact h

/-- Local subtraction reduces the actual rescaled full covariance to the
actual retained covariance with a controlled error on compact tensor smears. -/
theorem repaired_covariance_bound (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0)
    (hfs : ∀ x, f x ≠ 0 → ‖x‖ ≤ R) (hgs : ∀ x, g x ≠ 0 → ‖x‖ ≤ R)
    (ha : 0 < a) (hperiod : 2 * R + 2 * a < (n : ℝ) * a) :
    let wf := WilsonPhysicalCellWeights.weight n a plane f
    let wg := WilsonPhysicalCellWeights.weight n a plane' g
    ‖(((a ^ 8)⁻¹ *
        GibbsCrossCovariance.covariance (wilsonLaw n Q character β 2) (source n wf) (source n wg)
        : ℝ) : ℂ) -
      WilsonCompactContactSubtraction.contact4 n β a R S plane plane'
        (SchwartzProductTensor.tensor f g) -
      (((a ^ 8)⁻¹ *
        GibbsCrossCovariance.covariance (WilsonCrossCovariance.retainedLaw n Q character β 2 S)
          (retained n β S wf) (retained n β S wg) : ℝ) : ℂ)‖ ≤
      (WilsonNoiseTubeMass.massConstant R * 4 ^ 5 / 24) *
        SchwartzMap.seminorm ℝ 0 5 (SchwartzProductTensor.tensor f g) * a := by
  dsimp only
  have h := tensor_contact_bound n β a R S hS plane plane' f g hf hg hfs hgs ha hperiod
  have hc := covariance_sub_retained n β S (WilsonPhysicalCellWeights.weight n a plane f)
    (WilsonPhysicalCellWeights.weight n a plane' g)
  have he : bilinear n β S (WilsonPhysicalCellWeights.weight n a plane f)
      (WilsonPhysicalCellWeights.weight n a plane' g) =
      GibbsCrossCovariance.covariance (wilsonLaw n Q character β 2)
        (source n (WilsonPhysicalCellWeights.weight n a plane f))
        (source n (WilsonPhysicalCellWeights.weight n a plane' g)) -
      GibbsCrossCovariance.covariance (WilsonCrossCovariance.retainedLaw n Q character β 2 S)
        (retained n β S (WilsonPhysicalCellWeights.weight n a plane f))
        (retained n β S (WilsonPhysicalCellWeights.weight n a plane' g)) := by linarith
  rw [he, mul_sub, Complex.ofReal_sub] at h
  convert h using 1
  congr 1
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonNoiseCellPairing
