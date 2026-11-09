/- Literal physical interpolation of the actual second-stage removed covariance.
The coefficient uses the true first induced law, and the tensor pairing is
identified exactly with the finite-cell source Gram under that law. -/
import UnifiedTheory.Clay.YangMills.WilsonSuccessiveNoiseKernel
import UnifiedTheory.Clay.YangMills.WilsonNoiseCellPairing
import UnifiedTheory.Clay.YangMills.WilsonPhysicalSecondMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSecondNoiseCellPairing
noncomputable section
open MeasureTheory RegulatedGauge LocalFields PeriodicLattice4
open WilsonSingleLinkStaples FiniteCellSmearing WilsonSuccessiveNoiseKernel

local instance complexRealNormedSpace : NormedSpace ℝ ℂ :=
  InnerProductSpace.toNormedSpace

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- Literal a^-8 interpolation of the actual next-stage Wilson noise coefficient. -/
def kernel (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (plane plane' : Plane)
    (x y : Spacetime) : ℝ :=
  (a ^ 8)⁻¹ * coefficient n β S T
    (PeriodicCellSampling.sample n a plane x) (PeriodicCellSampling.sample n a plane' y)

theorem kernel_measurable (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (plane plane' : Plane) :
    Measurable (fun z : Spacetime × Spacetime => kernel n β a S T plane plane' z.1 z.2) := by
  have hgeneric (c : PlaquetteIndex n × PlaquetteIndex n → ℝ) :
      Measurable (fun z : Spacetime × Spacetime =>
        (a ^ 8)⁻¹ * c (PeriodicCellSampling.sample n a plane z.1,
          PeriodicCellSampling.sample n a plane' z.2)) := by
    have hc : Measurable c := measurable_of_countable c
    have hs : Measurable (fun z : Spacetime × Spacetime =>
        (PeriodicCellSampling.sample n a plane z.1, PeriodicCellSampling.sample n a plane' z.2)) :=
      ((PeriodicCellSampling.sample_measurable n a plane).comp measurable_fst).prodMk
        ((PeriodicCellSampling.sample_measurable n a plane').comp measurable_snd)
    exact measurable_const.mul (hc.comp hs)
  exact hgeneric (fun pq => coefficient n β S T pq.1 pq.2)

/-- The sharp interval covariance bound gives the actual physical amplitude. -/
theorem kernel_abs_le (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (plane plane' : Plane)
    (x y : Spacetime) : |kernel n β a S T plane plane' x y| ≤ 4 / a ^ 8 := by
  unfold kernel
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (a ^ 8)⁻¹)]
  calc
    _ ≤ (a ^ 8)⁻¹ * 4 := mul_le_mul_of_nonneg_left
      (coefficient_abs_le n β S T _ _) (by positivity)
    _ = _ := by ring

theorem tensor_expansion (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (plane plane' : Plane) (f g : TestFunction) (z : Spacetime × Spacetime) :
    (kernel n β a S T plane plane' z.1 z.2 : ℂ) * (f z.1 * g z.2) =
      ∑ p, ∑ q, (((a ^ 8)⁻¹ * coefficient n β S T p q : ℝ) : ℂ) *
        (cellFunction (PeriodicCellSampling.sample n a plane) p f z.1 *
          cellFunction (PeriodicCellSampling.sample n a plane') q g z.2) := by
  classical
  simp [cellFunction, mul_ite, ite_mul, kernel, eq_comm]

theorem tensor_summand_integrable (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (plane plane' : Plane) (f g : TestFunction) (p q : PlaquetteIndex n) :
    Integrable (fun z : Spacetime × Spacetime =>
      (((a ^ 8)⁻¹ * coefficient n β S T p q : ℝ) : ℂ) *
        (cellFunction (PeriodicCellSampling.sample n a plane) p f z.1 *
          cellFunction (PeriodicCellSampling.sample n a plane') q g z.2)) := by
  have hf := cellFunction_integrable volume (PeriodicCellSampling.sample n a plane)
    (PeriodicCellSampling.sample_measurable n a plane) p f f.integrable
  have hg := cellFunction_integrable volume (PeriodicCellSampling.sample n a plane')
    (PeriodicCellSampling.sample_measurable n a plane') q g g.integrable
  exact (hf.mul_prod hg).const_mul _

/-- The physical kernel times a tensor Schwartz test is genuinely integrable. -/
theorem tensor_integrable (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (plane plane' : Plane) (f g : TestFunction) :
    Integrable (fun z : Spacetime × Spacetime =>
      (kernel n β a S T plane plane' z.1 z.2 : ℂ) *
        (f z.1 * g z.2)) := by
  simp_rw [tensor_expansion n β a S T plane plane' f g]
  exact integrable_finset_sum _ (fun p _ => integrable_finset_sum _
    (fun q _ => tensor_summand_integrable n β a S T plane plane' f g p q))

/-- An exact finite-cell disintegration, before any asymptotic or contact expansion. -/
theorem tensor_pairing (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    (∫ z : Spacetime × Spacetime,
      (kernel n β a S T plane plane' z.1 z.2 : ℂ) * (f z.1 * g z.2)) =
      (((a ^ 8)⁻¹ * bilinear n β S T (WilsonPhysicalCellWeights.weight n a plane f)
        (WilsonPhysicalCellWeights.weight n a plane' g) : ℝ) : ℂ) := by
  simp_rw [tensor_expansion n β a S T plane plane' f g]
  rw [integral_finset_sum _ (fun p _ => integrable_finset_sum _
    (fun q _ => tensor_summand_integrable n β a S T plane plane' f g p q))]
  simp_rw [integral_finset_sum _
    (fun q _ => tensor_summand_integrable n β a S T plane plane' f g _ q)]
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
  change (∑ p, ∑ q, (((a ^ 8)⁻¹ * coefficient n β S T p q : ℝ) : ℂ) *
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


/-- The interpolated kernel is exactly the actual second removed Gram of physical cell sources. -/
theorem tensor_secondGram_pairing (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    (∫ z : Spacetime × Spacetime,
      (kernel n β a S T plane plane' z.1 z.2 : ℂ) * (f z.1 * g z.2)) =
      (((a ^ 8)⁻¹ * WilsonSuccessiveCovariance.secondGram n Q character β 2 S T
        (WilsonBlockNoiseKernel.source n (WilsonPhysicalCellWeights.weight n a plane f))
        (WilsonBlockNoiseKernel.source n (WilsonPhysicalCellWeights.weight n a plane' g))
        : ℝ) : ℂ) := by
  rw [tensor_pairing n β a S T plane plane' f g hf hg, bilinear_eq_secondGram]

/-- The physical second-stage pairing is the true first-minus-second retained covariance. -/
theorem tensor_covariance_pairing (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    let wf := WilsonPhysicalCellWeights.weight n a plane f
    let wg := WilsonPhysicalCellWeights.weight n a plane' g
    (∫ z : Spacetime × Spacetime,
      (kernel n β a S T plane plane' z.1 z.2 : ℂ) * (f z.1 * g z.2)) =
      (((a ^ 8)⁻¹ *
        (GibbsCrossCovariance.covariance (WilsonBlockMarginal.firstMarginal n Q character β 2 S T)
          (first n β S T wf) (first n β S T wg) -
        GibbsCrossCovariance.covariance (WilsonBlockMarginal.secondMarginal n Q character β 2 S T)
          (next n β S T wf) (next n β S T wg)) : ℝ) : ℂ) := by
  dsimp only
  rw [tensor_pairing n β a S T plane plane' f g hf hg]
  congr 1
  congr 1
  have h := covariance_sub_next n β S T (WilsonPhysicalCellWeights.weight n a plane f)
    (WilsonPhysicalCellWeights.weight n a plane' g)
  linarith


end
end UnifiedTheory.Clay.YangMills.WilsonSecondNoiseCellPairing
