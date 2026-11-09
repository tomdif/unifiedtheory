/- Literal Wilson covariance coefficients at arbitrary elimination depth.
The stage action and source are computed recursively from the original Wilson
law. The uniform coefficient amplitude follows from the inherited source interval;
finite range and physical limits require the separately proved support geometry. -/
import UnifiedTheory.Clay.YangMills.WilsonFactorTower
import UnifiedTheory.Clay.YangMills.WilsonBlockNoiseKernel
import UnifiedTheory.Clay.YangMills.WilsonSecondNoiseCellPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonIteratedNoiseKernel
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples LocalFields
open WilsonBlockNoiseKernel

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

def sourceMap (f : PlaquetteIndex n → ℝ) : C(Configuration (Vertex n) Q, ℝ) :=
  ⟨source n f, source_continuous n f⟩

def response (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) (j : ℕ) : C(Configuration (Vertex n) Q, ℝ) :=
  GibbsCoordinateTower.observable (compactHaar Q) T (WilsonFactorTower.initialAction n β)
    (sourceMap n f) j

def law (β : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (j : ℕ) :
    Measure (Configuration (Vertex n) Q) :=
  GibbsCoordinateTower.law (compactHaar Q) T (WilsonFactorTower.initialAction n β) j

def noise (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) (j : ℕ) : C(Configuration (Vertex n) Q, ℝ) :=
  response n β T f j - response n β T f (j + 1)

def coefficient (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (j : ℕ) (p q : PlaquetteIndex n) : ℝ :=
  GibbsCoordinateTower.coefficient (compactHaar Q) T (WilsonFactorTower.initialAction n β)
    (sourceMap n (basis n p)) (sourceMap n (basis n q)) j

def bilinear (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (j : ℕ) (f g : PlaquetteIndex n → ℝ) : ℝ :=
  ∑ p, ∑ q, f p * g q * coefficient n β T j p q

/-- Literal periodic physical interpolation of the actual stage covariance. -/
def kernel (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (j : ℕ) (plane plane' : Plane) (x y : Spacetime) : ℝ :=
  (a ^ 8)⁻¹ * coefficient n β T j
    (PeriodicCellSampling.sample n a plane x) (PeriodicCellSampling.sample n a plane' y)

theorem response_basis_bounds (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (j : ℕ) (p : PlaquetteIndex n) (U : Configuration (Vertex n) Q) :
    response n β T (basis n p) j U ∈ Set.Icc (0 : ℝ) 4 :=
  GibbsCoordinateTower.observable_bounds (compactHaar Q) T (WilsonFactorTower.initialAction n β)
    (sourceMap n (basis n p)) 0 4 (source_basis_bounds n p) j U

theorem coefficient_eq_integral (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (j : ℕ) (p q : PlaquetteIndex n) :
    coefficient n β T j p q =
      ∫ U, noise n β T (basis n p) j U * noise n β T (basis n q) j U ∂law n β T j := rfl

theorem coefficient_abs_le (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (j : ℕ) (p q : PlaquetteIndex n) : |coefficient n β T j p q| ≤ 4 := by
  have h := GibbsCoordinateTower.coefficient_abs_le (compactHaar Q) T
    (WilsonFactorTower.initialAction n β) (sourceMap n (basis n p))
    (sourceMap n (basis n q)) 0 4 0 4 (by norm_num) (by norm_num)
    (source_basis_bounds n p) (source_basis_bounds n q) j
  norm_num only at h
  exact h

theorem coefficient_symm (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (j : ℕ) (p q : PlaquetteIndex n) : coefficient n β T j p q = coefficient n β T j q p := by
  simp only [coefficient_eq_integral, mul_comm]

theorem coefficient_diagonal_nonneg (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (j : ℕ) (p : PlaquetteIndex n) : 0 ≤ coefficient n β T j p p :=
  GibbsCoordinateTower.coefficient_self_nonneg (compactHaar Q) T
    (WilsonFactorTower.initialAction n β) (sourceMap n (basis n p)) j

theorem kernel_measurable (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (j : ℕ) (plane plane' : Plane) :
    Measurable (fun z : Spacetime × Spacetime => kernel n β a T j plane plane' z.1 z.2) := by
  have hgeneric (c : PlaquetteIndex n × PlaquetteIndex n → ℝ) :
      Measurable (fun z : Spacetime × Spacetime =>
        (a ^ 8)⁻¹ * c (PeriodicCellSampling.sample n a plane z.1,
          PeriodicCellSampling.sample n a plane' z.2)) := by
    have hc : Measurable c := measurable_of_countable c
    have hs : Measurable (fun z : Spacetime × Spacetime =>
        (PeriodicCellSampling.sample n a plane z.1,
          PeriodicCellSampling.sample n a plane' z.2)) :=
      ((PeriodicCellSampling.sample_measurable n a plane).comp measurable_fst).prodMk
        ((PeriodicCellSampling.sample_measurable n a plane').comp measurable_snd)
    exact measurable_const.mul (hc.comp hs)
  exact hgeneric (fun pq => coefficient n β T j pq.1 pq.2)

theorem kernel_abs_le (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (j : ℕ) (plane plane' : Plane) (x y : Spacetime) :
    |kernel n β a T j plane plane' x y| ≤ 4 / a ^ 8 := by
  unfold kernel
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (a ^ 8)⁻¹)]
  calc
    _ ≤ (a ^ 8)⁻¹ * 4 := mul_le_mul_of_nonneg_left
      (coefficient_abs_le n β T j _ _) (by positivity)
    _ = _ := by ring

/-- Original Wilson covariance splits into all actual removed stage coefficients
and the true retained remainder. -/
theorem basis_covariance_telescope (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (N : ℕ) (p q : PlaquetteIndex n) :
    GibbsCrossCovariance.covariance (wilsonLaw n Q character β 2)
      (source n (basis n p)) (source n (basis n q)) =
      (∑ j ∈ Finset.range N, coefficient n β T j p q) +
      GibbsCrossCovariance.covariance (law n β T N)
        (response n β T (basis n p) N) (response n β T (basis n q) N) := by
  have h := GibbsCoordinateTower.covariance_telescope (compactHaar Q) T
    (WilsonFactorTower.initialAction n β) (sourceMap n (basis n p))
    (sourceMap n (basis n q)) N
  change GibbsCrossCovariance.covariance
    (CompactGibbsContinuity.law (Measure.pi (fun _ : Edge (Vertex n) => compactHaar Q))
      (WilsonFactorTower.initialAction n β)) (source n (basis n p)) (source n (basis n q)) = _ at h
  rw [WilsonFactorTower.initial_law] at h
  exact h

end
end UnifiedTheory.Clay.YangMills.WilsonIteratedNoiseKernel
