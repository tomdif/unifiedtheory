/- Physical cell smearing of the actual independent-block Wilson response.
The block size and lattice volume do not enter the approximation budget.
The cutoff-rescaled residual vanishes on a supplied strict-margin trajectory;
the retained response, physical trajectory and nonzero limit remain separate. -/
import UnifiedTheory.Clay.YangMills.SU2WilsonBlockApproximation
import UnifiedTheory.Clay.YangMills.WilsonPhysicalCellWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2WilsonPhysicalBlock
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 LocalFields
open WilsonSingleLinkStaples WilsonIndependentBlocks SU2WilsonBlockApproximation
open Filter Topology

def physicalEnvelope (β r₀ : ℝ) (f : TestFunction) : ℝ :=
  1280 * Real.exp 2 * r₀^2 * β^2 * Real.exp (-4 * β * r₀) * ∫ x, ‖f x‖

theorem physicalEnvelope_nonneg (β r₀ : ℝ) (f : TestFunction) :
    0 ≤ physicalEnvelope β r₀ f := by
  unfold physicalEnvelope
  positivity

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

omit [Fact (1 < n)] in
theorem envelope_le_physical (a : ℝ) (plane : Plane) (β r₀ : ℝ) (f : TestFunction) :
    errorEnvelope n β r₀ (WilsonPhysicalCellWeights.weight n a plane f) ≤
      physicalEnvelope β r₀ f :=
  mul_le_mul_of_nonneg_left (WilsonPhysicalCellWeights.weight_budget n a plane f)
    (by positivity)

theorem physical_hybrid_error_bound (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (a : ℝ) (plane : Plane)
    (β r₀ r₁ : ℝ) (hr₀ : 0 < r₀) (hcut : r₀ < r₁) (hβr : 3 / 4 ≤ β * r₀)
    (f : TestFunction) (b : WilsonBlockMarginal.Outside (G := Q) S) :
    |response n S β (WilsonPhysicalCellWeights.weight n a plane f) b -
      hybridSource n S β r₀ r₁ (WilsonPhysicalCellWeights.weight n a plane f) b| ≤
        physicalEnvelope β r₀ f :=
  (hybrid_error_bound n S hS β r₀ r₁ hr₀ hcut hβr _ b).trans
    (envelope_le_physical n a plane β r₀ f)

theorem physical_retained_error_l2_bound (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (a : ℝ) (plane : Plane)
    (β r₀ r₁ : ℝ) (hβ : 0 < β) (hr₀ : 0 < r₀) (hcut : r₀ < r₁)
    (hβr : 3 / 4 ≤ β * r₀) (f : TestFunction) :
    (∫ b, (response n S β (WilsonPhysicalCellWeights.weight n a plane f) b -
      hybridSource n S β r₀ r₁ (WilsonPhysicalCellWeights.weight n a plane f) b)^2
        ∂retainedLaw n S β) ≤ (physicalEnvelope β r₀ f)^2 :=
  (retained_error_l2_bound n S hS β r₀ r₁ hβ hr₀ hcut hβr _).trans
    (pow_le_pow_left₀ (errorEnvelope_nonneg n β r₀ _)
      (envelope_le_physical n a plane β r₀ f) 2)

omit n [NeZero n] [Fact (1 < n)] in
theorem rescaled_physicalEnvelope_tendsto {ι : Type*} {l : Filter ι}
    (a β : ι → ℝ) (b r₀ : ℝ) (f : TestFunction)
    (ha : Tendsto a l (𝓝[>] 0))
    (hβ : Tendsto (fun i => β i / Real.log (a i)⁻¹) l (𝓝 b))
    (hmargin : 1 < b * r₀) :
    Tendsto (fun i => (a i^4)⁻¹ * physicalEnvelope (β i) r₀ f) l (𝓝 0) := by
  have h := (CouplingTrajectoryRobustness.cutoffError_tendsto a β b r₀ ha hβ
    hmargin).const_mul (1280 * Real.exp 2 * r₀^2 * ∫ x, ‖f x‖)
  simp only [mul_zero] at h
  convert h using 1
  funext i
  unfold physicalEnvelope
  ring

omit n [NeZero n] [Fact (1 < n)] in
/-- Varying actual block responses with fixed physical smearing. The coefficient
budget is proved, rather than supplied as a uniform-weight hypothesis. -/
theorem rescaled_physical_hybrid_error_tendsto {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (S : ∀ i, Finset (Edge (Vertex (period i))))
    (hS : ∀ i, Independent (period i) ((S i).image (edgeCoord (period i))))
    (exterior : ∀ i, WilsonBlockMarginal.Outside (G := Q) (S i))
    (a β : ι → ℝ) (b r₀ r₁ : ℝ) (plane : Plane) (f : TestFunction)
    (ha : Tendsto a l (𝓝[>] 0))
    (hβ : Tendsto (fun i => β i / Real.log (a i)⁻¹) l (𝓝 b))
    (hr₀ : 0 < r₀) (hcut : r₀ < r₁) (hmargin : 1 < b * r₀) :
    Tendsto (fun i => (a i^4)⁻¹ *
      (response (period i) (S i) (β i)
        (WilsonPhysicalCellWeights.weight (period i) (a i) plane f) (exterior i) -
       hybridSource (period i) (S i) (β i) r₀ r₁
        (WilsonPhysicalCellWeights.weight (period i) (a i) plane f) (exterior i)))
      l (𝓝 0) := by
  have hb : 0 < b := by
    by_contra hn
    have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hr₀.le
    linarith
  have hbt := CouplingTrajectoryRobustness.coupling_tendsto_atTop a β b hb ha hβ
  apply squeeze_zero_norm' _ (rescaled_physicalEnvelope_tendsto a β b r₀ f ha hβ hmargin)
  filter_upwards [hbt.eventually_ge_atTop ((3 / 4) / r₀)] with i hi
  have hs : 0 ≤ (a i^4)⁻¹ := by positivity
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (physical_hybrid_error_bound (period i) (S i) (hS i) (a i) plane (β i) r₀ r₁
      hr₀ hcut ((div_le_iff₀ hr₀).mp hi) f (exterior i)) hs

omit n [NeZero n] [Fact (1 < n)] in
/-- Mean-square convergence uses the actual correlated retained law at each
cutoff, with the correct a^-8 rescaling for the square of an a^-4 source. -/
theorem rescaled_physical_error_l2_tendsto {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (S : ∀ i, Finset (Edge (Vertex (period i))))
    (hS : ∀ i, Independent (period i) ((S i).image (edgeCoord (period i))))
    (a β : ι → ℝ) (b r₀ r₁ : ℝ) (plane : Plane) (f : TestFunction)
    (ha : Tendsto a l (𝓝[>] 0))
    (hβ : Tendsto (fun i => β i / Real.log (a i)⁻¹) l (𝓝 b))
    (hr₀ : 0 < r₀) (hcut : r₀ < r₁) (hmargin : 1 < b * r₀) :
    Tendsto (fun i => ((a i^4)⁻¹)^2 *
      ∫ z, (response (period i) (S i) (β i)
        (WilsonPhysicalCellWeights.weight (period i) (a i) plane f) z -
       hybridSource (period i) (S i) (β i) r₀ r₁
        (WilsonPhysicalCellWeights.weight (period i) (a i) plane f) z)^2
          ∂retainedLaw (period i) (S i) (β i)) l (𝓝 0) := by
  have hb : 0 < b := by
    by_contra hn
    have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hr₀.le
    linarith
  have hbt := CouplingTrajectoryRobustness.coupling_tendsto_atTop a β b hb ha hβ
  have hlimit := (rescaled_physicalEnvelope_tendsto a β b r₀ f ha hβ hmargin).pow 2
  simp only [zero_pow (by decide : 2 ≠ 0)] at hlimit
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hlimit
  filter_upwards [hbt.eventually_ge_atTop ((3 / 4) / r₀), hbt.eventually_gt_atTop 0]
    with i hi hpos
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left
    (physical_retained_error_l2_bound (period i) (S i) (hS i) (a i) plane (β i) r₀ r₁
      hpos hr₀ hcut ((div_le_iff₀ hr₀).mp hi) f) (sq_nonneg _)

end
end UnifiedTheory.Clay.YangMills.SU2WilsonPhysicalBlock
