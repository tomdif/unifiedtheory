/- Unboundedly many actual ultraviolet Wilson eliminations with summable contact errors.
Every stage law, response and finite-range coefficient is derived from the original
Wilson measure. The largest removed physical neighborhood still shrinks to zero;
the final retained interacting covariance is not bounded by this theorem. -/
import UnifiedTheory.Clay.YangMills.WilsonIteratedNoiseLocality
import UnifiedTheory.Clay.YangMills.GrowingStageContactPath
import UnifiedTheory.Clay.YangMills.WilsonIteratedSourcePairing
import UnifiedTheory.Clay.YangMills.WilsonSchwartzCovariance
import UnifiedTheory.Clay.YangMills.WilsonGrowingBlockWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGrowingContact
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 LocalFields WilsonSingleLinkStaples
open WilsonFactorTower WilsonIteratedNoiseKernel GrowingStageContactPath
open scoped Topology

local instance pairVolumeHaar :
    (volume : Measure (Spacetime × Spacetime)).IsAddHaarMeasure := by
  change (volume.prod volume).IsAddHaarMeasure
  infer_instance

instance pathPeriodNeZero (k : ℕ) : NeZero (period k) :=
  ⟨by have := period_gt_one k; omega⟩

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

def pairing (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (j : ℕ)
    (plane plane' : Plane) (F : SchwartzMap (Spacetime × Spacetime) ℂ) : ℂ :=
  ∫ z : Spacetime × Spacetime, (kernel n β a T j plane plane' z.1 z.2 : ℂ) * F z

/-- Finite sum of the actual stage-specific degree-four diagonal contacts. -/
def contactSum (β a R : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (N : ℕ)
    (plane plane' : Plane) (F : SchwartzMap (Spacetime × Spacetime) ℂ) : ℂ :=
  ∑ j ∈ Finset.range N, FiniteRangeSchwartzContact.contact
    (fun z => kernel n β a T j plane plane' z.1 z.2) a R (3 * (2 : ℝ) ^ j) F

def remainder (β a R : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (N : ℕ)
    (plane plane' : Plane) (F : SchwartzMap (Spacetime × Spacetime) ℂ) : ℂ :=
  (∑ j ∈ Finset.range N, pairing n β a T j plane plane' F) -
    contactSum n β a R T N plane plane' F

theorem remainder_eq (β a R : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (N : ℕ)
    (plane plane' : Plane) (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    remainder n β a R T N plane plane' F = GrowingStageContact.remainder N
      (fun j z => kernel n β a T j plane plane' z.1 z.2) a R (fun j => 3 * (2 : ℝ) ^ j) F := by
  simp only [remainder, pairing, contactSum, GrowingStageContact.remainder, Finset.sum_sub_distrib]

/-- The finite cumulative contact is an actual continuous linear Schwartz functional. -/
def contactSumCLM (β a R : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (N : ℕ)
    (plane plane' : Plane) (ha : 0 < a) : SchwartzMap (Spacetime × Spacetime) ℂ →L[ℂ] ℂ :=
  ∑ j ∈ Finset.range N, FiniteRangeSchwartzContact.contactCLM
    (fun z => kernel n β a T j plane plane' z.1 z.2)
    (kernel_measurable n β a T j plane plane') a R (3 * (2 : ℝ) ^ j) 4 ha
    (by positivity) (by norm_num) (fun z => kernel_abs_le n β a T j plane plane' z.1 z.2)

theorem contactSumCLM_apply (β a R : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (N : ℕ)
    (plane plane' : Plane) (ha : 0 < a) (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    contactSumCLM n β a R T N plane plane' ha F = contactSum n β a R T N plane plane' F := by
  simp only [contactSumCLM, ContinuousLinearMap.sum_apply,
    FiniteRangeSchwartzContact.contactCLM_apply, contactSum]

theorem contactSum_diagonal_support (β a R : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (N : ℕ)
    (plane plane' : Plane) (F : SchwartzMap (Spacetime × Spacetime) ℂ)
    (hF : ∀ x : Spacetime, (x, x) ∉ tsupport F) : contactSum n β a R T N plane plane' F = 0 := by
  exact Finset.sum_eq_zero (fun j _ =>
    FiniteRangeSchwartzContact.contact_diagonal_support _ a R (3 * (2 : ℝ) ^ j) F hF)

omit [NeZero n] in
/-- The actual stage range and no-wrap conditions hold simultaneously for every j<k. -/
theorem path_kernel_zero (β : ℝ) (k : ℕ)
    (T : ℕ → Finset (Edge (Vertex (period k)))) (hT : Admissible (period k) T)
    (j : ℕ) (hj : j < k) (plane plane' : Plane) (z : Spacetime × Spacetime)
    (hx : ‖z.1‖ ≤ radius k) (hy : ‖z.2‖ ≤ radius k)
    (hfar : (4 * (3 * radius j)) * spacing k < ‖z.1 - z.2‖) :
    kernel (period k) β (spacing k) T j plane plane' z.1 z.2 = 0 := by
  have hp : 2 * radius k + (2 * (2 : ℝ) ^ j + 1) * spacing k <
      (period k : ℝ) * spacing k := by
    apply lt_of_le_of_lt _ (scaled_no_wrap k j hj.le)
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (spacing_pos k).le
    dsimp only [radius]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j]
  apply WilsonIteratedNoiseLocality.kernel_zero_far (period k) β (spacing k) (radius k)
    T hT j (spacing_pos k) hp plane plane' z.1 z.2 hx hy
  have hr : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hc : (4 * (2 : ℝ) ^ j + 2) ≤ 4 * (3 * (2 : ℝ) ^ j) := by nlinarith
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc (spacing_pos k).le) hfar

omit [NeZero n] in
/-- A genuinely growing number of actual removed Wilson distributions has vanishing
cumulative remainder after the constructed contacts, for every Schwartz test. -/
theorem growing_remainder_tendsto (β : ℕ → ℝ)
    (T : (k : ℕ) → ℕ → Finset (Edge (Vertex (period k))))
    (hT : ∀ k, Admissible (period k) (T k))
    (plane plane' : Plane) (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    Tendsto (fun k => remainder (period k) (β k) (spacing k) (radius k)
      (T k) k plane plane' F) atTop (𝓝 0) := by
  simp only [remainder_eq]
  exact scaled_accumulated_tendsto
    (fun k j z => kernel (period k) (β k) (spacing k) (T k) j plane plane' z.1 z.2)
    (fun k j _ => kernel_measurable _ _ _ _ _ _ _)
    (fun k j _ z => kernel_abs_le _ _ _ _ _ _ _ z.1 z.2)
    (fun k j hj z hx hy hfar => path_kernel_zero (β k) k (T k) (hT k)
      j hj plane plane' z hx hy hfar) F

/-- Physical covariance of the genuine Nth retained responses with the original cell smears. -/
def retainedCovariance (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (N : ℕ)
    (plane plane' : Plane) (f g : TestFunction) : ℝ :=
  (a ^ 8)⁻¹ * GibbsCrossCovariance.covariance (law n β T N)
    (response n β T (WilsonPhysicalCellWeights.weight n a plane f) N)
    (response n β T (WilsonPhysicalCellWeights.weight n a plane' g) N)

/-- Exact physical source dictionary for the cumulative removed kernels. -/
theorem physical_pairing_sum (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (N : ℕ)
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    (WilsonSchwartzCovariance.fullCovariance n β a plane plane' f g : ℂ) -
      (∑ j ∈ Finset.range N, pairing n β a T j plane plane' (SchwartzProductTensor.tensor f g)) =
      (retainedCovariance n β a T N plane plane' f g : ℂ) := by
  exact WilsonIteratedSourcePairing.physical_covariance_sub_sum n β a T N plane plane' f g hf hg

omit [NeZero n] in
/-- Physical covariance repair through k actual steps at cutoff k. The retained
covariance remains explicit and is not assumed bounded or nonzero. -/
theorem growing_repaired_covariance_tendsto (β : ℕ → ℝ)
    (T : (k : ℕ) → ℕ → Finset (Edge (Vertex (period k))))
    (hT : ∀ k, Admissible (period k) (T k))
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    Tendsto (fun k =>
      (WilsonSchwartzCovariance.fullCovariance (period k) (β k) (spacing k)
        plane plane' f g : ℂ) -
      contactSum (period k) (β k) (spacing k) (radius k) (T k) k plane plane'
        (SchwartzProductTensor.tensor f g) -
      (retainedCovariance (period k) (β k) (spacing k) (T k) k plane plane' f g : ℂ))
      atTop (𝓝 0) := by
  have h := growing_remainder_tendsto β T hT plane plane' (SchwartzProductTensor.tensor f g)
  have he (k : ℕ) := physical_pairing_sum (period k) (β k) (spacing k) (T k) k
    plane plane' f g hf hg
  convert h using 1
  funext k
  unfold remainder
  linear_combination he k

omit [NeZero n] in
/-- Separated full and k-times-retained physical covariances agree asymptotically. -/
theorem growing_separated_covariance_tendsto (β : ℕ → ℝ)
    (T : (k : ℕ) → ℕ → Finset (Edge (Vertex (period k))))
    (hT : ∀ k, Admissible (period k) (T k))
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0)
    (hdiag : ∀ x : Spacetime, (x, x) ∉ tsupport (SchwartzProductTensor.tensor f g)) :
    Tendsto (fun k =>
      (WilsonSchwartzCovariance.fullCovariance (period k) (β k) (spacing k)
        plane plane' f g : ℂ) -
      (retainedCovariance (period k) (β k) (spacing k) (T k) k plane plane' f g : ℂ))
      atTop (𝓝 0) := by
  have h := growing_repaired_covariance_tendsto β T hT plane plane' f g hf hg
  simpa only [contactSum_diagonal_support _ _ _ _ _ _ plane plane'
    (SchwartzProductTensor.tensor f g) hdiag, sub_zero] using h

omit [NeZero n] in
/-- The explicit sparse schedule removes k distinct actual links. Its first two
links share an original plaquette, so their union is not initially independent. -/
theorem explicit_repaired_covariance_tendsto (β : ℕ → ℝ)
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    Tendsto (fun k =>
      (WilsonSchwartzCovariance.fullCovariance (period k) (β k) (spacing k)
        plane plane' f g : ℂ) -
      contactSum (period k) (β k) (spacing k) (radius k)
        (WilsonGrowingBlockWitness.block (period k)) k plane plane'
        (SchwartzProductTensor.tensor f g) -
      (retainedCovariance (period k) (β k) (spacing k)
        (WilsonGrowingBlockWitness.block (period k)) k plane plane' f g : ℂ))
      atTop (𝓝 0) :=
  growing_repaired_covariance_tendsto β (fun k => WilsonGrowingBlockWitness.block (period k))
    WilsonGrowingBlockWitness.path_admissible plane plane' f g hf hg

end
end UnifiedTheory.Clay.YangMills.WilsonGrowingContact
