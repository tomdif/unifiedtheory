/- Keep all nonlocal coarse removals after ultraviolet contact subtraction.
The full coarse package equals the earlier retained covariance at every finite
cutoff. Its convergence or strict positivity is not asserted. -/
import UnifiedTheory.Clay.YangMills.WilsonGrowingContact

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCoarseCovariance
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 LocalFields WilsonSingleLinkStaples
open WilsonIteratedNoiseKernel WilsonGrowingContact GrowingStageContactPath
open scoped Topology

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- Exact covariance accounting between two arbitrary actual tower depths. -/
theorem covariance_interval (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (J L : ℕ) (f g : PlaquetteIndex n → ℝ) :
    GibbsCrossCovariance.covariance (law n β T J)
      (response n β T f J) (response n β T g J) =
      (∑ j ∈ Finset.range L, bilinear n β T (J + j) f g) +
      GibbsCrossCovariance.covariance (law n β T (J + L))
        (response n β T f (J + L)) (response n β T g (J + L)) := by
  have hJ := WilsonIteratedSourcePairing.covariance_telescope n β T J f g
  have hJL := WilsonIteratedSourcePairing.covariance_telescope n β T (J + L) f g
  rw [Finset.sum_range_add] at hJL
  linarith

/-- Coarse kernels are retained in full, together with the final actual covariance. -/
def coarseCovariance (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (J L : ℕ)
    (plane plane' : Plane) (f g : TestFunction) : ℝ :=
  (a ^ 8)⁻¹ * (∑ j ∈ Finset.range L, bilinear n β T (J + j)
    (WilsonPhysicalCellWeights.weight n a plane f)
    (WilsonPhysicalCellWeights.weight n a plane' g)) +
    retainedCovariance n β a T (J + L) plane plane' f g

/-- The nonlocal package is invariant under the number of further genuine eliminations. -/
theorem coarseCovariance_eq_retained (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (J L : ℕ) (plane plane' : Plane) (f g : TestFunction) :
    coarseCovariance n β a T J L plane plane' f g =
      retainedCovariance n β a T J plane plane' f g := by
  unfold coarseCovariance retainedCovariance
  rw [covariance_interval n β T J L, mul_add]

/-- Each coarse contribution is the full sampled physical kernel, without a Taylor replacement. -/
theorem coarseCovariance_kernel_pairing (β a : ℝ)
    (T : ℕ → Finset (Edge (Vertex n))) (J L : ℕ)
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    (coarseCovariance n β a T J L plane plane' f g : ℂ) =
      (∑ j ∈ Finset.range L, pairing n β a T (J + j) plane plane'
        (SchwartzProductTensor.tensor f g)) +
      (retainedCovariance n β a T (J + L) plane plane' f g : ℂ) := by
  unfold coarseCovariance pairing
  simp_rw [SchwartzProductTensor.tensor_apply,
    WilsonIteratedSourcePairing.tensor_pairing n β a T _ plane plane' f g hf hg]
  rw [Finset.mul_sum]
  push_cast
  rfl

/-- Every genuine retained diagonal physical covariance is nonnegative. -/
theorem retained_self_nonneg (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (J : ℕ) (plane : Plane) (f : TestFunction) :
    0 ≤ retainedCovariance n β a T J plane plane f f := by
  unfold retainedCovariance
  apply mul_nonneg (inv_nonneg.mpr (by positivity))
  exact GibbsCoordinateTower.covarianceAt_self_nonneg (compactHaar Q) T
    (WilsonFactorTower.initialAction n β)
    (sourceMap n (WilsonPhysicalCellWeights.weight n a plane f)) J

/-- Coarse grouping preserves diagonal positivity; it supplies no strictly positive lower bound. -/
theorem coarse_self_nonneg (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (J L : ℕ) (plane : Plane) (f : TestFunction) :
    0 ≤ coarseCovariance n β a T J L plane plane f f := by
  rw [coarseCovariance_eq_retained]
  exact retained_self_nonneg n β a T J plane f

/-- Discarding the coarse noise loses a nonnegative part of the retained diagonal covariance. -/
theorem final_le_coarse (β a : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (J L : ℕ) (plane : Plane) (f : TestFunction) :
    retainedCovariance n β a T (J + L) plane plane f f ≤
      coarseCovariance n β a T J L plane plane f f := by
  unfold coarseCovariance
  have h := Finset.sum_nonneg (s := Finset.range L) (fun j _ =>
    WilsonIteratedSourcePairing.positive_semidefinite n β T (J + j)
      (WilsonPhysicalCellWeights.weight n a plane f))
  have ha : 0 ≤ (a ^ 8)⁻¹ := inv_nonneg.mpr (by positivity)
  linarith [mul_nonneg ha h]

/-- Exact contact repair, with an arbitrary number of larger-scale kernels kept intact. -/
theorem repair_eq_remainder (β a R : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (J L : ℕ) (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    (WilsonSchwartzCovariance.fullCovariance n β a plane plane' f g : ℂ) -
      contactSum n β a R T J plane plane' (SchwartzProductTensor.tensor f g) -
      (coarseCovariance n β a T J L plane plane' f g : ℂ) =
      remainder n β a R T J plane plane' (SchwartzProductTensor.tensor f g) := by
  rw [coarseCovariance_eq_retained]
  have h := physical_pairing_sum n β a T J plane plane' f g hf hg
  unfold remainder
  linear_combination h

omit [NeZero n] in
/-- Any finite number of additional coarse steps is compatible with the proved UV error limit.
The entire nonlocal package remains explicit; no limit of that package is assumed here. -/
theorem growing_coarse_repair_tendsto (β : ℕ → ℝ)
    (T : (k : ℕ) → ℕ → Finset (Edge (Vertex (period k))))
    (hT : ∀ k, WilsonFactorTower.Admissible (period k) (T k)) (L : ℕ → ℕ)
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    Tendsto (fun k =>
      (WilsonSchwartzCovariance.fullCovariance (period k) (β k) (spacing k)
        plane plane' f g : ℂ) -
      contactSum (period k) (β k) (spacing k) (radius k) (T k) k plane plane'
        (SchwartzProductTensor.tensor f g) -
      (coarseCovariance (period k) (β k) (spacing k) (T k) k (L k) plane plane' f g : ℂ))
      atTop (𝓝 0) := by
  simp_rw [repair_eq_remainder _ _ _ _ _ _ _ _ _ _ _ hf hg]
  exact growing_remainder_tendsto β T hT plane plane' (SchwartzProductTensor.tensor f g)

omit [NeZero n] in
/-- Real contact-repaired covariance has the same vanishing error against the nonlocal package. -/
theorem growing_real_coarse_repair_tendsto (β : ℕ → ℝ)
    (T : (k : ℕ) → ℕ → Finset (Edge (Vertex (period k))))
    (hT : ∀ k, WilsonFactorTower.Admissible (period k) (T k)) (L : ℕ → ℕ)
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    Tendsto (fun k =>
      WilsonSchwartzCovariance.fullCovariance (period k) (β k) (spacing k) plane plane' f g -
      (contactSum (period k) (β k) (spacing k) (radius k) (T k) k plane plane'
        (SchwartzProductTensor.tensor f g)).re -
      coarseCovariance (period k) (β k) (spacing k) (T k) k (L k) plane plane' f g)
      atTop (𝓝 0) := by
  have h := (Complex.continuous_re.tendsto 0).comp
    (growing_coarse_repair_tendsto β T hT L plane plane' f g hf hg)
  simpa only [Function.comp_def, Complex.sub_re, Complex.ofReal_re, Complex.zero_re] using h

/-- Real part of the actual ultraviolet contact subtraction. -/
def repairedCovariance (β a R : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (J : ℕ)
    (plane plane' : Plane) (f g : TestFunction) : ℝ :=
  WilsonSchwartzCovariance.fullCovariance n β a plane plane' f g -
    (contactSum n β a R T J plane plane' (SchwartzProductTensor.tensor f g)).re

omit [NeZero n] in
/-- Convergence is equivalent to convergence of the entire nonlocal package.
This is a reduction of the missing continuum estimate, not a convergence proof. -/
theorem repaired_limit_iff_coarse_limit (β : ℕ → ℝ)
    (T : (k : ℕ) → ℕ → Finset (Edge (Vertex (period k))))
    (hT : ∀ k, WilsonFactorTower.Admissible (period k) (T k)) (L : ℕ → ℕ)
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) (c : ℝ) :
    Tendsto (fun k => repairedCovariance (period k) (β k) (spacing k) (radius k)
      (T k) k plane plane' f g) atTop (𝓝 c) ↔
    Tendsto (fun k => coarseCovariance (period k) (β k) (spacing k)
      (T k) k (L k) plane plane' f g) atTop (𝓝 c) := by
  have he := growing_real_coarse_repair_tendsto β T hT L plane plane' f g hf hg
  change Tendsto (fun k => repairedCovariance (period k) (β k) (spacing k) (radius k)
    (T k) k plane plane' f g - coarseCovariance (period k) (β k) (spacing k)
    (T k) k (L k) plane plane' f g) atTop (𝓝 0) at he
  constructor
  · intro h
    have hz := h.sub he
    simp only [sub_zero, sub_sub_cancel] at hz
    exact hz
  · intro h
    have hz := he.add h
    simp only [zero_add, sub_add_cancel] at hz
    exact hz

omit [NeZero n] in
/-- Any finite diagonal limit of the contact-repaired sequence is nonnegative.
Strict positivity, reflection positivity and existence of a limit remain separate questions. -/
theorem repaired_diagonal_limit_nonneg (β : ℕ → ℝ)
    (T : (k : ℕ) → ℕ → Finset (Edge (Vertex (period k))))
    (hT : ∀ k, WilsonFactorTower.Admissible (period k) (T k)) (L : ℕ → ℕ)
    (plane : Plane) (f : TestFunction) (hf : ∀ x, (f x).im = 0) (c : ℝ)
    (hc : Tendsto (fun k => repairedCovariance (period k) (β k) (spacing k) (radius k)
      (T k) k plane plane f f) atTop (𝓝 c)) : 0 ≤ c := by
  have h := (repaired_limit_iff_coarse_limit β T hT L plane plane f f hf hf c).mp hc
  exact ge_of_tendsto h (Filter.Eventually.of_forall (fun k =>
    coarse_self_nonneg (period k) (β k) (spacing k) (T k) k (L k) plane f))

end
end UnifiedTheory.Clay.YangMills.WilsonCoarseCovariance
