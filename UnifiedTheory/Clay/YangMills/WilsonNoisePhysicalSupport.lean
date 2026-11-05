/- The actual independent-block removed covariance has shrinking physical support
on compact tests. Periodic images are excluded by the proved no-wrap geometry.
This is not finite-range locality of the full interacting two-point function. -/
import UnifiedTheory.Clay.YangMills.WilsonBlockNoiseKernel
import UnifiedTheory.Clay.YangMills.WilsonPhysicalStencilLocality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonNoisePhysicalSupport
noncomputable section
open MeasureTheory Filter RegulatedGauge LocalFields PeriodicLattice4
open WilsonIndependentBlocks WilsonInfluenceGeometry SingleLinkWilsonOscillation
open PeriodicCellSampling
open scoped Topology

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- Actual a^-8-rescaled removed-noise coefficient at the two sampled physical points. -/
def kernel (β a : ℝ) (S : Finset (Edge (Vertex n))) (plane plane' : Plane)
    (x y : Spacetime) : ℝ :=
  (a ^ 8)⁻¹ * WilsonBlockNoiseKernel.coefficient n β S
    (sample n a plane x) (sample n a plane' y)

/-- The actual sampled coefficient is measurable on physical spacetime pairs. -/
theorem kernel_measurable (β a : ℝ) (S : Finset (Edge (Vertex n))) (plane plane' : Plane) :
    Measurable (fun z : Spacetime × Spacetime => kernel n β a S plane plane' z.1 z.2) := by
  have hgeneric (c : PlaquetteIndex n × PlaquetteIndex n → ℝ) :
      Measurable (fun z : Spacetime × Spacetime =>
        (a ^ 8)⁻¹ * c (sample n a plane z.1, sample n a plane' z.2)) := by
    have hc : Measurable c := measurable_of_countable c
    have hs : Measurable (fun z : Spacetime × Spacetime =>
        (sample n a plane z.1, sample n a plane' z.2)) :=
      ((sample_measurable n a plane).comp measurable_fst).prodMk
        ((sample_measurable n a plane').comp measurable_snd)
    exact measurable_const.mul (hc.comp hs)
  exact hgeneric (fun pq => WilsonBlockNoiseKernel.coefficient n β S pq.1 pq.2)

/-- A genuine coefficient-amplitude bound, with no coupling restriction. -/
theorem kernel_abs_le (β a : ℝ) (S : Finset (Edge (Vertex n))) (plane plane' : Plane)
    (x y : Spacetime) : |kernel n β a S plane plane' x y| ≤ 16 / a ^ 8 := by
  unfold kernel
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (a ^ 8)⁻¹)]
  calc
    _ ≤ (a ^ 8)⁻¹ * 16 := mul_le_mul_of_nonneg_left
      (WilsonBlockNoiseKernel.coefficient_abs_le n β S _ _) (by positivity)
    _ = _ := by ring

/-- On a fixed ball the actual removed kernel is zero beyond four lattice spacings. -/
theorem kernel_zero_far (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (ha : 0 < a)
    (hperiod : 2 * R + 2 * a < (n : ℝ) * a) (plane plane' : Plane)
    (x y : Spacetime) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hfar : 4 * a < ‖x - y‖) :
    kernel n β a S plane plane' x y = 0 := by
  have hq : sample n a plane' y ∉ WilsonBlockNoiseKernel.stencil n (sample n a plane x) := by
    intro hq
    change sample n a plane' y ∈ (incidentLinks n (sample n a plane x)).biUnion
      (fun e => affected n e.1 e.2) at hq
    obtain ⟨e, he, hqe⟩ := Finset.mem_biUnion.mp hq
    have hpe := (affected_iff_incident n (sample n a plane x) e).mpr
      ((mem_incidentLinks n (sample n a plane x) e).mp he)
    have hd := WilsonPhysicalStencilLocality.shared_sample_distance n a R ha hperiod
      plane plane' x y hx hy e.1 e.2 hpe hqe
    exact (not_lt_of_ge hd) hfar
  rw [kernel, WilsonBlockNoiseKernel.coefficient_zero_outside_stencil n β S hS _ _ hq, mul_zero]

omit [NeZero n] in
/-- Physical locality follows on each compact set for arbitrary expanding-volume regulators. -/
theorem eventually_kernel_zero_far {ι : Type*} (l : Filter ι) (N : ι → ℕ)
    [∀ k, NeZero (N k)] (β a : ι → ℝ) (S : (k : ι) → Finset (Edge (Vertex (N k))))
    (hS : ∀ k, Independent (N k) ((S k).image (edgeCoord (N k))))
    (R : ℝ) (plane plane' : Plane) (ha : ∀ᶠ k in l, 0 < a k)
    (ha0 : Tendsto a l (𝓝 0))
    (hlarge : Tendsto (fun k => (N k : ℝ) * a k) l atTop) :
    ∀ᶠ k in l, ∀ x y : Spacetime, ‖x‖ ≤ R → ‖y‖ ≤ R → 4 * a k < ‖x - y‖ →
      kernel (N k) (β k) (a k) (S k) plane plane' x y = 0 := by
  have ha1 := ha0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [ha, ha1, hlarge.eventually_gt_atTop (2 * R + 2)] with k hak ha1k hk
  intro x y hx hy hfar
  exact kernel_zero_far (N k) (β k) (a k) R (S k) (hS k) hak (by linarith)
    plane plane' x y hx hy hfar

omit [NeZero n] in
/-- The rescaled removed-noise kernel vanishes exactly on every fixed compact
separated test once the cutoff is small. No amplitude limit is needed. -/
theorem separated_integral_eventually_zero {ι : Type*} (l : Filter ι) (N : ι → ℕ)
    [∀ k, NeZero (N k)] (β a : ι → ℝ) (S : (k : ι) → Finset (Edge (Vertex (N k))))
    (hS : ∀ k, Independent (N k) ((S k).image (edgeCoord (N k))))
    (R δ : ℝ) (hδ : 0 < δ) (plane plane' : Plane)
    (F : Spacetime × Spacetime → ℂ)
    (hF : ∀ z, F z ≠ 0 → ‖z.1‖ ≤ R ∧ ‖z.2‖ ≤ R ∧ δ ≤ ‖z.1 - z.2‖)
    (ha : ∀ᶠ k in l, 0 < a k) (ha0 : Tendsto a l (𝓝 0))
    (hlarge : Tendsto (fun k => (N k : ℝ) * a k) l atTop) :
    ∀ᶠ k in l, (∫ z : Spacetime × Spacetime,
      (kernel (N k) (β k) (a k) (S k) plane plane' z.1 z.2 : ℂ) * F z) = 0 := by
  have haδ := (ha0.const_mul 4).eventually (gt_mem_nhds (by simpa using hδ))
  filter_upwards [eventually_kernel_zero_far l N β a S hS R plane plane' ha ha0 hlarge,
    haδ] with k hk hak
  apply integral_eq_zero_of_ae
  filter_upwards with z
  simp only [Pi.zero_apply]
  by_cases hz : F z = 0
  · simp only [hz, mul_zero]
  · obtain ⟨hx, hy, hxy⟩ := hF z hz
    rw [hk z.1 z.2 hx hy (hak.trans_le hxy), Complex.ofReal_zero, zero_mul]

end
end UnifiedTheory.Clay.YangMills.WilsonNoisePhysicalSupport
