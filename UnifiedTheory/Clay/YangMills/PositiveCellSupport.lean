/- Actual positive-time slab support implies closed-half cell support.
The strict upper bound prevents wrapping around the finite periodic lattice. -/
import UnifiedTheory.Clay.YangMills.ClosedHalfSmearing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PositiveCellSupport
noncomputable section
open PeriodicLattice4 PeriodicCellSampling PeriodicHalfGeometry PeriodicHalfAction
open LocalFields ContinuumControl

variable (n : ℕ) [NeZero n]

theorem sample_time_val_lt (a : ℝ) (ha : 0 < a) (x : Spacetime)
    (hzero : 0 ≤ x 0) (hupper : x 0 < (n : ℝ) * a) :
    (vertexSample (2*n) a x 0).val < n := by
  have hn := NeZero.pos n
  have hnonneg : 0 ≤ Int.floor (x 0 / a) := Int.floor_nonneg.mpr (div_nonneg hzero ha.le)
  have hfloor : Int.floor (x 0 / a) < (n : ℤ) := by
    apply Int.floor_lt.mpr
    exact_mod_cast (div_lt_iff₀ ha).mpr hupper
  have hnat : (Int.floor (x 0 / a)).toNat < n := by omega
  change ((Int.floor (x 0 / a) : ZMod (2*n))).val < n
  rw [← ZMod.natCast_toNat (2*n) hnonneg,
    ZMod.val_natCast_of_lt (by omega : (Int.floor (x 0 / a)).toNat < 2*n)]
  exact hnat

theorem sample_closed (a : ℝ) (ha : 0 < a) (plane : Plane) (x : Spacetime)
    (hzero : 0 ≤ x 0) (hupper : x 0 < (n : ℝ) * a) :
    BoundaryP n (sample (2*n) a plane x) ∨ PositiveP n (sample (2*n) a plane x) := by
  have hv := sample_time_val_lt n a ha x hzero hupper
  by_cases hμ : plane.val.1 = 0
  · right
    simpa only [PositiveP, Positive, sample, hμ, if_true] using hv
  · by_cases hz : (vertexSample (2*n) a x 0).val = 0
    · left
      exact ⟨hμ, Or.inl hz⟩
    · right
      change if plane.val.1 = 0 then _ else _
      rw [if_neg hμ]
      exact ⟨Nat.pos_of_ne_zero hz, hv⟩

/-- A concrete spacetime support condition, rather than a hypothesis about
unknown cell coefficients. It allows general multi-point Schwartz tests. -/
def SlabSupported (a : ℝ) (m : ℕ) (f : CorrelationTest m) : Prop :=
  ∀ x, f x ≠ 0 → ∀ j, 0 ≤ point m j x 0 ∧ point m j x 0 < (n : ℝ) * a

theorem supported_of_slab (a : ℝ) (ha : 0 < a) (plane : Plane)
    (m : ℕ) (f : CorrelationTest m) (hf : SlabSupported n a m f) :
    ClosedHalfSmearing.Supported n a plane m f := by
  intro x hx j
  exact sample_closed n a ha plane (point m j x) (hf x hx j).1 (hf x hx j).2

/-- Every fixed nonnegative-time slab eventually fits in an expanding physical
half-period. The continuum support condition is independent of the regulator. -/
theorem eventually_supported (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k)
    (hlarge : Filter.Tendsto (fun k => (period k : ℝ) * a k) Filter.atTop Filter.atTop)
    (plane : Plane) (m : ℕ) (f : CorrelationTest m) (R : ℝ)
    (hf : ∀ x, f x ≠ 0 → ∀ j, 0 ≤ point m j x 0 ∧ point m j x 0 ≤ R) :
    ∀ᶠ k in Filter.atTop, ClosedHalfSmearing.Supported (period k) (a k) plane m f := by
  filter_upwards [hlarge.eventually (Filter.eventually_gt_atTop R)] with k hk
  apply supported_of_slab (period k) (a k) (ha k) plane m f
  intro x hx j
  exact ⟨(hf x hx j).1, (hf x hx j).2.trans_lt hk⟩

end
end UnifiedTheory.Clay.YangMills.PositiveCellSupport
