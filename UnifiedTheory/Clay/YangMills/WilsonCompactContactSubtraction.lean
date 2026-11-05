/- Actual compact-test contact subtraction for one independent Wilson block.
The hard diagonal cutoff is explicit and the Taylor coefficients may depend on
position and cutoff. This does not replace the full interacting covariance. -/
import UnifiedTheory.Clay.YangMills.WilsonNoiseTubeMass
import UnifiedTheory.Clay.YangMills.SchwartzDiagonalTaylor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCompactContactSubtraction
noncomputable section
open MeasureTheory Filter RegulatedGauge LocalFields PeriodicLattice4
open WilsonIndependentBlocks WilsonInfluenceGeometry
open WilsonNoiseTubeMass SchwartzDiagonalTaylor
open scoped Topology

/-- Every finite directional Taylor jet is continuous in both its arguments. -/
theorem jet_continuous (f : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ) :
    Continuous (fun z : (Spacetime × Spacetime) × (Spacetime × Spacetime) =>
      jet f m z.1 z.2) := by
  unfold jet
  apply continuous_finset_sum
  intro j _
  apply Continuous.const_smul
  exact ((f.smooth j).continuous_iteratedFDeriv').comp continuous_fst |>.eval
    (continuous_pi (fun _ => continuous_snd))

/-- The degree-m relative-coordinate jet based at the physical diagonal. -/
def diagonalJet (f : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ)
    (z : Spacetime × Spacetime) : ℂ :=
  jet f m (z.1, z.1) (0, z.2 - z.1)

theorem diagonalJet_continuous (f : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ) :
    Continuous (diagonalJet f m) :=
  (jet_continuous f m).comp ((continuous_fst.prodMk continuous_fst).prodMk
    (continuous_const.prodMk (continuous_snd.sub continuous_fst)))

theorem diagonal_add (z : Spacetime × Spacetime) :
    (z.1, z.1) + (0, z.2 - z.1) = z := by
  ext <;> simp

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- Pairing with the literal sampled and rescaled removed covariance. -/
def pairing (β a : ℝ) (S : Finset (Edge (Vertex n))) (plane plane' : Plane)
    (f : SchwartzMap (Spacetime × Spacetime) ℂ) : ℂ :=
  ∫ z, (WilsonNoisePhysicalSupport.kernel n β a S plane plane' z.1 z.2 : ℂ) * f z

/-- An actual variable-coefficient order-four contact functional with a stated local cutoff. -/
def contact4 (β a R : ℝ) (S : Finset (Edge (Vertex n))) (plane plane' : Plane)
    (f : SchwartzMap (Spacetime × Spacetime) ℂ) : ℂ :=
  ∫ z, (truncated n β a R S plane plane' z : ℂ) * diagonalJet f 4 z

/-- The counterterm is supported on the physical diagonal, despite its varying coefficients. -/
theorem contact4_eq_zero_of_diagonal_disjoint (β a R : ℝ)
    (S : Finset (Edge (Vertex n))) (plane plane' : Plane)
    (f : SchwartzMap (Spacetime × Spacetime) ℂ)
    (hf : ∀ x : Spacetime, (x, x) ∉ tsupport f) :
    contact4 n β a R S plane plane' f = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with z
  simp only [Pi.zero_apply, diagonalJet,
    jet_eq_zero_of_not_mem_tsupport f 4 (z.1, z.1) (0, z.2 - z.1) (hf z.1), mul_zero]

/-- Actual coefficient amplitude and tube volume imply a degree-four O(a) remainder. -/
theorem truncated_subtraction_bound (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (f : SchwartzMap (Spacetime × Spacetime) ℂ) (ha : 0 < a) :
    ‖(∫ z, (truncated n β a R S plane plane' z : ℂ) * f z) -
      contact4 n β a R S plane plane' f‖ ≤
      (massConstant R * 4 ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 f * a := by
  have hw : Integrable (fun z => ‖(truncated n β a R S plane plane' z : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      truncated_abs_integrable n β a R S plane plane'
  have hF : Integrable (fun z => (truncated n β a R S plane plane' z : ℂ) *
      f ((z.1, z.1) + (0, z.2 - z.1))) := by
    simpa only [diagonal_add] using
      truncated_mul_continuous_integrable n β a R S plane plane' f f.continuous
  have hJ := truncated_mul_continuous_integrable n β a R S plane plane'
    (diagonalJet f 4) (diagonalJet_continuous f 4)
  have hd (z : Spacetime × Spacetime)
      (hz : (truncated n β a R S plane plane' z : ℂ) ≠ 0) :
      ‖((0, z.2 - z.1) : Spacetime × Spacetime)‖ ≤ 4 * a := by
    have hz' : truncated n β a R S plane plane' z ≠ 0 := by
      intro h
      exact hz (by simp only [h, Complex.ofReal_zero])
    simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using
      (truncated_support n β a R S plane plane' z hz').2
  have hm : (∫ z, ‖(truncated n β a R S plane plane' z : ℂ)‖) ≤
      massConstant R / a ^ 4 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      truncated_mass_le n β a R S plane plane' ha
  have h := fourth_order_subtraction_bound volume
    (fun z => (truncated n β a R S plane plane' z : ℂ))
    (fun z => (z.1, z.1)) (fun z => (0, z.2 - z.1)) hw f hF hJ a 4
    (massConstant R) ha (by norm_num) hd hm
  simpa only [diagonal_add, contact4, diagonalJet] using h

/-- On compact tests, the hard cutoff agrees with the actual sampled noise once wrapping
is excluded. The equality does not assume that the original kernel is globally local. -/
theorem pairing_eq_truncated (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (plane plane' : Plane)
    (f : SchwartzMap (Spacetime × Spacetime) ℂ)
    (hf : ∀ z, f z ≠ 0 → ‖z.1‖ ≤ R ∧ ‖z.2‖ ≤ R)
    (ha : 0 < a) (hperiod : 2 * R + 2 * a < (n : ℝ) * a) :
    pairing n β a S plane plane' f =
      ∫ z, (truncated n β a R S plane plane' z : ℂ) * f z := by
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : f z = 0
  · simp only [hz, mul_zero]
  · obtain ⟨hx, hy⟩ := hf z hz
    by_cases ht : z ∈ tube R a
    · rw [truncated, Set.indicator_of_mem ht]
    · have hd : 4 * a < ‖z.1 - z.2‖ := by
        have hd' : ¬ ‖z.2 - z.1‖ ≤ 4 * a := fun h => ht ⟨hx, h⟩
        simpa only [norm_sub_rev] using lt_of_not_ge hd'
      rw [truncated_zero_outside n β a R S plane plane' z ht,
        WilsonNoisePhysicalSupport.kernel_zero_far n β a R S hS ha hperiod
          plane plane' z.1 z.2 hx hy hd]

/-- A fully derived compact-test subtraction estimate for actual Wilson removed noise. -/
theorem compact_subtraction_bound (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (plane plane' : Plane)
    (f : SchwartzMap (Spacetime × Spacetime) ℂ)
    (hf : ∀ z, f z ≠ 0 → ‖z.1‖ ≤ R ∧ ‖z.2‖ ≤ R)
    (ha : 0 < a) (hperiod : 2 * R + 2 * a < (n : ℝ) * a) :
    ‖pairing n β a S plane plane' f - contact4 n β a R S plane plane' f‖ ≤
      (massConstant R * 4 ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 f * a := by
  rw [pairing_eq_truncated n β a R S hS plane plane' f hf ha hperiod]
  exact truncated_subtraction_bound n β a R S plane plane' f ha

omit [NeZero n] in
/-- On every fixed compact test, the actual locally subtracted one-block noise tends to zero
for arbitrary couplings and expanding physical volumes. No full-covariance limit is asserted. -/
theorem compact_subtraction_tendsto {ι : Type*} (l : Filter ι) (N : ι → ℕ)
    [∀ k, NeZero (N k)] (β a : ι → ℝ) (S : (k : ι) → Finset (Edge (Vertex (N k))))
    (hS : ∀ k, Independent (N k) ((S k).image (edgeCoord (N k))))
    (R : ℝ) (plane plane' : Plane) (f : SchwartzMap (Spacetime × Spacetime) ℂ)
    (hf : ∀ z, f z ≠ 0 → ‖z.1‖ ≤ R ∧ ‖z.2‖ ≤ R)
    (ha : ∀ᶠ k in l, 0 < a k) (ha0 : Tendsto a l (𝓝 0))
    (hlarge : Tendsto (fun k => (N k : ℝ) * a k) l atTop) :
    Tendsto (fun k => pairing (N k) (β k) (a k) (S k) plane plane' f -
      contact4 (N k) (β k) (a k) R (S k) plane plane' f) l (𝓝 0) := by
  have ha1 := ha0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hb : ∀ᶠ k in l, ‖pairing (N k) (β k) (a k) (S k) plane plane' f -
      contact4 (N k) (β k) (a k) R (S k) plane plane' f‖ ≤
      (massConstant R * 4 ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 f * a k := by
    filter_upwards [ha, ha1, hlarge.eventually_gt_atTop (2 * R + 2)] with k hak ha1k hk
    exact compact_subtraction_bound (N k) (β k) (a k) R (S k) (hS k) plane plane' f hf
      hak (by linarith)
  apply squeeze_zero_norm' hb
  simpa only [mul_zero] using
    ha0.const_mul ((massConstant R * 4 ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 f)

end
end UnifiedTheory.Clay.YangMills.WilsonCompactContactSubtraction
