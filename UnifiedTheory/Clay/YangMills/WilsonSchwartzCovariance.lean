/- Full-Schwartz covariance transport for the actual one-block Wilson integration.
The explicit counterterm removes the local covariance with a vanishing remainder.
Separated signals pass to the retained covariance if such a signal is established;
no positive signal, uniform retained bound or physical coupling is assumed proved. -/
import UnifiedTheory.Clay.YangMills.WilsonSchwartzContactPath
import UnifiedTheory.Clay.YangMills.WilsonNoiseCellPairing
import UnifiedTheory.Clay.YangMills.WilsonContactDistribution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSchwartzCovariance
noncomputable section
open MeasureTheory Filter RegulatedGauge LocalFields PeriodicLattice4
open WilsonBlockNoiseKernel WilsonSingleLinkStaples WilsonIndependentBlocks
open WilsonCompactContactSubtraction WilsonSchwartzContactPath
open scoped Topology NNReal

local instance complexRealNormedSpace : NormedSpace ℝ ℂ :=
  InnerProductSpace.toNormedSpace

local instance pairVolumeHaar :
    (volume : Measure (Spacetime × Spacetime)).IsAddHaarMeasure := by
  change (volume.prod volume).IsAddHaarMeasure
  infer_instance

/-- The fixed weighted-integral continuity constant on the physical two-point space. -/
def tailControlConstant : ℝ :=
  2 ^ (volume : Measure (Spacetime × Spacetime)).integrablePower *
    ∫ z : Spacetime × Spacetime,
      (1 + ‖z‖) ^ (-((volume : Measure (Spacetime × Spacetime)).integrablePower : ℝ))

theorem tailControlConstant_nonneg : 0 ≤ tailControlConstant := by
  unfold tailControlConstant
  positivity

/-- One continuous seminorm controls the entire removed-covariance remainder sequence. -/
def remainderControl : Seminorm ℝ (SchwartzMap (Spacetime × Spacetime) ℂ) := by
  let p5 : Seminorm ℝ (SchwartzMap (Spacetime × Spacetime) ℂ) := SchwartzMap.seminorm ℝ 0 5
  let p0 : Seminorm ℝ (SchwartzMap (Spacetime × Spacetime) ℂ) := SchwartzMap.seminorm ℝ 0 0
  let pK : Seminorm ℝ (SchwartzMap (Spacetime × Spacetime) ℂ) :=
    SchwartzMap.seminorm ℝ (72 + (volume : Measure (Spacetime × Spacetime)).integrablePower) 0
  let C : NNReal := ⟨WilsonNoiseTubeMass.massConstant 1 * 4 ^ 5 / 24,
    by have := WilsonNoiseTubeMass.massConstant_nonneg 1; positivity⟩
  let D : NNReal := ⟨16 * tailControlConstant,
    by have := tailControlConstant_nonneg; positivity⟩
  let q5 : Seminorm ℝ (SchwartzMap (Spacetime × Spacetime) ℂ) := C • p5
  let q0 : Seminorm ℝ (SchwartzMap (Spacetime × Spacetime) ℂ) := D • (p0 + pK)
  exact q5 + q0

theorem remainderControl_apply (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    remainderControl F =
      (WilsonNoiseTubeMass.massConstant 1 * 4 ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 F +
        (16 * tailControlConstant) * (SchwartzMap.seminorm ℝ 0 0 F +
          SchwartzMap.seminorm ℝ
            (72 + (volume : Measure (Spacetime × Spacetime)).integrablePower) 0 F) := rfl

theorem remainderControl_continuous : Continuous remainderControl := by
  change Continuous (fun F : SchwartzMap (Spacetime × Spacetime) ℂ =>
    (WilsonNoiseTubeMass.massConstant 1 * 4 ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 F +
      (16 * tailControlConstant) * (SchwartzMap.seminorm ℝ 0 0 F +
        SchwartzMap.seminorm ℝ
          (72 + (volume : Measure (Spacetime × Spacetime)).integrablePower) 0 F))
  have hc (k j : ℕ) : Continuous (SchwartzMap.seminorm ℝ k j :
      SchwartzMap (Spacetime × Spacetime) ℂ → ℝ) :=
    (schwartz_withSeminorms ℝ (Spacetime × Spacetime) ℂ).continuous_seminorm (k, j)
  exact (continuous_const.mul (hc 0 5)).add
    (continuous_const.mul ((hc 0 0).add (hc _ 0)))

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- The actual full covariance of physical real cell smears with the a^-8 scaling. -/
def fullCovariance (β a : ℝ) (plane plane' : Plane) (f g : TestFunction) : ℝ :=
  (a ^ 8)⁻¹ * GibbsCrossCovariance.covariance (wilsonLaw n Q character β 2)
    (source n (WilsonPhysicalCellWeights.weight n a plane f))
    (source n (WilsonPhysicalCellWeights.weight n a plane' g))

/-- The same physical scaling of the true conditional sources under the true marginal. -/
def retainedCovariance (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (f g : TestFunction) : ℝ :=
  (a ^ 8)⁻¹ * GibbsCrossCovariance.covariance
    (WilsonCrossCovariance.retainedLaw n Q character β 2 S)
    (retained n β S (WilsonPhysicalCellWeights.weight n a plane f))
    (retained n β S (WilsonPhysicalCellWeights.weight n a plane' g))

/-- Exact identification before any limit, including all periodic cell aliases. -/
theorem pairing_tensor_eq (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    pairing n β a S plane plane' (SchwartzProductTensor.tensor f g) =
      (fullCovariance n β a plane plane' f g : ℂ) -
        (retainedCovariance n β a S plane plane' f g : ℂ) := by
  have h := WilsonNoiseCellPairing.tensor_covariance_pairing n β a S plane plane' f g hf hg
  simpa only [pairing, SchwartzProductTensor.tensor_apply, fullCovariance,
    retainedCovariance, mul_sub, Complex.ofReal_sub] using h

omit [NeZero n] in
/-- Disjoint physical supports give precisely the diagonal-disjoint tensor condition. -/
theorem tensor_diagonal_disjoint (f g : TestFunction)
    (hfg : Disjoint (tsupport f) (tsupport g)) (x : Spacetime) :
    (x, x) ∉ tsupport (SchwartzProductTensor.tensor f g) := by
  intro hx
  change (x, x) ∈ tsupport (fun z : Spacetime × Spacetime => f z.1 * g z.2) at hx
  have hf : x ∈ tsupport f :=
    tsupport_comp_subset_preimage f continuous_fst (tsupport_mul_subset_left hx)
  have hg : x ∈ tsupport g :=
    tsupport_comp_subset_preimage g continuous_snd (tsupport_mul_subset_right hx)
  exact Set.disjoint_left.mp hfg hf hg

omit [NeZero n] in
/-- A single cutoff-independent continuous seminorm gives the explicit R^-4 remainder rate. -/
theorem uniform_remainder_bound (β : ℕ → ℝ)
    (S : (k : ℕ) → Finset (Edge (Vertex (period k))))
    (hS : ∀ k, Independent (period k) ((S k).image (edgeCoord (period k))))
    (plane plane' : Plane) (F : SchwartzMap (Spacetime × Spacetime) ℂ)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖WilsonContactDistribution.remainderCLM (period k) (β k) (spacing k) (radius k)
      (S k) plane plane' (spacing_pos k) F‖ ≤ remainderControl F / radius k ^ 4 := by
  have h := error_bound β S hS plane plane' F k hk
  have hm := SchwartzWeightedTail.weightedMoment_le_seminorms volume 72 F
  have hM := SchwartzWeightedTail.weightedMoment_nonneg volume 72 F
  have hx : 1 ≤ radius k := by
    unfold radius
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have h48 : radius k ^ 4 ≤ radius k ^ 8 := pow_le_pow_right₀ hx (by norm_num)
  have hd : (16 * SchwartzWeightedTail.weightedMoment volume 72 F) / radius k ^ 8 ≤
      (16 * SchwartzWeightedTail.weightedMoment volume 72 F) / radius k ^ 4 :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos (radius_pos k) 4) h48
  have hmc : (16 * SchwartzWeightedTail.weightedMoment volume 72 F) / radius k ^ 4 ≤
      ((16 * tailControlConstant) * (SchwartzMap.seminorm ℝ 0 0 F +
        SchwartzMap.seminorm ℝ
          (72 + (volume : Measure (Spacetime × Spacetime)).integrablePower) 0 F)) /
          radius k ^ 4 := by
    apply div_le_div_of_nonneg_right _ (pow_nonneg (radius_pos k).le 4)
    have hh := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 16)
    convert hh using 1
    dsimp [tailControlConstant]
    ring
  change ‖pairing _ _ _ _ _ _ F - contact4 _ _ _ _ _ _ _ F‖ ≤ _
  apply h.trans
  rw [remainderControl_apply, add_div]
  exact add_le_add le_rfl (hd.trans hmc)

omit [NeZero n] in
/-- The constructed continuous linear Schwartz remainder converges testwise to zero. -/
theorem remainder_distribution_tendsto (β : ℕ → ℝ)
    (S : (k : ℕ) → Finset (Edge (Vertex (period k))))
    (hS : ∀ k, Independent (period k) ((S k).image (edgeCoord (period k))))
    (plane plane' : Plane) (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    Tendsto (fun k => WilsonContactDistribution.remainderCLM
      (period k) (β k) (spacing k) (radius k) (S k) plane plane' (spacing_pos k) F)
      atTop (𝓝 0) :=
  subtraction_tendsto β S hS plane plane' F

omit [NeZero n] in
/-- The actual rescaled full-minus-retained covariance is repaired on every real Schwartz tensor.
The physical smears need no compact support and the coupling sequence is arbitrary. -/
theorem repaired_covariance_tendsto (β : ℕ → ℝ)
    (S : (k : ℕ) → Finset (Edge (Vertex (period k))))
    (hS : ∀ k, Independent (period k) ((S k).image (edgeCoord (period k))))
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    Tendsto (fun k => (fullCovariance (period k) (β k) (spacing k) plane plane' f g : ℂ) -
      contact4 (period k) (β k) (spacing k) (radius k) (S k) plane plane'
        (SchwartzProductTensor.tensor f g) -
      (retainedCovariance (period k) (β k) (spacing k) (S k) plane plane' f g : ℂ))
      atTop (𝓝 0) := by
  have h := subtraction_tendsto β S hS plane plane' (SchwartzProductTensor.tensor f g)
  simp_rw [pairing_tensor_eq _ _ _ _ plane plane' f g hf hg] at h
  convert h using 1
  funext k
  ring

omit [NeZero n] in
/-- The removed noise vanishes on all diagonal-disjoint Schwartz tests along this path. -/
theorem separated_pairing_tendsto (β : ℕ → ℝ)
    (S : (k : ℕ) → Finset (Edge (Vertex (period k))))
    (hS : ∀ k, Independent (period k) ((S k).image (edgeCoord (period k))))
    (plane plane' : Plane) (F : SchwartzMap (Spacetime × Spacetime) ℂ)
    (hF : ∀ x : Spacetime, (x, x) ∉ tsupport F) :
    Tendsto (fun k => pairing (period k) (β k) (spacing k) (S k) plane plane' F)
      atTop (𝓝 0) := by
  have h := subtraction_tendsto β S hS plane plane' F
  simpa only [contact4_eq_zero_of_diagonal_disjoint _ _ _ _ _ plane plane' F hF,
    sub_zero] using h

omit [NeZero n] in
/-- Actual separated smeared covariances agree asymptotically after the block is removed. -/
theorem separated_covariance_difference_tendsto (β : ℕ → ℝ)
    (S : (k : ℕ) → Finset (Edge (Vertex (period k))))
    (hS : ∀ k, Independent (period k) ((S k).image (edgeCoord (period k))))
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0)
    (hdiag : ∀ x : Spacetime, (x, x) ∉ tsupport (SchwartzProductTensor.tensor f g)) :
    Tendsto (fun k => (fullCovariance (period k) (β k) (spacing k) plane plane' f g : ℂ) -
      (retainedCovariance (period k) (β k) (spacing k) (S k) plane plane' f g : ℂ))
      atTop (𝓝 0) := by
  have h := separated_pairing_tendsto β S hS plane plane'
    (SchwartzProductTensor.tensor f g) hdiag
  simpa only [pairing_tensor_eq _ _ _ _ plane plane' f g hf hg] using h

omit [NeZero n] in
/-- A separated full-covariance limit, if established, is inherited by the true retained law. -/
theorem retained_limit_of_full (β : ℕ → ℝ)
    (S : (k : ℕ) → Finset (Edge (Vertex (period k))))
    (hS : ∀ k, Independent (period k) ((S k).image (edgeCoord (period k))))
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0)
    (hdiag : ∀ x : Spacetime, (x, x) ∉ tsupport (SchwartzProductTensor.tensor f g))
    (L : ℂ)
    (hL : Tendsto (fun k => (fullCovariance (period k) (β k) (spacing k)
      plane plane' f g : ℂ)) atTop (𝓝 L)) :
    Tendsto (fun k => (retainedCovariance (period k) (β k) (spacing k) (S k)
      plane plane' f g : ℂ)) atTop (𝓝 L) := by
  have h := hL.sub
    (separated_covariance_difference_tendsto β S hS plane plane' f g hf hg hdiag)
  simpa only [sub_sub_cancel, sub_zero] using h

end
end UnifiedTheory.Clay.YangMills.WilsonSchwartzCovariance
