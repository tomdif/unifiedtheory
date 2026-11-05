/- Six-plaquette source variation for actual physical Schwartz cell weights.
Spatial variation gains one lattice spacing. Differences between the three
incident plane components remain explicit and cannot be discarded. -/
import UnifiedTheory.Clay.YangMills.WilsonCellTranslation
import UnifiedTheory.Clay.YangMills.SU2AnnealedVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSourceVariation
noncomputable section
open MeasureTheory LocalFields RegulatedGauge PeriodicLattice4
open SingleLinkWilsonOscillation WilsonSingleLinkStaples WilsonCellTranslation
open SU2AnnealedVariance FiniteCellSmearing

variable (n : ℕ) [NeZero n] [Fact (1 < n)] (a : ℝ)

/-- Independent physical Schwartz tests for all six plaquette orientations. -/
def planeWeights (F : Plane → TestFunction) (p : PlaquetteIndex n) : ℝ :=
  siteWeight n a (F p.2) p.1

omit [NeZero n] [Fact (1 < n)] in
/-- Literal identification with the sum of the existing one-plane physical sources. -/
theorem planeWeights_eq_physical (F : Plane → TestFunction) (p : PlaquetteIndex n) :
    planeWeights n a F p = ∑ plane, WilsonPhysicalCellWeights.weight n a plane (F plane) p := by
  classical
  rw [Finset.sum_eq_single p.2]
  · exact (weight_on_plane n a p.2 (F p.2) p.1).symm
  · intro q _ hq
    exact WilsonPhysicalCellWeights.weight_other_plane n a q (F q) p (Ne.symm hq)
  · simp

omit [NeZero n] in
/-- Exact six-cell variation, including all three plane components. -/
theorem variation_eq_planes (x : Vertex n) (μ : Fin 4) (F : Plane → TestFunction) (c : ℝ) :
    weightVariation n x μ (planeWeights n a F) c =
      ∑ p ∈ planes μ, (|siteWeight n a (F p) x - c| +
        |siteWeight n a (F p) (x - Pi.single (transverse μ p) 1) - c|) := by
  classical
  unfold weightVariation affected
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro p _
    have hne : (x, p) ≠ (x - Pi.single (transverse μ p) 1, p) := by
      intro he
      exact backward_ne n x (transverse μ p) (congrArg Prod.fst he).symm
    rw [Finset.sum_pair hne]
    rfl
  · intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro b hbp hbq
    have hb : b.2 = p := by
      rcases Finset.mem_insert.mp hbp with h | h
      · exact congrArg Prod.snd h
      · exact congrArg Prod.snd (Finset.mem_singleton.mp h)
    have hb' : b.2 = q := by
      rcases Finset.mem_insert.mp hbq with h | h
      · exact congrArg Prod.snd h
      · exact congrArg Prod.snd (Finset.mem_singleton.mp h)
    exact hpq (hb.symm.trans hb')

omit [NeZero n] in
/-- The common radial coefficient cancels only the common plane component. -/
theorem variation_pointwise_bound (x : Vertex n) (μ : Fin 4)
    (F : Plane → TestFunction) (h : TestFunction) :
    weightVariation n x μ (planeWeights n a F) (siteWeight n a h x) ≤
      ∑ p ∈ planes μ, (2 * |siteWeight n a (F p) x - siteWeight n a h x| +
        |siteWeight n a (F p) (x - Pi.single (transverse μ p) 1) - siteWeight n a (F p) x|) := by
  rw [variation_eq_planes]
  apply Finset.sum_le_sum
  intro p _
  have ht := abs_sub_le (siteWeight n a (F p) (x - Pi.single (transverse μ p) 1))
    (siteWeight n a (F p) x) (siteWeight n a h x)
  linarith

/-- A volume-uniform bound retaining the directional anisotropy explicitly. -/
theorem variation_sum_bound (ha : a ≠ 0) (ha₁ : |a| ≤ 1)
    (μ : Fin 4) (F : Plane → TestFunction) (h : TestFunction) :
    (∑ x, weightVariation n x μ (planeWeights n a F) (siteWeight n a h x)) ≤
      ∑ p ∈ planes μ, (2 * (∫ y, ‖F p y - h y‖) + derivativeBudget (F p) * |a|) := by
  classical
  apply (Finset.sum_le_sum (fun x _ => variation_pointwise_bound n a x μ F h)).trans
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p _
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (siteWeight_difference_budget n a (F p) h) (by norm_num))
    (backward_difference_budget n a ha ha₁ (transverse μ p) (F p))

/-- A common scalar test on every plane does have the first-order gain. -/
theorem isotropic_variation_sum_bound (ha : a ≠ 0) (ha₁ : |a| ≤ 1)
    (μ : Fin 4) (f : TestFunction) :
    (∑ x, weightVariation n x μ (planeWeights n a (fun _ => f)) (siteWeight n a f x)) ≤
      3 * derivativeBudget f * |a| := by
  have h := variation_sum_bound n a ha ha₁ μ (fun _ => f) f
  simpa only [sub_self, norm_zero, integral_zero, mul_zero, zero_add, Finset.sum_const,
    planes_card, nsmul_eq_mul, Nat.cast_ofNat, mul_assoc] using h

/-- Squared variations retain the spacing gain after summing over the entire lattice. -/
theorem isotropic_variation_square_budget (ha : a ≠ 0) (ha₁ : |a| ≤ 1)
    (μ : Fin 4) (f : TestFunction) :
    (∑ x, (weightVariation n x μ (planeWeights n a (fun _ => f))
      (siteWeight n a f x)) ^ 2) ≤ (3 * derivativeBudget f * |a|) ^ 2 := by
  have hD := derivativeBudget_nonneg f
  apply (Finset.sum_sq_le_sq_sum_of_nonneg
    (fun x _ => weightVariation_nonneg n x μ _ _)).trans
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun x _ => weightVariation_nonneg n x μ _ _))
    (by positivity : 0 ≤ 3 * derivativeBudget f * |a|)).mpr
  exact isotropic_variation_sum_bound n a ha ha₁ μ f

omit [NeZero n] [Fact (1 < n)] in
theorem siteWeight_zero (x : Vertex n) : siteWeight n a 0 x = 0 := by
  simp [siteWeight, coefficient, cellFunction]

omit [NeZero n] [Fact (1 < n)] in
/-- The directional source recovers exactly the original single-plane cell weights. -/
theorem single_plane_identification (plane : Plane) (f : TestFunction) :
    planeWeights n a (fun p => if p = plane then f else 0) =
      WilsonPhysicalCellWeights.weight n a plane f := by
  classical
  funext p
  by_cases hp : p.2 = plane
  · subst plane
    simp only [planeWeights, ite_true]
    exact (weight_on_plane n a p.2 f p.1).symm
  · simp only [planeWeights, if_neg hp, siteWeight_zero]
    exact (WilsonPhysicalCellWeights.weight_other_plane n a plane f p hp).symm

omit [NeZero n] in
/-- Four of the six plaquettes lie outside a chosen incident plane. Their
contribution survives even when neighboring weights are spatially constant. -/
theorem single_plane_variation_lower (x : Vertex n) (μ : Fin 4) (plane : Plane)
    (hp : plane ∈ planes μ) (f : TestFunction) (c : ℝ) :
    4 * |c| ≤ weightVariation n x μ (WilsonPhysicalCellWeights.weight n a plane f) c := by
  classical
  rw [← single_plane_identification, variation_eq_planes]
  let T : Plane → ℝ := fun p =>
    |siteWeight n a (if p = plane then f else 0) x - c| +
      |siteWeight n a (if p = plane then f else 0)
        (x - Pi.single (transverse μ p) 1) - c|
  have he : (∑ p ∈ (planes μ).erase plane, T p) = 4 * |c| := by
    have hc : ((planes μ).erase plane).card = 2 := by
      rw [Finset.card_erase_of_mem hp, planes_card]
    calc
      _ = ∑ _p ∈ (planes μ).erase plane, 2 * |c| := by
        apply Finset.sum_congr rfl
        intro p hp'
        have hne := (Finset.mem_erase.mp hp').1
        simp only [T, if_neg hne, siteWeight_zero, zero_sub, abs_neg]
        ring
      _ = 4 * |c| := by simp [hc]; ring
  rw [← he]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
  intro p _ _
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

omit [Fact (1 < n)] in
/-- The radial coefficients have a volume-independent square budget. -/
theorem siteWeight_square_budget (f : TestFunction) :
    (∑ x, (siteWeight n a f x) ^ 2) ≤ (∫ y, ‖f y‖) ^ 2 := by
  have hs : (∑ x, (siteWeight n a f x) ^ 2) ≤ (∑ x, |siteWeight n a f x|) ^ 2 := by
    simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (f := fun x => |siteWeight n a f x|) (fun _ _ => abs_nonneg _)
  exact hs.trans ((sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (integral_nonneg (fun _ => norm_nonneg _))).mpr (siteWeight_budget n a f))

/-- An actual original-law sum of one-link conditional variances for the isotropic
physical source. This is not an approximate-tensorization or sequential-RG bound. -/
theorem isotropic_annealed_variance_sum (ha : a ≠ 0) (ha₁ : |a| ≤ 1)
    (μ : Fin 4) (f : TestFunction) (β r₀ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hr₆ : r₀ < 6) :
    (∑ x, ∫ U, originalVariance n x μ β (planeWeights n a (fun _ => f)) U
      ∂wilsonLaw n Q character β 2) ≤
      (15 / (2 * β ^ 2)) * (∫ y, ‖f y‖) ^ 2 +
        (12 / (β * r₀) + 144 * WilsonEnergyDensity.energyEnvelope β / (6 - r₀)) *
          (3 * derivativeBudget f * |a|) ^ 2 := by
  let C := 12 / (β * r₀) + 144 * WilsonEnergyDensity.energyEnvelope β / (6 - r₀)
  have hC : 0 ≤ C := by
    have hE := WilsonEnergyDensity.energyEnvelope_nonneg β hβ
    have hr : 0 < 6 - r₀ := by linarith
    dsimp only [C]
    positivity
  calc
    _ ≤ ∑ x, (15 * (siteWeight n a f x) ^ 2 / (2 * β ^ 2) +
        C * (weightVariation n x μ (planeWeights n a (fun _ => f))
          (siteWeight n a f x)) ^ 2) := by
      apply Finset.sum_le_sum
      intro x _
      exact annealed_variance_explicit n x μ β (siteWeight n a f x) r₀
        (planeWeights n a (fun _ => f)) hβ hr₀ hr₆
    _ = (15 / (2 * β ^ 2)) * (∑ x, (siteWeight n a f x) ^ 2) +
        C * (∑ x, (weightVariation n x μ (planeWeights n a (fun _ => f))
          (siteWeight n a f x)) ^ 2) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (siteWeight_square_budget n a f) (by positivity))
      (mul_le_mul_of_nonneg_left (isotropic_variation_square_budget n a ha ha₁ μ f) hC)

end
end UnifiedTheory.Clay.YangMills.WilsonSourceVariation
