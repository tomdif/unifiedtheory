/- Actual finite unions of high-energy block regions. Overlapping, correlated
regions share one residual budget; their explicit mass errors are summed. -/
import UnifiedTheory.Clay.YangMills.WilsonCutoffCover
import UnifiedTheory.Clay.YangMills.WilsonSpatialCutDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSpatialCutUnion
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay WilsonSpatialCutEnergy

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def rate (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) (R : ℝ) : ℝ :=
  Real.exp (-β*(R-8*(boundary n S).card-
    4 * (((bulk n S).card : ℝ)+S.card) * WilsonGroundSlabEnergy.envelope β))

def cutoff (S : Finset (SpatialVertex n × Fin 3)) (R : ℝ) : C(Slice n, ℝ) :=
  ⟨fun u => min 1 (max 0 ((bulkPotential n S u-R)/R)),
    continuous_const.min (continuous_const.max
      (((part_continuous n (bulk n S)).sub continuous_const).div_const R))⟩

theorem cutoff_range (S : Finset (SpatialVertex n × Fin 3)) (R : ℝ) (u : Slice n) :
    cutoff n S R u ∈ Set.Icc 0 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

theorem cutoff_supported (S : Finset (SpatialVertex n × Fin 3)) (R : ℝ) (hR : 0 < R)
    (u : Slice n) (hu : bulkPotential n S u < R) : cutoff n S R u = 0 := by
  change min 1 (max 0 ((bulkPotential n S u-R)/R)) = 0
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu.le) hR.le)]
  norm_num

theorem cutoff_one (S : Finset (SpatialVertex n × Fin 3)) (R : ℝ) (hR : 0 < R)
    (u : Slice n) (hu : 2 * R ≤ bulkPotential n S u) : cutoff n S R u = 1 := by
  apply min_eq_left
  apply (le_max_right _ _).trans'
  apply (le_div_iff₀ hR).mpr
  change 1*R ≤ bulkPotential n S u-R
  linarith

theorem cutoff_physical (S : Finset (SpatialVertex n × Fin 3)) (R : ℝ)
    (h : SliceGauge n Q) (u : Slice n) : cutoff n S R (gaugeSlice h u) = cutoff n S R u := by
  change min 1 (max 0 ((partPotential n (bulk n S) (gaugeSlice h u)-R)/R)) = _
  rw [part_gauge]
  rfl

theorem cutoff_output (β : ℝ) (hβ : 0 < β) (S : Finset (SpatialVertex n × Fin 3))
    (R : ℝ) (χ : C(Slice n, ℝ)) (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hs : ∀ u, bulkPotential n S u < R → χ u = 0) (f : C(Slice n, ℝ)) :
    mass n β hβ.le (χ*step n β hβ.le f) ≤ rate n β S R*mass n β hβ.le f := by
  apply WilsonCutoffCover.cutoff_output n β hβ.le χ _ (Real.exp_pos _).le hχ _ f
  intro h hh
  exact WilsonSpatialCutDecay.price_decay n β hβ S R h (fun u hu => hh u (hs u hu))

variable {I : Type*} [Fintype I]

def cover (S : I → Finset (SpatialVertex n × Fin 3)) (R : I → ℝ) (i : I) : C(Slice n, ℝ) :=
  CompactCutoffCover.weight (fun j => cutoff n (S j) (R j)) i

def bad (S : I → Finset (SpatialVertex n × Fin 3)) (R : I → ℝ) : Set (Slice n) :=
  {u | ∃ i, 2 * R i ≤ bulkPotential n (S i) u}

omit [Fintype I] in
theorem bad_measurable [Finite I] (S : I → Finset (SpatialVertex n × Fin 3)) (R : I → ℝ) :
    MeasurableSet (bad n S R) := by
  have he : bad n S R = ⋃ i, {u | 2 * R i ≤ bulkPotential n (S i) u} := by ext u; simp [bad]
  rw [he]
  exact MeasurableSet.iUnion (fun i =>
    measurableSet_le measurable_const (part_continuous n (bulk n (S i))).measurable)

theorem cover_range (S : I → Finset (SpatialVertex n × Fin 3)) (R : I → ℝ)
    (i : I) (u : Slice n) : cover n S R i u ∈ Set.Icc 0 1 :=
  CompactCutoffCover.weight_range _ (fun j => cutoff_range n (S j) (R j)) i u

theorem cover_supported (S : I → Finset (SpatialVertex n × Fin 3)) (R : I → ℝ)
    (hR : ∀ i, 0 < R i) (i : I) (u : Slice n) (hu : bulkPotential n (S i) u < R i) :
    cover n S R i u = 0 :=
  CompactCutoffCover.weight_zero _ i u (cutoff_supported n (S i) (R i) (hR i) u hu)

theorem cover_physical (S : I → Finset (SpatialVertex n × Fin 3)) (R : I → ℝ)
    (i : I) (h : SliceGauge n Q) (u : Slice n) :
    cover n S R i (gaugeSlice h u) = cover n S R i u :=
  CompactCutoffCover.weight_eq_of_values _ _ _ (fun j => cutoff_physical n (S j) (R j) h u) i

/-- The actual finite union pays loss once, even if every block overlaps. -/
theorem weighted_union (β : ℝ) (hβ : 0 < β) (S : I → Finset (SpatialVertex n × Fin 3))
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (f : C(Slice n, ℝ)) :
    (∫ u, (bad n S R).indicator (fun v => (f v)^2) u ∂groundLaw n β hβ.le) ≤
      2*loss n β hβ.le f+2*(∑ i, rate n β (S i) (R i))*mass n β hβ.le f := by
  apply (WilsonCutoffCover.event_le_sum_mass n β hβ.le (cover n S R) _
    (bad_measurable n S R) ?_ f).trans
  · exact WilsonCutoffCover.joint_localization n β hβ.le (cover n S R)
      (CompactCutoffCover.sum_square_le _) (fun i => rate n β (S i) (R i))
      (fun _ => (Real.exp_pos _).le)
      (fun i h => cutoff_output n β hβ (S i) (R i) (cover n S R i)
        (cover_range n S R i) (cover_supported n S R hR i) h) f
  · intro u hu
    obtain ⟨i,hi⟩ := hu
    exact CompactCutoffCover.sum_square_one _ u
      ⟨i, cutoff_one n (S i) (R i) (hR i) u hi⟩

theorem weighted_union_rate (β : ℝ) (hβ : 0 < β)
    (S : I → Finset (SpatialVertex n × Fin 3)) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (q : ℝ) (hq : ∀ i, rate n β (S i) (R i) ≤ q) (f : C(Slice n, ℝ)) :
    (∫ u, (bad n S R).indicator (fun v => (f v)^2) u ∂groundLaw n β hβ.le) ≤
      2*loss n β hβ.le f+2*(Fintype.card I : ℝ)*q*mass n β hβ.le f := by
  apply (weighted_union n β hβ S R hR f).trans
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hq i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hh := mul_le_mul_of_nonneg_right hs (mass_nonneg n β hβ.le f)
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonSpatialCutUnion
