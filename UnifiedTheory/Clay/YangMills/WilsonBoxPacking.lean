/- Concrete disjoint mesoscopic edge boxes in the actual periodic lattice.
Their size, number and surface criterion are derived. This is a packing;
the coordinate-zero boundary slices are not silently declared covered. -/
import UnifiedTheory.Clay.YangMills.WilsonMesoscopicBoxes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBoxPacking
noncomputable section
open RegulatedGauge PeriodicLattice4 WilsonIndependentBlocks WilsonInducedSupport
open WilsonRegionEnergy WilsonRegionClusters WilsonRegionDensityTail WilsonSingleLinkStaples
open WilsonMesoscopicBoxes MeasureTheory

abbrev Index (M : ℕ) := Fin 4 → Fin M

def origin (L M : ℕ) (i : Index M) (μ : Fin 4) : ℕ := 1 + L * (i μ).val

theorem origin_pos (L M : ℕ) (i : Index M) (μ : Fin 4) : 1 ≤ origin L M i μ := by
  unfold origin
  omega

theorem origin_bound (n L M : ℕ) (hn : L * M + 1 ≤ n) (i : Index M) (μ : Fin 4) :
    origin L M i μ + L ≤ n := by
  have h := Nat.mul_le_mul_left L (Nat.succ_le_of_lt (i μ).isLt)
  unfold origin
  nlinarith

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

def region (L M : ℕ) (i : Index M) : Finset (Edge (Vertex n)) :=
  block n (origin L M i) L

omit [NeZero n] in
theorem region_card (L M : ℕ) (hn : L * M + 1 ≤ n) (i : Index M) :
    (region n L M i).card = 4 * L ^ 4 :=
  block_card n _ L (origin_bound n L M hn i)

omit [NeZero n] in
theorem region_nonempty (L M : ℕ) (hL : 0 < L) (hn : L * M + 1 ≤ n) (i : Index M) :
    (region n L M i).Nonempty :=
  block_nonempty n _ L hL (origin_bound n L M hn i)

/-- The edge sets are disjoint even when neighboring boxes share boundary plaquettes. -/
theorem region_disjoint (L M : ℕ) (hn : L * M + 1 ≤ n) :
    Pairwise (fun i j : Index M => Disjoint (region n L M i) (region n L M j)) := by
  intro i j hij
  obtain ⟨μ,hμ⟩ := Function.ne_iff.mp hij
  have hv : (i μ).val ≠ (j μ).val := fun h => hμ (Fin.ext h)
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have hi := ((mem_vertices n _ L (origin_bound n L M hn i) _).mp
    ((mem_block n _ L e).mp hei)) μ
  have hj := ((mem_vertices n _ L (origin_bound n L M hn j) _).mp
    ((mem_block n _ L e).mp hej)) μ
  unfold origin at hi hj
  rcases lt_or_gt_of_ne hv with hv | hv
  · have h := Nat.mul_le_mul_left L (Nat.succ_le_of_lt hv)
    nlinarith
  · have h := Nat.mul_le_mul_left L (Nat.succ_le_of_lt hv)
    nlinarith

theorem index_card (M : ℕ) : Fintype.card (Index M) = M ^ 4 := by
  simp [Index]

theorem packing_card (L M : ℕ) (hn : L * M + 1 ≤ n) :
    (Finset.univ.biUnion (region n L M)).card = M ^ 4 * (4 * L ^ 4) := by
  rw [Finset.card_biUnion (fun i _ j _ hij => region_disjoint n L M hn hij)]
  simp only [region_card n L M hn, Finset.sum_const, Finset.card_univ, index_card, smul_eq_mul]

variable [Fact (1 < n)]

theorem region_surface (L M : ℕ) (hL : 0 < L) (hn : L * M + 1 ≤ n)
    (β : ℝ) (hβ : 0 ≤ β) (hscale : 24 * β ≤ L) (i : Index M) :
    β * (boundary n (region n L M i)).card ≤ (region n L M i).card :=
  surface_condition n _ L hL (origin_pos L M i) (origin_bound n L M hn i) β hβ hscale

def badBox (L M : ℕ) (β : ℝ) (i : Index M) : Set (Configuration (Vertex n) Q) :=
  {U | commonLevel β ≤ WilsonRegionEnergy.density n (region n L M i) β U}

omit [Fact (1 < n)] in
theorem badBox_measurable (L M : ℕ) (β : ℝ) (i : Index M) :
    MeasurableSet (badBox n L M β i) :=
  (isClosed_le continuous_const
    (WilsonRegionEnergy.density_continuous n (region n L M i) β)).measurableSet

/-- Every specified box family satisfies the joint bound with geometry discharged. -/
theorem joint_probability_bound (L M : ℕ) (hL : 0 < L) (hn : L * M + 1 ≤ n)
    (β : ℝ) (hβ : 0 < β) (hscale : 24 * β ≤ L) (s : Finset (Index M)) :
    (wilsonLaw n Q character β 2).real {U | ∀ i ∈ s, U ∈ badBox n L M β i} ≤
      Real.exp (-(4 * (L : ℝ) ^ 4 * s.card)) := by
  have h := joint_common_probability_bound n s (region n L M)
    (fun i _ j _ hij => region_disjoint n L M hn hij)
    (fun i _ => region_nonempty n L M hL hn i) β hβ
    (fun i _ => region_surface n L M hL hn β hβ.le hscale i)
  simpa only [badBox, region_card n L M hn, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    Finset.sum_const, nsmul_eq_mul, mul_comm] using h

/-- The finite packing entropy is included in the probability of any bad box. -/
theorem any_probability_bound (L M : ℕ) (hL : 0 < L) (hn : L * M + 1 ≤ n)
    (β : ℝ) (hβ : 0 < β) (hscale : 24 * β ≤ L) :
    (wilsonLaw n Q character β 2).real {U | ∃ i, U ∈ badBox n L M β i} ≤
      (M : ℝ) ^ 4 * Real.exp (-(4 * (L : ℝ) ^ 4)) := by
  classical
  have hs (i : Index M) : (wilsonLaw n Q character β 2).real (badBox n L M β i) ≤
      Real.exp (-(4 * (L : ℝ) ^ 4)) := by
    simpa using joint_probability_bound n L M hL hn β hβ hscale {i}
  have hu := measureReal_biUnion_finset_le (μ := wilsonLaw n Q character β 2)
    (Finset.univ : Finset (Index M)) (badBox n L M β)
  have he : (⋃ i ∈ (Finset.univ : Finset (Index M)), badBox n L M β i) =
      {U | ∃ i, U ∈ badBox n L M β i} := by ext U; simp
  rw [he] at hu
  calc
    _ ≤ ∑ i : Index M, (wilsonLaw n Q character β 2).real (badBox n L M β i) := hu
    _ ≤ ∑ _i : Index M, Real.exp (-(4 * (L : ℝ) ^ 4)) :=
      Finset.sum_le_sum (fun i _ => hs i)
    _ = _ := by simp

end
end UnifiedTheory.Clay.YangMills.WilsonBoxPacking
