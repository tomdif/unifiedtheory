/- Spatial boxes and their actual touched-link boundary. A supported gauge
change pays a surface cost; the periodic seam is not treated as an interior link. -/
import UnifiedTheory.Clay.YangMills.WilsonAxialRegularity
import UnifiedTheory.Clay.YangMills.WilsonMesoscopicBoxes
import UnifiedTheory.Clay.YangMills.WilsonGaugeBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonAxialBox
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonAxialGauge WilsonAxialRegularity
open WilsonMesoscopicBoxes (interval mem_interval interval_card val_sub_one)
open scoped Quaternion

variable (n : ℕ) [NeZero n]

def vertices (a b : ℕ) : Finset (SpatialVertex n) :=
  Fintype.piFinset (fun _ : Fin 3 => interval n a b)

theorem mem_vertices (a b : ℕ) (hb : b ≤ n) (x : SpatialVertex n) :
    x ∈ vertices n a b ↔ ∀ i, a ≤ (x i).val ∧ (x i).val < b := by
  simp only [vertices, Fintype.mem_piFinset, mem_interval n a b hb]

omit [NeZero n] in
theorem vertices_card (a b : ℕ) (hb : b ≤ n) :
    (vertices n a b).card = (b-a)^3 := by
  simp [vertices, Fintype.card_piFinset, interval_card n a b hb]

def block (L : ℕ) : Finset (SpatialVertex n) := vertices n 1 (L + 1)
def core (L : ℕ) : Finset (SpatialVertex n × Fin 3) :=
  (vertices n 1 L).product Finset.univ
def outer (L : ℕ) : Finset (SpatialVertex n × Fin 3) :=
  (vertices n 0 (L + 1)).product Finset.univ
def touched (L : ℕ) : Finset (SpatialVertex n × Fin 3) :=
  Finset.univ.filter (fun e => e.1 ∈ block n L ∨ spatialStep n e.1 e.2 ∈ block n L)

omit [NeZero n] in
theorem block_card (L : ℕ) (hL : L + 1 ≤ n) : (block n L).card = L^3 := by
  simp [block, vertices_card n 1 (L + 1) hL]

theorem core_subset_outer (L : ℕ) (hL : L + 1 ≤ n) : core n L ⊆ outer n L := by
  intro e he
  have hx := (mem_vertices n 1 L (by omega) e.1).mp (Finset.mem_product.mp he).1
  exact Finset.mem_product.mpr ⟨(mem_vertices n 0 (L + 1) hL e.1).mpr
    (fun i => by have := hx i; omega), Finset.mem_univ _⟩

theorem core_source (L : ℕ) (hL : L + 1 ≤ n) (e : SpatialVertex n × Fin 3)
    (he : e ∈ core n L) : e.1 ∈ block n L := by
  have hx := (mem_vertices n 1 L (by omega) e.1).mp (Finset.mem_product.mp he).1
  exact (mem_vertices n 1 (L + 1) hL e.1).mpr (fun i => by have := hx i; omega)

variable [Fact (1 < n)]

theorem core_target (L : ℕ) (hL : L + 1 ≤ n) (e : SpatialVertex n × Fin 3)
    (he : e ∈ core n L) : spatialStep n e.1 e.2 ∈ block n L := by
  have hx := (mem_vertices n 1 L (by omega) e.1).mp (Finset.mem_product.mp he).1
  apply (mem_vertices n 1 (L + 1) hL _).mpr
  intro i
  by_cases hi : i = e.2
  · subst i
    have hv : (e.1 e.2).val+1 < n := by have := hx e.2; omega
    have heq : (spatialStep n e.1 e.2) e.2 = e.1 e.2 + 1 := by simp [spatialStep]
    rw [heq, ZMod.val_add_of_lt (a := e.1 e.2) (b := 1)
      (by simpa only [ZMod.val_one] using hv), ZMod.val_one]
    have := hx e.2
    omega
  · simpa [spatialStep, Pi.single_apply, hi] using
      (show 1 ≤ (e.1 i).val ∧ (e.1 i).val < L + 1 by have := hx i; omega)

theorem touched_subset_outer (L : ℕ) (hL : L + 1 ≤ n) : touched n L ⊆ outer n L := by
  intro e he
  apply Finset.mem_product.mpr
  refine ⟨(mem_vertices n 0 (L + 1) hL e.1).mpr ?_, Finset.mem_univ _⟩
  rcases (Finset.mem_filter.mp he).2 with hs | ht
  · have hx := (mem_vertices n 1 (L + 1) hL e.1).mp hs
    intro i
    exact ⟨Nat.zero_le _, (hx i).2⟩
  · have hx := (mem_vertices n 1 (L + 1) hL _).mp ht
    intro i
    by_cases hi : i = e.2
    · subst i
      have heq : e.1 e.2 = (spatialStep n e.1 e.2) e.2 - 1 := by simp [spatialStep]
      rw [heq, val_sub_one n _ (by have := (hx e.2).1; omega)]
      have := hx e.2
      omega
    · have heq : (spatialStep n e.1 e.2) i = e.1 i := by
        simp [spatialStep, hi]
      exact ⟨Nat.zero_le _, by simpa only [heq] using (hx i).2⟩

omit [Fact (1 < n)] in
theorem shell_surface (L : ℕ) (hpos : 0 < L) (hL : L + 1 ≤ n) :
    (((outer n L \ core n L).card : ℕ) : ℝ) ≤ 24*(L : ℝ)^2 := by
  rw [Finset.card_sdiff_of_subset (core_subset_outer n L hL)]
  have hc : (core n L).card = (L - 1)^3*3 := by
    simp [core, Finset.card_product, vertices_card n 1 L (by omega)]
  have ho : (outer n L).card = (L + 1)^3*3 := by
    simp [outer, Finset.card_product, vertices_card n 0 (L + 1) hL]
  have hp : (L - 1)^3*3 ≤ (L + 1)^3*3 :=
    Nat.mul_le_mul_right 3 (Nat.pow_le_pow_left (by omega) 3)
  rw [hc, ho, Nat.cast_sub hp]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub (show 1 ≤ L by omega)]
  have h : (1 : ℝ) ≤ L := by exact_mod_cast hpos
  nlinarith [sq_nonneg ((L : ℝ)-1)]

end
end UnifiedTheory.Clay.YangMills.WilsonAxialBox
