/- Explicit no-wrap four-dimensional Wilson edge boxes with a surface bound.
The estimate is derived from actual plaquette supports, not a supplied
surface-to-volume hypothesis. It does not control the retained correlations. -/
import UnifiedTheory.Clay.YangMills.WilsonRegionClusters
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonMesoscopicBoxes
noncomputable section
open RegulatedGauge PeriodicLattice4 WilsonIndependentBlocks WilsonInducedSupport
open SingleLinkWilsonOscillation WilsonRegionEnergy WilsonRegionClusters WilsonUniformVariance

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (PlaquetteIndex n) := Classical.decEq _

def interval (a b : ℕ) : Finset (ZMod n) := (Finset.Ico a b).image (fun j : ℕ => (j : ZMod n))

theorem mem_interval (a b : ℕ) (hb : b ≤ n) (x : ZMod n) :
    x ∈ interval n a b ↔ a ≤ x.val ∧ x.val < b := by
  constructor
  · intro hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    rw [ZMod.val_natCast_of_lt ((Finset.mem_Ico.mp hj).2.trans_le hb)]
    exact Finset.mem_Ico.mp hj
  · intro hx
    exact Finset.mem_image.mpr ⟨x.val, Finset.mem_Ico.mpr hx, ZMod.natCast_zmod_val x⟩

omit [NeZero n] in
theorem interval_card (a b : ℕ) (hb : b ≤ n) : (interval n a b).card = b - a := by
  rw [interval, Finset.card_image_of_injOn, Nat.card_Ico]
  intro i hi j hj hij
  have h := congrArg ZMod.val hij
  simpa only [ZMod.val_natCast_of_lt ((Finset.mem_Ico.mp hi).2.trans_le hb),
    ZMod.val_natCast_of_lt ((Finset.mem_Ico.mp hj).2.trans_le hb)] using h

def vertices (o : Fin 4 → ℕ) (L : ℕ) : Finset (Vertex n) :=
  Fintype.piFinset (fun μ => interval n (o μ) (o μ + L))

theorem mem_vertices (o : Fin 4 → ℕ) (L : ℕ) (hb : ∀ μ, o μ + L ≤ n) (x : Vertex n) :
    x ∈ vertices n o L ↔ ∀ μ, o μ ≤ (x μ).val ∧ (x μ).val < o μ + L := by
  simp only [vertices, Fintype.mem_piFinset, mem_interval n _ _ (hb _)]

omit [NeZero n] in
theorem vertices_card (o : Fin 4 → ℕ) (L : ℕ) (hb : ∀ μ, o μ + L ≤ n) :
    (vertices n o L).card = L ^ 4 := by
  simp [vertices, Fintype.card_piFinset, interval_card n _ _ (hb _)]

def block (o : Fin 4 → ℕ) (L : ℕ) : Finset (Edge (Vertex n)) :=
  ((vertices n o L).product Finset.univ).image (fun a => selectedLink n a.1 a.2)

omit [NeZero n] in
theorem mem_block (o : Fin 4 → ℕ) (L : ℕ) (e : Edge (Vertex n)) :
    e ∈ block n o L ↔ (edgeCoord n e).1 ∈ vertices n o L := by
  constructor
  · intro he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_product.mp ha).1
  · intro he
    exact Finset.mem_image.mpr ⟨edgeCoord n e, Finset.mem_product.mpr ⟨he,Finset.mem_univ _⟩,
      selected_edgeCoord n e⟩

omit [NeZero n] in
theorem block_card (o : Fin 4 → ℕ) (L : ℕ) (hb : ∀ μ, o μ + L ≤ n) :
    (block n o L).card = 4 * L ^ 4 := by
  have hinj : Function.Injective (fun a : Link n => selectedLink n a.1 a.2) := by
    intro a b hab
    exact congrArg (edgeCoord n) hab
  simp [block, Finset.card_image_of_injective _ hinj, Finset.card_product,
    vertices_card n o L hb, mul_comm]

omit [NeZero n] in
theorem block_nonempty (o : Fin 4 → ℕ) (L : ℕ) (hL : 0 < L) (hb : ∀ μ, o μ + L ≤ n) :
    (block n o L).Nonempty := by
  rw [← Finset.card_pos, block_card n o L hb]
  positivity

variable [Fact (1 < n)]

theorem val_sub_one (x : ZMod n) (hx : 0 < x.val) : (x - 1).val = x.val - 1 := by
  rw [ZMod.val_sub (by simpa only [ZMod.val_one] using hx), ZMod.val_one]

/-- A touched plaquette base lies in the box expanded backwards by one lattice unit. -/
theorem touching_base (o : Fin 4 → ℕ) (L : ℕ) (ho : ∀ μ, 1 ≤ o μ)
    (hb : ∀ μ, o μ + L ≤ n) (p : PlaquetteIndex n)
    (hp : p ∈ touching n (block n o L)) :
    p.1 ∈ vertices n (fun μ => o μ - 1) (L + 1) := by
  obtain ⟨e,he,hep⟩ := (mem_touching n _ p).mp hp
  have hx := (mem_vertices n o L hb _).mp ((mem_block n o L e).mp he)
  apply (mem_vertices n _ _ (fun μ => by have := hb μ; have := ho μ; omega) _).mpr
  intro μ
  obtain ⟨d,hd0,hd1,hd⟩ := WilsonPhysicalStencilLocality.affected_coordinate n
    (edgeCoord n e).1 (edgeCoord n e).2 μ p ((mem_plaquetteEdges n p e).mp hep)
  have hcases : d = 0 ∨ d = 1 := by omega
  rcases hcases with rfl | rfl
  · simp only [Int.cast_zero, sub_zero] at hd
    rw [hd]
    have := hx μ
    have := ho μ
    omega
  · simp only [Int.cast_one] at hd
    rw [hd, val_sub_one n _ (by have := hx μ; have := ho μ; omega)]
    have := hx μ
    have := ho μ
    omega

/-- A plaquette based in the contracted box has all four actual edges inside the region. -/
theorem inner_plaquette (o : Fin 4 → ℕ) (L : ℕ) (hL : 0 < L)
    (hb : ∀ μ, o μ + L ≤ n) (p : PlaquetteIndex n)
    (hp : p.1 ∈ vertices n o (L - 1)) : plaquetteEdges n p ⊆ block n o L := by
  have hx := (mem_vertices n o (L - 1) (fun μ => by have := hb μ; omega) p.1).mp hp
  intro e he
  apply (mem_block n o L e).mpr
  apply (mem_vertices n o L hb _).mpr
  intro μ
  obtain ⟨d,hd0,hd1,hd⟩ := WilsonPhysicalStencilLocality.affected_coordinate n
    (edgeCoord n e).1 (edgeCoord n e).2 μ p ((mem_plaquetteEdges n p e).mp he)
  have hcases : d = 0 ∨ d = 1 := by omega
  rcases hcases with rfl | rfl
  · simp only [Int.cast_zero, sub_zero] at hd
    rw [← hd]
    have := hx μ
    omega
  · simp only [Int.cast_one] at hd
    have heq : (edgeCoord n e).1 μ = p.1 μ + 1 := (eq_sub_iff_add_eq.mp hd).symm
    rw [heq, ZMod.val_add_of_lt (by
      rw [ZMod.val_one]; have := hx μ; have := hb μ; omega), ZMod.val_one]
    have := hx μ
    omega

omit [Fact (1 < n)] in
theorem inner_subset_outer (o : Fin 4 → ℕ) (L : ℕ) (ho : ∀ μ, 1 ≤ o μ)
    (hb : ∀ μ, o μ + L ≤ n) :
    vertices n o (L - 1) ⊆ vertices n (fun μ => o μ - 1) (L + 1) := by
  intro x hx
  have hi := (mem_vertices n o (L - 1) (fun μ => by have := hb μ; omega) x).mp hx
  apply (mem_vertices n _ _ (fun μ => by have := hb μ; have := ho μ; omega) x).mpr
  intro μ
  have := hi μ
  have := ho μ
  omega

theorem boundary_subset_shell (o : Fin 4 → ℕ) (L : ℕ) (hL : 0 < L)
    (ho : ∀ μ, 1 ≤ o μ) (hb : ∀ μ, o μ + L ≤ n) :
    boundary n (block n o L) ⊆
      ((vertices n (fun μ => o μ - 1) (L + 1)) \ vertices n o (L - 1)).product Finset.univ := by
  intro p hp
  have ht := (Finset.mem_sdiff.mp hp).1
  have hn := ((WilsonRegionClusters.mem_boundary n _ p).mp hp).2
  exact Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr
    ⟨touching_base n o L ho hb p ht, fun hi => hn (inner_plaquette n o L hL hb p hi)⟩,
      Finset.mem_univ _⟩

theorem boundary_card (o : Fin 4 → ℕ) (L : ℕ) (hL : 0 < L)
    (ho : ∀ μ, 1 ≤ o μ) (hb : ∀ μ, o μ + L ≤ n) :
    (boundary n (block n o L)).card ≤ 6 * ((L + 1) ^ 4 - (L - 1) ^ 4) := by
  have h := Finset.card_le_card (boundary_subset_shell n o L hL ho hb)
  simp only [Finset.product_eq_sprod, Finset.card_product] at h
  rw [Finset.card_sdiff_of_subset (inner_subset_outer n o L ho hb),
    vertices_card n _ _ (fun μ => by have := hb μ; have := ho μ; omega),
    vertices_card n _ _ (fun μ => by have := hb μ; omega),
    Finset.card_univ, WilsonLocalOscillation.plane_card] at h
  simpa only [mul_comm] using h

/-- The actual four-dimensional surface count is cubic in the side length. -/
theorem boundary_surface_bound (o : Fin 4 → ℕ) (L : ℕ) (hL : 0 < L)
    (ho : ∀ μ, 1 ≤ o μ) (hb : ∀ μ, o μ + L ≤ n) :
    ((boundary n (block n o L)).card : ℝ) ≤ 96 * (L : ℝ) ^ 3 := by
  have h := boundary_card n o L hL ho hb
  have hp : (L - 1) ^ 4 ≤ (L + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hc : ((boundary n (block n o L)).card : ℝ) ≤
      6 * (((L : ℝ) + 1) ^ 4 - ((L : ℝ) - 1) ^ 4) := by
    have hh : ((boundary n (block n o L)).card : ℝ) ≤
        ((6 * ((L + 1) ^ 4 - (L - 1) ^ 4) : ℕ) : ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hp, Nat.cast_pow,
      Nat.cast_add, Nat.cast_one, Nat.cast_sub (show 1 ≤ L by omega)] using hh
  have hpow : (L : ℝ) ≤ (L : ℝ) ^ 3 := by
    simpa using pow_le_pow_right₀ hr (show 1 ≤ 3 by norm_num)
  nlinarith

/-- A proved choice of side length discharges the regional surface hypothesis. -/
theorem surface_condition (o : Fin 4 → ℕ) (L : ℕ) (hL : 0 < L)
    (ho : ∀ μ, 1 ≤ o μ) (hb : ∀ μ, o μ + L ≤ n)
    (β : ℝ) (hβ : 0 ≤ β) (hscale : 24 * β ≤ L) :
    β * (boundary n (block n o L)).card ≤ (block n o L).card := by
  have h := mul_le_mul_of_nonneg_left (boundary_surface_bound n o L hL ho hb) hβ
  have hs := mul_le_mul_of_nonneg_right hscale (show 0 ≤ 4 * (L : ℝ) ^ 3 by positivity)
  rw [block_card n o L hb]
  push_cast
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonMesoscopicBoxes
