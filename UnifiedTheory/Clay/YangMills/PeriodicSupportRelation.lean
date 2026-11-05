/- Periodic coordinate geometry for arbitrary finite-stage support growth.
The relation composes by adding integer radii. Actual Wilson plaquette factors
and sources satisfy the initial bounds, and shared sampled supports have an
explicit physical range once periodic wrapping is excluded. -/
import UnifiedTheory.Clay.YangMills.WilsonResponseStencilLocality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PeriodicSupportRelation
noncomputable section
open RegulatedGauge PeriodicLattice4 WilsonIndependentBlocks WilsonInducedSupport
open WilsonPhysicalStencilLocality WilsonResponseStencilLocality
open SingleLinkWilsonOscillation PeriodicCellSampling LocalFields WilsonUniformVariance

variable (n : ℕ)
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- Every coordinate displacement has a bounded integer representative modulo the period. -/
def Close (r : ℕ) (e d : Edge (Vertex n)) : Prop :=
  ∀ ν : Fin 4, ∃ t : ℤ, |t| ≤ (r : ℤ) ∧
    (edgeCoord n d).1 ν - (edgeCoord n e).1 ν = (t : ZMod n)

theorem close_refl (r : ℕ) (e : Edge (Vertex n)) : Close n r e e := by
  intro ν
  exact ⟨0, by simp, by simp⟩

theorem close_symm (r : ℕ) (e d : Edge (Vertex n)) (h : Close n r e d) : Close n r d e := by
  intro ν
  obtain ⟨t, ht, he⟩ := h ν
  refine ⟨-t, by simpa only [abs_neg] using ht, ?_⟩
  rw [Int.cast_neg, ← he]
  ring

theorem close_mono (r s : ℕ) (e d : Edge (Vertex n)) (hrs : r ≤ s)
    (h : Close n r e d) : Close n s e d := by
  intro ν
  obtain ⟨t, ht, he⟩ := h ν
  exact ⟨t, ht.trans (by exact_mod_cast hrs), he⟩

theorem close_add (r s : ℕ) (e d f : Edge (Vertex n))
    (hed : Close n r e d) (hdf : Close n s d f) : Close n (r + s) e f := by
  intro ν
  obtain ⟨u, hu, heu⟩ := hed ν
  obtain ⟨v, hv, hdv⟩ := hdf ν
  refine ⟨u + v, ?_, ?_⟩
  · exact (abs_add_le _ _).trans (by exact_mod_cast add_le_add hu hv)
  · rw [Int.cast_add, ← heu, ← hdv]
    ring

/-- A plaquette base is represented by an actual link with fixed dummy direction zero. -/
def center (p : PlaquetteIndex n) : Edge (Vertex n) := selectedLink n p.1 0

theorem center_base (p : PlaquetteIndex n) : (edgeCoord n (center n p)).1 = p.1 := by
  exact congrArg Prod.fst (edgeCoord_selected n (p.1, 0))

variable [NeZero n]

/-- Actual plaquette factors have relation diameter one, including periodic boundary faces. -/
theorem plaquette_diameter (p : PlaquetteIndex n) (e d : Edge (Vertex n))
    (he : e ∈ plaquetteEdges n p) (hd : d ∈ plaquetteEdges n p) : Close n 1 e d := by
  intro ν
  obtain ⟨t, ht0, ht1, ht⟩ := star_coordinate n e d
    (plaquetteEdges_subset_star n p e he hd) ν
  exact ⟨t, abs_le.mpr ⟨ht0, ht1⟩, ht⟩

/-- The literal plaquette source is initially centered within radius one of its base. -/
theorem plaquette_centered (p : PlaquetteIndex n) (d : Edge (Vertex n))
    (hd : d ∈ plaquetteEdges n p) : Close n 1 (center n p) d := by
  intro ν
  obtain ⟨t, ht0, ht1, ht⟩ := affected_coordinate n (edgeCoord n d).1
    (edgeCoord n d).2 ν p ((mem_plaquetteEdges n p d).mp hd)
  refine ⟨t, abs_le.mpr ⟨by omega, ht1⟩, ?_⟩
  rw [center_base, ht]
  ring

omit [NeZero n] in
/-- A common coordinate bounds the displacement of two source centers by twice their radius. -/
theorem shared_center_coordinate (r : ℕ) (p q : PlaquetteIndex n)
    (d : Edge (Vertex n)) (hp : Close n r (center n p) d)
    (hq : Close n r (center n q) d) (ν : Fin 4) :
    ∃ t : ℤ, -(2 * (r : ℤ)) ≤ t ∧ t ≤ 2 * (r : ℤ) ∧
      p.1 ν - q.1 ν = (t : ZMod n) := by
  obtain ⟨t, ht, he⟩ := close_add n r r (center n q) d (center n p) hq
    (close_symm n r (center n p) d hp) ν
  rw [center_base, center_base] at he
  obtain ⟨ht0, ht1⟩ := abs_le.mp ht
  refine ⟨t, ?_, ?_, he⟩ <;> norm_cast at ht0 ht1 ⊢ <;> omega

omit [NeZero n] in
/-- Integer relation radii yield physical range without suppressing periodic aliases. -/
theorem shared_sample_distance (r : ℕ) (a R : ℝ) (ha : 0 < a)
    (hperiod : 2 * R + (2 * (r : ℝ) + 1) * a < (n : ℝ) * a)
    (plane plane' : Plane) (x y : Spacetime) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R)
    (d : Edge (Vertex n))
    (hp : Close n r (center n (sample n a plane x)) d)
    (hq : Close n r (center n (sample n a plane' y)) d) :
    ‖x - y‖ ≤ (4 * (r : ℝ) + 2) * a := by
  have hcoord (ν : Fin 4) : |x ν - y ν| ≤ (2 * (r : ℝ) + 1) * a := by
    obtain ⟨t, ht0, ht1, hres⟩ := shared_center_coordinate n r
      (sample n a plane x) (sample n a plane' y) d hp hq ν
    have hX : |x ν| ≤ R := (PiLp.norm_apply_le x ν).trans hx
    have hY : |y ν| ≤ R := (PiLp.norm_apply_le y ν).trans hy
    have he := WilsonResponseStencilLocality.floor_residue_no_wrap n a R (x ν) (y ν) ha
      (2 * r) hX hY (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hperiod) t
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using ht0)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using ht1) hres
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      WilsonResponseStencilLocality.coordinate_distance_le a (x ν) (y ν) ha (2 * r) t
        (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using ht0)
        (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using ht1) he
  have hs : ‖x - y‖ ^ 2 ≤ 4 * ((2 * (r : ℝ) + 1) * a) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _ν : Fin 4, ((2 * (r : ℝ) + 1) * a) ^ 2 := by
        apply Finset.sum_le_sum
        intro ν _
        simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
          pow_le_pow_left₀ (abs_nonneg (x ν - y ν)) (hcoord ν) 2
      _ = _ := by simp
  have hnonneg : 0 ≤ (4 * (r : ℝ) + 2) * a := by positivity
  nlinarith [norm_nonneg (x - y)]

omit [NeZero n] in
/-- Any actual support family with the derived center bound is disjoint at larger separation. -/
theorem sample_supports_disjoint (D : PlaquetteIndex n → Finset (Edge (Vertex n)))
    (r : ℕ) (hD : ∀ p, ∀ d ∈ D p, Close n r (center n p) d)
    (a R : ℝ) (ha : 0 < a)
    (hperiod : 2 * R + (2 * (r : ℝ) + 1) * a < (n : ℝ) * a)
    (plane plane' : Plane) (x y : Spacetime) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R)
    (hfar : (4 * (r : ℝ) + 2) * a < ‖x - y‖) :
    Disjoint (D (sample n a plane x)) (D (sample n a plane' y)) := by
  apply Finset.disjoint_left.mpr
  intro d hp hq
  exact (not_lt_of_ge (shared_sample_distance n r a R ha hperiod plane plane' x y hx hy d
    (hD _ d hp) (hD _ d hq))) hfar

end
end UnifiedTheory.Clay.YangMills.PeriodicSupportRelation
