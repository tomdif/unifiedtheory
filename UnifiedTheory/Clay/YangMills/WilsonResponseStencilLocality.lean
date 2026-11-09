/- Actual first-response supports remain within a fixed physical stencil.
Periodic wrapping is excluded explicitly. This is support geometry for the
induced response, not locality of the full interacting covariance. -/
import UnifiedTheory.Clay.YangMills.WilsonInducedSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonResponseStencilLocality
noncomputable section
open MeasureTheory Filter LocalFields RegulatedGauge PeriodicLattice4
open WilsonIndependentBlocks WilsonInducedSupport WilsonPhysicalStencilLocality
open PeriodicCellSampling SingleLinkWilsonOscillation
open scoped Topology

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- Every coordinate in a retained plaquette response is within two integer steps of its base. -/
theorem response_coordinate (S : Finset (Edge (Vertex n))) (p : PlaquetteIndex n)
    (d : Edge (Vertex n)) (hd : d ∈ responseSupport n S p) (ν : Fin 4) :
    ∃ t : ℤ, -2 ≤ t ∧ t ≤ 2 ∧ p.1 ν - (edgeCoord n d).1 ν = (t : ZMod n) := by
  obtain ⟨hd, _⟩ := Finset.mem_sdiff.mp hd
  rcases Finset.mem_union.mp hd with hd | hd
  · obtain ⟨u, hu0, hu1, hu⟩ := affected_coordinate n (edgeCoord n d).1
      (edgeCoord n d).2 ν p ((mem_plaquetteEdges n p d).mp hd)
    refine ⟨-u, by omega, by omega, ?_⟩
    rw [hu, Int.cast_neg]
    ring
  · obtain ⟨e, he, hde⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨u, hu0, hu1, hu⟩ := affected_coordinate n (edgeCoord n e).1
      (edgeCoord n e).2 ν p ((mem_plaquetteEdges n p e).mp (Finset.mem_inter.mp he).1)
    obtain ⟨t, ht0, ht1, ht⟩ := star_coordinate n e d hde ν
    refine ⟨-u - t, by omega, by omega, ?_⟩
    calc
      _ = -(u : ZMod n) - ((edgeCoord n d).1 ν - (edgeCoord n e).1 ν) := by rw [hu]; ring
      _ = _ := by rw [ht, Int.cast_sub, Int.cast_neg]

/-- Overlapping true response supports force a four-step residue bound. -/
theorem shared_response_coordinate (S : Finset (Edge (Vertex n)))
    (p q : PlaquetteIndex n) (d : Edge (Vertex n))
    (hp : d ∈ responseSupport n S p) (hq : d ∈ responseSupport n S q) (ν : Fin 4) :
    ∃ t : ℤ, -4 ≤ t ∧ t ≤ 4 ∧ p.1 ν - q.1 ν = (t : ZMod n) := by
  obtain ⟨u, hu0, hu1, hu⟩ := response_coordinate n S p d hp ν
  obtain ⟨v, hv0, hv1, hv⟩ := response_coordinate n S q d hq ν
  refine ⟨u - v, by omega, by omega, ?_⟩
  calc
    _ = (p.1 ν - (edgeCoord n d).1 ν) - (q.1 ν - (edgeCoord n d).1 ν) := by ring
    _ = _ := by rw [hu, hv, Int.cast_sub]

omit [NeZero n] in
/-- Any fixed integer stencil has an explicit sufficient physical no-wrap margin. -/
theorem floor_residue_no_wrap (a R X Y : ℝ) (ha : 0 < a) (M : ℕ)
    (hX : |X| ≤ R) (hY : |Y| ≤ R)
    (hperiod : 2 * R + ((M : ℝ) + 1) * a < (n : ℝ) * a)
    (d : ℤ) (hd0 : -(M : ℤ) ≤ d) (hd1 : d ≤ M)
    (hres : (Int.floor (X / a) : ZMod n) - (Int.floor (Y / a) : ZMod n) = (d : ZMod n)) :
    Int.floor (X / a) - Int.floor (Y / a) = d := by
  let z : ℤ := Int.floor (X / a) - Int.floor (Y / a) - d
  have hzcast : (z : ZMod n) = 0 := by
    dsimp only [z]
    push_cast
    rw [hres, sub_self]
  have hdiv : (n : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z n).mp hzcast
  have hxlo := (le_div_iff₀ ha).mp (Int.floor_le (X / a))
  have hxhi := (div_lt_iff₀ ha).mp (Int.lt_floor_add_one (X / a))
  have hylo := (le_div_iff₀ ha).mp (Int.floor_le (Y / a))
  have hyhi := (div_lt_iff₀ ha).mp (Int.lt_floor_add_one (Y / a))
  have hdlo : -(M : ℝ) ≤ d := by exact_mod_cast hd0
  have hdhi : (d : ℝ) ≤ M := by exact_mod_cast hd1
  have hda0 := mul_le_mul_of_nonneg_right hdlo ha.le
  have hda1 := mul_le_mul_of_nonneg_right hdhi ha.le
  have hzsmall : |(z : ℝ)| < (n : ℝ) := by
    rw [abs_lt]
    constructor
    · apply (mul_lt_mul_iff_right₀ ha).mp
      dsimp only [z]
      push_cast
      nlinarith [(abs_le.mp hX).1, (abs_le.mp hY).2]
    · apply (mul_lt_mul_iff_right₀ ha).mp
      dsimp only [z]
      push_cast
      nlinarith [(abs_le.mp hX).2, (abs_le.mp hY).1]
  have hzi : |z| < (n : ℤ) := by exact_mod_cast hzsmall
  have hz0 : |z| = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg z) hzi
    ((dvd_abs (n : ℤ) z).mpr hdiv)
  have hzero : z = 0 := abs_eq_zero.mp hz0
  dsimp only [z] at hzero
  omega

omit n [NeZero n] in
/-- A bounded integer-cell offset gives its physical coordinate distance including cell widths. -/
theorem coordinate_distance_le (a X Y : ℝ) (ha : 0 < a) (M : ℕ) (d : ℤ)
    (hd0 : -(M : ℤ) ≤ d) (hd1 : d ≤ M)
    (he : Int.floor (X / a) - Int.floor (Y / a) = d) :
    |X - Y| ≤ ((M : ℝ) + 1) * a := by
  have hxlo := (le_div_iff₀ ha).mp (Int.floor_le (X / a))
  have hxhi := (div_lt_iff₀ ha).mp (Int.lt_floor_add_one (X / a))
  have hylo := (le_div_iff₀ ha).mp (Int.floor_le (Y / a))
  have hyhi := (div_lt_iff₀ ha).mp (Int.lt_floor_add_one (Y / a))
  have hdlo : -(M : ℝ) ≤ d := by exact_mod_cast hd0
  have hdhi : (d : ℝ) ≤ M := by exact_mod_cast hd1
  have hda0 := mul_le_mul_of_nonneg_right hdlo ha.le
  have hda1 := mul_le_mul_of_nonneg_right hdhi ha.le
  have he' : (Int.floor (X / a) : ℝ) - (Int.floor (Y / a) : ℝ) = d := by exact_mod_cast he
  have hea := congrArg (fun t : ℝ => t * a) he'
  rw [abs_le]
  constructor <;> nlinarith

/-- Actual overlapping first-response supports are confined to ten physical lattice spacings. -/
theorem shared_sample_distance (S : Finset (Edge (Vertex n))) (a R : ℝ) (ha : 0 < a)
    (hperiod : 2 * R + 5 * a < (n : ℝ) * a) (plane plane' : Plane)
    (x y : Spacetime) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (d : Edge (Vertex n))
    (hp : d ∈ responseSupport n S (sample n a plane x))
    (hq : d ∈ responseSupport n S (sample n a plane' y)) : ‖x - y‖ ≤ 10 * a := by
  have hcoord (ν : Fin 4) : |x ν - y ν| ≤ 5 * a := by
    obtain ⟨t, ht0, ht1, hres⟩ := shared_response_coordinate n S
      (sample n a plane x) (sample n a plane' y) d hp hq ν
    have hX : |x ν| ≤ R := (PiLp.norm_apply_le x ν).trans hx
    have hY : |y ν| ≤ R := (PiLp.norm_apply_le y ν).trans hy
    have he := floor_residue_no_wrap n a R (x ν) (y ν) ha 4 hX hY
      (by norm_num; exact hperiod) t ht0 ht1 hres
    simpa only [Nat.cast_ofNat, show (4 : ℝ) + 1 = 5 by norm_num] using
      coordinate_distance_le a (x ν) (y ν) ha 4 t ht0 ht1 he
  have hs : ‖x - y‖ ^ 2 ≤ 100 * a ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _ν : Fin 4, (5 * a) ^ 2 := by
        apply Finset.sum_le_sum
        intro ν _
        simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
          pow_le_pow_left₀ (abs_nonneg (x ν - y ν)) (hcoord ν) 2
      _ = _ := by simp; ring
  nlinarith [norm_nonneg (x - y)]

/-- A physical separation beyond that stencil makes the literal generated response sets disjoint. -/
theorem responseSupport_disjoint_far (S : Finset (Edge (Vertex n))) (a R : ℝ) (ha : 0 < a)
    (hperiod : 2 * R + 5 * a < (n : ℝ) * a) (plane plane' : Plane)
    (x y : Spacetime) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hfar : 10 * a < ‖x - y‖) :
    Disjoint (responseSupport n S (sample n a plane x))
      (responseSupport n S (sample n a plane' y)) := by
  apply Finset.disjoint_left.mpr
  intro d hp hq
  exact (not_lt_of_ge (shared_sample_distance n S a R ha hperiod plane plane' x y hx hy d hp hq))
    hfar

omit n [NeZero n] in
/-- The generated response stencil is physically local along arbitrary expanding volumes. -/
theorem eventually_responseSupport_disjoint_far {ι : Type*} (l : Filter ι)
    (N : ι → ℕ) [∀ k, NeZero (N k)] (a : ι → ℝ)
    (S : (k : ι) → Finset (Edge (Vertex (N k)))) (R : ℝ)
    (ha : ∀ᶠ k in l, 0 < a k) (ha0 : Tendsto a l (𝓝 0))
    (hlarge : Tendsto (fun k => (N k : ℝ) * a k) l atTop) :
    ∀ᶠ k in l, ∀ (plane plane' : Plane) (x y : Spacetime),
      ‖x‖ ≤ R → ‖y‖ ≤ R → 10 * a k < ‖x - y‖ →
      Disjoint (responseSupport (N k) (S k) (sample (N k) (a k) plane x))
        (responseSupport (N k) (S k) (sample (N k) (a k) plane' y)) := by
  have ha1 := ha0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [ha, ha1, hlarge.eventually_gt_atTop (2 * R + 5)] with k hak ha1k hk
  intro plane plane' x y hx hy hfar
  exact responseSupport_disjoint_far (N k) (S k) (a k) R hak (by linarith)
    plane plane' x y hx hy hfar

end
end UnifiedTheory.Clay.YangMills.WilsonResponseStencilLocality
