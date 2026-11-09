/- Actual periodic Wilson incidence becomes Euclidean locality on compact physical supports.
The floor/residue sampler and its periodic images are handled explicitly.
No assertion of finite range for the full Wilson covariance is made. -/
import UnifiedTheory.Clay.YangMills.WilsonInfluenceGeometry
import UnifiedTheory.Clay.YangMills.PeriodicCellSampling

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonPhysicalStencilLocality
noncomputable section
open MeasureTheory Filter LocalFields PeriodicLattice4 WilsonIndependentBlocks
open SingleLinkWilsonOscillation WilsonInfluenceGeometry PeriodicCellSampling
open scoped Topology

variable (n : ℕ)

/-- An affected plaquette base is zero or one coordinate step behind the selected link. -/
theorem affected_coordinate (z : Vertex n) (μ ν : Fin 4) (p : PlaquetteIndex n)
    (hp : p ∈ affected n z μ) :
    ∃ d : ℤ, 0 ≤ d ∧ d ≤ 1 ∧ p.1 ν = z ν - (d : ZMod n) := by
  rcases (mem_affected_iff n z μ p).mp hp with ⟨_, h | h⟩
  · refine ⟨0, le_rfl, by norm_num, ?_⟩
    simp only [h, Int.cast_zero, sub_zero]
  · by_cases hv : ν = transverse μ p.2
    · refine ⟨1, by norm_num, le_rfl, ?_⟩
      simp [h, Pi.sub_apply, hv]
    · refine ⟨0, le_rfl, by norm_num, ?_⟩
      simp [h, Pi.sub_apply, hv]

/-- Two plaquettes sharing an actual link have a coordinate residue difference at most one. -/
theorem shared_coordinate (z : Vertex n) (μ ν : Fin 4) (p q : PlaquetteIndex n)
    (hp : p ∈ affected n z μ) (hq : q ∈ affected n z μ) :
    ∃ d : ℤ, -1 ≤ d ∧ d ≤ 1 ∧ p.1 ν - q.1 ν = (d : ZMod n) := by
  obtain ⟨dp, hp0, hp1, hpe⟩ := affected_coordinate n z μ ν p hp
  obtain ⟨dq, hq0, hq1, hqe⟩ := affected_coordinate n z μ ν q hq
  refine ⟨dq - dp, by omega, by omega, ?_⟩
  rw [hpe, hqe, Int.cast_sub]
  ring

/-- Bounded physical coordinates exclude every nonzero periodic image. -/
theorem floor_residue_no_wrap (a R X Y : ℝ) (ha : 0 < a)
    (hX : |X| ≤ R) (hY : |Y| ≤ R) (hperiod : 2 * R + 2 * a < (n : ℝ) * a)
    (d : ℤ) (hd0 : -1 ≤ d) (hd1 : d ≤ 1)
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
  have hdlo : (-1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hdhi : (d : ℝ) ≤ 1 := by exact_mod_cast hd1
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

/-- Neighboring integer cells have coordinate separation at most two spacings. -/
theorem coordinate_distance_le (a X Y : ℝ) (ha : 0 < a) (d : ℤ)
    (hd0 : -1 ≤ d) (hd1 : d ≤ 1)
    (he : Int.floor (X / a) - Int.floor (Y / a) = d) : |X - Y| ≤ 2 * a := by
  have hxlo := (le_div_iff₀ ha).mp (Int.floor_le (X / a))
  have hxhi := (div_lt_iff₀ ha).mp (Int.lt_floor_add_one (X / a))
  have hylo := (le_div_iff₀ ha).mp (Int.floor_le (Y / a))
  have hyhi := (div_lt_iff₀ ha).mp (Int.lt_floor_add_one (Y / a))
  have hdlo : (-1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hdhi : (d : ℝ) ≤ 1 := by exact_mod_cast hd1
  have hda0 := mul_le_mul_of_nonneg_right hdlo ha.le
  have hda1 := mul_le_mul_of_nonneg_right hdhi ha.le
  have he' : (Int.floor (X / a) : ℝ) - (Int.floor (Y / a) : ℝ) = d := by
    exact_mod_cast he
  have hea := congrArg (fun t : ℝ => t * a) he'
  rw [abs_le]
  constructor <;> nlinarith

/-- Actual shared-link sampling is confined to a shrinking physical diagonal
inside every fixed ball once the physical period exceeds its diameter. -/
theorem shared_sample_distance (a R : ℝ) (ha : 0 < a)
    (hperiod : 2 * R + 2 * a < (n : ℝ) * a) (plane plane' : Plane)
    (x y : Spacetime) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R)
    (z : Vertex n) (μ : Fin 4)
    (hp : sample n a plane x ∈ affected n z μ)
    (hq : sample n a plane' y ∈ affected n z μ) : ‖x - y‖ ≤ 4 * a := by
  have hcoord (ν : Fin 4) : |x ν - y ν| ≤ 2 * a := by
    obtain ⟨d, hd0, hd1, hres⟩ := shared_coordinate n z μ ν
      (sample n a plane x) (sample n a plane' y) hp hq
    have hX : |x ν| ≤ R := (PiLp.norm_apply_le x ν).trans hx
    have hY : |y ν| ≤ R := (PiLp.norm_apply_le y ν).trans hy
    exact coordinate_distance_le a (x ν) (y ν) ha d hd0 hd1
      (floor_residue_no_wrap n a R (x ν) (y ν) ha hX hY hperiod d hd0 hd1 hres)
  have hs : ‖x - y‖ ^ 2 ≤ 16 * a ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _ν : Fin 4, (2 * a) ^ 2 := by
        apply Finset.sum_le_sum
        intro ν _
        simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
          pow_le_pow_left₀ (abs_nonneg (x ν - y ν)) (hcoord ν) 2
      _ = _ := by simp; ring
  nlinarith [norm_nonneg (x - y)]

/-- The actual sampled stencil becomes local on every fixed compact ball along
any shrinking-mesh, expanding-volume regulator family. -/
theorem eventually_shared_sample_distance {ι : Type*} (l : Filter ι)
    (N : ι → ℕ) (a : ι → ℝ) (R : ℝ)
    (ha : ∀ᶠ k in l, 0 < a k) (ha0 : Tendsto a l (𝓝 0))
    (hlarge : Tendsto (fun k => (N k : ℝ) * a k) l atTop) :
    ∀ᶠ k in l, ∀ (plane plane' : Plane) (x y : Spacetime),
      ‖x‖ ≤ R → ‖y‖ ≤ R → ∀ (z : Vertex (N k)) (μ : Fin 4),
      sample (N k) (a k) plane x ∈ affected (N k) z μ →
      sample (N k) (a k) plane' y ∈ affected (N k) z μ → ‖x - y‖ ≤ 4 * a k := by
  have ha1 := ha0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [ha, ha1, hlarge.eventually_gt_atTop (2 * R + 2)] with k hak ha1k hk
  intro plane plane' x y hx hy z μ hp hq
  exact shared_sample_distance (N k) (a k) R hak (by linarith) plane plane' x y hx hy z μ hp hq

end
end UnifiedTheory.Clay.YangMills.WilsonPhysicalStencilLocality
