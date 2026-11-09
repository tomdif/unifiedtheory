/- Explicit coordinate-tree gauge for the actual periodic spatial lattice.
Interior tree links are fixed exactly. Periodic seam links are not fixed. -/
import UnifiedTheory.Clay.YangMills.QuaternionDefectCurvature

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonAxialGauge
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonSlabGauge QuaternionSymmetricChange
open scoped Quaternion

variable (n : ℕ)

def vertex (a b c : ℕ) : SpatialVertex n := ![(a : ZMod n), (b : ZMod n), (c : ZMod n)]

theorem vertex_step_zero (a b c : ℕ) :
    spatialStep n (vertex n a b c) 0 = vertex n (a + 1) b c := by
  funext i
  fin_cases i <;> simp [spatialStep, vertex]

theorem vertex_step_one (a b c : ℕ) :
    spatialStep n (vertex n a b c) 1 = vertex n a (b + 1) c := by
  funext i
  fin_cases i <;> simp [spatialStep, vertex]

theorem vertex_step_two (a b c : ℕ) :
    spatialStep n (vertex n a b c) 2 = vertex n a b (c + 1) := by
  funext i
  fin_cases i <;> simp [spatialStep, vertex]

def axis (x : SpatialVertex n) (i : Fin 3) (k : ℕ) : SpatialVertex n :=
  x + Pi.single i (k : ZMod n)

def line (u : Slice n) (x : SpatialVertex n) (i : Fin 3) : ℕ → Q
  | 0 => 1
  | k+1 => line u x i k * u (axis n x i k,i)

def path (u : Slice n) (a b c : ℕ) : Q :=
  line n u (vertex n 0 0 0) 0 a *
    line n u (vertex n a 0 0) 1 b * line n u (vertex n a b 0) 2 c

theorem axis_vertex_zero (a : ℕ) : axis n (vertex n 0 0 0) 0 a = vertex n a 0 0 := by
  funext i
  fin_cases i <;> simp [axis, vertex]

theorem axis_vertex_one (a b : ℕ) : axis n (vertex n a 0 0) 1 b = vertex n a b 0 := by
  funext i
  fin_cases i <;> simp [axis, vertex]

theorem axis_vertex_two (a b c : ℕ) : axis n (vertex n a b 0) 2 c = vertex n a b c := by
  funext i
  fin_cases i <;> simp [axis, vertex]

theorem path_succ_zero (u : Slice n) (a : ℕ) :
    path n u (a + 1) 0 0 = path n u a 0 0 * u (vertex n a 0 0,0) := by
  simp [path, line, axis_vertex_zero]

theorem path_succ_one (u : Slice n) (a b : ℕ) :
    path n u a (b + 1) 0 = path n u a b 0 * u (vertex n a b 0,1) := by
  simp [path, line, axis_vertex_one, mul_assoc]

theorem path_succ_two (u : Slice n) (a b c : ℕ) :
    path n u a b (c + 1) = path n u a b c * u (vertex n a b c,2) := by
  simp [path, line, axis_vertex_two, mul_assoc]

def gauge (u : Slice n) (x : SpatialVertex n) : Q :=
  path n u (x 0).val (x 1).val (x 2).val

theorem gauge_vertex (u : Slice n) (a b c : ℕ) (ha : a < n) (hb : b < n) (hc : c < n) :
    gauge n u (vertex n a b c) = path n u a b c := by
  simp [gauge, vertex, ZMod.val_natCast_of_lt ha,
    ZMod.val_natCast_of_lt hb, ZMod.val_natCast_of_lt hc]

theorem tree_zero (u : Slice n) (a : ℕ) (ha : a + 1 < n) :
    gaugeSlice (gauge n u) u (vertex n a 0 0,0) = 1 := by
  have h0 : 0 < n := by omega
  simp only [gaugeSlice, vertex_step_zero, gauge_vertex n u a 0 0 (by omega) h0 h0,
    gauge_vertex n u (a + 1) 0 0 ha h0 h0, path_succ_zero]
  group

theorem tree_one (u : Slice n) (a b : ℕ) (ha : a < n) (hb : b + 1 < n) :
    gaugeSlice (gauge n u) u (vertex n a b 0,1) = 1 := by
  have h0 : 0 < n := by omega
  simp only [gaugeSlice, vertex_step_one, gauge_vertex n u a b 0 ha (by omega) h0,
    gauge_vertex n u a (b + 1) 0 ha hb h0, path_succ_one]
  group

theorem tree_two (u : Slice n) (a b c : ℕ) (ha : a < n) (hb : b < n) (hc : c + 1 < n) :
    gaugeSlice (gauge n u) u (vertex n a b c,2) = 1 := by
  simp only [gaugeSlice, vertex_step_two, gauge_vertex n u a b c ha hb (by omega),
    gauge_vertex n u a b (c + 1) ha hb hc, path_succ_two]
  group

omit n in
theorem chord_mul_right (a b c : Q) :
    ‖((a*c : Q) : ℍ)-((b*c : Q) : ℍ)‖ = ‖(a : ℍ)-(b : ℍ)‖ := by
  change ‖(a : ℍ)*(c : ℍ)-(b : ℍ)*(c : ℍ)‖ = _
  rw [← sub_mul, norm_mul, unit_norm, mul_one]

omit n in
theorem chord_mul_left (a b c : Q) :
    ‖((a*b : Q) : ℍ)-((a*c : Q) : ℍ)‖ = ‖(b : ℍ)-(c : ℍ)‖ := by
  change ‖(a : ℍ)*(b : ℍ)-(a : ℍ)*(c : ℍ)‖ = _
  rw [← mul_sub, norm_mul, unit_norm, one_mul]

omit n in
theorem conjugate_defect (a b : Q) :
    ‖((a*b*a⁻¹ : Q) : ℍ)-1‖ = ‖(b : ℍ)-1‖ := by
  have h := chord_mul_right (a*b) a a⁻¹
  have h2 := chord_mul_left a b 1
  simp only [mul_one, OneMemClass.coe_one] at h2
  simpa only [mul_inv_cancel, OneMemClass.coe_one] using h.trans h2

theorem holonomy_defect_gauge (h : SliceGauge n Q) (u : Slice n)
    (x : SpatialVertex n) (i j : Fin 3) :
    ‖((spatialHolonomy (gaugeSlice h u) x i j : Q) : ℍ)-1‖ =
      ‖((spatialHolonomy u x i j : Q) : ℍ)-1‖ := by
  rw [spatialHolonomy_gauge, conjugate_defect]

theorem strip_difference (U : Slice n) (x : SpatialVertex n) (i j : Fin 3)
    (h0 : U (x, j) = 1) (h1 : U (spatialStep n x i, j) = 1) :
    ‖(U (x,i) : ℍ)-(U (spatialStep n x j,i) : ℍ)‖ =
      ‖((spatialHolonomy U x i j : Q) : ℍ)-1‖ := by
  have h := chord_mul_right (U (x,i)) (U (spatialStep n x j,i))
    (U (spatialStep n x j,i))⁻¹
  simpa only [spatialHolonomy, h0, h1, mul_one, inv_one, mul_inv_cancel,
    OneMemClass.coe_one] using h.symm

end
end UnifiedTheory.Clay.YangMills.WilsonAxialGauge
