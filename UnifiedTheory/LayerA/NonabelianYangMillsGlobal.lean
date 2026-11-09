/-
Supporting proofs for NONABELIAN_YANG_MILLS_GLOBAL_LIMIT.md.
The scalar barrier theorem is fully proved here; the Fourier convergence
assembly and the cited global continuum existence theorem are not formalized.
-/
import UnifiedTheory.LayerA.NonabelianYangMillsEnergy
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.NonabelianYangMillsGlobal
noncomputable section

open Set NonabelianYangMillsEnergy

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem relative_gradient_identity (f l c : E) :
    -inner (𝕜 := ℝ) (f + l + c) (l + (2 : ℝ) • c) + inner (𝕜 := ℝ) f l =
      -‖l‖ ^ 2 - 3 * inner (𝕜 := ℝ) l c - 2 * ‖c‖ ^ 2 -
        2 * inner (𝕜 := ℝ) f c := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm c l]
  ring

theorem relative_square_completion (f l c : E) :
    -‖l‖ ^ 2 - 3 * inner (𝕜 := ℝ) l c - 2 * ‖c‖ ^ 2 -
        2 * inner (𝕜 := ℝ) f c =
      -‖l + (3 / 2 : ℝ) • c‖ ^ 2 + ‖c‖ ^ 2 / 4 -
        2 * inner (𝕜 := ℝ) f c := by
  simp only [norm_add_sq_real, real_inner_smul_right, norm_smul]
  norm_num
  ring

theorem relative_gradient_upper (f l c : E) :
    -inner (𝕜 := ℝ) (f + l + c) (l + (2 : ℝ) • c) + inner (𝕜 := ℝ) f l ≤
      ‖c‖ ^ 2 / 4 - 2 * inner (𝕜 := ℝ) f c := by
  rw [relative_gradient_identity, relative_square_completion]
  nlinarith [sq_nonneg ‖l + (3 / 2 : ℝ) • c‖]

end Hilbert

theorem bracket_normsq_identity (u v : Vec) :
    dot (bracket u v) (bracket u v) =
      4 * (dot u u * dot v v - (dot u v) ^ 2) := by
  simp [dot, bracket]
  ring

theorem bracket_pair_bound (u v : Vec) :
    dot (bracket u v) (bracket u v) ≤ (dot u u + dot v v) ^ 2 := by
  rw [bracket_normsq_identity]
  nlinarith [sq_nonneg (dot u u - dot v v), sq_nonneg (dot u v)]

theorem forcing_young (x r : ℝ) : 2 * x * r ≤ x ^ 2 + r ^ 2 := by
  nlinarith [sq_nonneg (x - r)]

def envelope (a r t : ℝ) : ℝ := 2 * r ^ 2 * Real.exp ((a + 1) * t)

theorem envelope_pos (a r t : ℝ) (hr : 0 < r) : 0 < envelope a r t := by
  unfold envelope
  positivity

theorem envelope_lower (a r t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    2 * r ^ 2 ≤ envelope a r t := by
  have hexp : 1 ≤ Real.exp ((a + 1) * t) :=
    Real.one_le_exp_iff.mpr (by positivity)
  unfold envelope
  nlinarith [mul_le_mul_of_nonneg_left hexp (show 0 ≤ 2 * r ^ 2 by positivity)]

theorem envelope_mono (a r s t : ℝ) (ha : 0 ≤ a) (hst : s ≤ t) :
    envelope a r s ≤ envelope a r t := by
  unfold envelope
  gcongr

theorem envelope_hasDerivAt (a r t : ℝ) :
    HasDerivAt (envelope a r) ((a + 1) * envelope a r t) t := by
  convert (((hasDerivAt_id t).const_mul (a + 1)).exp.const_mul (2 * r ^ 2)) using 1
  dsimp [envelope]
  ring

/-- At contact with the exponential envelope, the Riccati inequality is strict. -/
theorem contact_derivative_strict (a b r z rate : ℝ) (hz : 0 < z)
    (hlower : 2 * r ^ 2 ≤ z) (hsmall : b * z ≤ 1 / 4)
    (hrate : rate ≤ a * z + b * z ^ 2 + r ^ 2) : rate < (a + 1) * z := by
  have hquad := mul_le_mul_of_nonneg_right hsmall (le_of_lt hz)
  nlinarith

/-- The complete scalar comparison: no smallness assumption on y itself.
Only the explicit envelope must fit below the Riccati threshold. -/
theorem riccati_envelope_bound {y dy : ℝ → ℝ} {a b r T : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 < r)
    (hy : ContinuousOn y (Icc 0 T))
    (hdy : ∀ t ∈ Ico 0 T, HasDerivWithinAt y (dy t) (Ici t) t)
    (hzero : y 0 ≤ 0)
    (hdiff : ∀ t ∈ Ico 0 T, dy t ≤ a * y t + b * (y t) ^ 2 + r ^ 2)
    (hsmall : b * envelope a r T ≤ 1 / 4) :
    ∀ t ∈ Icc 0 T, y t ≤ envelope a r t := by
  apply image_le_of_deriv_right_lt_deriv_boundary hy hdy
  · exact hzero.trans (le_of_lt (envelope_pos a r 0 hr))
  · exact envelope_hasDerivAt a r
  · intro t ht hcontact
    have hlocal : b * envelope a r t ≤ 1 / 4 :=
      (mul_le_mul_of_nonneg_left (envelope_mono a r t T ha (le_of_lt ht.2)) hb).trans hsmall
    have hrate := hdiff t ht
    rw [hcontact] at hrate
    exact contact_derivative_strict a b r (envelope a r t) (dy t)
      (envelope_pos a r t hr) (envelope_lower a r t ha ht.1) hlocal hrate

/-- Scalar assembly of the cutoff threshold, before substituting powers of N. -/
theorem spectral_threshold (beta d n z : ℝ) (hb : 0 ≤ beta)
    (hd : 0 ≤ d) (hn : 0 ≤ n) (hz : 0 ≤ z) (hdn : d ≤ 2 * n)
    (hsmall : 16 * beta * n ^ 2 * z ≤ 1) : beta * d ^ 2 * z ≤ 1 / 4 := by
  have hd2 : d ^ 2 ≤ 4 * n ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hd2 (mul_nonneg hb hz)
  nlinarith

/-- Unit-circle coordinates of a spatially gauge-rotated homogeneous solution. -/
def rotatedOne (a c s h : ℝ) : Vec := ![a * c, a * s, -h]
def rotatedTwo (a c s j : ℝ) : Vec := ![-a * s, a * c, -j]
def rotatedTwoDx (a c s h k : ℝ) : Vec := ![-2 * a * h * c, -2 * a * h * s, -k]
def rotatedOneDy (a c s j k : ℝ) : Vec := ![-2 * a * j * s, 2 * a * j * c, -k]

theorem rotated_curvature (a c s h j k : ℝ) (hcircle : c ^ 2 + s ^ 2 = 1) :
    rotatedTwoDx a c s h k - rotatedOneDy a c s j k +
      bracket (rotatedOne a c s h) (rotatedTwo a c s j) =
      ![0, 0, 2 * a ^ 2] := by
  funext i
  fin_cases i <;> simp [rotatedOne, rotatedTwo, rotatedTwoDx, rotatedOneDy, bracket,
    Pi.add_apply]
  all_goals nlinarith [congrArg (fun x : ℝ => 2 * a ^ 2 * x) hcircle]

theorem rotated_gradient_one (a c s j : ℝ) :
    -bracket (rotatedTwo a c s j) ![0, 0, 2 * a ^ 2] =
      ![-4 * a ^ 3 * c, -4 * a ^ 3 * s, 0] := by
  funext i
  fin_cases i <;> simp [rotatedTwo, bracket, Pi.neg_apply] <;> ring

theorem rotated_gradient_two (a c s h : ℝ) :
    bracket (rotatedOne a c s h) ![0, 0, 2 * a ^ 2] =
      ![4 * a ^ 3 * s, -4 * a ^ 3 * c, 0] := by
  funext i
  fin_cases i <;> simp [rotatedOne, bracket] <;> ring

end
end UnifiedTheory.LayerA.NonabelianYangMillsGlobal
