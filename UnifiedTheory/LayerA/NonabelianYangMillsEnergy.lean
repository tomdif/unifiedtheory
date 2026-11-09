/-
Algebraic ingredients for NONABELIAN_YANG_MILLS_ENERGY.md.
The maximum principle, Fourier integrals, and global finite-ODE continuation
are proved analytically in the note, not formalized by these lemmas.
-/
import UnifiedTheory.LayerA.NonabelianYangMillsLocal
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.NonabelianYangMillsEnergy
noncomputable section

open NonabelianYangMillsLocal

/-- The jet-level identity [D1,D2] phi = [F12,phi]. -/
theorem covariant_derivatives_commute_to_curvature {R : Type*} [Ring R]
    (a b ay bx phi px py pxy : R) :
    (pxy + comm bx phi + comm b px + comm a (py + comm b phi)) -
      (pxy + comm ay phi + comm a py + comm b (px + comm a phi)) =
      comm (bx - ay + comm a b) phi := by
  dsimp [NonabelianYangMillsLocal.comm]
  noncomm_ring

abbrev Vec := Fin 3 → ℝ

def dot (u v : Vec) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Imaginary-quaternion coordinates for the su(2) bracket. -/
def bracket (u v : Vec) : Vec :=
  ![2 * (u 1 * v 2 - u 2 * v 1),
    2 * (u 2 * v 0 - u 0 * v 2),
    2 * (u 0 * v 1 - u 1 * v 0)]

theorem dot_self_nonneg (u : Vec) : 0 ≤ dot u u := by
  dsimp [dot]
  nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]

theorem dot_bracket_skew (a u v : Vec) :
    dot (bracket a u) v = -dot u (bracket a v) := by
  simp [dot, bracket]
  ring

theorem gauge_term_orthogonal (f phi : Vec) : dot f (bracket f phi) = 0 := by
  simp [dot, bracket]
  ring

def covariantJet (a f df : Vec) : Vec := df + bracket a f

def covariantSecondJet (a da f df ddf : Vec) : Vec :=
  ddf + bracket da f + (2 : ℝ) • bracket a df + bracket a (bracket a f)

def curvatureHeatJet (a b ax b_y f fx fy fxx fyy phi : Vec) : Vec :=
  covariantSecondJet a ax f fx fxx + covariantSecondJet b b_y f fy fyy + bracket f phi

/-- Pointwise Bochner identity with all nonabelian jet terms present. -/
theorem curvature_bochner_identity (a b ax b_y f fx fy fxx fyy phi : Vec) :
    2 * dot f (curvatureHeatJet a b ax b_y f fx fy fxx fyy phi) -
      2 * (dot fx fx + dot f fxx + dot fy fy + dot f fyy) =
      -2 * (dot (covariantJet a f fx) (covariantJet a f fx) +
        dot (covariantJet b f fy) (covariantJet b f fy)) := by
  simp [dot, bracket, covariantJet, covariantSecondJet, curvatureHeatJet,
    Pi.add_apply, smul_eq_mul, Matrix.vecHead, Matrix.vecTail]
  ring

theorem curvature_bochner_nonpos (a b ax b_y f fx fy fxx fyy phi : Vec) :
    2 * dot f (curvatureHeatJet a b ax b_y f fx fy fxx fyy phi) -
      2 * (dot fx fx + dot f fxx + dot fy fy + dot f fyy) ≤ 0 := by
  rw [curvature_bochner_identity]
  nlinarith [dot_self_nonneg (covariantJet a f fx),
    dot_self_nonneg (covariantJet b f fy)]

def curvatureJet (a b ay bx : Vec) : Vec := bx - ay + bracket a b

def curvatureVariation (a b u v uy vx : Vec) : Vec :=
  vx - uy + bracket a v + bracket u b

/-- Curvature along a connection-space line has an exact quadratic expansion. -/
theorem curvature_line_expansion (a b ay bx u v uy vx : Vec) (t : ℝ) :
    curvatureJet (a + t • u) (b + t • v) (ay + t • uy) (bx + t • vx) =
      curvatureJet a b ay bx + t • curvatureVariation a b u v uy vx +
        t ^ 2 • bracket u v := by
  funext i
  fin_cases i <;>
    simp [curvatureJet, curvatureVariation, bracket, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- The pointwise quartic used by the energy line search. -/
theorem energy_line_expansion (f l c : Vec) (t : ℝ) :
    dot (f + t • l + t ^ 2 • c) (f + t • l + t ^ 2 • c) / 2 =
      dot f f / 2 + t * dot f l +
        t ^ 2 * (dot l l / 2 + dot f c) + t ^ 3 * dot l c +
        t ^ 4 * dot c c / 2 := by
  simp [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orthogonality property of P_N identifies projected gradient dissipation. -/
theorem projected_gradient_pairing (g p : E)
    (horth : inner (𝕜 := ℝ) (g - p) p = 0) :
    inner (𝕜 := ℝ) g p = ‖p‖ ^ 2 := by
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at horth
  linarith

theorem projected_gradient_dissipation (g p : E)
    (horth : inner (𝕜 := ℝ) (g - p) p = 0) :
    -inner (𝕜 := ℝ) g p = -‖p‖ ^ 2 := by
  rw [projected_gradient_pairing g p horth]

end Hilbert

theorem energy_defect_absorption (g r : ℝ) :
    -g ^ 2 + g * r ≤ -(g ^ 2) / 2 + r ^ 2 / 2 := by
  nlinarith [sq_nonneg (g - r)]

theorem perturbed_energy_dissipation (rate g r : ℝ)
    (h : rate ≤ -g ^ 2 + g * r) : rate + g ^ 2 / 2 ≤ r ^ 2 / 2 := by
  have hh := energy_defect_absorption g r
  linarith

/-- The integrated energy balance bounds the integrated squared speed. -/
theorem integrated_speed_bound (initial current speed : ℝ) (hcurrent : 0 ≤ current)
    (hbalance : current + speed = initial) : speed ≤ initial := by
  linarith

/-- Scalar final step after the time Cauchy--Schwarz estimate. -/
theorem excursion_squared_bound (distance time speed initial : ℝ)
    (ht : 0 ≤ time) (hs : speed ≤ initial)
    (hcauchy : distance ^ 2 ≤ time * speed) : distance ^ 2 ≤ time * initial := by
  exact hcauchy.trans (mul_le_mul_of_nonneg_left hs ht)

theorem accepted_step_energy_nonincrease (before after step normSq : ℝ)
    (hs : 0 ≤ step) (hn : 0 ≤ normSq)
    (haccept : after ≤ before - step * normSq / 2) : after ≤ before := by
  nlinarith [mul_nonneg hs hn]

end
end UnifiedTheory.LayerA.NonabelianYangMillsEnergy
