/-
  Support for GRAVITY_FROM_CLOCK_CONSTRAINTS.md. The metric phase space,
  functional derivatives, hypersurface-deformation algebra, and microscopic
  limit are separate suppliers. This module does not prove emergent gravity.
-/
import UnifiedTheory.Audit.KFCausalMicroscopicSpinTwo
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGravityConstraint
noncomputable section

theorem complete_tensor_trace_channel (x y z : ℝ) :
    (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 / 3 +
      (2 / 3 : ℝ) * (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 =
      (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 := by ring

theorem positive_band_has_no_linear_slope (f : ℝ → ℝ) (slope : ℝ)
    (hzero : f 0 = 0) (hpositive : ∀ x, 0 ≤ f x)
    (hd : HasDerivAt f slope 0) : slope = 0 := by
  have hm : IsMinOn f Set.univ 0 := by
    intro x _
    simpa [hzero] using hpositive x
  exact (hm.isLocalMin Filter.univ_mem).hasDerivAt_eq_zero hd

theorem pairing_frequency_identity (J r g ell : ℝ) :
    ((J + r + g * ell) / 2) ^ 2 - ((r + g * ell - J) / 2) ^ 2 =
      J * (r + g * ell) := by ring

theorem naive_hardcore_vacuum_is_higher (J : ℝ) (hJ : 0 < J) :
    J / 4 < 6 * J / 4 := by linarith

theorem finite_occupation_root_error (x s : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (he : s ^ 2 = 1 - x) : 1 - s ≤ x := by
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1)]

theorem curvature_trace_contraction (x y z u v w lam : ℝ) :
    (x - lam * (x + y + z)) * (v + w) +
      (y - lam * (x + y + z)) * (u + w) +
      (z - lam * (x + y + z)) * (u + v) =
      (1 - 2 * lam) * (x + y + z) * (u + v + w) - (x * u + y * v + z * w) := by
  ring

theorem trace_closure_fixes_dewitt_coefficient (a b lam : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 2 * (a * b) * (1 - 2 * lam) = 0) :
    lam = 1 / 2 := by
  have hp : 0 < a * b := mul_pos ha hb
  nlinarith

theorem independent_generators_fix_coefficients (cg cm anomaly : ℝ)
    (h : ∀ x y z : ℝ, (cg - 1) * x + (cm - 1) * y + anomaly * z = 0) :
    cg = 1 ∧ cm = 1 ∧ anomaly = 0 := by
  have hx := h 1 0 0
  have hy := h 0 1 0
  have hz := h 0 0 1
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem common_clock_matches_wave_speeds (a b u v : ℝ)
    (hg : a * b = 1) (hm : u * v = 1) : u * v = a * b := by rw [hg, hm]

theorem extrinsic_momentum_trace (x y z : ℝ) :
    (x - (x + y + z)) + (y - (x + y + z)) + (z - (x + y + z)) =
      -2 * (x + y + z) := by ring

def normSquared (x y z xy yz zx : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2 + 2 * (xy ^ 2 + yz ^ 2 + zx ^ 2)

theorem dewitt_extrinsic_curvature_identity (x y z xy yz zx : ℝ) :
    normSquared (x - (x + y + z)) (y - (x + y + z)) (z - (x + y + z)) xy yz zx -
      (-2 * (x + y + z)) ^ 2 / 2 =
      normSquared x y z xy yz zx - (x + y + z) ^ 2 := by
  unfold normSquared
  ring

theorem gravitational_legendre_identity (x y z xy yz zx : ℝ) :
    2 * (x * (x - (x + y + z)) + y * (y - (x + y + z)) +
      z * (z - (x + y + z)) + 2 * (xy ^ 2 + yz ^ 2 + zx ^ 2)) -
      (normSquared x y z xy yz zx - (x + y + z) ^ 2) =
      normSquared x y z xy yz zx - (x + y + z) ^ 2 := by
  unfold normSquared
  ring

theorem scalar_legendre_identity (rho lapse u velocity : ℝ)
    (hr : rho ≠ 0) (hN : lapse ≠ 0) (hu : u ≠ 0) :
    (rho * velocity / (lapse * u)) * velocity -
      lapse * u * (rho * velocity / (lapse * u)) ^ 2 / (2 * rho) =
      rho * velocity ^ 2 / (2 * lapse * u) := by
  field_simp
  ring

theorem newton_poisson_coefficient (b laplacian density : ℝ)
    (hb : b ≠ 0) (hc : b * (4 * laplacian) = density) :
    laplacian = density / (4 * b) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) hb)).mpr
  nlinarith

theorem soft_exchange_fixes_universal_coupling (gA gB momentum : ℝ)
    (hp : momentum ≠ 0) (hw : (gA - gB) * momentum = 0) : gA = gB := by
  have h := (mul_eq_zero.mp hw).resolve_right hp
  linarith

#print axioms complete_tensor_trace_channel
#print axioms positive_band_has_no_linear_slope
#print axioms pairing_frequency_identity
#print axioms naive_hardcore_vacuum_is_higher
#print axioms finite_occupation_root_error
#print axioms curvature_trace_contraction
#print axioms trace_closure_fixes_dewitt_coefficient
#print axioms independent_generators_fix_coefficients
#print axioms common_clock_matches_wave_speeds
#print axioms extrinsic_momentum_trace
#print axioms dewitt_extrinsic_curvature_identity
#print axioms gravitational_legendre_identity
#print axioms scalar_legendre_identity
#print axioms newton_poisson_coefficient
#print axioms soft_exchange_fixes_universal_coupling

end
end UnifiedTheory.Audit.KFCausalGravityConstraint
