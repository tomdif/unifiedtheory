/- The quartic neutral transport has a controlled negative part.
A square completion retains the profile derivative and an exact boundary
derivative. Integrating that boundary term is a separate domain step. -/
import UnifiedTheory.Audit.KFCausalNeutralRadialActualObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalQuarticNeutralDefect
noncomputable section
open scoped ComplexConjugate
open KFCausalQuarticPlaneDomination (potential potentialSlope potential_positive potentialSlope_bound)

def potentialSecond (x : ℝ) : ℝ := 1+3*x^2
def connection (x : ℝ) : ℝ := potentialSlope x/(2*potential x)
def logCurvature (x : ℝ) : ℝ := potentialSecond x-(potentialSlope x)^2/potential x

theorem potentialSlope_derivative (x : ℝ) :
    HasDerivAt potentialSlope (potentialSecond x) x := by
  convert (hasDerivAt_id x).add ((hasDerivAt_id x).pow 3) using 1
  dsimp [potentialSlope,potentialSecond]
  ring

theorem connection_bound (x : ℝ) : |connection x| ≤ 1 := by
  unfold connection
  rw [abs_div,abs_of_pos (mul_pos (by norm_num) (potential_positive x))]
  exact (div_le_one (mul_pos (by norm_num) (potential_positive x))).mpr (potentialSlope_bound x)

theorem logCurvature_lower (x : ℝ) : -4*potential x ≤ logCurvature x := by
  have hp := potential_positive x
  have hb := mul_self_le_mul_self (abs_nonneg (potentialSlope x)) (potentialSlope_bound x)
  rw [← sq,sq_abs] at hb
  have hh : (potentialSlope x)^2/potential x ≤ 4*potential x := by
    apply (div_le_iff₀ hp).mpr
    nlinarith
  unfold logCurvature potentialSecond
  nlinarith [sq_nonneg x]

def direction (η L x : ℝ) (z z' : ℂ) : ℂ :=
  (η:ℂ)*Complex.I*z'+((L:ℂ)+(η:ℂ)*Complex.I)*(connection x:ℂ)*z
def firstDensity (η L x : ℝ) (z z' : ℂ) : ℝ :=
  L*potentialSlope x*‖z‖^2-2*η*potential x*(conj z*z').im
def secondDensity (η L x : ℝ) (z z' : ℂ) : ℝ :=
  4*η^2*potential x*‖z'‖^2-4*L*η*potentialSlope x*(conj z*z').im+
    (L^2-η^2)*potentialSecond x*‖z‖^2
def boundaryDensity (x : ℝ) (z z' : ℂ) : ℝ :=
  potentialSecond x*‖z‖^2+2*potentialSlope x*(conj z*z').re

theorem first_pairing (η L x : ℝ) (z z' : ℂ) :
    firstDensity η L x z z' = 2*potential x*(conj z*direction η L x z z').re := by
  have hp := (potential_positive x).ne'
  simp only [firstDensity,direction,connection,Complex.mul_re,Complex.mul_im,Complex.add_re,
    Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.conj_re,Complex.conj_im,Complex.sq_norm,Complex.normSq_apply]
  field_simp
  ring

theorem square_completion (η L x : ℝ) (z z' : ℂ) :
    secondDensity η L x z z'+2*η^2*boundaryDensity x z z' =
      4*potential x*‖direction η L x z z'‖^2+
        (L^2+η^2)*logCurvature x*‖z‖^2 := by
  have hp := (potential_positive x).ne'
  simp only [secondDensity,boundaryDensity,direction,connection,logCurvature,
    Complex.sq_norm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.add_re,
    Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.conj_re,Complex.conj_im]
  field_simp
  ring

theorem defect_lower (η L x : ℝ) (z z' : ℂ) :
    4*potential x*‖direction η L x z z'‖^2-
        4*(L^2+η^2)*potential x*‖z‖^2 ≤
      secondDensity η L x z z'+2*η^2*boundaryDensity x z z' := by
  rw [square_completion]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (logCurvature_lower x) (by positivity : 0 ≤ L^2+η^2))
    (sq_nonneg ‖z‖)
  nlinarith

#print axioms potentialSlope_derivative
#print axioms connection_bound
#print axioms logCurvature_lower
#print axioms first_pairing
#print axioms square_completion
#print axioms defect_lower
end
end UnifiedTheory.Audit.KFCausalQuarticNeutralDefect
