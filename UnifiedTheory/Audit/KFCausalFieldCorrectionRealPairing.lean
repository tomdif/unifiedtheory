/- Real field multiples of one complex wavefunction cancel the imaginary
clock coefficient in the real pairing. This remains exact for arbitrary
complex superpositions and gives a quadratic shift estimate for the
actual derivative correction. -/
import UnifiedTheory.Audit.KFCausalRealShearCorrectionBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFieldCorrectionRealPairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower fieldPower_graph)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope fieldSlope)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (shearCorrection)
open UnifiedTheory.Audit.KFCausalFieldShearResponseCorrection (derivativeCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalRealShearCorrectionBound

theorem mixed_real_inner (a b : ℝ) (z w : ℂ) :
    (inner ℂ ((a:ℂ)*w) (z*((b:ℂ)*w))).re = z.re*a*b*‖w‖^2 := by
  have he : inner ℂ ((a:ℂ)*w) (z*((b:ℂ)*w)) =
      (a:ℂ)*(z*(b:ℂ))*(‖w‖:ℂ)^2 := by
    change inner ℂ ((a:ℂ) • w) (z • ((b:ℂ) • w)) = _
    rw [inner_smul_left,inner_smul_right,inner_smul_right,inner_self_eq_norm_sq_to_K,Complex.conj_ofReal]
    change (a:ℂ)*(z*((b:ℂ)*(‖w‖:ℂ)^2)) = _
    ring
  rw [he,← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,sub_zero,add_zero]
  ring

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "D" => defectOperator ε hε
local notation "C" => shearCorrection ε hε h hb
local notation "A" => realCorrection ε hε h hb

theorem common_phase_pairing (a b : Configuration → ℝ) (g u d : Hilbert)
    (hu : u =ᵐ[volume] fun x => (a x:ℂ)*g x)
    (hd : d =ᵐ[volume] fun x => (b x:ℂ)*g x) :
    (inner ℂ u (C d)).re = (inner ℂ u (A d)).re := by
  have h1 := integral_re (L2.integrable_inner (𝕜 := ℂ) u (C d))
  have h2 := integral_re (L2.integrable_inner (𝕜 := ℂ) u (A d))
  change (∫ x, (inner ℂ (u x) (C d x)).re) = (∫ x, inner ℂ (u x) (C d x)).re at h1
  change (∫ x, (inner ℂ (u x) (A d x)).re) = (∫ x, inner ℂ (u x) (A d x)).re at h2
  rw [L2.inner_def,L2.inner_def,← h1,← h2]
  apply integral_congr_ae
  filter_upwards [hu,hd,shearCorrection_coe ε hε h hb d,realCorrection_coe ε hε h hb d]
    with x hu hd hc ha
  rw [hu,hc,ha,hd,mixed_real_inner,mixed_real_inner]
  simp only [Complex.div_ofReal_re,Complex.sub_re,Complex.ofReal_re]

theorem common_phase_bound (a b : Configuration → ℝ) (g u d : Hilbert)
    (hu : u =ᵐ[volume] fun x => (a x:ℂ)*g x)
    (hd : d =ᵐ[volume] fun x => (b x:ℂ)*g x) :
    |derivativeCorrection ε hε h hb u d| ≤ (20*h^2/ε^3)*‖u‖*‖D (D (D d))‖ := by
  unfold derivativeCorrection
  rw [common_phase_pairing ε hε h hb a b g u d hu hd,abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc
    _ ≤ 2*(‖u‖*‖A d‖) := mul_le_mul_of_nonneg_left
      ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)) (by norm_num)
    _ ≤ 2*(‖u‖*((10*h^2/ε^3)*‖D (D (D d))‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (realCorrection_bound ε hε h hb d) (norm_nonneg u)) (by norm_num)
    _ = _ := by ring

theorem field_correction_bound (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (g u d : Hilbert)
    (hu : (g,u) ∈ (fieldPower l i).graph)
    (hd : d =ᵐ[volume] fun x => powerSlope l i x*g x) :
    |derivativeCorrection ε hε h hb u d| ≤ (20*h^2/ε^3)*‖u‖*‖D (D (D d))‖ := by
  apply common_phase_bound ε hε h hb
    (fun x => (l x.2)^(i.val+1))
    (fun x => (i.val+1:ℕ)*(l x.2)^i.val*fieldSlope l x.2) g u d
  · simpa only [Complex.ofReal_pow] using (fieldPower_graph l i g u).mp hu
  · filter_upwards [hd] with x hx
    rw [hx]
    simp only [powerSlope,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast]

#print axioms mixed_real_inner
#print axioms common_phase_pairing
#print axioms common_phase_bound
#print axioms field_correction_bound
end
end UnifiedTheory.Audit.KFCausalFieldCorrectionRealPairing
