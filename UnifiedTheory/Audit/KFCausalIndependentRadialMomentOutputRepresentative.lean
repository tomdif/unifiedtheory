/- Exact half/full output representatives for the actual radial/source/field
moment states. The physical baseline is supplied by its proved Fourier
transform and clock chart; existing bounded multiplier actions then give
the actual outputs for every finite polynomial and all moment orders. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialShiftedBaseline

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialMomentOutputRepresentative
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (split)
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalIndependentRadialMomentExponential
  (halfState fullState baselineHalfOutput baselineOutput multiplierAction_clockMixed)
open KFCausalIndependentRadialShiftedBaseline (baseline_half_coe baseline_full_coe)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalIndependentRadialShiftedField (coefficient)
open KFCausalIndependentRadialMomentInput (numerator)
open KFCausalTwoShearClockQuotient (shift)

variable (ε h a W wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (m n : ℕ) (hε : 0<ε) (hh : h≠0) (ha : 0<a) (hL : 1≤wL)
  (hR : 1≤wR) (hW : wL≤W) (hb : |h|≤ε/10)
local notation "α" => groundWidth h
local notation "c" => momentumScale h

theorem half_coe (k : ℕ) :
    clockMixed ε hε (halfState ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k) =ᵐ[volume]
      fun x : Product => coefficient ε h α wL wR c (shift (h/2) (x.2 0:ℂ))
        ((split 2 4).symm x)^k *
          numerator ε a α wL wR c C p b P m n (shift (h/2) (x.2 0:ℂ))
            ((split 2 4).symm x) := by
  have hWp : 0<W := (zero_lt_one.trans_le hL).trans_le hW
  have hs : |-h/2|≤|h| := by
    rw [abs_div,abs_neg,show |(2:ℝ)|=2 by norm_num]
    linarith [abs_nonneg h]
  have ht := multiplierAction_clockMixed ε h a W wL wR C p b P m n
    hε hh ha hL hR hW hb k (-h/2) hs (baselineHalfOutput ε h a W hε hh ha hb)
  filter_upwards [ht,baseline_half_coe ε h a W wL wR hε hh ha hWp
    (zero_lt_one.trans_le hL) (zero_lt_one.trans_le hR) hb] with x hx hxbase
  simp only [halfState] at *
  rw [hx,hxbase]
  have he : (x.2 0:ℂ)+(-h/2:ℝ)*Complex.I=shift (h/2) (x.2 0:ℂ) := by
    unfold shift
    push_cast
    ring
  rw [he]
  exact KFCausalIndependentRadialMomentMultiplier.multiplier_mul_baseline
    ε h a α W wL wR c C p b P m n k hWp.ne' _ _

theorem full_coe (k : ℕ) :
    clockMixed ε hε (fullState ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k) =ᵐ[volume]
      fun x : Product => coefficient ε h α wL wR c (shift h (x.2 0:ℂ))
        ((split 2 4).symm x)^k *
          numerator ε a α wL wR c C p b P m n (shift h (x.2 0:ℂ))
            ((split 2 4).symm x) := by
  have hWp : 0<W := (zero_lt_one.trans_le hL).trans_le hW
  have ht := multiplierAction_clockMixed ε h a W wL wR C p b P m n
    hε hh ha hL hR hW hb k (-h) (by simp) (baselineOutput ε h a W hε hh ha hb)
  filter_upwards [ht,baseline_full_coe ε h a W wL wR hε hh ha hWp
    (zero_lt_one.trans_le hL) (zero_lt_one.trans_le hR) hb] with x hx hxbase
  simp only [fullState] at *
  rw [hx,hxbase]
  have he : (x.2 0:ℂ)+(-h:ℝ)*Complex.I=shift h (x.2 0:ℂ) := by
    unfold shift
    push_cast
    ring
  rw [he]
  exact KFCausalIndependentRadialMomentMultiplier.multiplier_mul_baseline
    ε h a α W wL wR c C p b P m n k hWp.ne' _ _

#print axioms half_coe
#print axioms full_coe
end
end UnifiedTheory.Audit.KFCausalIndependentRadialMomentOutputRepresentative
