/- The actual bounded inverse clock half commutes with the narrow partial
Fourier unitary on all L2 vectors. The paired coordinate representative and
the existing spectator-multiplier commutation prove the identification.
These are the narrow coordinates, not the distinct charge coordinates. -/
import UnifiedTheory.Audit.KFCausalVacuumMixedClockNormalization
import UnifiedTheory.Audit.KFCausalNarrowFourierGeneralCoordinates
import UnifiedTheory.Audit.KFCausalPartialFourierMultiplier
import UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNarrowFourierInverseHalf
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open KFCausalNarrowFourierGeneralCoordinates
open KFCausalNarrowFourierCoordinates (pairedCoordinates mixedCoordinates)
open KFCausalPartialFourier (leftFourier)
open KFCausalPartialFourierMultiplier
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalVacuumMixedClockNormalization (inverseHalf)

variable (ε : ℝ) (hε : 0 < ε)

def symbol (v : Block 4) : ℂ := (Real.sqrt ε:ℂ)*inverseHalf ε (v 0)

theorem symbol_measurable : Measurable (symbol ε) := by
  unfold symbol inverseHalf
  fun_prop

include hε in
theorem symbol_bound (v : Block 4) : ‖symbol ε v‖ ≤ 1 := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hv : 0 < Real.sqrt (Real.exp (v 0)+ε) := Real.sqrt_pos.mpr (by positivity)
  have hb := KFCausalClockFloorClockHalf.inverseWeight_bound ε hε (v 0,0)
  change (Real.sqrt (Real.exp (v 0)+ε))⁻¹ ≤ (Real.sqrt ε)⁻¹ at hb
  simp only [symbol,inverseHalf,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hs,abs_of_pos hv]
  exact (mul_le_mul_of_nonneg_left hb hs.le).trans_eq (mul_inv_cancel₀ hs.ne')

def inverseProduct : ProductHilbert 2 4 →L[ℂ] ProductHilbert 2 4 :=
  (Real.sqrt ε:ℂ)⁻¹ • rightMultiplier 2 4 (symbol ε) (symbol_measurable ε) (symbol_bound ε hε)

theorem inverseProduct_coe (f : ProductHilbert 2 4) :
    inverseProduct ε hε f =ᵐ[volume] fun z => inverseHalf ε (z.2 0)*f z := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt ε:ℂ)⁻¹
    (rightMultiplier 2 4 (symbol ε) (symbol_measurable ε) (symbol_bound ε hε) f),
    rightMultiplier_coe 2 4 (symbol ε) (symbol_measurable ε) (symbol_bound ε hε) f]
      with z hs hr
  change ((Real.sqrt ε:ℂ)⁻¹ • rightMultiplier 2 4 (symbol ε)
    (symbol_measurable ε) (symbol_bound ε hε) f) z = _
  rw [hs,Pi.smul_apply,smul_eq_mul,hr]
  unfold symbol
  have hn : (Real.sqrt ε:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hε).ne'
  rw [← mul_assoc,← mul_assoc,inv_mul_cancel₀ hn,one_mul]

theorem inverseProduct_fourier (f : ProductHilbert 2 4) :
    leftFourier 2 4 (inverseProduct ε hε f) =
      inverseProduct ε hε (leftFourier 2 4 f) := by
  change leftFourier 2 4 ((Real.sqrt ε:ℂ)⁻¹ • rightMultiplier 2 4 _ _ _ f) = _
  rw [map_smul,leftFourier_commutes]
  rfl

theorem paired_inverse (f : Hilbert) :
    pairedCoordinates (inverseL ε hε f) = inverseProduct ε hε (pairedCoordinates f) := by
  have hi : inverseL ε hε f =ᵐ[volume] fun x => inverseHalf ε x.1*f x :=
    KFCausalClockFloorClockHalf.inverseAction_coe ε hε f
  have hp := pairedChart_preserves_volume.symm.quasiMeasurePreserving.ae hi
  apply Lp.ext
  filter_upwards [pairedCoordinates_coe (inverseL ε hε f),pairedCoordinates_coe f,
    inverseProduct_coe ε hε (pairedCoordinates f),hp] with z hz hf hr hi
  simp only [pairedChart_symm] at hi
  rw [hz,hr,hf]
  exact hi

theorem mixed_inverse (f : Hilbert) :
    mixedCoordinates (inverseL ε hε f) = inverseProduct ε hε (mixedCoordinates f) := by
  change leftFourier 2 4 (pairedCoordinates (inverseL ε hε f)) = _
  rw [paired_inverse,inverseProduct_fourier]
  rfl

theorem mixed_inverse_coe (f : Hilbert) :
    mixedCoordinates (inverseL ε hε f) =ᵐ[volume]
      fun z => inverseHalf ε (z.2 0)*(mixedCoordinates f) z := by
  rw [mixed_inverse]
  exact inverseProduct_coe ε hε _

#print axioms symbol_measurable
#print axioms symbol_bound
#print axioms inverseProduct_coe
#print axioms inverseProduct_fourier
#print axioms paired_inverse
#print axioms mixed_inverse
#print axioms mixed_inverse_coe
end
end UnifiedTheory.Audit.KFCausalNarrowFourierInverseHalf
