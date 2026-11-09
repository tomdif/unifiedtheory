/- Exact relative squeeze virial along the actual full quantum evolution.
The derivative of a difference of bounded characteristics is established
without assuming either endpoint has an unbounded-generator moment. -/
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeNormalizedRate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSqueezeRelativeVirial
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (FormSpace)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEhrenfest (characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeBalance (bounded_squeeze_integral)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeNormalizedRate
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "χ" => characteristic ε hε h hne hh m g k

def increment (a s b c : ℝ) (w : V) : ℂ := χ a s c w-χ a s b w

theorem increment_factorization (a s b c : ℝ) (w : V) : increment ε hε h hne hh m g k a s b c w =
    (a:ℂ)*(∫ t in b..c, normalizedRate ε hε h hne hh m g k a s t w) := by
  unfold increment
  rw [← bounded_squeeze_integral]
  simp only [outputRate_normalized,intervalIntegral.integral_const_mul]

theorem increment_zero (s b c : ℝ) (w : V) : increment ε hε h hne hh m g k 0 s b c w = 0 := by
  rw [increment_factorization,Complex.ofReal_zero,zero_mul]

theorem relative_slope_balance (s b c : ℝ) (w : V) :
    Tendsto (fun a : ℝ => a⁻¹ • increment ε hε h hne hh m g k a s b c w) (𝓝[≠] 0)
      (𝓝 (coefficient h*∫ t in b..c, (signedVariation ε hε h hne hh m g k s t w : ℂ))) := by
  have he : (fun a : ℝ => a⁻¹ • increment ε hε h hne hh m g k a s b c w) =ᶠ[𝓝[≠] 0]
      fun a => ∫ t in b..c, normalizedRate ε hε h hne hh m g k a s t w := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hane : a ≠ 0 := ha
    rw [increment_factorization,Complex.real_smul,Complex.ofReal_inv,← mul_assoc,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hane),one_mul]
  exact ((normalizedIntegral_limit ε hε h hne hh m g k s b c w).mono_left nhdsWithin_le_nhds).congr' he.symm

theorem relative_virial_derivative (s b c : ℝ) (w : V) :
    HasDerivAt (fun a => increment ε hε h hne hh m g k a s b c w)
      (coefficient h*∫ t in b..c, (signedVariation ε hε h hne hh m g k s t w : ℂ)) 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add,increment_zero,sub_zero] using
    relative_slope_balance ε hε h hne hh m g k s b c w

#print axioms increment_factorization
#print axioms increment_zero
#print axioms relative_slope_balance
#print axioms relative_virial_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorSqueezeRelativeVirial
