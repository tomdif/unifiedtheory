/- Identification of the relative virial with generator expectations when
both actual endpoint graphs are supplied. Endpoint domain propagation is
not claimed or inserted into the unconditional relative-balance theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeRelativeVirial
import UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSqueezeGeneratorBalance
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport)
open UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator (squeezeMomentum squeeze_graph_derivative)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEhrenfest (characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeNormalizedRate (signedVariation)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeRelativeVirial (increment relative_virial_derivative)

theorem generator_pairing_derivative (h : ℝ) (hne : h ≠ 0) (f z : Hilbert)
    (hfz : (f,z) ∈ (squeezeMomentum h).graph) :
    HasDerivAt (fun a => inner ℂ f (transport a f)) (coefficient h*inner ℂ f z) 0 := by
  have hd := (hasDerivAt_const (0:ℝ) f).inner ℂ ((squeeze_graph_derivative h hne f z).mp hfz)
  simpa only [inner_smul_right,inner_zero_left,add_zero,coefficient,div_eq_mul_inv,
    one_mul,Complex.ofReal_inv,Complex.ofReal_one] using hd

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "U" => evolution ε hε h hne hh m g k

theorem endpoint_generator_balance (s b c : ℝ) (w : V) (zb zc : Hilbert)
    (hb : (U s b (J w),zb) ∈ (squeezeMomentum h).graph)
    (hc : (U s c (J w),zc) ∈ (squeezeMomentum h).graph) :
    (∫ t in b..c, (signedVariation ε hε h hne hh m g k s t w : ℂ)) =
      inner ℂ (U s c (J w)) zc-inner ℂ (U s b (J w)) zb := by
  have hd := (generator_pairing_derivative h hne _ _ hc).sub
    (generator_pairing_derivative h hne _ _ hb)
  have he := (relative_virial_derivative ε hε h hne hh m g k s b c w).unique hd
  have hcoef : coefficient h ≠ 0 := by
    unfold coefficient
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (one_div_ne_zero hne))
  apply mul_left_cancel₀ hcoef
  exact he.trans (by ring)

#print axioms generator_pairing_derivative
#print axioms endpoint_generator_balance
end
end UnifiedTheory.Audit.KFCausalClockFloorSqueezeGeneratorBalance
