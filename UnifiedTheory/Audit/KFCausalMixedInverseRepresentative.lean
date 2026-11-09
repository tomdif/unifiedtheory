/- Exact inverse representatives of the physical mixed clock chart.
The inverse preserves null sets; L2 membership follows from the original
Hilbert vector and is not assumed for arbitrary weighted compositions. -/
import UnifiedTheory.Audit.KFCausalChargeRotatedSecondInput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalMixedInverseRepresentative
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Block Joint split)
open KFCausalPhysicalMixedCoordinates (mixedCoordinates)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorMixedRadial (clockMixed clockMixed_coe)
open KFCausalClockFloorMixedCoordinates (mixedWeight)
open KFCausalClockFloorMixedChart (mixedMap fiber fiber_quasiMeasurePreserving clockInverse_differentiable)
open KFCausalClockFloorPairedStraightening (clockInverse dilation clockInverse_continuous pair_symm_clock)
open KFCausalClockFloorSpectatorChart (forward backward backward_forward forward_backward)
open KFCausalClockFloorPairedChart (pair pair_preserves_volume pair_coordinate)
open KFCausalClockFloorFlow (coordinateHomeomorph)
open KFCausalClockFloorLpCoordinates (coordinate_quasiMeasurePreserving)
open KFCausalRegularizedLongitudinalChart (chartIso)

def mixedForward (ε : ℝ) (x : Block 2 × Block 4) : Block 2 × Block 4 :=
  (Real.exp (x.2 0/2) • x.1,forward ε x.2)

def inverseProfile (ε : ℝ) (ρ : Block 2 × Block 4 → ℂ)
    (x : Block 2 × Block 4) : ℂ :=
  (Real.sqrt (Real.exp (x.2 0)+ε):ℂ)*ρ (mixedForward ε x)

def chargeProfile (ε : ℝ) (ρ : Block 2 × Block 4 → ℂ) (x : Joint 2 4) : ℂ :=
  inverseProfile ε ρ (split 2 4 x)

variable (ε : ℝ) (hε : 0 < ε)

theorem clockInverse_forward (x : Block 4) : clockInverse ε hε (forward ε x)=x 0 :=
  (chartIso ε hε).symm_apply_apply _

theorem mixedMap_mixedForward (x : Block 2 × Block 4) :
    mixedMap ε hε (mixedForward ε x)=x := by
  simp only [mixedMap,mixedForward,dilation,clockInverse_forward,backward_forward,
    smul_smul,inv_mul_cancel₀ (Real.exp_ne_zero _),one_smul]

theorem mixedForward_mixedMap (x : Block 2 × Block 4) :
    mixedForward ε (mixedMap ε hε x)=x := by
  change (Real.exp (clockInverse ε hε x.2/2) • ((dilation ε hε x.2)⁻¹ • x.1),
    forward ε (backward ε hε x.2))=x
  simp only [dilation,smul_smul,mul_inv_cancel₀ (Real.exp_ne_zero _),one_smul,forward_backward]

theorem mixedForward_factor : mixedForward ε =
    fiber (clockInverse ε hε) (clockInverse_continuous ε hε) ∘
      (fun x => pair (coordinateHomeomorph ε hε (pair.symm x))) := by
  funext x
  have hp := pair_coordinate ε hε (pair.symm x)
  simp only [pair_symm_clock,MeasurableEquiv.apply_symm_apply] at hp
  simp only [Function.comp_apply,hp,fiber,mixedForward]
  congr 1
  rw [smul_smul,← Real.exp_add]
  congr 2
  rw [clockInverse_forward]
  ring

include hε in
theorem mixedForward_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (mixedForward ε) volume volume := by
  rw [mixedForward_factor ε hε]
  exact (fiber_quasiMeasurePreserving _ (clockInverse_differentiable ε hε)).comp
    (pair_preserves_volume.quasiMeasurePreserving.comp
      ((coordinate_quasiMeasurePreserving ε hε).comp
        pair_preserves_volume.symm.quasiMeasurePreserving))

theorem inverse_representative (f : Hilbert) (ρ : Block 2 × Block 4 → ℂ)
    (hf : clockMixed ε hε f =ᵐ[volume] ρ) :
    mixedCoordinates f =ᵐ[volume] inverseProfile ε ρ := by
  filter_upwards [(mixedForward_quasiMeasurePreserving ε hε).ae (clockMixed_coe ε hε f),
    (mixedForward_quasiMeasurePreserving ε hε).ae hf] with x hx hr
  change clockMixed ε hε f (mixedForward ε x)=
    mixedWeight ε hε (mixedForward ε x)*
      mixedCoordinates f (mixedMap ε hε (mixedForward ε x)) at hx
  rw [mixedMap_mixedForward ε hε x] at hx
  have hn : (Real.sqrt (Real.exp (x.2 0)+ε):ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (add_pos (Real.exp_pos _) hε)).ne'
  change clockMixed ε hε f (mixedForward ε x)=ρ (mixedForward ε x) at hr
  rw [hr] at hx
  simp only [mixedWeight,mixedForward,clockInverse_forward] at hx
  change ρ (mixedForward ε x)=(Real.sqrt (Real.exp (x.2 0)+ε):ℂ)⁻¹*mixedCoordinates f x at hx
  unfold inverseProfile
  rw [hx,← mul_assoc,mul_inv_cancel₀ hn,one_mul]

theorem charge_representative (f : Hilbert) (ρ : Block 2 × Block 4 → ℂ)
    (hf : clockMixed ε hε f =ᵐ[volume] ρ) :
    chargeCoordinates f =ᵐ[volume] chargeProfile ε ρ :=
  KFCausalChargeRotatedSecondInput.charge_of_mixed f _ (inverse_representative ε hε f ρ hf)

theorem chargeProfile_memLp (f : Hilbert) (ρ : Block 2 × Block 4 → ℂ)
    (hf : clockMixed ε hε f =ᵐ[volume] ρ) : MemLp (chargeProfile ε ρ) 2 :=
  (Lp.memLp (chargeCoordinates f)).ae_eq (charge_representative ε hε f ρ hf)

#print axioms clockInverse_forward
#print axioms mixedMap_mixedForward
#print axioms mixedForward_mixedMap
#print axioms mixedForward_factor
#print axioms mixedForward_quasiMeasurePreserving
#print axioms inverse_representative
#print axioms charge_representative
#print axioms chargeProfile_memLp
end
end UnifiedTheory.Audit.KFCausalMixedInverseRepresentative
