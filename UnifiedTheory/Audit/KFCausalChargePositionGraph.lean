/- The natural momentum graph in an antisymmetric charge coordinate is
the original position graph after undoing the partial Fourier transform.
The derivative is identified almost everywhere without smoothness of the
state or a preassigned position moment. -/
import UnifiedTheory.Audit.KFCausalChargePositionPhase
import UnifiedTheory.Audit.KFCausalSelfAdjointMultiplierIdentification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalChargePositionGraph
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (FrequencyHilbert)
open UnifiedTheory.Audit.KFCausalChargePositionPhase
open UnifiedTheory.Audit.KFCausalFourierTranslation (translation)
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum

theorem inverse_momentum_graph_coe (h : ℝ) (hh : h ≠ 0) (a : Block 2)
    (f g : JointHilbert 2 4) (hfg : (f,g) ∈ (spectralMomentum h (leftVector a)).graph) :
    chargeEuclidean.symm g =ᵐ[volume] fun x =>
      ((2*Real.pi*h*inner ℝ (split 2 4 (modeIsometry x)).1 (-a):ℝ):ℂ)*(chargeEuclidean.symm f) x := by
  have hd := ((chargeEuclidean.symm : JointHilbert 2 4 →L[ℂ] FrequencyHilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((spectralMomentum_graph_derivative h hh (leftVector a) f g).mp hfg)
  change HasDerivAt (fun t => chargeEuclidean.symm (translation (t • leftVector a) f))
    (chargeEuclidean.symm ((Complex.I/(h:ℂ)) • g)) 0 at hd
  rw [map_smul] at hd
  have hr := KFCausalLpDerivativeRepresentative.derivative_representative _ _ _ _
    (fun t => inverse_directional_coe a t f) hd
    (fun x => phase_derivative (-a) (split 2 4 (modeIsometry x)).1 ((chargeEuclidean.symm f) x))
  filter_upwards [hr,Lp.coeFn_smul (Complex.I/(h:ℂ)) (chargeEuclidean.symm g)] with x hx hs
  rw [hs] at hx
  simp only [Pi.smul_apply,smul_eq_mul] at hx
  have he := congrArg (fun z : ℂ => (-Complex.I*(h:ℂ))*z) hx
  dsimp only at he
  have hi : (-Complex.I*(h:ℂ))*(Complex.I/(h:ℂ)) = 1 := by
    rw [mul_comm,KFCausalUnitaryMomentumEvolution.inverse_coefficient h hh]
  rw [← mul_assoc,hi,one_mul] at he
  rw [he]
  push_cast
  ring_nf
  norm_num [Complex.I_sq]

#print axioms inverse_momentum_graph_coe

end
end UnifiedTheory.Audit.KFCausalChargePositionGraph
