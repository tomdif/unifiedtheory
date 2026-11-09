/- Classical L2 directional derivatives of actual charge representatives
give original symmetric momentum graphs. This retains the maximal
Fourier relation, with no assumed translation derivative. -/
import UnifiedTheory.Audit.KFCausalSymmetricMomentumGraphEquivalence
import UnifiedTheory.Audit.KFCausalL2DirectionalDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalChargeProfileMomentumGraph
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalSymmetricMomentumCoordinates (symmetricDirection symmetricVector)
open KFCausalDirectionalTranslationMomentum (multiplier)

theorem derivative_graph (h : ℝ) (hh : h ≠ 0) (i : Fin 2) (f d : Hilbert)
    (F G : Joint 2 4 → ℂ) (hf : chargeCoordinates f =ᵐ[volume] F)
    (hd : chargeCoordinates d =ᵐ[volume] G)
    (hder : ∀ x, HasDerivAt (fun t : ℝ => F (x+t • symmetricVector i)) (G x) 0) :
    (f,(-Complex.I*(h:ℂ)) • d) ∈ (transverseMomentum h (symmetricDirection i)).graph := by
  have hF : MemLp F 2 volume := (memLp_congr_ae hf).mp (Lp.memLp (chargeCoordinates f))
  have hG : MemLp G 2 volume := (memLp_congr_ae hd).mp (Lp.memLp (chargeCoordinates d))
  have hfe : hF.toLp F=chargeCoordinates f := Lp.ext (hF.coeFn_toLp.trans hf.symm)
  have hge : hG.toLp G=chargeCoordinates d := Lp.ext (hG.coeFn_toLp.trans hd.symm)
  apply (KFCausalSymmetricMomentumGraphEquivalence.symmetric_graph_iff h hh i _ _).mpr
  rw [map_smul,← hfe,← hge]
  apply (KFCausalUnitaryRealMultiplier.realPullback_graph _ _ _ _ _).mpr
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ))
    ((Lp.fourierTransformₗᵢ (Joint 2 4) ℂ) (hG.toLp G)),
    KFCausalL2DirectionalDerivative.derivative_fourier F G (symmetricVector i) hF hG hder]
      with x hx hdx
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul,hdx,multiplier,Complex.ofReal_mul,Complex.ofReal_ofNat]
  calc
    _ = -(Complex.I*Complex.I)*(2*(Real.pi:ℂ)*(h:ℂ)*(inner ℝ x (symmetricVector i):ℂ)*
      ((Lp.fourierTransformₗᵢ (Joint 2 4) ℂ) (hF.toLp F)) x) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

#print axioms derivative_graph
end
end UnifiedTheory.Audit.KFCausalChargeProfileMomentumGraph
