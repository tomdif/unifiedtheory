/- The five-coordinate partial Fourier transform diagonalizes every
clock-preserving translation in the actual mixed representation. Its
generator identity applies to full natural momentum graphs. -/
import UnifiedTheory.Audit.KFCausalChargeTransverseSplit
import UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalChargeDualMomentum
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit
open UnifiedTheory.Audit.KFCausalPartialFourier (leftFourier)
open UnifiedTheory.Audit.KFCausalPartialFourierTranslation
open UnifiedTheory.Audit.KFCausalFourierTranslation (translation translation_coe shift_preserves_volume phase)
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum

def transverseBlock (v : Joint 2 4) : Block 5 := (split 5 1 (repackIsometry v)).1

theorem transverseBlock_smul (t : ℝ) (v : Joint 2 4) : transverseBlock (t • v) = t • transverseBlock v := by
  ext i
  simp [transverseBlock,split_fst]

theorem split_repack_add (v : Joint 2 4) (hv : v (.inr 0) = 0) (x : Joint 2 4) :
    split 5 1 (repackIsometry (x+v)) =
      ((split 5 1 (repackIsometry x)).1+transverseBlock v,(split 5 1 (repackIsometry x)).2) := by
  rw [map_add]
  ext i
  · simp [transverseBlock,split_fst]
  · fin_cases i
    simp [split_snd,repack_clock,hv]

theorem pull_coordinates_coe (f : ProductHilbert 5 1) :
    repackPullback (coordinates 5 1 f) =ᵐ[volume] fun x => f (split 5 1 (repackIsometry x)) := by
  filter_upwards [repackPullback_coe (coordinates 5 1 f),
    repack_preserves.quasiMeasurePreserving.ae (coordinates_coe 5 1 f)] with x hr hc
  exact hr.trans hc

theorem pull_coordinates_translation (v : Joint 2 4) (hv : v (.inr 0) = 0) (f : ProductHilbert 5 1) :
    translation v (repackPullback (coordinates 5 1 f)) =
      repackPullback (coordinates 5 1 (leftTranslation 5 1 (transverseBlock v) f)) := by
  apply Lp.ext
  filter_upwards [translation_coe v (repackPullback (coordinates 5 1 f)),
    (shift_preserves_volume v).quasiMeasurePreserving.ae (pull_coordinates_coe f),
    pull_coordinates_coe (leftTranslation 5 1 (transverseBlock v) f),
    repack_preserves.quasiMeasurePreserving.ae ((split_preserves_volume 5 1).quasiMeasurePreserving.ae
      (leftTranslation_coe 5 1 (transverseBlock v) f))] with x ht hf hg hl
  change (repackPullback (coordinates 5 1 f)) (x+v) = f (split 5 1 (repackIsometry (x+v))) at hf
  rw [ht,hf,hg,hl,split_repack_add v hv]

theorem transverseCoordinates_translation (v : Joint 2 4) (hv : v (.inr 0) = 0) (f : JointHilbert 2 4) :
    transverseCoordinates (translation v f) = leftTranslation 5 1 (transverseBlock v) (transverseCoordinates f) := by
  apply (coordinates 5 1).injective
  apply repackPullback.injective
  rw [transverseCoordinates_inverse,← pull_coordinates_translation v hv,transverseCoordinates_inverse]

theorem dualMixed_translation_coe (v : Joint 2 4) (hv : v (.inr 0) = 0) (f : JointHilbert 2 4) :
    dualMixed (translation v f) =ᵐ[volume]
      fun x => phase (transverseBlock v) (split 5 1 x).1*(dualMixed f) x := by
  have he : dualMixed (translation v f) =
      coordinates 5 1 (leftPhase 5 1 (transverseBlock v) (leftFourier 5 1 (transverseCoordinates f))) := by
    change coordinates 5 1 (leftFourier 5 1 (transverseCoordinates (translation v f))) = _
    rw [transverseCoordinates_translation v hv,leftFourier_translation]
  rw [he]
  filter_upwards [coordinates_coe 5 1 (leftPhase 5 1 (transverseBlock v) (leftFourier 5 1 (transverseCoordinates f))),
    (split_preserves_volume 5 1).quasiMeasurePreserving.ae
      (leftPhase_coe 5 1 (transverseBlock v) (leftFourier 5 1 (transverseCoordinates f))),
    coordinates_coe 5 1 (leftFourier 5 1 (transverseCoordinates f))] with x hc hp hf
  change (dualMixed f) x = _ at hf
  simp only [Function.comp_apply] at hc hf
  rw [hc,hp,hf]

theorem dualMixed_directional_coe (v : Joint 2 4) (hv : v (.inr 0) = 0) (t : ℝ) (f : JointHilbert 2 4) :
    dualMixed (translation (t • v) f) =ᵐ[volume] fun x =>
      Complex.exp ((2*Real.pi*t*inner ℝ (split 5 1 x).1 (transverseBlock v) : ℝ)*Complex.I)*(dualMixed f) x := by
  have ht : (t • v) (.inr 0) = 0 := by simp [hv]
  filter_upwards [dualMixed_translation_coe (t • v) ht f] with x hx
  rw [hx,transverseBlock_smul,phase_eq]

def dualSymbol (h : ℝ) (v : Joint 2 4) (x : Joint 5 1) : ℝ :=
  2*Real.pi*h*inner ℝ (split 5 1 x).1 (transverseBlock v)

theorem dualMomentum_graph_coe (h : ℝ) (hh : h ≠ 0) (v : Joint 2 4) (hv : v (.inr 0) = 0)
    (f g : JointHilbert 2 4) (hfg : (f,g) ∈ (spectralMomentum h v).graph) :
    dualMixed g =ᵐ[volume] fun x => (dualSymbol h v x : ℂ)*(dualMixed f) x := by
  have hd := ((dualMixed : JointHilbert 2 4 →L[ℂ] JointHilbert 5 1).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((spectralMomentum_graph_derivative h hh v f g).mp hfg)
  change HasDerivAt (fun t => dualMixed (translation (t • v) f))
    (dualMixed ((Complex.I/(h:ℂ)) • g)) 0 at hd
  rw [map_smul] at hd
  have hr := KFCausalLpDerivativeRepresentative.derivative_representative _ _ _ _
    (fun t => dualMixed_directional_coe v hv t f) hd
    (fun x => phase_derivative (transverseBlock v) (split 5 1 x).1 ((dualMixed f) x))
  filter_upwards [hr,Lp.coeFn_smul (Complex.I/(h:ℂ)) (dualMixed g)] with x hx hs
  rw [hs] at hx
  simp only [Pi.smul_apply,smul_eq_mul] at hx
  have he := congrArg (fun z : ℂ => (-Complex.I*(h:ℂ))*z) hx
  dsimp only at he
  have hi : (-Complex.I*(h:ℂ))*(Complex.I/(h:ℂ)) = 1 := by
    rw [mul_comm,KFCausalUnitaryMomentumEvolution.inverse_coefficient h hh]
  rw [← mul_assoc,hi,one_mul] at he
  rw [he]
  unfold dualSymbol
  push_cast
  ring_nf
  norm_num [Complex.I_sq]

#print axioms transverseBlock_smul
#print axioms split_repack_add
#print axioms pull_coordinates_coe
#print axioms pull_coordinates_translation
#print axioms transverseCoordinates_translation
#print axioms dualMixed_translation_coe
#print axioms dualMixed_directional_coe
#print axioms dualMomentum_graph_coe

end
end UnifiedTheory.Audit.KFCausalChargeDualMomentum
