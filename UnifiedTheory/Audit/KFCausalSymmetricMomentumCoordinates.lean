/- The remaining two physical kinetic directions retain their derivative
momentum graphs in the actual charge coordinates. The second direction
contains the neutral derivative as well as the paired symmetric one. -/
import UnifiedTheory.Audit.KFCausalPartialFourierRightTranslation
import UnifiedTheory.Audit.KFCausalAntisymmetricMomentumCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space FrequencyHilbert euclideanPullback)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalPartialFourierRightTranslation
open UnifiedTheory.Audit.KFCausalPartialFourier (leftFourier)
open UnifiedTheory.Audit.KFCausalFourierTranslation (translation translation_coe shift_preserves_volume)
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum (spectralMomentum spectralMomentum_graph_derivative)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum (transverseMomentum transverseVector)
open UnifiedTheory.Audit.KFCausalClockFloorKineticDefect (transverse_graph_iff)
open UnifiedTheory.Audit.KFCausalAntisymmetricMomentumCoordinates (transverseVector_explicit)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)

def rightVector (b : Block 4) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl _ => 0
  | .inr i => b i

theorem rightVector_smul (t : ℝ) (b : Block 4) : rightVector (t • b) = t • rightVector b := by
  ext i
  rcases i with i | i <;> simp [rightVector]

theorem split_add_right (x : Joint 2 4) (b : Block 4) :
    split 2 4 (x+rightVector b) = ((split 2 4 x).1,(split 2 4 x).2+b) := by
  ext i <;> simp [split_fst,split_snd,rightVector]

theorem positionCoordinates_rightTranslation (v : Space) (b : Block 4)
    (hv : modeIsometry v = rightVector b) (f : ProductHilbert 2 4) :
    translation v (modePullback (coordinates 2 4 f)) =
      modePullback (coordinates 2 4 (rightTranslation 2 4 b f)) := by
  apply Lp.ext
  filter_upwards [translation_coe v (modePullback (coordinates 2 4 f)),
    (shift_preserves_volume v).quasiMeasurePreserving.ae (positionCoordinates_coe f),
    positionCoordinates_coe (rightTranslation 2 4 b f),
    mode_preserves_volume.quasiMeasurePreserving.ae
      ((split_preserves_volume 2 4).quasiMeasurePreserving.ae (rightTranslation_coe 2 4 b f))] with x ht hf hg hl
  change (modePullback (coordinates 2 4 f)) (x+v) = f (split 2 4 (modeIsometry (x+v))) at hf
  rw [ht,hf,hg,hl,map_add,hv,split_add_right]

theorem pairedEuclidean_rightTranslation (v : Space) (b : Block 4)
    (hv : modeIsometry v = rightVector b) (f : FrequencyHilbert) :
    pairedEuclidean (translation v f) = rightTranslation 2 4 b (pairedEuclidean f) := by
  apply (coordinates 2 4).injective
  apply modePullback.injective
  have he (g : FrequencyHilbert) : modePullback (coordinates 2 4 (pairedEuclidean g)) = g := by
    simp only [pairedEuclidean,LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.apply_symm_apply]
  rw [he,← positionCoordinates_rightTranslation v b hv,he]

theorem coordinates_rightTranslation (b : Block 4) (f : ProductHilbert 2 4) :
    coordinates 2 4 (rightTranslation 2 4 b f) = translation (rightVector b) (coordinates 2 4 f) := by
  apply Lp.ext
  filter_upwards [coordinates_coe 2 4 (rightTranslation 2 4 b f),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae (rightTranslation_coe 2 4 b f),
    translation_coe (rightVector b) (coordinates 2 4 f),
    (shift_preserves_volume (rightVector b)).quasiMeasurePreserving.ae (coordinates_coe 2 4 f)] with x hc hr ht hf
  change (coordinates 2 4 f) (x+rightVector b) = f (split 2 4 (x+rightVector b)) at hf
  simp only [Function.comp_apply] at hc
  rw [hc,hr,ht,hf,split_add_right]

theorem chargeEuclidean_rightTranslation (v : Space) (b : Block 4)
    (hv : modeIsometry v = rightVector b) (f : FrequencyHilbert) :
    chargeEuclidean (translation v f) = translation (rightVector b) (chargeEuclidean f) := by
  change coordinates 2 4 (leftFourier 2 4 (pairedEuclidean (translation v f))) = _
  rw [pairedEuclidean_rightTranslation v b hv,leftFourier_rightTranslation,coordinates_rightTranslation]
  rfl

theorem transverse_charge_graph (h : ℝ) (hh : h ≠ 0) (v : Transverse) (b : Block 4)
    (hv : modeIsometry (transverseVector v) = rightVector b) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h v).graph) :
    (chargeCoordinates f,chargeCoordinates g) ∈ (spectralMomentum h (rightVector b)).graph := by
  have hd := ((chargeEuclidean : FrequencyHilbert →L[ℂ] JointHilbert 2 4).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((spectralMomentum_graph_derivative h hh _ _ _).mp ((transverse_graph_iff h v f g).mp hfg))
  have he (t : ℝ) : chargeEuclidean (translation (t • transverseVector v) (euclideanPullback f)) =
      translation (t • rightVector b) (chargeCoordinates f) := by
    have hvt : modeIsometry (t • transverseVector v) = rightVector (t • b) := by
      rw [map_smul,hv,rightVector_smul]
    rw [chargeEuclidean_rightTranslation _ _ hvt,rightVector_smul,chargeEuclidean_physical]
  apply (spectralMomentum_graph_derivative h hh _ _ _).mpr
  change HasDerivAt (fun t => chargeEuclidean (translation (t • transverseVector v) (euclideanPullback f)))
    (chargeEuclidean ((Complex.I/(h:ℂ)) • euclideanPullback g)) 0 at hd
  simpa only [he,map_smul,chargeEuclidean_physical] using hd

def symmetricDirection (i : Fin 2) : Transverse := ![modelDirections 0,modelDirections 1] i
def symmetricBlock (i : Fin 2) : Block 4 :=
  WithLp.toLp 2 (![![0,2*scale,0,0],![0,0,2*scale,1]] i)
def symmetricVector (i : Fin 2) : Joint 2 4 := rightVector (symmetricBlock i)

theorem symmetricDirection_mode (i : Fin 2) :
    modeIsometry (transverseVector (symmetricDirection i)) = symmetricVector i := by
  rw [transverseVector_explicit]
  fin_cases i <;> ext j <;> rcases j with j | j <;> fin_cases j <;>
    simp [modeIsometry,modeEquiv,forward,symmetricDirection,modelDirections,symmetricVector,rightVector,symmetricBlock]
  all_goals ring

theorem symmetric_graph (h : ℝ) (hh : h ≠ 0) (i : Fin 2) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h (symmetricDirection i)).graph) :
    (chargeCoordinates f,chargeCoordinates g) ∈ (spectralMomentum h (symmetricVector i)).graph :=
  transverse_charge_graph h hh _ _ (symmetricDirection_mode i) f g hfg

#print axioms rightVector_smul
#print axioms split_add_right
#print axioms positionCoordinates_rightTranslation
#print axioms pairedEuclidean_rightTranslation
#print axioms coordinates_rightTranslation
#print axioms chargeEuclidean_rightTranslation
#print axioms transverse_charge_graph
#print axioms symmetricDirection_mode
#print axioms symmetric_graph

end
end UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates
