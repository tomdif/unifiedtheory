/- Both directions of the symmetric physical momentum graph transport.
The exact inverse translation intertwining retains the neutral derivative. -/
import UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSymmetricMomentumGraphEquivalence
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanConfiguration (FrequencyHilbert euclideanPullback)
open KFCausalEuclideanProductCoordinates (JointHilbert)
open KFCausalPairedTranslationCoordinates (chargeEuclidean chargeEuclidean_physical)
open KFCausalPairedModeCoordinates (modeIsometry)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalPhysicalTransverseMomentum (transverseMomentum transverseVector)
open KFCausalClockFloorKineticDefect (transverse_graph_iff)
open KFCausalDirectionalTranslationMomentum (spectralMomentum spectralMomentum_graph_derivative)
open KFCausalFourierTranslation (translation)
open KFCausalSymmetricMomentumCoordinates
  (symmetricDirection symmetricBlock symmetricVector symmetricDirection_mode
    rightVector_smul chargeEuclidean_rightTranslation symmetric_graph)

theorem symmetric_graph_reverse (h : ℝ) (hh : h ≠ 0) (i : Fin 2) (f g : Hilbert)
    (hfg : (chargeCoordinates f,chargeCoordinates g) ∈ (spectralMomentum h (symmetricVector i)).graph) :
    (f,g) ∈ (transverseMomentum h (symmetricDirection i)).graph := by
  have hd := (spectralMomentum_graph_derivative h hh _ _ _).mp hfg
  have hb := ((chargeEuclidean.symm : JointHilbert 2 4 →L[ℂ] FrequencyHilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  have he (t : ℝ) :
      chargeEuclidean (translation (t • transverseVector (symmetricDirection i)) (euclideanPullback f)) =
        translation (t • symmetricVector i) (chargeCoordinates f) := by
    have hv : modeIsometry (t • transverseVector (symmetricDirection i)) =
        KFCausalSymmetricMomentumCoordinates.rightVector (t • symmetricBlock i) := by
      rw [map_smul,symmetricDirection_mode,rightVector_smul]
      rfl
    rw [chargeEuclidean_rightTranslation _ _ hv,rightVector_smul,chargeEuclidean_physical]
    rfl
  have hi (t : ℝ) :
      chargeEuclidean.symm (translation (t • symmetricVector i) (chargeCoordinates f)) =
        translation (t • transverseVector (symmetricDirection i)) (euclideanPullback f) := by
    rw [← he,LinearIsometryEquiv.symm_apply_apply]
  have ho : chargeEuclidean.symm ((Complex.I/(h:ℂ)) • chargeCoordinates g) =
      (Complex.I/(h:ℂ)) • euclideanPullback g := by
    rw [map_smul,← chargeEuclidean_physical,LinearIsometryEquiv.symm_apply_apply]
  apply (transverse_graph_iff h (symmetricDirection i) f g).mpr
  apply (spectralMomentum_graph_derivative h hh _ _ _).mpr
  change HasDerivAt (fun t => chargeEuclidean.symm (translation (t • symmetricVector i) (chargeCoordinates f)))
    (chargeEuclidean.symm ((Complex.I/(h:ℂ)) • chargeCoordinates g)) 0 at hb
  simpa only [hi,ho] using hb

theorem symmetric_graph_iff (h : ℝ) (hh : h ≠ 0) (i : Fin 2) (f g : Hilbert) :
    (f,g) ∈ (transverseMomentum h (symmetricDirection i)).graph ↔
      (chargeCoordinates f,chargeCoordinates g) ∈ (spectralMomentum h (symmetricVector i)).graph :=
  ⟨symmetric_graph h hh i f g,symmetric_graph_reverse h hh i f g⟩

theorem symmetric_domain_iff (h : ℝ) (hh : h ≠ 0) (i : Fin 2) (f : Hilbert) :
    f ∈ (transverseMomentum h (symmetricDirection i)).domain ↔
      chargeCoordinates f ∈ (spectralMomentum h (symmetricVector i)).domain := by
  constructor
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph
      ((symmetric_graph_iff h hh i f _).mp ((transverseMomentum h (symmetricDirection i)).mem_graph ⟨f,hf⟩))
  · intro hf
    have hg := (spectralMomentum h (symmetricVector i)).mem_graph ⟨chargeCoordinates f,hf⟩
    let g : Hilbert := chargeCoordinates.symm ((spectralMomentum h (symmetricVector i)) ⟨chargeCoordinates f,hf⟩)
    have hfg : (f,g) ∈ (transverseMomentum h (symmetricDirection i)).graph := by
      apply (symmetric_graph_iff h hh i f g).mpr
      simpa only [g,LinearIsometryEquiv.apply_symm_apply] using hg
    exact LinearPMap.mem_domain_of_mem_graph hfg

#print axioms symmetric_graph_reverse
#print axioms symmetric_graph_iff
#print axioms symmetric_domain_iff
end
end UnifiedTheory.Audit.KFCausalSymmetricMomentumGraphEquivalence
