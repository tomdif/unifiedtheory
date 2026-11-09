/- Every physical charge modulation state is in the exact ordered linear
and quadratic matter-factor domains, using its checked spectral output. -/
import UnifiedTheory.Audit.KFCausalClockFloorTrialMatter
import UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral
import UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput
import UnifiedTheory.Audit.KFCausalPhysicalField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentMatter
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse flow)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chartIso)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFlow
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFieldMoments (fieldLine)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (fieldLine_grouping matterFactor)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

theorem quadratic_configuration_memLp (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) :
    MemLp (fun x : Configuration => (l ((coordinateHomeomorph ε hε).symm x).2:ℂ)^2*
      configurationLine ε a α β p b y x) 2 volume := by
  have hm := (quadratic_line_memLp ε a α β p b y hε ha hα hβ hw hy l).comp_measurePreserving grouping_preserves_volume
  simpa only [Function.comp_def,fieldLine_grouping,configurationLine] using hm

theorem gaussianState_quadratic_memLp (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) :
    MemLp (fun x : Configuration => (l x.2:ℂ)^2*gaussianState ε a α β p b y hε ha hα hβ hw hy x) 2 volume := by
  have hm := weighted_memLp ε hε _ (quadratic_configuration_memLp ε a α β p b y hε ha hα hβ hw hy l)
  apply hm.ae_eq
  filter_upwards [gaussianState_coe ε a α β p b y hε ha hα hβ hw hy] with x hx
  rw [hx]
  simp only [weightedFunction,Homeomorph.symm_apply_apply]
  ring

theorem gaussianState_fieldSquare_domain (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) :
    gaussianState ε a α β p b y hε ha hα hβ hw hy ∈ (fieldSquare l).domain :=
  (fieldSquare_domain l _).mpr (gaussianState_quadratic_memLp ε a α β p b y hε ha hα hβ hw hy l)

theorem shiftedOutput_fieldSquare_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    shiftedOutput ε a hbar hε ha hh hbound k ∈ (fieldSquare l).domain :=
  (fieldSquare l).domain.smul_mem (amplitudeConstant hbar k)
    (gaussianState_fieldSquare_domain ε a _ _ (clockFrequency k) (sourceCoefficients hbar k) (-hbar/2) hε ha
      (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
      (neutralWidth_bound hbar) (shift_bound ε hbar hbound) l)

theorem shiftedOutput_physicalField_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    shiftedOutput ε a hbar hε ha hh hbound k ∈ (physicalField l).domain :=
  fieldSquare_domain_le_physicalField l (shiftedOutput_fieldSquare_domain ε a hbar hε ha hh hbound k l)

theorem state_linearMatter_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k ∈ (matterFactor ε hε hbar (physicalField l)).domain := by
  apply (composition_domain _ _ _).mpr
  exact ⟨_,state_ordered_graph ε a hbar hε ha hh hbound k,
    shiftedOutput_physicalField_domain ε a hbar hε ha hh hbound k l⟩

theorem state_quadraticMatter_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k ∈ (matterFactor ε hε hbar (fieldSquare l)).domain := by
  apply (composition_domain _ _ _).mpr
  exact ⟨_,state_ordered_graph ε a hbar hε ha hh hbound k,
    shiftedOutput_fieldSquare_domain ε a hbar hε ha hh hbound k l⟩

#print axioms quadratic_configuration_memLp
#print axioms gaussianState_quadratic_memLp
#print axioms gaussianState_fieldSquare_domain
#print axioms shiftedOutput_fieldSquare_domain
#print axioms shiftedOutput_physicalField_domain
#print axioms state_linearMatter_domain
#print axioms state_quadraticMatter_domain

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentMatter
