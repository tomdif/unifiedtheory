/- The explicit shifted output belongs to both maximal physical field
domains. Consequently the original invariant trial belongs to the exact
natural ordered domains Phi E D and Phi^2 E D. -/
import UnifiedTheory.Audit.KFCausalClockFloorFieldMoments
import UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput
import UnifiedTheory.Audit.KFCausalPhysicalField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorTrialMatter
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse flow)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chartIso)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFlow
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFieldMoments
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

theorem fieldLine_grouping (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ) (x : Configuration) :
    fieldLine ε hε l (grouping x) = l ((coordinateHomeomorph ε hε).symm x).2 := by
  change l (flow ((chartIso ε hε).symm x.1) ![x.2 0,x.2 1,x.2 2,x.2 3,x.2 4]) =
    l (flow ((chartIso ε hε).symm x.1) x.2)
  have he : (![x.2 0,x.2 1,x.2 2,x.2 3,x.2 4]:Transverse) = x.2 := by
    funext i
    fin_cases i <;> rfl
  rw [he]

theorem quadratic_configuration_memLp (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) :
    MemLp (fun x : Configuration => (l ((coordinateHomeomorph ε hε).symm x).2:ℂ)^2*
      configurationLine ε a α β y x) 2 volume := by
  have hm := (quadratic_line_memLp ε a α β y hε ha hα hβ hw hy l).comp_measurePreserving grouping_preserves_volume
  simpa only [Function.comp_def,fieldLine_grouping,configurationLine] using hm

theorem gaussianState_quadratic_memLp (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) :
    MemLp (fun x : Configuration => (l x.2:ℂ)^2*gaussianState ε a α β y hε ha hα hβ hw hy x) 2 volume := by
  have hm := weighted_memLp ε hε _ (quadratic_configuration_memLp ε a α β y hε ha hα hβ hw hy l)
  apply hm.ae_eq
  filter_upwards [gaussianState_coe ε a α β y hε ha hα hβ hw hy] with x hx
  rw [hx]
  simp only [weightedFunction,Homeomorph.symm_apply_apply]
  ring

theorem gaussianState_fieldSquare_domain (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) :
    gaussianState ε a α β y hε ha hα hβ hw hy ∈ (fieldSquare l).domain :=
  (fieldSquare_domain l _).mpr (gaussianState_quadratic_memLp ε a α β y hε ha hα hβ hw hy l)

theorem shiftedOutput_fieldSquare_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (l : Transverse →L[ℝ] ℝ) :
    shiftedOutput ε a hbar hε ha hh hbound ∈ (fieldSquare l).domain :=
  gaussianState_fieldSquare_domain ε a _ _ (-hbar/2) hε ha
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
    (neutralWidth_bound hbar) (shift_bound ε hbar hbound) l

theorem shiftedOutput_physicalField_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (l : Transverse →L[ℝ] ℝ) :
    shiftedOutput ε a hbar hε ha hh hbound ∈ (physicalField l).domain :=
  fieldSquare_domain_le_physicalField l (shiftedOutput_fieldSquare_domain ε a hbar hε ha hh hbound l)

def matterFactor (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (T : Hilbert →ₗ.[ℂ] Hilbert) : Hilbert →ₗ.[ℂ] Hilbert :=
  composition T (orderedExponential ε hε hbar)

theorem trialState_linearMatter_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (l : Transverse →L[ℝ] ℝ) :
    trialState ε a hbar hε ha hh ∈ (matterFactor ε hε hbar (physicalField l)).domain := by
  apply (composition_domain _ _ _).mpr
  exact ⟨_,trialState_shifted_graph ε a hbar hε ha hh hbound,
    shiftedOutput_physicalField_domain ε a hbar hε ha hh hbound l⟩

theorem trialState_quadraticMatter_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (l : Transverse →L[ℝ] ℝ) :
    trialState ε a hbar hε ha hh ∈ (matterFactor ε hε hbar (fieldSquare l)).domain := by
  apply (composition_domain _ _ _).mpr
  exact ⟨_,trialState_shifted_graph ε a hbar hε ha hh hbound,
    shiftedOutput_fieldSquare_domain ε a hbar hε ha hh hbound l⟩

#print axioms fieldLine_grouping
#print axioms quadratic_configuration_memLp
#print axioms gaussianState_quadratic_memLp
#print axioms gaussianState_fieldSquare_domain
#print axioms shiftedOutput_fieldSquare_domain
#print axioms shiftedOutput_physicalField_domain
#print axioms trialState_linearMatter_domain
#print axioms trialState_quadraticMatter_domain

end
end UnifiedTheory.Audit.KFCausalClockFloorTrialMatter
