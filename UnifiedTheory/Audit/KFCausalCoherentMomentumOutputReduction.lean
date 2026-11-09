/- Exact cancellation of the shear outputs inside T B on coherent states.
The inverse complex clock is identified with the existing shifted defect,
so the reduced output uses bounded clock operators on two Gaussian widths. -/
import UnifiedTheory.Audit.KFCausalCoherentVacuumCompositionOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (clockFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalShiftedClockMomentOperator
open UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential (inverseClock)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (argument)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shiftedDefect)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical (physicalSymbol shiftedDefect_physical_coe)
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (complexDefect)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain (clockInverse)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (pureCorrection shearCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator (correction)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalCoherentVacuumCompositionOrbit

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

theorem inverseOperator_eq : inverseOperator ε (-h/2) hε (shift_bound ε h hb) =
    (1/(ε:ℂ)) • shiftedDefect ε hε h hb := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [inverseOperator_coe ε (-h/2) hε (shift_bound ε h hb) f,
    Lp.coeFn_smul (1/(ε:ℂ)) (shiftedDefect ε hε h hb f),
    shiftedDefect_physical_coe ε hε h hb f] with x hi hs hz
  change inverseOperator ε (-h/2) hε (shift_bound ε h hb) f x =
    ((1/(ε:ℂ)) • shiftedDefect ε hε h hb f) x
  rw [hi,hs]
  simp only [Pi.smul_apply,smul_eq_mul,hz,inverseClock,physicalSymbol,argument,complexDefect]
  field_simp [Complex.ofReal_ne_zero.mpr hε.ne']

def reducedOutput (p : ℝ) (f g : Hilbert) : Hilbert :=
  (-Complex.I*(h:ℂ)) • (((p:ℂ)*Complex.I-1) • inverseOperator ε (-h/2) hε (shift_bound ε h hb) f-
    (2*(a:ℂ)) • momentOperator ε a (-h/2) ha g)-correction ε hε h hb f

theorem reducedOutput_continuous (p : ℝ) (f g : ℝ → Hilbert) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun θ => reducedOutput ε a h hε ha hb p (f θ) (g θ)) :=
  (((((inverseOperator ε (-h/2) hε (shift_bound ε h hb)).continuous.comp hf).const_smul _).sub
    (((momentOperator ε a (-h/2) ha).continuous.comp hg).const_smul _)).const_smul _).sub
      ((correction ε hε h hb).continuous.comp hf)

theorem orderedMomentumOutput_eq (k : Joint 2 4) :
    orderedMomentumOutput ε a h hε ha hh hb k = reducedOutput ε a h hε ha hb (clockFrequency k)
      (shiftedOutput ε a h hε ha hh hb k) (shiftedOutput ε (a/2) h hε (by positivity) hh hb k) := by
  unfold orderedMomentumOutput pureOutput longitudinalOutput pureCorrection reducedOutput shiftedMoment
  simp only [inverseOperator_eq ε h hε hb,clockInverse,shearCorrection,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,smul_sub]
  abel

theorem reducedOutput_graph (k : Joint 2 4) (b : Hilbert)
    (hB : (state ε a h hε ha hh k,b) ∈ (pureMomentum ε hε h).graph) :
    (b,reducedOutput ε a h hε ha hb (clockFrequency k)
      (shiftedOutput ε a h hε ha hh hb k) (shiftedOutput ε (a/2) h hε (by positivity) hh hb k)) ∈
        (orderedExponential ε hε h).graph := by
  rw [← orderedMomentumOutput_eq]
  exact orderedMomentumOutput_graph ε a h hε ha hh hb k b hB

#print axioms inverseOperator_eq
#print axioms reducedOutput_continuous
#print axioms orderedMomentumOutput_eq
#print axioms reducedOutput_graph
end
end UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction
