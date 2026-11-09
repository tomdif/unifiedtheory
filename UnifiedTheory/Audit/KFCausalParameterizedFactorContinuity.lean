/- Every actual Gaussian energy-factor output is jointly continuous
under bounded continuous source parameters, including both source-circle
and charge-orbit angles. The ordered field outputs remain actual graphs. -/
import UnifiedTheory.Audit.KFCausalParameterizedSourceContinuity
import UnifiedTheory.Audit.KFCausalSourcedCurveDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalParameterizedFactorContinuity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedMultiplierContinuity
open UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMatterOrbit
  (pulledField pulledField_continuous linear_base_memLp quadratic_base_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMultiplierOrbit (baseLine_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (gaussianState gaussianState_coe)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceSize)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates (weightedFunction)
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare

open UnifiedTheory.Audit.KFCausalClockFloorSourcedFieldContinuity
  (scalarBase scalarOutput_eq linearOutput_eq quadraticOutput_eq)
open UnifiedTheory.Audit.KFCausalParameterizedSourceContinuity
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum (state)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (clockFunction clockFunction_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
  (halfClockFunction halfClockFunction_memLp dampedClockFunction dampedClockFunction_memLp)
variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
local notation "hy" => shift_bound ε h hb
local notation "Y" => shiftedOutput ε a α β hε ha hα hβ hw
local notation "L" => linearOutput ε a α β hε ha hα hβ hw
local notation "Q" => quadraticOutput ε a α β hε ha hα hβ hw
local notation "O" => outputState ε a α β (-h/2) hε ha hα hβ hw hy

theorem outputs_continuous (P B : ℝ) (C : X → ℂ) (p : X → ℝ) (b : X → Fin 5 → ℂ)
    (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
    (hC : ∀ θ, ‖C θ‖ ≤ 1) (hp : ∀ θ, |p θ| ≤ P) (hB : ∀ θ, sourceSize (b θ) ≤ B) :
    Continuous (fun θ => Y (C θ) (p θ) (b θ) h hb) ∧
      (∀ l, Continuous (fun θ => L (C θ) (p θ) (b θ) h hb l)) ∧
      (∀ l, Continuous (fun θ => Q (C θ) (p θ) (b θ) h hb l)) := by
  have hc (m : Configuration → ℂ) (hm : AEStronglyMeasurable m volume)
      (hbase : MemLp (fun x => m x*baseLine ε a α β (-h/2) x) 2) :
      Continuous (fun θ => O m hm hbase (C θ) (p θ) (b θ)) :=
    (coordinates ε hε).continuous.comp
      (shiftedLine_continuous ε a α β (-h/2) P B hε ha hα hβ hw hy m hm hbase
        C p b hCc hpc hbc hC hp hB)
  refine ⟨?_,?_,?_⟩
  · have he := funext (fun θ => scalarOutput_eq ε a h hε ha hh hb (C θ) (p θ) (b θ))
    rw [← he]
    exact hc _ _ _
  · intro l
    have he := funext (fun θ => linearOutput_eq ε a h hε ha hh hb (C θ) (p θ) (b θ) l)
    rw [← he]
    exact hc _ _ _
  · intro l
    have he := funext (fun θ => quadraticOutput_eq ε a h hε ha hh hb (C θ) (p θ) (b θ) l)
    rw [← he]
    exact hc _ _ _

variable (P B : ℝ) (C : X → ℂ) (p : X → ℝ) (b : X → Fin 5 → ℂ)
  (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
  (hC : ∀ θ, ‖C θ‖ ≤ 1) (hp : ∀ θ, |p θ| ≤ P) (hB : ∀ θ, sourceSize (b θ) ≤ B)

include hCc hpc hbc hC hB in
theorem state_continuous :
    Continuous (fun θ => state ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ)) :=
  profile_continuous α β B hα hβ hw C p b (clockFunction ε a)
    (clockFunction_memLp ε a hε ha) hCc hpc hbc hC hB

include hCc hpc hbc hC hp hB in
theorem factor_continuous (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    Continuous (fun θ => factorOutput ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb v l i) := by
  have hc := profile_continuous α β B hα hβ hw C p b
    (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha) hCc hpc hbc hC hB
  have hm (u : Transverse) := (continuous_const (y := -Complex.I*(h:ℂ))).smul
    (derivative_continuous α β B hα hβ hw C p b
      (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha) hCc hpc hbc hC hB u)
  have hs := outputs_continuous ε a h hε ha hh hb
    P B C p b hCc hpc hbc hC hp hB
  fin_cases i
  · exact hc
  · exact hm (v 0)
  · exact hm (v 1)
  · exact hm (v 2)
  · exact hm (v 3)
  · exact hs.2.1 l
  · exact hs.2.2 l
  · exact hs.1

#print axioms outputs_continuous
#print axioms state_continuous
#print axioms factor_continuous
end
end UnifiedTheory.Audit.KFCausalParameterizedFactorContinuity
