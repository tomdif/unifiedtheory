/- Pure-clock differentiation of the clock-half output of an arbitrary
directional polynomial packet. Both compositions are obtained from
actual sourced graphs by closed graph integration. -/
import UnifiedTheory.Audit.KFCausalDirectionalClockMomentum
import UnifiedTheory.Audit.KFCausalPolynomialClockComposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalDirectionalClockComposition
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalClockFloorPureClockMomentum (pureMomentum pure_closed)
open KFCausalClockFloorPureClockKinetic (correction)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open KFCausalProjectedKineticResponse (integral_closed_graph)
open KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalDirectionalGaussianCoefficients
  (sourceCurve sourceBound sourceCurve_continuous sourceCurve_bound)
open KFCausalSourceCircleCoefficients
open KFCausalDirectionalGaussianDomain (output)
open KFCausalDirectionalClockMomentum (factorCurve factorCurve_continuous factor)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (C : ℂ) (p : ℝ) (d : Transverse)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h

theorem composition_graph (n : ℕ) :
    (output ε a h hε ha hh C p d n hb modelDirections pointField 0,
      factor ε a h hε ha hh p d C hb n modelDirections pointField 0-
        correction ε hε h (output ε a h hε ha hh C p d n hb modelDirections pointField 0)) ∈
      (pureMomentum ε hε h).graph := by
  let G : ℝ → Hilbert := fun θ => KFCausalClockFloorSourcedCommonDomain.factorOutput
    ε a α β hε ha hα hβ hw (weight n θ) p (sourceCurve d θ) h hb modelDirections pointField 0
  let K := factorCurve ε a h hε ha hh p d hb n modelDirections pointField 0
  have hG : Continuous G := KFCausalSourcedCurveDomain.factor_continuous ε a h hε ha hh hb
    |p| (sourceBound d) (weight n) (fun _ => p) (sourceCurve d)
    (weight_continuous n) continuous_const (sourceCurve_continuous d)
    (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (sourceCurve_bound d)
    modelDirections pointField 0
  have hK : Continuous K := factorCurve_continuous ε a h hε ha hh p d hb n modelDirections pointField 0
  have hg (θ : ℝ) : (G θ,K θ-correction ε hε h (G θ)) ∈ (pureMomentum ε hε h).graph :=
    KFCausalPolynomialClockComposition.sourced_composition_graph
      ε a α β h hε ha hα hβ hw hh hb (weight n θ) p (sourceCurve d θ)
  have hi := (continuous_angle_memLp _ hG).integrable (by norm_num)
  have hj := (continuous_angle_memLp _ hK).integrable (by norm_num)
  have he := integral_closed_graph _ (pure_closed ε hε h hh) G
    (fun θ => K θ-correction ε hε h (G θ)) hG
    (hK.sub ((correction ε hε h).continuous.comp hG)) hg
  rw [integral_sub hj ((correction ε hε h).integrable_comp hi),
    (correction ε hε h).integral_comp_comm hi] at he
  have hs := (pureMomentum ε hε h).graph.smul_mem (C*normalization n) he
  simpa only [output,factor,KFCausalSourcedCurveDomain.meanFactor,
    Prod.smul_mk,smul_sub,map_smul,G,K] using hs

#print axioms composition_graph
end
end UnifiedTheory.Audit.KFCausalDirectionalClockComposition
