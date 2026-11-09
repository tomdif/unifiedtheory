/- The remaining interpolation cost is an intrinsic nonnegative quadratic
functional on the coherent span. The actual matter response lower bound
is stated directly in terms of the state, without existential expansion
parameters. No comparison with the Hamiltonian energy is asserted. -/
import UnifiedTheory.Audit.KFCausalIntrinsicMatterInterpolation
import UnifiedTheory.Audit.KFCausalInterpolatedMatterResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalIntrinsicMatterResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope)
open UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage (matterIndex)
open UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition (rate)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root)
open UnifiedTheory.Audit.KFCausalMatterScalarAbsorption (coefficient)
open UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight (moment)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalIntrinsicMatterInterpolation

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "S" => coherentSpan ε a h hε ha hh

def meanCost (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (W : Hilbert →L[ℂ] Hilbert) (f : S) : ℝ :=
  ∫ θ, pathCost ε a h hε ha hh hb l i W f θ ∂angleMeasure

theorem meanCost_nonnegative (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (W : Hilbert →L[ℂ] Hilbert) (f : S) :
    0 ≤ meanCost ε a h hε ha hh hb l i W f :=
  integral_nonneg (pathCost_nonnegative ε a h hε ha hh hb l i W f)

theorem meanCost_smul (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (W : Hilbert →L[ℂ] Hilbert) (c : ℂ) (f : S) :
    meanCost ε a h hε ha hh hb l i W (c • f) = ‖c‖^2*meanCost ε a h hε ha hh hb l i W f := by
  simp only [meanCost,pathCost_smul,integral_const_mul]

theorem meanCost_parallelogram (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (W : Hilbert →L[ℂ] Hilbert) (f g : S) :
    meanCost ε a h hε ha hh hb l i W (f+g)+meanCost ε a h hε ha hh hb l i W (f-g) =
      2*(meanCost ε a h hε ha hh hb l i W f+meanCost ε a h hε ha hh hb l i W g) := by
  have hI := pathCost_angle_integrable ε a h hε ha hh hb l i W
  unfold meanCost
  rw [← integral_add (hI (f+g)) (hI (f-g))]
  simp_rw [pathCost_parallelogram]
  rw [integral_const_mul,integral_add (hI f) (hI g)]

local notation "W" => root ε hε h hb hh

theorem actual_average_lower (f : S) (b : Hilbert) (hB : ((f:Hilbert),b) ∈ (pureMomentum ε hε h).graph)
    (g k : Fin 8 → ℝ → Hilbert)
    (hOut : ∀ θ i,
      (action h hh (2*Real.pi*θ) (f:Hilbert),g i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph ∧
      (action h hh (2*Real.pi*θ) b,k i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph)
    (hc : ∀ i, Continuous (g i) ∧ Continuous (k i)) :
    ∃ d : Fin 2 → ℝ → Hilbert,
      (∀ i, Continuous (d i)) ∧
      (∀ θ i, d i θ =ᵐ[volume] fun x => powerSlope pointField i x*g 7 θ x) ∧
      (∀ i, Integrable (fun θ => moment ε hε (d i θ)) angleMeasure) ∧
      (∀ i, Integrable (fun θ => expectation ε a h hε ha hh hb pointField i W f θ 0) angleMeasure ∧
        Integrable (pathCost ε a h hε ha hh hb pointField i W f) angleMeasure ∧
        (4/ε^2)*(∫ θ, expectation ε a h hε ha hh hb pointField i W f θ 0 ∂angleMeasure)-
          (h^2/ε^3)*meanCost ε a h hε ha hh hb pointField i W f-
          coefficient ε h*(∫ θ, moment ε hε (d i θ) ∂angleMeasure) ≤ rate h g k (matterIndex i)) := by
  obtain ⟨n,p,z,d,hf,hd,hrep,hMI,hr⟩ :=
    KFCausalInterpolatedMatterResponse.actual_average_lower ε a h hε ha hh hb f f.property b hB g k hOut hc
  refine ⟨d,hd,hrep,hMI,?_⟩
  intro i
  refine ⟨expectation_angle_integrable ε a h hε ha hh hb pointField i W f 0,
    pathCost_angle_integrable ε a h hε ha hh hb pointField i W f,?_⟩
  unfold meanCost
  simp_rw [expectation_of_representation ε a h hε ha hh hb pointField i W f p z hf,
    pathCost_of_representation ε a h hε ha hh hb pointField i W f p z hf]
  exact (hr i).2.2

#print axioms meanCost_nonnegative
#print axioms meanCost_smul
#print axioms meanCost_parallelogram
#print axioms actual_average_lower
end
end UnifiedTheory.Audit.KFCausalIntrinsicMatterResponse
