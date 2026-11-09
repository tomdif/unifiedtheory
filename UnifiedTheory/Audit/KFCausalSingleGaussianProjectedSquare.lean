/- The charge projection of the first singleton-Gaussian vacuum-square
output lies in the next vacuum-square domain. Integration takes place in
the closed longitudinal-exponential graph, not in an assumed closed
graph of the boundedly sandwiched square. -/
import UnifiedTheory.Audit.KFCausalClosedGraphPathIntegral
import UnifiedTheory.Audit.KFCausalSingleGaussianMixedSquareContinuity
import UnifiedTheory.Audit.KFCausalStandingChargeOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalSingleGaussianProjectedSquare
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorExponential (longitudinalExponential longitudinal_exponential_selfAdjoint)
open KFCausalClockFloorVacuumSquare (square square_graph)
open KFCausalPhysicalCircleAction (action action_strong_continuous)
open KFCausalStandingChargeOperator (zeroProjection zeroProjection_integral)
open KFCausalSingleGaussianSecondInput (firstOutput)
open KFCausalSingleGaussianMixedSquare (original_strip exponentialOutput secondOutput second_exponential_graph)

variable (ε h a : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hb : |h| ≤ ε/10)
local notation "D" => inverseL ε hε
local notation "P" => zeroProjection h hh
local notation "E" => longitudinalExponential ε hε h 1
local notation "first" => firstOutput ε h a hε hh ha (original_strip ε h hε hb)
local notation "output" => exponentialOutput ε h a hε hh ha hb

def averagedExponentialOutput : Hilbert :=
  (2*Real.pi)⁻¹ • ∫ θ in 0..2*Real.pi, output θ

def projectedOutput : Hilbert := D (averagedExponentialOutput ε h a hε hh ha hb)

theorem projected_exponential_graph :
    (D (P first),averagedExponentialOutput ε h a hε hh ha hb) ∈ (E).graph := by
  have hu := action_strong_continuous h hh first
  have hv := KFCausalSingleGaussianMixedSquareContinuity.exponentialOutput_continuous ε h a hε hh ha hb
  have hg := KFCausalClosedGraphPathIntegral.integral_graph E
    (longitudinal_exponential_selfAdjoint ε hε h 1).isClosed
    (fun θ => D (action h hh θ first)) output ((D).continuous.comp hu) hv
    (second_exponential_graph ε h a hε hh ha hb) 0 (2*Real.pi)
  have hs := ((E).graph.restrictScalars ℝ).smul_mem (2*Real.pi)⁻¹ hg
  change ((2*Real.pi)⁻¹ • ∫ θ in 0..2*Real.pi, D (action h hh θ first),
    averagedExponentialOutput ε h a hε hh ha hb) ∈ (E).graph at hs
  have he : D (P first) = (2*Real.pi)⁻¹ • ∫ θ in 0..2*Real.pi, D (action h hh θ first) := by
    rw [zeroProjection_integral,ContinuousLinearMap.map_smul_of_tower,
      ← (D).intervalIntegral_comp_comm (hu.intervalIntegrable 0 (2*Real.pi))]
  rw [he]
  exact hs

theorem projected_square_graph :
    (P first,projectedOutput ε h a hε hh ha hb) ∈ (square ε hε h).graph :=
  (square_graph ε hε h _ _).mpr
    ⟨_,projected_exponential_graph ε h a hε hh ha hb,rfl⟩

theorem projected_square_domain : P first ∈ (square ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (projected_square_graph ε h a hε hh ha hb)

theorem projectedOutput_integral :
    projectedOutput ε h a hε hh ha hb =
      (2*Real.pi)⁻¹ • ∫ θ in 0..2*Real.pi, secondOutput ε h a hε hh ha hb θ := by
  have hv := KFCausalSingleGaussianMixedSquareContinuity.exponentialOutput_continuous ε h a hε hh ha hb
  unfold projectedOutput averagedExponentialOutput
  rw [ContinuousLinearMap.map_smul_of_tower,
    ← (D).intervalIntegral_comp_comm (hv.intervalIntegrable 0 (2*Real.pi))]
  rfl

#print axioms projected_exponential_graph
#print axioms projected_square_graph
#print axioms projected_square_domain
#print axioms projectedOutput_integral
end
end UnifiedTheory.Audit.KFCausalSingleGaussianProjectedSquare
