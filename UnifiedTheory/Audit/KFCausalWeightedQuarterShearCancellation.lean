/- Quarter-turn cancellation of the actual shear graphs survives any
bounded weight that commutes with charge. Smoothness is required only
of the unweighted state in mixed coordinates, not of the clock weight. -/
import UnifiedTheory.Audit.KFCausalChargeShearQuarterGraphs
import UnifiedTheory.Audit.KFCausalClockFloorShearWeight
import UnifiedTheory.Audit.KFCausalBoundedClockCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalWeightedQuarterShearCancellation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action action_coordinates action_reverse chargeCoordinates)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalChargeShearQuarterGraphs (four_graph_outputs_cancel reverseOutput)

variable (h : ℝ) (hh : h ≠ 0) (W : Hilbert →L[ℂ] Hilbert)
variable (hW : ∀ θ f, W (action h hh θ f) = action h hh θ (W f))

include hW in
theorem pairing_reverse (θ : ℝ) (f g : Hilbert) :
    inner ℂ (W (action h hh θ f)) (W g) = inner ℂ (W f) (W (action h hh (-θ) g)) := by
  calc
    _ = inner ℂ (action h hh (-θ) (W (action h hh θ f))) (action h hh (-θ) (W g)) :=
      ((action h hh (-θ)).inner_map_map _ _).symm
    _ = _ := by rw [← hW,action_reverse,← hW]

theorem physical_outputs_cancel (f g₀ g₁ g₂ g₃ : Hilbert)
    (φ : Joint 2 4 → ℂ) (hφ : chargeCoordinates f =ᵐ[volume] φ) (hs : Differentiable ℝ φ)
    (h₀ : (action h hh 0 f,g₀) ∈ (shearMomentum h).graph)
    (h₁ : (action h hh (Real.pi/2) f,g₁) ∈ (shearMomentum h).graph)
    (h₂ : (action h hh Real.pi f,g₂) ∈ (shearMomentum h).graph)
    (h₃ : (action h hh (-Real.pi/2) f,g₃) ∈ (shearMomentum h).graph) :
    action h hh (-0) g₀+action h hh (-(Real.pi/2)) g₁+
      action h hh (-Real.pi) g₂+action h hh (-(-Real.pi/2)) g₃ = 0 := by
  apply chargeCoordinates.injective
  simpa only [map_add,map_zero,action_coordinates,reverseOutput] using
    four_graph_outputs_cancel h hh f g₀ g₁ g₂ g₃ φ hφ hs h₀ h₁ h₂ h₃

include hW in
theorem four_pairings_cancel (f g₀ g₁ g₂ g₃ : Hilbert)
    (φ : Joint 2 4 → ℂ) (hφ : chargeCoordinates f =ᵐ[volume] φ) (hs : Differentiable ℝ φ)
    (h₀ : (action h hh 0 f,g₀) ∈ (shearMomentum h).graph)
    (h₁ : (action h hh (Real.pi/2) f,g₁) ∈ (shearMomentum h).graph)
    (h₂ : (action h hh Real.pi f,g₂) ∈ (shearMomentum h).graph)
    (h₃ : (action h hh (-Real.pi/2) f,g₃) ∈ (shearMomentum h).graph) :
    (inner ℂ (W (action h hh 0 f)) (W g₀)).re+
      (inner ℂ (W (action h hh (Real.pi/2) f)) (W g₁)).re+
      (inner ℂ (W (action h hh Real.pi f)) (W g₂)).re+
      (inner ℂ (W (action h hh (-Real.pi/2) f)) (W g₃)).re = 0 := by
  simp only [pairing_reverse h hh W hW,← Complex.add_re,← inner_add_right,← map_add]
  rw [physical_outputs_cancel h hh f g₀ g₁ g₂ g₃ φ hφ hs h₀ h₁ h₂ h₃,map_zero,inner_zero_right,Complex.zero_re]

theorem root_charge (ε : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (θ : ℝ) (f : Hilbert) :
    KFCausalClockFloorShearWeight.root ε hε h hb hh (action h hh θ f) =
      action h hh θ (KFCausalClockFloorShearWeight.root ε hε h hb hh f) :=
  KFCausalClockChargeMultiplier.multiplier_action
    (fun s => (KFCausalClockFloorShearWeight.rootValue ε h s:ℂ))
    (Complex.continuous_ofReal.comp (KFCausalClockFloorShearWeight.rootValue_continuous ε hε h hb)).measurable
    (KFCausalClockFloorShearWeight.rootValue_contractive ε hε h hb hh) h hh θ f

#print axioms pairing_reverse
#print axioms physical_outputs_cancel
#print axioms four_pairings_cancel
#print axioms root_charge
end
end UnifiedTheory.Audit.KFCausalWeightedQuarterShearCancellation
