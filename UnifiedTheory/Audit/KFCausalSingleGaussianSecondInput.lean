/- The actual singleton Gaussian and its first vacuum-square output.
The rotated input representative is specialized without assuming any
membership in a second exponential domain. -/
import UnifiedTheory.Audit.KFCausalChargeRotatedSecondInput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalSingleGaussianSecondInput
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalCorrelatedClusteredProfiles
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalPhysicalCircleAction (action)
open KFCausalChargeRotatedSecondInput (rotatedPoint)

def family : Family 1 where
  degree _ := 0
  source _ := 0
  polynomial _ := 1
  amplitude _ := 1

theorem family_count : count family=1 := by
  simp [count,Index,family]

theorem family_width (δ : ℝ) (j : Fin (count family)) : widths family δ j=1 := by
  simp [widths,family,KFCausalClusteredWidthProfiles.widths]

theorem family_coefficient (δ : ℝ) (j : Fin (count family)) : coefficients family δ j=1 := by
  simp [coefficients,family,KFCausalClusteredWidthProfiles.coefficients,
    KFCausalClusteredWidthProfiles.widths]

def density (ε h a : ℝ) (x : Product) : ℂ :=
  KFCausalVacuumMixedClockNormalization.normalizedClock ε a 0 (-h) (x.2 0)*
    ((Real.pi:ℂ)/(KFCausalChargeGaussianGeometry.groundWidth h:ℂ))*
    Complex.exp (-KFCausalShiftedPhysicalFourierSlices.radius
      ((KFCausalChargeGaussianGeometry.groundWidth h:ℂ)*
        (KFCausalClockFloorRelativeShift.scale ε (-h) (x.2 0))^2) 1 x.1 x.2)*
    KFCausalShiftedNarrowFourierSlices.neutralPacket
      (KFCausalClockFloorInvariantTrial.neutralWidth h)
      (KFCausalClockFloorRelativeShift.scale ε (-h) (x.2 0)) 0 1 x.2

theorem normalized_density (ε h a δ : ℝ) (x : Product) :
    KFCausalCorrelatedClusteredPhysicalFourierBridge.normalizedFinite
      family ε (fun _ => a) (fun _ => 0) h δ x = density ε h a x := by
  unfold KFCausalCorrelatedClusteredPhysicalFourierBridge.normalizedFinite
  simp only [family_width,family_coefficient]
  simp [sources,polynomials,family,density,count,Index]

variable (ε h a : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a)
  (hb : |h| ≤ Real.pi*ε/3)

def state : Hilbert :=
  KFCausalCorrelatedClusteredInputProfiles.finiteState family ε h
    (fun _ => a) (fun _ => 0) hε hh (fun _ => ha) 1

def firstOutput : Hilbert :=
  KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteSeconds family ε h
    (fun _ => a) (fun _ => 0) hε hh (fun _ => ha) hb 1 7

theorem first_graph :
    (state ε h a hε hh ha,firstOutput ε h a hε hh ha hb) ∈
      (KFCausalClockFloorVacuumSquare.square ε hε h).graph := by
  rw [firstOutput,KFCausalCorrelatedClusteredVacuumSecondLimit.finiteSeconds_eq
    family ε h (fun _ => a) (fun _ => 0) hε hh (fun _ => ha) hb 1 (by norm_num)]
  exact KFCausalVacuumParameterRescale.doubled_square_graph ε hε h _ _
    (KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput_graph
      family ε h (fun _ => a) (fun _ => 0) hε hh (fun _ => ha) hb 1 (by norm_num))

theorem first_mixed :
    KFCausalPhysicalMixedCoordinates.mixedCoordinates (firstOutput ε h a hε hh ha hb) =ᵐ[volume]
      density ε h a := by
  have he := KFCausalCorrelatedClusteredPhysicalFourierBridge.original_finite_square_mixed
      family ε (fun _ => a) (fun _ => 0) hε h hh (fun _ => ha) hb 1 (by norm_num)
  filter_upwards [he] with x hx
  exact hx.trans (normalized_density ε h a 1 x)

theorem rotated_second_input (θ : ℝ) :
    clockMixed ε hε (inverseL ε hε (action h hh θ (firstOutput ε h a hε hh ha hb))) =ᵐ[volume]
      fun x => ((Real.exp (KFCausalClockFloorPairedStraightening.clockInverse ε hε x.2)+ε:ℝ):ℂ)⁻¹*
        density ε h a (rotatedPoint h hh θ (KFCausalClockFloorMixedChart.mixedMap ε hε x)) :=
  KFCausalChargeRotatedSecondInput.rotated_second_input ε hε h hh θ _ _
    (first_mixed ε h a hε hh ha hb)

#print axioms family_count
#print axioms family_width
#print axioms family_coefficient
#print axioms normalized_density
#print axioms first_graph
#print axioms first_mixed
#print axioms rotated_second_input
end
end UnifiedTheory.Audit.KFCausalSingleGaussianSecondInput
