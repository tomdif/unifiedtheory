/- The sourced analytic line is the representative of the actual inverse
clock factor and inverse coordinate unitary applied to every physical
charge modulation state. The full neutral shear is retained. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentSources
import UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (flow)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCoordinates (displacement spectatorParameter)
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (clockFunction neutralWidth)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge (amplitude inverse_clock_factor)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor)

theorem position_real_flow (s : ℝ) (x : Grouped) (i : Fin 5) :
    position (s:ℂ) x i = (flow s ![x.1 0,x.1 1,x.1 2,x.1 3,x.2] i:ℂ) := by
  have hs : complexScale (s:ℂ) = (KFCausalTransverseDilationFlow.scale s:ℂ) := by
    simp [complexScale,KFCausalTransverseDilationFlow.scale,Complex.ofReal_exp]
  fin_cases i <;> simp [position,neutral,mix,flow,hs]

theorem source_real_flow (b : Fin 5 → ℂ) (s : ℝ) (x : Grouped) :
    source b (s:ℂ) x = linearSource b (flow s ![x.1 0,x.1 1,x.1 2,x.1 3,x.2]) := by
  simp only [source,linearSource,position_real_flow]

def dampedProfile (ε a α β : ℝ) (v : Block 2) (r : Block 4) (x : Configuration) : ℂ :=
  (Real.sqrt (Real.exp x.1+ε):ℂ)⁻¹*configurationProfile α β (clockFunction ε a) v r x

theorem inverse_dampedProfile_grouping (ε a α β : ℝ) (hε : 0 < ε) (v : Block 2) (r : Block 4)
    (z : ℝ × Grouped) :
    inverseFunction ε hε (dampedProfile ε a α β v r) (grouping.symm z) =
      constant α v*line ε a α β (frequency r) (coefficients α v r) 0 z := by
  let s := (chartIso ε hε).symm z.1
  have hc : chart ε s = z.1 := (chartIso ε hε).apply_symm_apply _
  rw [grouping_symm_apply]
  simp only [line,trial,Complex.ofReal_zero,zero_mul,add_zero,complexInverse_real ε hε,
    coherentPacket,source_real_flow]
  change (amplitude ε s:ℂ)⁻¹*((Real.sqrt (Real.exp s+ε):ℂ)⁻¹*
    (constant α v*clockPhase (frequency r) (s:ℂ)*
      Complex.exp (linearSource (coefficients α v r) (flow s ![z.2.1 0,z.2.1 1,z.2.1 2,z.2.1 3,z.2.2]))*
      (clockFunction ε a s*physicalGaussian α β (flow s ![z.2.1 0,z.2.1 1,z.2.1 2,z.2.1 3,z.2.2])))) = _
  rw [← packet_real_flow α β s z.2.1 z.2.2]
  calc
    _ = constant α v*clockPhase (frequency r) (s:ℂ)*
        Complex.exp (linearSource (coefficients α v r) (flow s ![z.2.1 0,z.2.1 1,z.2.1 2,z.2.1 3,z.2.2]))*
        ((amplitude ε s:ℂ)⁻¹*((Real.sqrt (Real.exp s+ε):ℂ)⁻¹*clockFunction ε a s))*
        packet α β (s:ℂ) z.2 := by ring
    _ = _ := by rw [inverse_clock_factor ε a s hε,hc]; ring

def dampedState (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) : Hilbert :=
  inverseAction ε hε (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k)

theorem dampedState_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k,dampedState ε a hbar hε ha hh k) ∈
      (inverseClockHalf ε).graph :=
  (inverseClockHalf ε).mem_graph ⟨_,inverseClockHalf_domain ε hε _⟩

theorem dampedState_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    dampedState ε a hbar hε ha hh k =ᵐ[volume]
      dampedProfile ε a (groundWidth hbar) (neutralWidth hbar) (displacement hbar k) (spectatorParameter k) := by
  filter_upwards [inverseAction_coe ε hε (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k),
    state_configuration_coe ε a hbar hε ha hh k] with x hx hy
  exact hx.trans (congrArg (fun z : ℂ => (Real.sqrt (Real.exp x.1+ε):ℂ)⁻¹*z) hy)

theorem inverse_dampedState_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    (coordinates ε hε).symm (dampedState ε a hbar hε ha hh k) =ᵐ[volume]
      inverseFunction ε hε (dampedProfile ε a (groundWidth hbar) (neutralWidth hbar)
        (displacement hbar k) (spectatorParameter k)) := by
  filter_upwards [coordinates_inverse_coe ε hε (dampedState ε a hbar hε ha hh k),
    (coordinate_inverse_quasiMeasurePreserving ε hε).ae (dampedState_coe ε a hbar hε ha hh k)]
    with x hx hy
  rw [hx]
  unfold inverseFunction
  rw [hy]

def amplitudeConstant (hbar : ℝ) (k : Joint 2 4) : ℂ := constant (groundWidth hbar) (displacement hbar k)
def clockFrequency (k : Joint 2 4) : ℝ := frequency (spectatorParameter k)
def sourceCoefficients (hbar : ℝ) (k : Joint 2 4) : Fin 5 → ℂ :=
  coefficients (groundWidth hbar) (displacement hbar k) (spectatorParameter k)

theorem straightenedState_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    groupedCoordinates ((coordinates ε hε).symm (dampedState ε a hbar hε ha hh k)) =ᵐ[volume]
      fun z => amplitudeConstant hbar k *
        line ε a (groundWidth hbar) (neutralWidth hbar) (clockFrequency k) (sourceCoefficients hbar k) 0 z := by
  filter_upwards [groupedCoordinates_coe ((coordinates ε hε).symm (dampedState ε a hbar hε ha hh k)),
    grouping_preserves_volume.symm.quasiMeasurePreserving.ae
      (inverse_dampedState_coe ε a hbar hε ha hh k)] with z hz hz'
  exact hz.trans (hz'.trans (inverse_dampedProfile_grouping ε a _ _ hε _ _ z))

#print axioms position_real_flow
#print axioms source_real_flow
#print axioms inverse_dampedProfile_grouping
#print axioms dampedState_graph
#print axioms dampedState_coe
#print axioms inverse_dampedState_coe
#print axioms straightenedState_coe

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary
