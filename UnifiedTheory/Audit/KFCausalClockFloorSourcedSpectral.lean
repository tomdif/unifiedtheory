/- The actual ordered exponential graph for arbitrary physical Gaussian
sources. The inverse-clock output is identified with the analytic line
through the existing coordinate unitary, retaining the neutral shear. -/
import UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum
import UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (flow)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative (physicalProfile clockMultiplier)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments (sourcedPacket)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (linearSource)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (source_real_flow)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (coherentPacket)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge (amplitude inverse_clock_factor)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (clockFunction)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy (dampedClockFunction)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral
  (gaussianState configurationLine configurationLine_memLp gaussianState_exponential_graph)
open UnifiedTheory.Audit.KFCausalClockFloorExponential (longitudinalExponential)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

theorem inverse_dampedProfile (ε a α β : ℝ) (hε : 0 < ε) (C : ℂ) (p : ℝ)
    (b : Fin 5 → ℂ) (z : ℝ × Grouped) :
    inverseFunction ε hε (physicalProfile C p α β b (dampedClockFunction ε a)) (grouping.symm z) =
      C*line ε a α β p b 0 z := by
  let s := (chartIso ε hε).symm z.1
  have hc : chart ε s = z.1 := (chartIso ε hε).apply_symm_apply _
  rw [grouping_symm_apply]
  simp only [line,trial,Complex.ofReal_zero,zero_mul,add_zero,complexInverse_real ε hε,
    coherentPacket,source_real_flow]
  change (amplitude ε s:ℂ)⁻¹*((C*clockPhase p (s:ℂ)*
    ((Real.sqrt (Real.exp s+ε):ℂ)⁻¹*clockFunction ε a s))*
    (Complex.exp (linearSource b (flow s ![z.2.1 0,z.2.1 1,z.2.1 2,z.2.1 3,z.2.2]))*
      physicalGaussian α β (flow s ![z.2.1 0,z.2.1 1,z.2.1 2,z.2.1 3,z.2.2]))) = _
  rw [← packet_real_flow α β s z.2.1 z.2.2]
  calc
    _ = C*clockPhase p (s:ℂ)*
        Complex.exp (linearSource b (flow s ![z.2.1 0,z.2.1 1,z.2.1 2,z.2.1 3,z.2.2]))*
        ((amplitude ε s:ℂ)⁻¹*((Real.sqrt (Real.exp s+ε):ℂ)⁻¹*clockFunction ε a s))*
        packet α β (s:ℂ) z.2 := by ring
    _ = _ := by rw [inverse_clock_factor ε a s hε,hc]; ring

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)
local notation "S" => state ε a α β hε ha hα hβ hw C p b
local notation "D" => dampedState ε a α β hε ha hα hβ hw C p b

theorem inverse_dampedState_coe :
    (coordinates ε hε).symm D =ᵐ[volume]
      inverseFunction ε hε (physicalProfile C p α β b (dampedClockFunction ε a)) := by
  filter_upwards [coordinates_inverse_coe ε hε D,
    (coordinate_inverse_quasiMeasurePreserving ε hε).ae
      (dampedState_coe ε a α β hε ha hα hβ hw C p b)] with x hx hy
  rw [hx]
  unfold inverseFunction
  rw [hy]

theorem dampedState_gaussian :
    D = C • gaussianState ε a α β p b 0 hε ha hα hβ hw (by simp; positivity) := by
  apply (coordinates ε hε).symm.injective
  rw [map_smul]
  unfold gaussianState
  rw [LinearIsometryEquiv.symm_apply_apply]
  apply Lp.ext
  filter_upwards [inverse_dampedState_coe ε a α β hε ha hα hβ hw C p b,
    Lp.coeFn_smul C ((configurationLine_memLp ε a α β p b 0 hε ha hα hβ hw (by simp; positivity)).toLp _),
    (configurationLine_memLp ε a α β p b 0 hε ha hα hβ hw (by simp; positivity)).coeFn_toLp]
    with x hx hy hz
  rw [hx,hy]
  change _ = C * _
  rw [hz]
  have he := inverse_dampedProfile ε a α β hε C p b (grouping x)
  rw [MeasurableEquiv.symm_apply_apply] at he
  exact he

def shiftedOutput (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) : Hilbert :=
  C • gaussianState ε a α β p b (-h/2) hε ha hα hβ hw (shift_bound ε h hb)

theorem shiftedOutput_graph (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) :
    (D,shiftedOutput ε a α β hε ha hα hβ hw C p b h hb) ∈
      (longitudinalExponential ε hε h (1/2)).graph := by
  rw [dampedState_gaussian]
  exact (longitudinalExponential ε hε h (1/2)).graph.smul_mem C
    (gaussianState_exponential_graph ε a α β p b h hε ha hα hβ hw hb)

theorem state_ordered_graph (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) :
    (S,shiftedOutput ε a α β hε ha hα hβ hw C p b h hb) ∈ (orderedExponential ε hε h).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,dampedState_graph ε a α β hε ha hα hβ hw C p b,
    shiftedOutput_graph ε a α β hε ha hα hβ hw C p b h hb⟩

theorem state_ordered_domain (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) :
    S ∈ (orderedExponential ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (state_ordered_graph ε a α β hε ha hα hβ hw C p b h hb)

#print axioms inverse_dampedProfile
#print axioms inverse_dampedState_coe
#print axioms dampedState_gaussian
#print axioms shiftedOutput_graph
#print axioms state_ordered_graph
#print axioms state_ordered_domain

end
end UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral
