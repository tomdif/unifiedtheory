/- The charge-averaged vacuum shear and response are nonnegative on every
finite complex coherent superposition. This uses the derived interpolation
comparison and actual initial cancellation, not an assumed sign or an
identification with the full Hamiltonian evolution derivative. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearQuarterComparison
import UnifiedTheory.Audit.KFCausalPeriodicFourTermAverage
import UnifiedTheory.Audit.KFCausalAveragedShearPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalCoherentVacuumShearSign
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state action_state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput state_ordered_graph)
open UnifiedTheory.Audit.KFCausalCoherentShearCompositions (shiftedShearOutput shiftedOutput_shear_graph)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalImaginaryShearQuarterComparison
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalAveragedShearPairing (meanShear pairing)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
variable {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)

def orbitInput (θ : ℝ) : Hilbert := ∑ i, z i • shiftedOutput ε a h hε ha hh hb (parameter (2*Real.pi*θ) (k i))
def orbitShear (θ : ℝ) : Hilbert := ∑ i, z i • shiftedShearOutput ε a h hε ha hh hb (parameter (2*Real.pi*θ) (k i))
local notation "G" => orbitInput ε a h hε ha hh hb k z
local notation "J" => orbitShear ε a h hε ha hh hb k z

theorem input_continuous : Continuous G :=
  continuous_finset_sum _ (fun i _ =>
    ((KFCausalClockFloorCoherentShiftedOrbit.shiftedOutput_orbit_continuous ε a h hε ha hh hb (k i)).comp
      (continuous_const.mul continuous_id)).const_smul (z i))

theorem shear_continuous : Continuous J :=
  continuous_finset_sum _ (fun i _ =>
    ((KFCausalCoherentShearOrbit.shiftedShearOutput_orbit_continuous ε a h hε ha hh hb (k i)).comp
      (continuous_const.mul continuous_id)).const_smul (z i))

theorem shear_graph (θ : ℝ) : (G θ,J θ) ∈ (shearMomentum h).graph :=
  KFCausalImaginaryShearSuperposition.graph_sum h z _ _ (fun i =>
    shiftedOutput_shear_graph ε a h hε ha hh hb (parameter (2*Real.pi*θ) (k i)))

theorem ordered_graph (θ : ℝ) :
    (action h hh (2*Real.pi*θ) (∑ i, z i • state ε a h hε ha hh (k i)),G θ) ∈
      (orderedExponential ε hε h).graph := by
  rw [map_sum]
  simp_rw [map_smul,action_state]
  have hs := (orderedExponential ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => (orderedExponential ε hε h).graph.smul_mem (z i)
      (state_ordered_graph ε a h hε ha hh hb (parameter (2*Real.pi*θ) (k i))))
  simpa only [Prod.smul_mk,← prod_mk_sum] using hs

theorem meanShear_nonnegative : 0 ≤ meanShear ε h hε hh hb G J := by
  change 0 ≤ ∫ θ, finalPair ε a h hε ha hh hb k z (2*Real.pi*θ) ∂angleMeasure
  refine KFCausalPeriodicFourTermAverage.nonnegative
    (fun θ => finalPair ε a h hε ha hh hb k z (2*Real.pi*θ))
    ((finalPair_continuous ε a h hε ha hh hb k z).comp (continuous_const.mul continuous_id))
    ?_ (1/4) (1/2) (-1/4) ?_
  · intro θ
    change finalPair ε a h hε ha hh hb k z (2*Real.pi*(θ+1)) =
      finalPair ε a h hε ha hh hb k z (2*Real.pi*θ)
    rw [mul_add,mul_one]
    exact finalPair_periodic ε a h hε ha hh hb k z (2*Real.pi*θ)
  · intro θ
    dsimp only
    rw [show 2*Real.pi*(θ+1/4) = 2*Real.pi*θ+Real.pi/2 by ring,
      show 2*Real.pi*(θ+1/2) = 2*Real.pi*θ+Real.pi by ring,
      show 2*Real.pi*(θ+(-1/4)) = 2*Real.pi*θ+(-Real.pi/2) by ring]
    exact final_four_nonnegative ε a h hε ha hh hb k z (2*Real.pi*θ)

theorem meanShear_nonnegative_actual_outputs (g j : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) (∑ i, z i • state ε a h hε ha hh (k i)),g θ) ∈
      (orderedExponential ε hε h).graph ∧ (g θ,j θ) ∈ (shearMomentum h).graph) :
    0 ≤ meanShear ε h hε hh hb g j := by
  have he := KFCausalAveragedShearPairing.meanShear_unique ε h hε hh hb
    (∑ i, z i • state ε a h hε ha hh (k i)) G J g j
    (fun θ => ⟨ordered_graph ε a h hε ha hh hb k z θ,shear_graph ε a h hε ha hh hb k z θ⟩) hg
  rw [← he]
  exact meanShear_nonnegative ε a h hε ha hh hb k z

theorem vacuum_response_lower_bound :
    (∫ θ, KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb (G θ) ∂angleMeasure) ≤
      ∫ θ, KFCausalClockFloorPureClockVacuumResponse.response ε hε h hb (G θ) (J θ) ∂angleMeasure := by
  rw [KFCausalAveragedShearPairing.response_integral_split ε h hε hh hb G J
    (input_continuous ε a h hε ha hh hb k z) (shear_continuous ε a h hε ha hh hb k z)
    (shear_graph ε a h hε ha hh hb k z)]
  exact le_add_of_nonneg_right
    (mul_nonneg (by positivity) (meanShear_nonnegative ε a h hε ha hh hb k z))

theorem vacuum_response_nonnegative :
    0 ≤ ∫ θ, KFCausalClockFloorPureClockVacuumResponse.response ε hε h hb (G θ) (J θ) ∂angleMeasure :=
  (integral_nonneg (fun θ =>
    (KFCausalClockFloorVacuumMomentumResponse.response_bounds ε hε h hb (G θ)).1)).trans
      (vacuum_response_lower_bound ε a h hε ha hh hb k z)

theorem scaled_shear_nonnegative (κ t : ℝ) (hκ : 0 ≤ κ) :
    0 ≤ (4*κ*Real.exp (2*t)/ε^2)*meanShear ε h hε hh hb G J :=
  mul_nonneg (by positivity) (meanShear_nonnegative ε a h hε ha hh hb k z)

#print axioms input_continuous
#print axioms shear_continuous
#print axioms shear_graph
#print axioms ordered_graph
#print axioms meanShear_nonnegative
#print axioms meanShear_nonnegative_actual_outputs
#print axioms vacuum_response_lower_bound
#print axioms vacuum_response_nonnegative
#print axioms scaled_shear_nonnegative
end
end UnifiedTheory.Audit.KFCausalCoherentVacuumShearSign
