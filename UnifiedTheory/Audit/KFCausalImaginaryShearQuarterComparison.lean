/- The modified initial endpoint cancels in four charge directions.
Combining the four proved interpolation inequalities gives a nonnegative
sum of final expectations, with every superposition cross term retained. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearInitialRegularity
import UnifiedTheory.Audit.KFCausalWeightedQuarterShearCancellation
import UnifiedTheory.Audit.KFCausalCoherentShearOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalImaginaryShearQuarterComparison
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter parameter_compose parameter_period)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoherentBridge (coherentSeed)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalCoherentShearCompositions (shiftedShearOutput)
open UnifiedTheory.Audit.KFCausalImaginaryShearInitialRegularity
open UnifiedTheory.Audit.KFCausalWeightedQuarterShearCancellation
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
variable {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)
local notation "W" => KFCausalClockFloorShearWeight.root ε hε h hb hh

def initial (θ : ℝ) : Hilbert :=
  KFCausalImaginaryShearCoherentBridge.input ε a h hε ha hh hb (fun i => parameter θ (k i)) z 0
def initialOutput (θ : ℝ) : Hilbert :=
  KFCausalImaginaryShearCoherentBridge.shear ε a h hε ha hh hb (fun i => parameter θ (k i)) z 0
def initialPair (θ : ℝ) : ℝ :=
  (inner ℂ (W (initial ε a h hε ha hh hb k z θ)) (W (initialOutput ε a h hε ha hh hb k z θ))).re
def finalPair (θ : ℝ) : ℝ :=
  (inner ℂ (W (∑ i, z i • shiftedOutput ε a h hε ha hh hb (parameter θ (k i))))
    (W (∑ i, z i • shiftedShearOutput ε a h hε ha hh hb (parameter θ (k i))))).re

theorem initial_rotate (θ φ : ℝ) : action h hh φ (initial ε a h hε ha hh hb k z θ) =
    initial ε a h hε ha hh hb k z (θ+φ) := by
  have he := KFCausalImaginaryShearInitialEndpoint.initial_charge ε a h hε hb ha hh φ
    (fun i => parameter θ (k i)) z
  simpa only [parameter_compose] using he.symm

theorem initial_graph (θ : ℝ) :
    (initial ε a h hε ha hh hb k z θ,initialOutput ε a h hε ha hh hb k z θ) ∈ (shearMomentum h).graph :=
  KFCausalImaginaryShearSuperposition.input_graph ε h hε hb
    (fun i => coherentSeed a h ha hh (parameter θ (k i)))
    (fun i => z i*amplitudeConstant h (parameter θ (k i))) hh ⟨0,by constructor <;> norm_num⟩

theorem initial_four_cancel (θ : ℝ) :
    initialPair ε a h hε ha hh hb k z θ+initialPair ε a h hε ha hh hb k z (θ+Real.pi/2)+
      initialPair ε a h hε ha hh hb k z (θ+Real.pi)+initialPair ε a h hε ha hh hb k z (θ+(-Real.pi/2)) = 0 := by
  have hg (φ : ℝ) : (action h hh φ (initial ε a h hε ha hh hb k z θ),
      initialOutput ε a h hε ha hh hb k z (θ+φ)) ∈ (shearMomentum h).graph := by
    rw [initial_rotate]
    exact initial_graph ε a h hε ha hh hb k z (θ+φ)
  have hc := four_pairings_cancel h hh W (root_charge h hh ε hε hb)
    (initial ε a h hε ha hh hb k z θ)
    (initialOutput ε a h hε ha hh hb k z (θ+0))
    (initialOutput ε a h hε ha hh hb k z (θ+Real.pi/2))
    (initialOutput ε a h hε ha hh hb k z (θ+Real.pi))
    (initialOutput ε a h hε ha hh hb k z (θ+(-Real.pi/2)))
    (mixedSum ε a h (fun i => parameter θ (k i)) z)
    (initial_coordinates ε a h hε ha hh hb (fun i => parameter θ (k i)) z)
    ((mixedSum_smooth ε a h hε hb (fun i => parameter θ (k i)) z).differentiable (by norm_num))
    (hg 0) (hg (Real.pi/2)) (hg Real.pi) (hg (-Real.pi/2))
  simpa only [initial_rotate,add_zero,initialPair] using hc

theorem endpoint_comparison (θ : ℝ) : initialPair ε a h hε ha hh hb k z θ ≤ finalPair ε a h hε ha hh hb k z θ :=
  KFCausalImaginaryShearCoherentBridge.charge_angle_comparison ε a h hε ha hh hb k z θ

theorem final_four_nonnegative (θ : ℝ) :
    0 ≤ finalPair ε a h hε ha hh hb k z θ+finalPair ε a h hε ha hh hb k z (θ+Real.pi/2)+
      finalPair ε a h hε ha hh hb k z (θ+Real.pi)+finalPair ε a h hε ha hh hb k z (θ+(-Real.pi/2)) := by
  have hc := initial_four_cancel ε a h hε ha hh hb k z θ
  have h0 := endpoint_comparison ε a h hε ha hh hb k z θ
  have h1 := endpoint_comparison ε a h hε ha hh hb k z (θ+Real.pi/2)
  have h2 := endpoint_comparison ε a h hε ha hh hb k z (θ+Real.pi)
  have h3 := endpoint_comparison ε a h hε ha hh hb k z (θ+(-Real.pi/2))
  linarith

theorem finalPair_continuous : Continuous (finalPair ε a h hε ha hh hb k z) := by
  have hg := continuous_finset_sum Finset.univ (fun (i : Fin n) _ =>
    (KFCausalClockFloorCoherentShiftedOrbit.shiftedOutput_orbit_continuous ε a h hε ha hh hb (k i)).const_smul (z i))
  have hj := continuous_finset_sum Finset.univ (fun (i : Fin n) _ =>
    (KFCausalCoherentShearOrbit.shiftedShearOutput_orbit_continuous ε a h hε ha hh hb (k i)).const_smul (z i))
  exact Complex.continuous_re.comp (((W).continuous.comp hg).inner ((W).continuous.comp hj))

theorem finalPair_periodic : Function.Periodic (finalPair ε a h hε ha hh hb k z) (2*Real.pi) := by
  intro θ
  simp only [finalPair,parameter_period]

#print axioms initial_rotate
#print axioms initial_graph
#print axioms initial_four_cancel
#print axioms endpoint_comparison
#print axioms final_four_nonnegative
#print axioms finalPair_continuous
#print axioms finalPair_periodic
end
end UnifiedTheory.Audit.KFCausalImaginaryShearQuarterComparison
