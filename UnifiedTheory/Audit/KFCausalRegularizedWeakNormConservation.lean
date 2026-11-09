/- Conservation of the physical norm of the constructed homogeneous weak
solution, obtained by differentiating mass-regularized energies and passing
to their limit. It implies strong continuity and strong convergence along
the constructed cutoff subsequence. Uniqueness and convergence of the full
cutoff family are not asserted here. -/
import UnifiedTheory.Audit.KFCausalRegularizedMassEnergy
import UnifiedTheory.Audit.KFCausalRegularizedEnergyLimit
import UnifiedTheory.Audit.KFCausalWeakNormStrongLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedWeakNormConservation
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedFormWindowBound
open UnifiedTheory.Audit.KFCausalRegularizedYosidaDynamics
open UnifiedTheory.Audit.KFCausalRegularizedCountableLimit
open UnifiedTheory.Audit.KFCausalRegularizedWeakTrajectory
open UnifiedTheory.Audit.KFCausalRegularizedWeakIntegralEquation
open UnifiedTheory.Audit.KFCausalRegularizedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalRegularizedMassEnergy
open UnifiedTheory.Audit.KFCausalRegularizedEnergyLimit
open UnifiedTheory.Audit.KFCausalWeakNormStrongLimit

theorem physical_norm_square_conserved (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w) (r t : ℝ) :
    ‖embedding ε hε hbar coupling 0 (V.formState t)‖^2 =
      ‖embedding ε hε hbar coupling 0 (V.formState r)‖^2 := by
  apply conserved_of_regularized_energies
    (fun n z => massEnergy ε hε hbar coupling s w V (massScale n) z)
    (fun n z => massEnergyDerivative ε hε hbar coupling s w V (massScale n) z)
    (fun z => ‖embedding ε hε hbar coupling 0 (V.formState z)‖^2) r t
    (2*massLipschitzBound ε hε hbar coupling s (max |r| |t|) w *
      windowRadius ε hε hbar coupling s (max |r| |t|) w)
  · intro n z
    exact massEnergy_derivative ε hε hbar coupling s w V _ z (massScale_pos n)
  · intro n
    exact massEnergyDerivative_continuous ε hε hbar coupling s w V _
  · intro n z hz
    exact massEnergyDerivative_window_bound ε hε hbar coupling s w V _ _ z (massScale_pos n)
      (le_max_of_le_left (abs_nonneg r)) (abs_le_window_of_mem_uIcc r t z hz)
  · exact massEnergy_tendsto ε hε hbar coupling s w V
  · exact massEnergyDerivative_tendsto_zero ε hε hbar coupling s w V

theorem physical_norm_conserved (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w) (r t : ℝ) :
    ‖embedding ε hε hbar coupling 0 (V.formState t)‖ =
      ‖embedding ε hε hbar coupling 0 (V.formState r)‖ := by
  have hh := physical_norm_square_conserved ε hε hbar coupling s w V r t
  nlinarith [norm_nonneg (embedding ε hε hbar coupling 0 (V.formState t)),
    norm_nonneg (embedding ε hε hbar coupling 0 (V.formState r))]

theorem physical_norm_initial (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w) (t : ℝ) :
    ‖embedding ε hε hbar coupling 0 (V.formState t)‖ = ‖embedding ε hε hbar coupling 0 w‖ := by
  rw [physical_norm_conserved ε hε hbar coupling s w V s t,weak_trajectory_initial]

theorem physical_state_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w) :
    Continuous (fun t => embedding ε hε hbar coupling 0 (V.formState t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply strong_of_weak_and_norm
  · intro y
    exact (weak_trajectory_weakly_continuous ε hε hbar coupling s w V y).tendsto t
  · simpa only [physical_norm_initial] using
      (tendsto_const_nhds (x := ‖embedding ε hε hbar coupling 0 w‖) (f := 𝓝 t))

theorem cutoff_subsequence_strong_convergence (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w) (t : ℝ) :
    Tendsto (fun n => dynamics ε hε hbar coupling (cutoff (V.subsequence n))
      (cutoff_pos (V.subsequence n)) s t (embedding ε hε hbar coupling 0 w)) atTop
      (𝓝 (embedding ε hε hbar coupling 0 (V.formState t))) := by
  apply strong_of_weak_and_norm (V.physicalConvergence t)
  simpa only [dynamics_norm,physical_norm_initial] using
    (tendsto_const_nhds (x := ‖embedding ε hε hbar coupling 0 w‖) (f := atTop))

#print axioms physical_norm_square_conserved
#print axioms physical_norm_conserved
#print axioms physical_norm_initial
#print axioms physical_state_continuous
#print axioms cutoff_subsequence_strong_convergence

end
end UnifiedTheory.Audit.KFCausalRegularizedWeakNormConservation
