/- The quadrupled vacuum-parameter exponential has actual Hilbert limits on both
physical clustered inputs. Derived shifted clock coefficients discharge
the L2 hypotheses; closed natural graphs identify the limiting actions. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredQuadrupleVacuumProfiles
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumPotentialLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredQuadrupleVacuumLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredQuadrupleVacuumProfiles
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalClockFloorBoundedInverse (orderedExponential_closed inverseL)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalClockFloorVacuumSquare (exponential_rescale)
open KFCausalClockFloorBoundedInverse (ordered_graph_iff)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |2*h| ≤ Real.pi*ε/3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hy" => le_trans (le_of_eq (abs_neg (2*h))) hb
local notation "c" => inputAmplitudes ε h a p
local notation "d" => momentumAmplitudes ε h a p
local notation "U" => finiteOutput f ε h a p hε hh ha hb
local notation "V" => finiteMomentumOutput f ε h a p hε hh ha hb
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "B" => KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha

theorem output_exists_limit : ∃ v : Hilbert, Tendsto U (𝓝[>] 0) (𝓝 v) :=
  KFCausalCorrelatedClusteredPhysicalTransfer.exists_limit f c α β ε (-(2*h))
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy
    (fun i => (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε (a i) (p i) (-(2*h)) hε hy).continuous)
    (fun i => KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε (a i) (p i) (-(2*h)) hε (ha i) hy)
    U (finiteOutput_coe f ε h a p hε hh ha hb)

theorem momentumOutput_exists_limit : ∃ v : Hilbert, Tendsto V (𝓝[>] 0) (𝓝 v) :=
  KFCausalCorrelatedClusteredPhysicalTransfer.exists_limit f d α β ε (-(2*h))
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy
    (fun i => KFCausalShiftedMomentumClockAmplitude.amplitude_continuous ε (a i) (p i) (-(2*h)) h hε hy)
    (fun i => KFCausalShiftedMomentumClockAmplitude.amplitude_memLp ε (a i) (p i) (-(2*h)) h hε (ha i) hy)
    V (finiteMomentumOutput_coe f ε h a p hε hh ha hb)

def limitingOutput : Hilbert := Classical.choose (output_exists_limit f ε h a p hε hh ha hb)
def limitingMomentumOutput : Hilbert := Classical.choose (momentumOutput_exists_limit f ε h a p hε hh ha hb)

theorem output_tendsto : Tendsto U (𝓝[>] 0) (𝓝 (limitingOutput f ε h a p hε hh ha hb)) :=
  Classical.choose_spec (output_exists_limit f ε h a p hε hh ha hb)

theorem momentumOutput_tendsto : Tendsto V (𝓝[>] 0) (𝓝 (limitingMomentumOutput f ε h a p hε hh ha hb)) :=
  Classical.choose_spec (momentumOutput_exists_limit f ε h a p hε hh ha hb)

theorem limiting_graph : (ψ,limitingOutput f ε h a p hε hh ha hb) ∈
    (orderedExponential ε hε (4*h)).graph := by
  apply (orderedExponential_closed ε hε (4*h)).mem_of_tendsto
    ((KFCausalCorrelatedClusteredInputGraphLimit.state_tendsto f ε h a p hε hh ha).prodMk_nhds
      (output_tendsto f ε h a p hε hh ha hb))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finiteOutput_graph f ε h a p hε hh ha hb δ hδ

theorem limitingMomentum_graph : (B,limitingMomentumOutput f ε h a p hε hh ha hb) ∈
    (orderedExponential ε hε (4*h)).graph := by
  apply (orderedExponential_closed ε hε (4*h)).mem_of_tendsto
    ((KFCausalCorrelatedClusteredPureMomentumLimit.momentum_tendsto f ε h a p hε hh ha).prodMk_nhds
      (momentumOutput_tendsto f ε h a p hε hh ha hb))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finiteMomentumOutput_graph f ε h a p hε hh ha hb δ hδ

theorem input_spectral_graph : (inverseL ε hε ψ,limitingOutput f ε h a p hε hh ha hb) ∈
    (longitudinalExponential ε hε h 2).graph := by
  have hg := (ordered_graph_iff ε hε (4*h) _ _).mp (limiting_graph f ε h a p hε hh ha hb)
  simpa only [show (1/2:ℝ)*4=2 by norm_num] using
    (exponential_rescale ε hε h 4 (1/2) _ _).mp hg

theorem momentum_spectral_graph : (inverseL ε hε B,limitingMomentumOutput f ε h a p hε hh ha hb) ∈
    (longitudinalExponential ε hε h 2).graph := by
  have hg := (ordered_graph_iff ε hε (4*h) _ _).mp (limitingMomentum_graph f ε h a p hε hh ha hb)
  simpa only [show (1/2:ℝ)*4=2 by norm_num] using
    (exponential_rescale ε hε h 4 (1/2) _ _).mp hg

#print axioms output_exists_limit
#print axioms momentumOutput_exists_limit
#print axioms output_tendsto
#print axioms momentumOutput_tendsto
#print axioms limiting_graph
#print axioms limitingMomentum_graph
#print axioms input_spectral_graph
#print axioms momentum_spectral_graph
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredQuadrupleVacuumLimit
