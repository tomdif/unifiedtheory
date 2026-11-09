/- The actual half-clock output converges with the input. Closedness
places the clustered limit in the natural half-clock domain. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredHalfClockLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalCorrelatedClusteredInputProfiles (inputAmplitude finiteState finiteState_coe)
open KFCausalCorrelatedClusteredInputGraphLimit (limitingState state_tendsto finite_output_graph)
open KFCausalCorrelatedClusteredPhysicalCauchy (finiteOutput)
open KFCausalClockFloorClockHalf (halfWeight clockHalf clockHalf_graph clockHalf_selfAdjoint)
open KFCausalClockFloorTrialClockEnergy (halfClockFunction halfClockFunction_continuous halfClockFunction_memLp)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalClockFloorCoherentDerivative (clockMultiplier_memLp)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalImaginaryShearInitialMultiplier (scale_zero)
open KFCausalCorrelatedClusteredL2Error (errorMass)

def amplitude (ε a p s : ℝ) : ℂ := clockPhase p (s:ℂ)*halfClockFunction ε a s

theorem amplitude_continuous (ε a p : ℝ) : Continuous (amplitude ε a p) := by
  have hc : Continuous (fun s : ℝ => clockPhase p (s:ℂ)) := by unfold clockPhase; fun_prop
  exact hc.mul (halfClockFunction_continuous ε a)

theorem amplitude_memLp (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    MemLp (amplitude ε a p) 2 volume := by
  have hm := clockMultiplier_memLp 1 p (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha)
  change MemLp (fun s : ℝ => 1*clockPhase p (s:ℂ)*halfClockFunction ε a s) 2 volume at hm
  simpa only [one_mul] using hm

def amplitudes {m : ℕ} (ε : ℝ) (a p : Fin m → ℝ) (s : ℝ) (i : Fin m) : ℂ := amplitude ε (a i) (p i) s

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (ha : ∀ i, 0 < a i)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "c" => amplitudes ε a p
local notation "U" => finiteState f ε h a p hε hh ha
local notation "V" => fun δ => finiteOutput f ε h a p hε hh hb ha δ 0

include hε in
theorem represented_identity (δ : ℝ) (x : Configuration) :
    KFCausalCorrelatedClusteredPhysicalTransfer.represented f c α β ε 0 δ x =
      (halfWeight ε x:ℂ)*KFCausalCorrelatedClusteredInputProfiles.represented f ε h a p δ x := by
  unfold KFCausalCorrelatedClusteredPhysicalTransfer.represented KFCausalCorrelatedClusteredInputProfiles.represented
  rw [scale_zero ε x.1 hε]
  unfold KFCausalReciprocalNeutralPhysicalSliceNorm.wave
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ((f.amplitude (index f j).1*amplitude ε (a (index f j).1) (p (index f j).1) x.1)*
      KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*_ =
    (halfWeight ε x:ℂ)*(((f.amplitude (index f j).1*inputAmplitude ε (a (index f j).1) (p (index f j).1) x.1)*
      KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*_)
  unfold amplitude halfClockFunction halfWeight inputAmplitude
  ring

theorem finiteOutput_coe (δ : ℝ) (hδ : 0 < δ) :
    finiteOutput f ε h a p hε hh hb ha δ 0 =ᵐ[volume]
      KFCausalCorrelatedClusteredPhysicalTransfer.represented f c α β ε 0 δ := by
  have hg := finite_output_graph f ε h a p hε hh ha hb δ hδ 0
  change (U δ,finiteOutput f ε h a p hε hh hb ha δ 0) ∈ (clockHalf ε).graph at hg
  have he := (clockHalf_graph ε _ _).mp hg
  filter_upwards [he,finiteState_coe f ε h a p hε hh ha δ hδ] with x hv hu
  rw [hv,hu,represented_identity f ε h a p hε δ x]

theorem output_distance_bound (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ‖finiteOutput f ε h a p hε hh hb ha δ 0-finiteOutput f ε h a p hε hh hb ha η 0‖^2 ≤
      2*errorMass f c α β ε 0 δ+2*errorMass f c α β ε 0 η := by
  apply KFCausalCorrelatedClusteredPhysicalTransfer.distance_bound f c α β ε 0
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε
    (by simp only [abs_zero]; positivity)
    (fun i => amplitude_continuous ε (a i) (p i)) (fun i => amplitude_memLp ε (a i) (p i) hε (ha i))
    V (finiteOutput_coe f ε h a p hε hh hb ha) δ η hδ hη

theorem output_exists_limit : ∃ v : Hilbert, Tendsto V (𝓝[>] 0) (𝓝 v) := by
  apply KFCausalCorrelatedClusteredPhysicalTransfer.exists_limit f c α β ε 0
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε
    (by simp only [abs_zero]; positivity)
    (fun i => amplitude_continuous ε (a i) (p i)) (fun i => amplitude_memLp ε (a i) (p i) hε (ha i))
    V (finiteOutput_coe f ε h a p hε hh hb ha)

def limitingOutput : Hilbert := Classical.choose (output_exists_limit f ε h a p hε hh hb ha)

theorem output_tendsto : Tendsto V (𝓝[>] 0) (𝓝 (limitingOutput f ε h a p hε hh hb ha)) :=
  Classical.choose_spec (output_exists_limit f ε h a p hε hh hb ha)

theorem limiting_graph :
    (limitingState f ε h a p hε hh ha,limitingOutput f ε h a p hε hh hb ha) ∈ (clockHalf ε).graph := by
  apply (clockHalf_selfAdjoint ε).isClosed.mem_of_tendsto
    ((state_tendsto f ε h a p hε hh ha).prodMk_nhds (output_tendsto f ε h a p hε hh hb ha))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_output_graph f ε h a p hε hh ha hb δ hδ 0

include hb in
theorem limiting_domain : limitingState f ε h a p hε hh ha ∈ (clockHalf ε).domain :=
  LinearPMap.mem_domain_of_mem_graph (limiting_graph f ε h a p hε hh hb ha)

theorem graph_tendsto :
    Tendsto (fun δ => (U δ,finiteOutput f ε h a p hε hh hb ha δ 0)) (𝓝[>] 0)
      (𝓝 (limitingState f ε h a p hε hh ha,limitingOutput f ε h a p hε hh hb ha)) :=
  (state_tendsto f ε h a p hε hh ha).prodMk_nhds (output_tendsto f ε h a p hε hh hb ha)

#print axioms amplitude_continuous
#print axioms amplitude_memLp
#print axioms represented_identity
#print axioms finiteOutput_coe
#print axioms output_distance_bound
#print axioms output_exists_limit
#print axioms output_tendsto
#print axioms limiting_graph
#print axioms limiting_domain
#print axioms graph_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredHalfClockLimit
