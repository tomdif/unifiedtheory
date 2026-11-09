/- The natural second clock action exists on the physical clustered
state and its pure-clock momentum. Its original finite strong-Hamiltonian
outputs converge to the constructed full-clock vectors. -/
import UnifiedTheory.Audit.KFCausalFullMomentumClockAmplitude
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredOriginalKineticSeconds
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredHalfMomentumLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockSecondLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredClockVectors (profile profile_sum profile_transfer vector vector_coe limitingVector vector_tendsto)
open KFCausalClockFloorClockHalf (halfWeight clockHalf clockHalf_graph clockHalf_selfAdjoint)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalFullMomentumClockAmplitude
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalCorrelatedClusteredOriginalKineticSeconds (finiteSeconds finiteMomentumSeconds)

theorem profile_relation {m : ℕ} (f : Family m) (c d : ℝ → Fin m → ℂ) (α β : ℝ)
    (w : ℝ → ℂ) (hd : ∀ s i, d s i=w s*c s i) (δ : ℝ) (x : Configuration) :
    profile f d α β δ x = w x.1*profile f c α β δ x := by
  rw [profile_sum,profile_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by rw [hd]; ring)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
local notation "c" => fun s i => amplitude ε (a i) (p i) s
local notation "hc" => fun i => amplitude_continuous ε (a i) (p i)
local notation "hc2" => fun i => amplitude_memLp ε (a i) (p i) hε (ha i)
local notation "d" => amplitudes ε h a p
local notation "hd" => fun i => momentumAmplitude_continuous ε (a i) (p i) h hε
local notation "hd2" => fun i => momentumAmplitude_memLp ε (a i) (p i) h hε (ha i)
local notation "A" => KFCausalCorrelatedClusteredPhysicalCauchy.finiteOutput f ε h a p hε hh hb₀ ha
local notation "M" => KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput f ε h a p hε hh hb₀ ha
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "b" => KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha

def inputSecond : Hilbert := limitingVector f c α β hα hβ hw hc2 hc
def momentumSecond : Hilbert := limitingVector f d α β hα hβ hw hd2 hd

theorem finite_input_graph (δ : ℝ) (hδ : 0 < δ) :
    (A δ 0,vector f c α β hα hβ hw hc2 δ) ∈ (clockHalf ε).graph := by
  have hf := KFCausalCorrelatedClusteredHalfClockLimit.finiteOutput_coe f ε h a p hε hh hb₀ ha δ hδ
  rw [← profile_transfer f (KFCausalCorrelatedClusteredHalfClockLimit.amplitudes ε a p) α β ε hε δ] at hf
  rw [clockHalf_graph]
  filter_upwards [hf,vector_coe f c α β hα hβ hw hc2 δ hδ] with x hx hv
  rw [hv,hx]
  exact profile_relation f _ c α β (fun s => (Real.sqrt (Real.exp s+ε):ℂ))
    (fun s i => amplitude_half_identity ε (a i) (p i) s hε) δ x

theorem finite_momentum_graph (δ : ℝ) (hδ : 0 < δ) :
    (M δ 0,vector f d α β hα hβ hw hd2 δ) ∈ (clockHalf ε).graph := by
  have hf := KFCausalCorrelatedClusteredHalfMomentumLimit.finiteOutput_coe f ε h a p hε hh hb₀ ha δ hδ
  rw [← profile_transfer f (KFCausalHalfMomentumClockAmplitude.amplitudes ε h a p) α β ε hε δ] at hf
  rw [clockHalf_graph]
  filter_upwards [hf,vector_coe f d α β hα hβ hw hd2 δ hδ] with x hx hv
  rw [hv,hx]
  exact profile_relation f _ d α β (fun s => (Real.sqrt (Real.exp s+ε):ℂ))
    (fun s i => momentumAmplitude_half_identity ε (a i) (p i) h s hε) δ x

theorem finiteSeconds_eq (δ : ℝ) (hδ : 0 < δ) :
    finiteSeconds f ε h a p hε hh ha hb δ 0 = vector f c α β hα hβ hw hc2 δ :=
  (clockHalf ε).mem_graph_snd_inj'
    (KFCausalCorrelatedClusteredOriginalKineticSeconds.finite_reverse_graph f ε h a p hε hh ha hb δ hδ 0)
    (finite_input_graph f ε h a p hε hh ha hb δ hδ) rfl

theorem finiteMomentumSeconds_eq (δ : ℝ) (hδ : 0 < δ) :
    finiteMomentumSeconds f ε h a p hε hh ha hb δ 0 = vector f d α β hα hβ hw hd2 δ :=
  (clockHalf ε).mem_graph_snd_inj'
    (KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteMomentum_reverse_graph f ε h a p hε hh ha hb δ hδ 0)
    (finite_momentum_graph f ε h a p hε hh ha hb δ hδ) rfl

theorem inputSecond_tendsto :
    Tendsto (fun δ => finiteSeconds f ε h a p hε hh ha hb δ 0) (𝓝[>] 0)
      (𝓝 (inputSecond f ε h a p hε hh ha)) := by
  apply Tendsto.congr' _ (vector_tendsto f c α β hα hβ hw hc2 hc)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteSeconds_eq f ε h a p hε hh ha hb δ hδ).symm

theorem momentumSecond_tendsto :
    Tendsto (fun δ => finiteMomentumSeconds f ε h a p hε hh ha hb δ 0) (𝓝[>] 0)
      (𝓝 (momentumSecond f ε h a p hε hh ha)) := by
  apply Tendsto.congr' _ (vector_tendsto f d α β hα hβ hw hd2 hd)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteMomentumSeconds_eq f ε h a p hε hh ha hb δ hδ).symm

theorem input_reverse_graph :
    (KFCausalCorrelatedClusteredHalfClockLimit.limitingOutput f ε h a p hε hh hb₀ ha,
      inputSecond f ε h a p hε hh ha) ∈ (clockHalf ε).graph := by
  apply (clockHalf_selfAdjoint ε).isClosed.mem_of_tendsto
    ((KFCausalCorrelatedClusteredHalfClockLimit.output_tendsto f ε h a p hε hh hb₀ ha).prodMk_nhds
      (vector_tendsto f c α β hα hβ hw hc2 hc))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_input_graph f ε h a p hε hh ha hb δ hδ

theorem momentum_reverse_graph :
    (KFCausalCorrelatedClusteredHalfMomentumLimit.limitingOutput f ε h a p hε hh hb₀ ha,
      momentumSecond f ε h a p hε hh ha) ∈ (clockHalf ε).graph := by
  apply (clockHalf_selfAdjoint ε).isClosed.mem_of_tendsto
    ((KFCausalCorrelatedClusteredHalfMomentumLimit.output_tendsto f ε h a p hε hh hb₀ ha).prodMk_nhds
      (vector_tendsto f d α β hα hβ hw hd2 hd))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_momentum_graph f ε h a p hε hh ha hb δ hδ

include hb in
theorem input_second_graph :
    (ψ,inputSecond f ε h a p hε hh ha) ∈ (composition (clockHalf ε) (clockHalf ε)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,
    KFCausalCorrelatedClusteredHalfClockLimit.limiting_graph f ε h a p hε hh hb₀ ha,
    input_reverse_graph f ε h a p hε hh ha hb⟩

include hb in
theorem momentum_second_graph :
    (b,momentumSecond f ε h a p hε hh ha) ∈ (composition (clockHalf ε) (clockHalf ε)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,
    KFCausalCorrelatedClusteredHalfMomentumLimit.limiting_graph f ε h a p hε hh hb₀ ha,
    momentum_reverse_graph f ε h a p hε hh ha hb⟩

include hb in
theorem second_domains : ψ ∈ (composition (clockHalf ε) (clockHalf ε)).domain ∧
    b ∈ (composition (clockHalf ε) (clockHalf ε)).domain :=
  ⟨LinearPMap.mem_domain_of_mem_graph (input_second_graph f ε h a p hε hh ha hb),
   LinearPMap.mem_domain_of_mem_graph (momentum_second_graph f ε h a p hε hh ha hb)⟩

#print axioms profile_relation
#print axioms finite_input_graph
#print axioms finite_momentum_graph
#print axioms finiteSeconds_eq
#print axioms finiteMomentumSeconds_eq
#print axioms inputSecond_tendsto
#print axioms momentumSecond_tendsto
#print axioms input_reverse_graph
#print axioms momentum_reverse_graph
#print axioms input_second_graph
#print axioms momentum_second_graph
#print axioms second_domains
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockSecondLimit
