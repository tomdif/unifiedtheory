/- The half-clock action on pure momentum converges in the original
physical Hilbert space, closing its natural graph at the momentum limit. -/
import UnifiedTheory.Audit.KFCausalHalfMomentumClockAmplitude
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumPotentialProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredHalfMomentumLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredPureMomentumLimit (finiteMomentum finiteMomentum_eq limitingMomentum momentum_tendsto)
open KFCausalCorrelatedClusteredMomentumPotentialProfiles (finiteMomentumOutput finiteMomentumOutput_graph)
open KFCausalHalfMomentumClockAmplitude (amplitudes momentumAmplitude momentumAmplitude_identity momentumAmplitude_continuous momentumAmplitude_memLp)
open KFCausalClockFloorClockHalf (halfWeight clockHalf clockHalf_graph clockHalf_selfAdjoint)
open KFCausalCorrelatedClusteredClockVectors (profile vector vector_coe)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalImaginaryShearInitialMultiplier (scale_zero)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalClockFloorPureClockMomentum (pureMomentum)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (ha : ∀ i, 0 < a i)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
local notation "d" => KFCausalCorrelatedClusteredMomentumAmplitudes.amplitudes ε a p
local notation "hd2" => fun i => KFCausalCorrelatedClusteredMomentumAmplitudes.amplitude_memLp ε (a i) (p i) hε (ha i)
local notation "c" => amplitudes ε h a p
local notation "M" => finiteMomentum f ε h a p hε hh ha
local notation "K" => fun δ => finiteMomentumOutput f ε h a p hε hh hb ha δ 0
local notation "B" => limitingMomentum f ε h a p hε hh ha
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha

theorem finiteMomentum_coe (δ : ℝ) (hδ : 0 < δ) :
    M δ =ᵐ[volume] fun x => (-Complex.I*(h:ℂ))*profile f d α β δ x := by
  rw [finiteMomentum_eq f ε h a p hε hh ha δ hδ]
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ)) (vector f d α β hα hβ hw hd2 δ),
    vector_coe f d α β hα hβ hw hd2 δ hδ] with x hs hv
  simp only [hs,Pi.smul_apply,smul_eq_mul,hv]

theorem finiteMomentum_differential_coe (δ : ℝ) (hδ : 0 < δ) :
    M δ =ᵐ[volume] fun x => (-Complex.I*(h:ℂ))*KFCausalClockFloorPureClockDerivative.differential ε
      (profile f (KFCausalCorrelatedClusteredInputProfiles.amplitudes ε a p) α β δ) x := by
  filter_upwards [finiteMomentum_coe f ε h a p hε hh ha δ hδ] with x hx
  rw [KFCausalCorrelatedClusteredClockDifferential.input_differential f α β δ ε a p hε]
  exact hx

include hε in
theorem represented_identity (δ : ℝ) (x : Configuration) :
    KFCausalCorrelatedClusteredPhysicalTransfer.represented f c α β ε 0 δ x =
      (halfWeight ε x:ℂ)*((-Complex.I*(h:ℂ))*profile f d α β δ x) := by
  unfold KFCausalCorrelatedClusteredPhysicalTransfer.represented profile
  rw [scale_zero ε x.1 hε]
  unfold KFCausalReciprocalNeutralPhysicalSliceNorm.wave
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ((f.amplitude (index f j).1*momentumAmplitude ε (a (index f j).1) (p (index f j).1) h x.1)*
    KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*_ =
    (halfWeight ε x:ℂ)*((-Complex.I*(h:ℂ))*(((f.amplitude (index f j).1*
      KFCausalCorrelatedClusteredMomentumAmplitudes.amplitude ε (a (index f j).1) (p (index f j).1) x.1)*
        KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*_))
  rw [momentumAmplitude_identity]
  unfold halfWeight
  ring

theorem finiteOutput_coe (δ : ℝ) (hδ : 0 < δ) :
    finiteMomentumOutput f ε h a p hε hh hb ha δ 0 =ᵐ[volume]
      KFCausalCorrelatedClusteredPhysicalTransfer.represented f c α β ε 0 δ := by
  have hg := finiteMomentumOutput_graph f ε h a p hε hh hb ha δ hδ 0
  change (M δ,finiteMomentumOutput f ε h a p hε hh hb ha δ 0) ∈ (clockHalf ε).graph at hg
  filter_upwards [(clockHalf_graph ε _ _).mp hg,finiteMomentum_coe f ε h a p hε hh ha δ hδ] with x hg' hb'
  rw [hg',hb',represented_identity f ε h a p hε δ x]

theorem output_exists_limit : ∃ v : Hilbert, Tendsto K (𝓝[>] 0) (𝓝 v) :=
  KFCausalCorrelatedClusteredPhysicalTransfer.exists_limit f c α β ε 0 hα hβ hw hε
    (by simp only [abs_zero]; positivity)
    (fun i => momentumAmplitude_continuous ε (a i) (p i) h hε)
    (fun i => momentumAmplitude_memLp ε (a i) (p i) h hε (ha i)) K
    (finiteOutput_coe f ε h a p hε hh hb ha)

def limitingOutput : Hilbert := Classical.choose (output_exists_limit f ε h a p hε hh hb ha)

theorem output_tendsto : Tendsto K (𝓝[>] 0) (𝓝 (limitingOutput f ε h a p hε hh hb ha)) :=
  Classical.choose_spec (output_exists_limit f ε h a p hε hh hb ha)

theorem limiting_graph : (B,limitingOutput f ε h a p hε hh hb ha) ∈ (clockHalf ε).graph := by
  apply (clockHalf_selfAdjoint ε).isClosed.mem_of_tendsto
    ((momentum_tendsto f ε h a p hε hh ha).prodMk_nhds (output_tendsto f ε h a p hε hh hb ha))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finiteMomentumOutput_graph f ε h a p hε hh hb ha δ hδ 0

include hb in
theorem limiting_domain : B ∈ (clockHalf ε).domain :=
  LinearPMap.mem_domain_of_mem_graph (limiting_graph f ε h a p hε hh hb ha)

theorem composition_graph_limit :
    (ψ,limitingOutput f ε h a p hε hh hb ha) ∈ (composition (clockHalf ε) (pureMomentum ε hε h)).graph :=
  (composition_graph _ _ _ _).mpr ⟨B,
    KFCausalCorrelatedClusteredPureMomentumLimit.limiting_graph f ε h a p hε hh ha,
    limiting_graph f ε h a p hε hh hb ha⟩

include hb in
theorem composition_domain_limit : ψ ∈ (composition (clockHalf ε) (pureMomentum ε hε h)).domain :=
  LinearPMap.mem_domain_of_mem_graph (composition_graph_limit f ε h a p hε hh hb ha)

theorem graph_tendsto :
    Tendsto (fun δ => (M δ,finiteMomentumOutput f ε h a p hε hh hb ha δ 0)) (𝓝[>] 0)
      (𝓝 (B,limitingOutput f ε h a p hε hh hb ha)) :=
  (momentum_tendsto f ε h a p hε hh ha).prodMk_nhds (output_tendsto f ε h a p hε hh hb ha)

#print axioms finiteMomentum_coe
#print axioms finiteMomentum_differential_coe
#print axioms represented_identity
#print axioms finiteOutput_coe
#print axioms output_exists_limit
#print axioms output_tendsto
#print axioms limiting_graph
#print axioms limiting_domain
#print axioms composition_graph_limit
#print axioms composition_domain_limit
#print axioms graph_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredHalfMomentumLimit
