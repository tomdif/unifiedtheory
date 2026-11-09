/- Both orders of the half-clock and pure momentum act on the
limiting input. Their actual clock response obeys the established
state-independent bounds, with no trajectory regularity assumed. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredHalfMomentumLimit
import UnifiedTheory.Audit.KFCausalClockHalfMomentumDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockCompositionLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredInputProfiles (finiteState finiteState_coe)
open KFCausalCorrelatedClusteredPhysicalCauchy (finiteOutput)
open KFCausalCorrelatedClusteredMomentumPotentialProfiles (finiteMomentumOutput finiteMomentumOutput_graph)
open KFCausalCorrelatedClusteredPureMomentumLimit (finiteMomentum limitingMomentum)
open KFCausalClockFloorPureClockMomentum (pureMomentum pure_closed)
open KFCausalClockFloorPureClockKinetic (correction)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (ha : ∀ i, 0 < a i)
local notation "U" => finiteState f ε h a p hε hh ha
local notation "A" => fun δ => finiteOutput f ε h a p hε hh hb ha δ 0
local notation "M" => finiteMomentum f ε h a p hε hh ha
local notation "K" => fun δ => finiteMomentumOutput f ε h a p hε hh hb ha δ 0
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "v" => KFCausalCorrelatedClusteredHalfClockLimit.limitingOutput f ε h a p hε hh hb ha
local notation "b" => limitingMomentum f ε h a p hε hh ha
local notation "k" => KFCausalCorrelatedClusteredHalfMomentumLimit.limitingOutput f ε h a p hε hh hb ha

theorem finite_reverse_graph (δ : ℝ) (hδ : 0 < δ) :
    (finiteOutput f ε h a p hε hh hb ha δ 0,
      finiteMomentumOutput f ε h a p hε hh hb ha δ 0-
        correction ε hε h (finiteOutput f ε h a p hε hh hb ha δ 0)) ∈ (pureMomentum ε hε h).graph := by
  let F := KFCausalCorrelatedClusteredClockVectors.profile f
    (KFCausalCorrelatedClusteredInputProfiles.amplitudes ε a p)
    (KFCausalChargeGaussianGeometry.groundWidth h) (KFCausalClockFloorInvariantTrial.neutralWidth h) δ
  have hs : Differentiable ℝ F := KFCausalCorrelatedClusteredClockDifferential.profile_differentiable f _ _ _ δ
    (fun i s => (KFCausalCorrelatedClusteredMomentumAmplitudes.input_derivative ε (a i) (p i) s hε).differentiableAt)
  have hg : (U δ,A δ) ∈ (clockHalf ε).graph :=
    KFCausalCorrelatedClusteredInputGraphLimit.finite_output_graph f ε h a p hε hh ha hb δ hδ 0
  have hk : (M δ,K δ) ∈ (clockHalf ε).graph := finiteMomentumOutput_graph f ε h a p hε hh hb ha δ hδ 0
  have hd := KFCausalClockHalfMomentumDifferential.half_momentum_domain ε hε h hh F hs
    (U δ) (M δ) (A δ) (K δ) (finiteState_coe f ε h a p hε hh ha δ hδ)
    (KFCausalCorrelatedClusteredHalfMomentumLimit.finiteMomentum_differential_coe f ε h a p hε hh ha δ hδ) hg hk
  let bg := (pureMomentum ε hε h) ⟨A δ,hd⟩
  have hbg : (A δ,bg) ∈ (pureMomentum ε hε h).graph := (pureMomentum ε hε h).mem_graph ⟨A δ,hd⟩
  have he : bg = K δ-correction ε hε h (A δ) := by
    have hc := KFCausalClockFloorPureClockClockResponse.commutator ε hε h hh
      (U δ) (A δ) (M δ) (K δ) bg hg
      (KFCausalCorrelatedClusteredPureMomentumLimit.finite_graph f ε h a p hε hh ha δ hδ) hk hbg
    simpa only [sub_eq_add_neg,add_comm] using sub_eq_iff_eq_add.mp hc
  exact he ▸ hbg

theorem reverse_graph_tendsto :
    Tendsto (fun δ => (finiteOutput f ε h a p hε hh hb ha δ 0,
      finiteMomentumOutput f ε h a p hε hh hb ha δ 0-
        correction ε hε h (finiteOutput f ε h a p hε hh hb ha δ 0)))
      (𝓝[>] 0) (𝓝 (v,k-correction ε hε h v)) := by
  have hv := KFCausalCorrelatedClusteredHalfClockLimit.output_tendsto f ε h a p hε hh hb ha
  have hk := KFCausalCorrelatedClusteredHalfMomentumLimit.output_tendsto f ε h a p hε hh hb ha
  exact hv.prodMk_nhds (hk.sub (((correction ε hε h).continuous.tendsto _).comp hv))

theorem limiting_reverse_graph : (v,k-correction ε hε h v) ∈ (pureMomentum ε hε h).graph := by
  apply (pure_closed ε hε h hh).mem_of_tendsto (reverse_graph_tendsto f ε h a p hε hh hb ha)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_reverse_graph f ε h a p hε hh hb ha δ hδ

theorem limiting_reverse_domain : v ∈ (pureMomentum ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (limiting_reverse_graph f ε h a p hε hh hb ha)

theorem reverse_composition_graph :
    (ψ,k-correction ε hε h v) ∈ (composition (pureMomentum ε hε h) (clockHalf ε)).graph :=
  (composition_graph _ _ _ _).mpr ⟨v,
    KFCausalCorrelatedClusteredHalfClockLimit.limiting_graph f ε h a p hε hh hb ha,
    limiting_reverse_graph f ε h a p hε hh hb ha⟩

include hb in
theorem reverse_composition_domain : ψ ∈ (composition (pureMomentum ε hε h) (clockHalf ε)).domain :=
  LinearPMap.mem_domain_of_mem_graph (reverse_composition_graph f ε h a p hε hh hb ha)

theorem clock_response_identity : (-2/h)*(inner ℂ v k).im =
    -KFCausalClockFloorPureClockKineticResponse.response ε hε v :=
  KFCausalClockFloorPureClockClockResponse.weak_response ε hε h hh ψ v b k (k-correction ε hε h v)
    (KFCausalCorrelatedClusteredHalfClockLimit.limiting_graph f ε h a p hε hh hb ha)
    (KFCausalCorrelatedClusteredPureMomentumLimit.limiting_graph f ε h a p hε hh ha)
    (KFCausalCorrelatedClusteredHalfMomentumLimit.limiting_graph f ε h a p hε hh hb ha)
    (limiting_reverse_graph f ε h a p hε hh hb ha)

theorem clock_response_bounds :
    -(1/(4*ε))*‖v‖^2 ≤ (-2/h)*(inner ℂ v k).im ∧ (-2/h)*(inner ℂ v k).im ≤ 0 := by
  rw [clock_response_identity f ε h a p hε hh hb ha]
  exact KFCausalClockFloorPureClockClockResponse.response_bounds ε hε ψ v

theorem clock_response_norm_bound :
    -‖ψ‖^2 ≤ (-2/h)*(inner ℂ v k).im ∧ (-2/h)*(inner ℂ v k).im ≤ 0 := by
  rw [clock_response_identity f ε h a p hε hh hb ha]
  exact KFCausalClockFloorPureClockClockResponse.response_norm_bound ε hε ψ v
    (KFCausalCorrelatedClusteredHalfClockLimit.limiting_graph f ε h a p hε hh hb ha)

theorem clock_response_tendsto :
    Tendsto (fun δ => (-2/h)*(inner ℂ (finiteOutput f ε h a p hε hh hb ha δ 0)
      (finiteMomentumOutput f ε h a p hε hh hb ha δ 0)).im) (𝓝[>] 0)
      (𝓝 ((-2/h)*(inner ℂ v k).im)) := by
  have hp := (KFCausalCorrelatedClusteredHalfClockLimit.output_tendsto f ε h a p hε hh hb ha).inner (𝕜 := ℂ)
    (KFCausalCorrelatedClusteredHalfMomentumLimit.output_tendsto f ε h a p hε hh hb ha)
  exact ((Complex.continuous_im.tendsto _).comp hp).const_mul (-2/h)

#print axioms finite_reverse_graph
#print axioms reverse_graph_tendsto
#print axioms limiting_reverse_graph
#print axioms limiting_reverse_domain
#print axioms reverse_composition_graph
#print axioms reverse_composition_domain
#print axioms clock_response_identity
#print axioms clock_response_bounds
#print axioms clock_response_norm_bound
#print axioms clock_response_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockCompositionLimit
