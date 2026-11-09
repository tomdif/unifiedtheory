/- Identify the full-clock response limit with the actual potential
form pairing of the limiting input and its pure-clock momentum. This
does not assert a strong Hamiltonian action or a trajectory derivative. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumPotentialLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredVacuumUniformLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalResponsePairing
noncomputable section
open Filter
open scoped Topology
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredPhysicalClockLimit (finiteResponse limitingResponse potentialResponse_tendsto)
open KFCausalCorrelatedClusteredPhysicalCauchy (finiteOutput potentialIndex)
open KFCausalCorrelatedClusteredMomentumPotentialProfiles (finiteMomentumOutput)
open KFCausalCorrelatedClusteredPotentialGraphLimit (limitingOutput output_tendsto)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (ha : ∀ i, 0 < a i)
local notation "U" => finiteOutput f ε h a p hε hh hb ha
local notation "M" => finiteMomentumOutput f ε h a p hε hh hb ha
local notation "V" => limitingOutput f ε h a p hε hh hb ha
local notation "W" => KFCausalCorrelatedClusteredMomentumPotentialLimit.limitingOutput f ε h a p hε hh hb ha

def pairing : ℂ := inner ℂ (V 0) (W 0)+inner ℂ (V 1) (W 1)/2+inner ℂ (V 2) (W 2)/4
def response : ℝ := (-2/h)*(pairing f ε h a p hε hh hb ha).im

theorem pairing_tendsto :
    Tendsto (fun δ => inner ℂ (U δ 7) (M δ 7)+inner ℂ (U δ 5) (M δ 5)/2+inner ℂ (U δ 6) (M δ 6)/4)
      (𝓝[>] 0) (𝓝 (pairing f ε h a p hε hh hb ha)) := by
  have hk (k : Fin 3) := (output_tendsto f ε h a p hε hh hb ha k).inner (𝕜 := ℂ)
    (KFCausalCorrelatedClusteredMomentumPotentialLimit.output_tendsto f ε h a p hε hh hb ha k)
  exact ((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4)

theorem finiteResponse_identity (δ : ℝ) (hδ : 0 < δ) :
    finiteResponse f ε h a p hε hh hb ha δ =
      (-2/h)*(inner ℂ (U δ 7) (M δ 7)+inner ℂ (U δ 5) (M δ 5)/2+inner ℂ (U δ 6) (M δ 6)/4).im := by
  simp only [finiteResponse,finiteOutput,finiteMomentumOutput,dif_pos hδ,
    KFCausalReciprocalNeutralPotentialTransport.potentialResponse]

theorem response_tendsto :
    Tendsto (finiteResponse f ε h a p hε hh hb ha) (𝓝[>] 0)
      (𝓝 (response f ε h a p hε hh hb ha)) := by
  have ht := ((Complex.continuous_im.tendsto _).comp (pairing_tendsto f ε h a p hε hh hb ha)).const_mul (-2/h)
  apply Tendsto.congr' _ ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteResponse_identity f ε h a p hε hh hb ha δ hδ).symm

theorem limiting_response_identity :
    limitingResponse f ε h a p = response f ε h a p hε hh hb ha :=
  tendsto_nhds_unique (potentialResponse_tendsto f ε h a p hε hh hb ha)
    (response_tendsto f ε h a p hε hh hb ha)

include hb in
theorem zero_input_response
    (hz : KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha = 0) :
    limitingResponse f ε h a p = 0 := by
  have hv (k : Fin 3) : V k = 0 :=
    (KFCausalClockFloorCommonDomain.energyFactor ε hε h KFCausalPhysicalEnergyFactors.modelDirections
      KFCausalMatterOrderedDomain.pointField (potentialIndex k)).graph_fst_eq_zero_snd
        (KFCausalCorrelatedClusteredInputGraphLimit.limiting_potential_graph f ε h a p hε hh ha hb k) hz
  rw [limiting_response_identity f ε h a p hε hh hb ha]
  simp only [response,pairing,hv,inner_zero_left,zero_div,zero_add,Complex.zero_im,mul_zero]

theorem exists_uniform_vacuum_form_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (z : Fin m → ℂ)
      (ε h : ℝ) (a : Fin m → ℝ) (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
      (hb : |h| ≤ Real.pi*ε/3),
      let f := KFCausalCorrelatedClusteredVacuumUniformLimit.family d z;
      let hb' := KFCausalGaussianVacuumSquare.original_strip ε h hε hb;
      let outputs := limitingOutput f ε h a (fun _ => 0) hε hh hb' ha;
      -((C+2)/ε)*(‖outputs 0‖^2+‖outputs 1‖^2/2+‖outputs 2‖^2/4) ≤ response f ε h a (fun _ => 0) hε hh hb' ha := by
  obtain ⟨C,hC,hbound⟩ := KFCausalCorrelatedClusteredVacuumUniformLimit.exists_uniform_physical_limit_response
  refine ⟨C,hC,?_⟩
  intro m d z ε h a hε hh ha hb
  dsimp only
  rw [← limiting_response_identity]
  exact hbound m d z ε h a hε hh ha hb

#print axioms pairing_tendsto
#print axioms finiteResponse_identity
#print axioms response_tendsto
#print axioms limiting_response_identity
#print axioms zero_input_response
#print axioms exists_uniform_vacuum_form_response
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalResponsePairing
