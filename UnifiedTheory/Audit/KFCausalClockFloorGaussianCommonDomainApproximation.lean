/- Actual Gaussian approximation in the simultaneous static/growing
operator graph. Both graph memberships are derived from the original
operators, and all three Hilbert components converge. This does not
identify a joint finite-packet core or replace the full reference form. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianStaticCommutation
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianCommonDomainApproximation
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorGaussianGrowingTransport (action)
open KFCausalClockFloorGaussianGrowingApproximation (action_tendsto)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "out" => KFCausalClockFloorGaussianGrowingDomain.output ε hε h hh hb m g k

theorem common_graphs (a : ℝ) (ha : 0 ≤ a) (f : Hilbert)
    (ht : f ∈ (T).domain) (hg : f ∈ (G).domain) :
    (action ε a ha 0 f,action ε a ha 0 (T ⟨f,ht⟩)) ∈ (T).graph ∧
      (action ε a ha 0 f,out a ha ⟨f,hg⟩) ∈ (G).graph :=
  ⟨KFCausalClockFloorGaussianStaticCommutation.static_graph ε hε a ha h 0 f _
      ((T).mem_graph ⟨f,ht⟩),
    KFCausalClockFloorGaussianGrowingDomain.gaussian_graph ε hε h hh hb m g k a ha ⟨f,hg⟩⟩

theorem common_domain (a : ℝ) (ha : 0 ≤ a) (f : Hilbert)
    (ht : f ∈ (T).domain) (hg : f ∈ (G).domain) :
    action ε a ha 0 f ∈ (T).domain ∧ action ε a ha 0 f ∈ (G).domain := by
  have hfg := common_graphs ε hε h hh hb m g k a ha f ht hg
  exact ⟨LinearPMap.mem_domain_of_mem_graph hfg.1,LinearPMap.mem_domain_of_mem_graph hfg.2⟩

theorem common_graph_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hz : Tendsto a l (𝓝 0))
    (f : Hilbert) (ht : f ∈ (T).domain) (hg : f ∈ (G).domain) :
    Tendsto (fun i => (action ε (a i) (ha i) 0 f,
      (action ε (a i) (ha i) 0 (T ⟨f,ht⟩),out (a i) (ha i) ⟨f,hg⟩))) l
        (𝓝 (f,(T ⟨f,ht⟩,G ⟨f,hg⟩))) :=
  (action_tendsto ε 0 a ha hz f).prodMk_nhds
    ((action_tendsto ε 0 a ha hz (T ⟨f,ht⟩)).prodMk_nhds
      (KFCausalClockFloorGaussianGrowingDomain.output_tendsto ε hε h hh hb m g k a ha hz ⟨f,hg⟩))

theorem sequence_approximation (f : Hilbert) (ht : f ∈ (T).domain) (hg : f ∈ (G).domain) :
    (∀ n : ℕ,
      (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 f,
        action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 (T ⟨f,ht⟩)) ∈ (T).graph ∧
      (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 f,
        out (((n:ℝ)+1)⁻¹) (by positivity) ⟨f,hg⟩) ∈ (G).graph) ∧
    Tendsto (fun n : ℕ => (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 f,
      (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 (T ⟨f,ht⟩),
        out (((n:ℝ)+1)⁻¹) (by positivity) ⟨f,hg⟩))) atTop
          (𝓝 (f,(T ⟨f,ht⟩,G ⟨f,hg⟩))) := by
  refine ⟨fun n => common_graphs ε hε h hh hb m g k _ (by positivity) f ht hg,?_⟩
  apply common_graph_tendsto ε hε h hh hb m g k _ _ _ f ht hg
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

#print axioms common_graphs
#print axioms common_domain
#print axioms common_graph_tendsto
#print axioms sequence_approximation
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianCommonDomainApproximation
