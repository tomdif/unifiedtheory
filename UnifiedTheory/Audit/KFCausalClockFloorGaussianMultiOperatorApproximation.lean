/- Simultaneous clock-Gaussian graph regularization and strong convergence across
the static operator T, the radial operator K, the potential Hamiltonian P, the
growing Hamiltonian G, the residual Hamiltonian S(t), and the full time-shifted
Hamiltonian H(t). -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianResidualForm
import UnifiedTheory.Audit.KFCausalClockFloorGaussianCommonDomainApproximation
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumThreeOperatorDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianMultiOperatorApproximation
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorGaussianGrowingTransport (action)
open KFCausalClockFloorGaussianGrowingApproximation (action_tendsto)
open KFCausalClockFloorGaussianStaticCommutation (static_graph)
open KFCausalClockFloorGaussianGrowingRadialPairing (radial_gaussian_graph)
open KFCausalClockFloorGaussianPotentialDomain (gaussian_graph_of_mem)
open KFCausalClockFloorGaussianResidualForm (residualFormAction residualFormAction_embedding)
open KFCausalClockFloorPositiveVacuumThreeOperatorDomain
  (three_operator_hamiltonian_graph three_operator_residual_graph)

private theorem sum_graph {H : Type*} [AddCommGroup H] [Module ℂ H]
    (K P : H →ₗ.[ℂ] H) (f r p : H)
    (hr : (f,r) ∈ K.graph) (hp : (f,p) ∈ P.graph) : (f,r+p) ∈ (K+P).graph := by
  have hk := LinearPMap.mem_domain_of_mem_graph hr
  have hp' := LinearPMap.mem_domain_of_mem_graph hp
  have heK : K ⟨f,hk⟩=r := K.mem_graph_snd_inj' (K.mem_graph ⟨f,hk⟩) hr rfl
  have heP : P ⟨f,hp'⟩=p := P.mem_graph_snd_inj' (P.mem_graph ⟨f,hp'⟩) hp rfl
  exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨f,⟨hk,hp'⟩⟩,rfl,by
    change K ⟨f,hk⟩+P ⟨f,hp'⟩=r+p
    rw [heK,heP]⟩

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k t
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t

theorem component_graphs (a : ℝ) (ha : 0 ≤ a) (f y r z : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hr : (f,r) ∈ (K).graph) (hp : (f,z) ∈ (P).graph) :
    (action ε a ha 0 f,action ε a ha 0 y) ∈ (T).graph ∧
      (action ε a ha 0 f,action ε a ha 0 r) ∈ (K).graph ∧
      (action ε a ha 0 f,action ε a ha (-h) z) ∈ (P).graph :=
  ⟨static_graph ε hε a ha h 0 f y ht,
    radial_gaussian_graph ε hε a ha h 0 f r hr,
    gaussian_graph_of_mem ε hε h hh hw m g k a ha f z hp⟩

theorem growing_sum_graph (a : ℝ) (ha : 0 ≤ a) (f r z : Hilbert)
    (hr : (f,r) ∈ (K).graph) (hp : (f,z) ∈ (P).graph) :
    (action ε a ha 0 f,action ε a ha 0 r+action ε a ha (-h) z) ∈ (G).graph := by
  rw [KFCausalClockFloorGrowingPotentialSum.operator_sum ε hε h hh hb m g k]
  exact sum_graph (K) (P) (action ε a ha 0 f) (action ε a ha 0 r) (action ε a ha (-h) z)
    (radial_gaussian_graph ε hε a ha h 0 f r hr)
    (gaussian_graph_of_mem ε hε h hh hw m g k a ha f z hp)

theorem residual_sum_graph_of_domain (a : ℝ) (ha : 0 ≤ a) (f y z : Hilbert)
    (hs : f ∈ (S).domain) (ht : (f,y) ∈ (T).graph) (hp : (f,z) ∈ (P).graph) :
    (action ε a ha 0 f,action ε a ha 0 y+(Real.exp (2*t):ℂ) • action ε a ha (-h) z) ∈ (S).graph := by
  let w0 := KFCausalClosedGraphForm.formLift SD ⟨f,hs⟩
  let w := residualFormAction ε hε a ha h hh hw 0 m g k t w0
  have hw0 : KFCausalClosedGraphForm.embedding SD w0=f :=
    KFCausalClosedGraphForm.embedding_formLift SD ⟨f,hs⟩
  have hw' : KFCausalClosedGraphForm.embedding SD w=action ε a ha 0 f :=
    (residualFormAction_embedding ε hε a ha h hh hw 0 m g k t w0).trans
      (congrArg (action ε a ha 0) hw0)
  have ht' : (KFCausalClosedGraphForm.embedding SD w,action ε a ha 0 y) ∈ (T).graph :=
    (congrArg (fun x : Hilbert => (x,action ε a ha 0 y) ∈ (T).graph) hw'.symm).mp
      (static_graph ε hε a ha h 0 f y ht)
  have hp' : (KFCausalClosedGraphForm.embedding SD w,action ε a ha (-h) z) ∈ (P).graph :=
    (congrArg (fun x : Hilbert => (x,action ε a ha (-h) z) ∈ (P).graph) hw'.symm).mp
      (gaussian_graph_of_mem ε hε h hh hw m g k a ha f z hp)
  have hg := KFCausalClockFloorResidualStaticPotentialDecomposition.sum_graph
    ε hε h hh hw m g k t w (action ε a ha 0 y) (action ε a ha (-h) z) ht' hp'
  exact (congrArg (fun x : Hilbert =>
    (x,action ε a ha 0 y+(Real.exp (2*t):ℂ) • action ε a ha (-h) z) ∈ (S).graph) hw').mp hg

theorem hamiltonian_sum_graph_of_domain (a : ℝ) (ha : 0 ≤ a) (f y r z : Hilbert)
    (hhd : f ∈ (H).domain) (ht : (f,y) ∈ (T).graph)
    (hr : (f,r) ∈ (K).graph) (hp : (f,z) ∈ (P).graph) :
    (action ε a ha 0 f,
      action ε a ha 0 y+(Real.exp (2*t):ℂ) • (action ε a ha 0 r+action ε a ha (-h) z)) ∈ (H).graph := by
  have hs : f ∈ (S).domain :=
    KFCausalClockFloorHamiltonianRadialSum.residual_domain ε hε h hh hb m g k t ⟨f,hhd⟩
  have hS := residual_sum_graph_of_domain ε hε h hh hb m g k t a ha f y z hs ht hp
  have hK := radial_gaussian_graph ε hε a ha h 0 f r hr
  have hk0 := LinearPMap.mem_domain_of_mem_graph hK
  have heK : K ⟨action ε a ha 0 f,hk0⟩=action ε a ha 0 r :=
    (K).mem_graph_snd_inj' ((K).mem_graph ⟨action ε a ha 0 f,hk0⟩) hK rfl
  have hK' : (action ε a ha 0 f,(Real.exp (2*t):ℂ) • action ε a ha 0 r) ∈
      ((Real.exp (2*t):ℂ) • (K)).graph :=
    (LinearPMap.mem_graph_iff _).mpr
      ⟨⟨action ε a ha 0 f,hk0⟩,rfl,congrArg ((Real.exp (2*t):ℂ) • ·) heK⟩
  have hg : (action ε a ha 0 f,
      (Real.exp (2*t):ℂ) • action ε a ha 0 r+
        (action ε a ha 0 y+(Real.exp (2*t):ℂ) • action ε a ha (-h) z)) ∈ (H).graph := by
    rw [KFCausalClockFloorHamiltonianRadialSum.operator_sum ε hε h hh hb m g k t]
    exact sum_graph ((Real.exp (2*t):ℂ) • (K)) (S) (action ε a ha 0 f) _ _ hK' hS
  have hout : (Real.exp (2*t):ℂ) • action ε a ha 0 r+
      (action ε a ha 0 y+(Real.exp (2*t):ℂ) • action ε a ha (-h) z)=
      action ε a ha 0 y+(Real.exp (2*t):ℂ) • (action ε a ha 0 r+action ε a ha (-h) z) := by
    rw [smul_add]
    abel
  exact (congrArg (fun v : Hilbert => (action ε a ha 0 f,v) ∈ (H).graph) hout).mp hg

theorem positive_vacuum_graphs (hk : 0 < k) (a : ℝ) (ha : 0 ≤ a) (f y r z : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hr : (f,r) ∈ (K).graph) (hp : (f,z) ∈ (P).graph) :
    (action ε a ha 0 f,action ε a ha 0 y+(Real.exp (2*t):ℂ) • action ε a ha (-h) z) ∈ (S).graph ∧
      (action ε a ha 0 f,
        action ε a ha 0 y+(Real.exp (2*t):ℂ) • (action ε a ha 0 r+action ε a ha (-h) z)) ∈ (H).graph := by
  obtain ⟨ht',hr',hp'⟩ := component_graphs ε hε h hh hb m g k a ha f y r z ht hr hp
  exact ⟨three_operator_residual_graph ε hε h hh hb m g k t hk _ _ _ _ ht' hr' hp',
    three_operator_hamiltonian_graph ε hε h hh hb m g k t hk _ _ _ _ ht' hr' hp'⟩

theorem multi_operator_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hz : Tendsto a l (𝓝 0)) (f y r z : Hilbert) :
    Tendsto (fun i =>
      (action ε (a i) (ha i) 0 f,
        (action ε (a i) (ha i) 0 y,
          (action ε (a i) (ha i) 0 r,
            (action ε (a i) (ha i) (-h) z,
              (action ε (a i) (ha i) 0 r+action ε (a i) (ha i) (-h) z,
                (action ε (a i) (ha i) 0 y+(Real.exp (2*t):ℂ) • action ε (a i) (ha i) (-h) z,
                  action ε (a i) (ha i) 0 y+
                    (Real.exp (2*t):ℂ) • (action ε (a i) (ha i) 0 r+action ε (a i) (ha i) (-h) z)))))))) l
      (𝓝 (f,(y,(r,(z,(r+z,(y+(Real.exp (2*t):ℂ) • z,y+(Real.exp (2*t):ℂ) • (r+z)))))))) := by
  have hf := action_tendsto ε 0 a ha hz f
  have hy := action_tendsto ε 0 a ha hz y
  have hr := action_tendsto ε 0 a ha hz r
  have hp := action_tendsto ε (-h) a ha hz z
  have hg := hr.add hp
  have hs := hy.add (hp.const_smul (Real.exp (2*t):ℂ))
  have hh' := hy.add (hg.const_smul (Real.exp (2*t):ℂ))
  exact hf.prodMk_nhds (hy.prodMk_nhds (hr.prodMk_nhds (hp.prodMk_nhds (hg.prodMk_nhds (hs.prodMk_nhds hh')))))

theorem sequence_multi_operator_approximation (hk : 0 < k) (f y r z : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hr : (f,r) ∈ (K).graph) (hp : (f,z) ∈ (P).graph) :
    (∀ n : ℕ,
      (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 f,
        action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 y) ∈ (T).graph ∧
      (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 f,
        action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 r) ∈ (K).graph ∧
      (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 f,
        action ε (((n:ℝ)+1)⁻¹) (by positivity) (-h) z) ∈ (P).graph ∧
      (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 f,
        action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 r+
          action ε (((n:ℝ)+1)⁻¹) (by positivity) (-h) z) ∈ (G).graph ∧
      (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 f,
        action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 y+
          (Real.exp (2*t):ℂ) • action ε (((n:ℝ)+1)⁻¹) (by positivity) (-h) z) ∈ (S).graph ∧
      (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 f,
        action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 y+
          (Real.exp (2*t):ℂ) • (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 r+
            action ε (((n:ℝ)+1)⁻¹) (by positivity) (-h) z)) ∈ (H).graph) ∧
    Tendsto (fun n : ℕ =>
      (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 f,
        (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 y,
          (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 r,
            (action ε (((n:ℝ)+1)⁻¹) (by positivity) (-h) z,
              (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 r+action ε (((n:ℝ)+1)⁻¹) (by positivity) (-h) z,
                (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 y+
                  (Real.exp (2*t):ℂ) • action ε (((n:ℝ)+1)⁻¹) (by positivity) (-h) z,
                  action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 y+
                    (Real.exp (2*t):ℂ) • (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 r+
                      action ε (((n:ℝ)+1)⁻¹) (by positivity) (-h) z)))))))) atTop
      (𝓝 (f,(y,(r,(z,(r+z,(y+(Real.exp (2*t):ℂ) • z,y+(Real.exp (2*t):ℂ) • (r+z)))))))) := by
  refine ⟨fun n => ?_,?_⟩
  · obtain ⟨ht',hr',hp'⟩ := component_graphs ε hε h hh hb m g k (((n:ℝ)+1)⁻¹) (by positivity) f y r z ht hr hp
    have hg' := growing_sum_graph ε hε h hh hb m g k (((n:ℝ)+1)⁻¹) (by positivity) f r z hr hp
    obtain ⟨hs',hh'⟩ := positive_vacuum_graphs ε hε h hh hb m g k t hk (((n:ℝ)+1)⁻¹) (by positivity) f y r z ht hr hp
    exact ⟨ht',hr',hp',hg',hs',hh'⟩
  · apply multi_operator_tendsto ε h t _ _ _ f y r z
    exact tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

#print axioms component_graphs
#print axioms growing_sum_graph
#print axioms residual_sum_graph_of_domain
#print axioms hamiltonian_sum_graph_of_domain
#print axioms positive_vacuum_graphs
#print axioms multi_operator_tendsto
#print axioms sequence_multi_operator_approximation
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianMultiOperatorApproximation
