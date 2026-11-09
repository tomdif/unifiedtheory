/- Unconditional clock-Gaussian multi-operator graph regularization and strong
convergence for all real couplings (including zero or negative vacuum coupling).
Because the reference residual form domain Dom Tres(0) and the full averaged
form domain Dom Eavg(t) are invariant under centered clock Gaussians, any
vector in (Dom T ∩ Dom K ∩ Dom P) ∩ Dom Tres(0) has Gaussian regularizations
 simultaneously in the graphs of T, K, P, G, S(t), and H(t) that converge
strongly in all six operator graphs as the Gaussian width tends to zero. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianMultiOperatorApproximation
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalThreeOperatorDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianUnconditionalMultiOperatorApproximation
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalPhysicalEnergyTransport (timeOutput timeOutput_apply)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp energy_graph_transport)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorGaussianGrowingTransport (action)
open KFCausalClockFloorGaussianGrowingForm (outputAction)
open KFCausalClockFloorGaussianResidualForm
  (outputActionLp timeOutput_outputAction reference_full_stability residual_graph_action)
open KFCausalClockFloorGaussianMultiOperatorApproximation
  (component_graphs growing_sum_graph multi_operator_tendsto)
open KFCausalClockFloorUnconditionalThreeOperatorDecomposition
  (unconditional_three_operator_residual_graph unconditional_three_operator_hamiltonian_graph)

private theorem point_time_trans (r t s : ℝ) (z : Output (Fin 8) Hilbert) :
    timeOutput t s (timeOutput r t z)=timeOutput r s z := by
  have he : Complex.exp ((s:ℂ)-(t:ℂ))*Complex.exp ((t:ℂ)-(r:ℂ))=
      Complex.exp ((s:ℂ)-(r:ℂ)) := by
    rw [← Complex.exp_add,show (s:ℂ)-(t:ℂ)+((t:ℂ)-(r:ℂ))=(s:ℂ)-(r:ℂ) by ring]
  apply PiLp.ext
  intro i
  by_cases h3 : i.val < 3
  · simp [timeOutput_apply,h3]
  · simp [timeOutput_apply,h3,smul_smul,he]

private theorem lp_time_trans (r t s : ℝ) (z : EnergyOutputSpace) :
    timeOutputLp t s (timeOutputLp r t z)=timeOutputLp r s z := by
  let w := timeOutputLp r t z
  apply Lp.ext
  filter_upwards [(timeOutput t s).coeFn_compLp w,
    (timeOutput r t).coeFn_compLp z,
    (timeOutput r s).coeFn_compLp z] with θ h1 h2 h3
  change (timeOutput t s).compLp w θ=(timeOutput r s).compLp z θ
  rw [h1,h3]
  change timeOutput t s ((timeOutput r t).compLp z θ)=timeOutput r s (z θ)
  rw [h2,point_time_trans]

private theorem point_time_self (t : ℝ) (z : Output (Fin 8) Hilbert) :
    timeOutput t t z=z := by
  apply PiLp.ext
  intro i
  by_cases h3 : i.val < 3 <;>
    simp [timeOutput_apply,h3,sub_self,one_smul]

private theorem lp_time_self (t : ℝ) (z : EnergyOutputSpace) :
    timeOutputLp t t z=z := by
  apply Lp.ext
  filter_upwards [(timeOutput t t).coeFn_compLp z] with θ h1
  change (timeOutput t t).compLp z θ=z θ
  rw [h1,point_time_self]

private theorem lp_time_inv (s t : ℝ) (z : EnergyOutputSpace) :
    timeOutputLp t s (timeOutputLp s t z)=z :=
  (lp_time_trans s t s z).trans (lp_time_self s z)

private theorem mem_graph_of_eq {A : Hilbert →ₗ.[ℂ] EnergyOutputSpace}
    (f1 f2 : Hilbert) (z1 z2 : EnergyOutputSpace)
    (hf : f1=f2) (hz : z1=z2) (hm : (f1,z1) ∈ A.graph) :
    (f2,z2) ∈ A.graph := by
  rwa [← hf,← hz]

variable (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a)
  (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (y : ℝ) (m g k : ℝ)

theorem timeOutputLp_outputActionLp (t : ℝ) (z : EnergyOutputSpace) :
    timeOutputLp 0 t (outputActionLp ε a ha h y z)=
      outputActionLp ε a ha h y (timeOutputLp 0 t z) := by
  let o := outputActionLp ε a ha h y z
  let to2 := timeOutputLp 0 t z
  apply Lp.ext
  filter_upwards [(timeOutput 0 t).coeFn_compLp o,
    (outputAction ε a ha h y).coeFn_compLp z,
    (outputAction ε a ha h y).coeFn_compLp to2,
    (timeOutput 0 t).coeFn_compLp z]
    with θ h1 h2 h3 h4
  change ((timeOutput 0 t).compLp o) θ=((outputAction ε a ha h y).compLp to2) θ
  rw [h1,h3]
  change timeOutput 0 t (((outputAction ε a ha h y).compLp z) θ)=
    outputAction ε a ha h y (((timeOutput 0 t).compLp z) θ)
  rw [h2,h4,timeOutput_outputAction]

theorem residual_form_domain_action (t : ℝ) (f : Hilbert)
    (hf : f ∈ (KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hb m g k t).domain) :
    action ε a ha y f ∈
      (KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hb m g k t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (residual_graph_action ε hε a ha h hh hb y m g k t f _
      ((KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hb m g k t).mem_graph ⟨f,hf⟩))

local notation "hs" => hamiltonian_bound ε h hb
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h hs hh m g k
local notation "AD" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hb m g k
local notation "VT" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hb m g k
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb m g k 0
local notation "RA" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hb m g k 0

private theorem reference_pair_mem (v : VT 0) :
    (RJ v,RA v) ∈ (Eavg 0).graph := v.property

private theorem averaged_zero_graph_action (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (Eavg 0).graph) :
    (action ε a ha y f,outputActionLp ε a ha h y z) ∈ (Eavg 0).graph := by
  let u : VT 0 := ⟨WithLp.toLp 2 (f,z),hz⟩
  let hstab := reference_full_stability ε hε a ha h hh hb y m g k u
  let v := Classical.choose hstab
  have hv := Classical.choose_spec hstab
  exact mem_graph_of_eq (RJ v) (action ε a ha y f) (RA v) (outputActionLp ε a ha h y z)
    hv.1 hv.2 (reference_pair_mem ε hε h hh hb m g k v)

theorem averaged_graph_action (t : ℝ) (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (Eavg t).graph) :
    (action ε a ha y f,outputActionLp ε a ha h y z) ∈ (Eavg t).graph := by
  have hz0 : (f,timeOutputLp t 0 z) ∈ (Eavg 0).graph :=
    energy_graph_transport ε hε h hs hh m g k t 0 (f,z) hz
  have ha0 := averaged_zero_graph_action ε hε a ha h hh hb y m g k f (timeOutputLp t 0 z) hz0
  have hat : (action ε a ha y f,
      timeOutputLp 0 t (outputActionLp ε a ha h y (timeOutputLp t 0 z))) ∈ (Eavg t).graph :=
    energy_graph_transport ε hε h hs hh m g k 0 t _ ha0
  have hout : timeOutputLp 0 t (outputActionLp ε a ha h y (timeOutputLp t 0 z))=
      outputActionLp ε a ha h y z :=
    (timeOutputLp_outputActionLp ε a ha h y t (timeOutputLp t 0 z)).trans
      (congrArg (outputActionLp ε a ha h y) (lp_time_inv t 0 z))
  exact mem_graph_of_eq (action ε a ha y f) (action ε a ha y f)
    (timeOutputLp 0 t (outputActionLp ε a ha h y (timeOutputLp t 0 z)))
    (outputActionLp ε a ha h y z) rfl hout hat

def averagedFormAction (t : ℝ) : VT t →L[ℂ] VT t :=
  KFCausalClosedGraphDiagonalAction.action (AD t) (action ε a ha y) (outputActionLp ε a ha h y)
    (averaged_graph_action ε hε a ha h hh hb y m g k t)

theorem averagedFormAction_embedding (t : ℝ) (u : VT t) :
    KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb m g k t
      (averagedFormAction ε hε a ha h hh hb y m g k t u)=
        action ε a ha y
          (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb m g k t u) := rfl

theorem averagedFormAction_output (t : ℝ) (u : VT t) :
    KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hb m g k t
      (averagedFormAction ε hε a ha h hh hb y m g k t u)=
        outputActionLp ε a ha h y
          (KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hb m g k t u) := rfl

theorem averaged_form_domain_action (t : ℝ) (f : Hilbert)
    (hf : f ∈ (Eavg t).domain) :
    action ε a ha y f ∈ (Eavg t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (averaged_graph_action ε hε a ha h hh hb y m g k t f _ ((Eavg t).mem_graph ⟨f,hf⟩))

variable (hb' : |h| ≤ Real.pi*ε/3) (t : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb'
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k

theorem unconditional_graphs (f y r z : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hr : (f,r) ∈ (K).graph) (hp : (f,z) ∈ (P).graph)
    (hf : f ∈ (Tres 0).domain) :
    (action ε a ha 0 f,action ε a ha 0 y+(Real.exp (2*t):ℂ) • action ε a ha (-h) z) ∈ (S).graph ∧
      (action ε a ha 0 f,
        action ε a ha 0 y+(Real.exp (2*t):ℂ) • (action ε a ha 0 r+action ε a ha (-h) z)) ∈ (H).graph := by
  obtain ⟨ht',hr',hp'⟩ := component_graphs ε hε h hh hb' m g k a ha f y r z ht hr hp
  have hf' : action ε a ha 0 f ∈ (Tres 0).domain :=
    residual_form_domain_action ε hε a ha h hh hw 0 m g k 0 f hf
  exact ⟨unconditional_three_operator_residual_graph ε hε h hh hb' m g k t _ _ _ ht' hp' hf',
    unconditional_three_operator_hamiltonian_graph ε hε h hh hb' m g k t _ _ _ _ ht' hr' hp' hf'⟩

theorem unconditional_sequence_multi_operator_approximation (f y r z : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hr : (f,r) ∈ (K).graph) (hp : (f,z) ∈ (P).graph)
    (hf : f ∈ (Tres 0).domain) :
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
  · obtain ⟨ht',hr',hp'⟩ := component_graphs ε hε h hh hb' m g k (((n:ℝ)+1)⁻¹) (by positivity) f y r z ht hr hp
    have hg' := growing_sum_graph ε hε h hh hb' m g k (((n:ℝ)+1)⁻¹) (by positivity) f r z hr hp
    obtain ⟨hs',hh'⟩ := unconditional_graphs ε hε (((n:ℝ)+1)⁻¹) (by positivity) h hh m g k hb' t f y r z ht hr hp hf
    exact ⟨ht',hr',hp',hg',hs',hh'⟩
  · apply multi_operator_tendsto ε h t _ _ _ f y r z
    exact tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

#print axioms timeOutputLp_outputActionLp
#print axioms residual_form_domain_action
#print axioms averaged_graph_action
#print axioms averagedFormAction_embedding
#print axioms averagedFormAction_output
#print axioms averaged_form_domain_action
#print axioms unconditional_graphs
#print axioms unconditional_sequence_multi_operator_approximation
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianUnconditionalMultiOperatorApproximation
