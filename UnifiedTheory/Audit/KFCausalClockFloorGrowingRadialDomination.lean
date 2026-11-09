/- Separate radial kinetic control on the ENTIRE domain of the actual
growing Hamiltonian. Original-form stability legitimizes the bounded
radial test. Its shifted potential output is accretive, and Fatou removes
the cutoff. No joint operator core or radial domain is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaGrowing
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaOutputAccretivity
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaPairing
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialDomination
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaSymbol (action)
open KFCausalClockFloorRadialYosidaReference (wide_bound growingActionLp)
open KFCausalClockFloorRadialYosidaGrowing (formAction formAction_embedding formAction_output)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOperator rootOutput rootOutput_graph rootOutput_inner)
open KFCausalClockFloorRadialYosidaPairing (root_graph kinetic_pairing_lower)
open KFCausalClockFloorRadialYosidaDomain (operator domain_of_uniform_bound norm_of_uniform_bound)

private theorem pairing_comparison {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (x r s t : X) (y z w : Y) (φ : Y → ℂ)
    (hst : s=t) (hp : inner ℂ r s=φ z) (hzw : z=w)
    (hk : ‖x‖^2 ≤ (inner ℂ r t).re)
    (hu : (φ w).re ≤ (inner ℂ y w).re) :
    ‖x‖^2 ≤ (inner ℂ y z).re := by
  rw [hzw]
  rw [hst,hzw] at hp
  exact (hk.trans_eq (congrArg Complex.re hp)).trans hu

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "D" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "V" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hw m g k
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "B" => KFCausalClosedGraphForm.energyOutput D
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "R" => rootOutput ε hε h hh hw m g k

theorem root_intertwining (N : ℝ) (hN : 0 < N) (u : V) :
    R (formAction ε hε h N hN hb hh m g k u)=action ε hε h N hN (R u) := by
  have h1 := rootOutput_graph ε hε h hh hw m g k
    (formAction ε hε h N hN hb hh m g k u)
  have h2 := root_graph ε hε h N hN (J u) (R u)
    (rootOutput_graph ε hε h hh hw m g k u)
  rw [formAction_embedding] at h1
  exact (rootOperator ε hε h).mem_graph_snd_inj' h1 h2 rfl

theorem form_lower (N : ℝ) (hN : 0 < N) (u : V) :
    ‖action ε hε h N hN (J u)‖^2 ≤
      (inner ℂ (B u) (B (formAction ε hε h N hN hb hh m g k u))).re := by
  exact pairing_comparison (action ε hε h N hN (J u)) (R u)
    (R (formAction ε hε h N hN hb hh m g k u)) (action ε hε h N hN (R u))
    (B u) (B (formAction ε hε h N hN hb hh m g k u))
    (growingActionLp ε hε h N hN hb (B u))
    (fun z => inner ℂ (KFCausalClockFloorAveragedSqueezeEnergy.coordinateLp 3 (B u))
      (KFCausalClockFloorAveragedSqueezeEnergy.coordinateLp 3 z)+
        inner ℂ (KFCausalClockFloorAveragedSqueezeEnergy.coordinateLp 4 (B u))
          (KFCausalClockFloorAveragedSqueezeEnergy.coordinateLp 4 z))
    (root_intertwining ε hε h hh hb m g k N hN u)
    (rootOutput_inner ε hε h hh hw m g k u (formAction ε hε h N hN hb hh m g k u))
    (formAction_output ε hε h N hN hb hh m g k u)
    (kinetic_pairing_lower ε hε h N hN (J u) (R u)
      (rootOutput_graph ε hε h hh hw m g k u))
    (KFCausalClockFloorRadialYosidaOutputAccretivity.kinetic_pairing_le ε hε h N hN hb (B u))

theorem cutoff_bound (N : ℝ) (hN : 0 < N) (x : (G).domain) :
    ‖action ε hε h N hN (x:Hilbert)‖ ≤ ‖G x‖ := by
  have hl := form_lower ε hε h hh hb m g k N hN (KFCausalClosedGraphForm.formLift D x)
  have hp := KFCausalClosedGraphForm.hamiltonian_represents_form D x
    (formAction ε hε h N hN hb hh m g k (KFCausalClosedGraphForm.formLift D x))
  rw [hp,formAction_embedding,KFCausalClosedGraphForm.embedding_formLift] at hl
  change ‖action ε hε h N hN (x:Hilbert)‖^2 ≤
    (inner ℂ (G x) (action ε hε h N hN (x:Hilbert))).re at hl
  have hu := re_inner_le_norm (𝕜 := ℂ) (G x) (action ε hε h N hN (x:Hilbert))
  change (inner ℂ (G x) (action ε hε h N hN (x:Hilbert))).re ≤
    ‖G x‖*‖action ε hε h N hN (x:Hilbert)‖ at hu
  have hn := norm_nonneg (action ε hε h N hN (x:Hilbert))
  have hg := norm_nonneg (G x)
  by_contra hbad
  have hb' : ‖G x‖ < ‖action ε hε h N hN (x:Hilbert)‖ := lt_of_not_ge hbad
  nlinarith only [hl,hu,hn,hg,hb']

theorem radial_domain (x : (G).domain) : (x:Hilbert) ∈ (operator ε hε h).domain :=
  domain_of_uniform_bound ε hε h x ‖G x‖
    (fun n => cutoff_bound ε hε h hh hb m g k ((n:ℝ)+1) (by positivity) x)

theorem radial_norm (x : (G).domain) :
    ‖operator ε hε h ⟨(x:Hilbert),radial_domain ε hε h hh hb m g k x⟩‖ ≤ ‖G x‖ :=
  norm_of_uniform_bound ε hε h x ‖G x‖
    (fun n => cutoff_bound ε hε h hh hb m g k ((n:ℝ)+1) (by positivity) x)

#print axioms root_intertwining
#print axioms form_lower
#print axioms cutoff_bound
#print axioms radial_domain
#print axioms radial_norm
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialDomination
