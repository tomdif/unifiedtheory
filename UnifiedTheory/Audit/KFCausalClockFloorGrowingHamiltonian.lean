/- The growing restriction has a canonical closed form and a positive
self-adjoint physical Hamiltonian. The original full reference form
is dense in this smaller form norm by construction and proof. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingOutputClosure
import UnifiedTheory.Audit.KFCausalClockFloorFastTimeDynamics

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingHamiltonian
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity (growingMap)
open UnifiedTheory.Audit.KFCausalClockFloorGrowingOutputClosure

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "B" => growingMap ε hε h hne hb m g k

def formData : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace where
  operator := operator ε hε h hne hb m g k
  closed := operator_closed ε hε h hne hb m g k
  dense := operator_dense ε hε h hne hb m g k

local notation "D" => formData ε hε h hne hb m g k
abbrev GrowingForm := KFCausalClosedGraphForm.FormSpace D

def referenceLift (u : V) : GrowingForm ε hε h hne hb m g k :=
  ⟨WithLp.toLp 2 (J u,B u),reference_graph ε hε h hne hb m g k u⟩

theorem referenceLift_embedding (u : V) :
    KFCausalClosedGraphForm.embedding D (referenceLift ε hε h hne hb m g k u) = J u := rfl

theorem referenceLift_output (u : V) :
    KFCausalClosedGraphForm.energyOutput D (referenceLift ε hε h hne hb m g k u) = B u := rfl

theorem referenceLift_norm (u : V) :
    ‖referenceLift ε hε h hne hb m g k u‖^2 = ‖J u‖^2+‖B u‖^2 :=
  KFCausalClosedGraphForm.form_norm_identity D (referenceLift ε hε h hne hb m g k u)

theorem referenceLift_dense : DenseRange (referenceLift ε hε h hne hb m g k) := by
  intro w
  have hw : WithLp.ofLp w.val ∈ (initialGraph ε hε h hne hb m g k).topologicalClosure := by
    rw [← operator_graph]
    exact w.property
  obtain ⟨z,hz,ht⟩ := mem_closure_iff_seq_limit.mp
    (show WithLp.ofLp w.val ∈ closure (initialGraph ε hε h hne hb m g k : Set (Hilbert × EnergyOutputSpace)) from hw)
  have hex (n : ℕ) : ∃ u : V, (J u,B u) = z n := hz n
  choose u hu using hex
  have hu' : Tendsto (fun n => (J (u n),B (u n))) atTop (𝓝 (WithLp.ofLp w.val)) := by
    simpa only [hu] using ht
  have hl : Tendsto (fun n => referenceLift ε hε h hne hb m g k (u n)) atTop (𝓝 w) := by
    apply tendsto_subtype_rng.mpr
    exact ((WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert EnergyOutputSpace).symm.continuous.tendsto
      (WithLp.ofLp w.val)).comp hu'
  exact mem_closure_of_tendsto hl (Eventually.of_forall (fun n => Set.mem_range_self (u n)))

def hamiltonian : Hilbert →ₗ.[ℂ] Hilbert := KFCausalClosedGraphForm.hamiltonian D

theorem hamiltonian_selfAdjoint : IsSelfAdjoint (hamiltonian ε hε h hne hb m g k) :=
  KFCausalClosedGraphForm.hamiltonian_selfAdjoint D

theorem hamiltonian_closed : (hamiltonian ε hε h hne hb m g k).IsClosed :=
  KFCausalClosedGraphForm.hamiltonian_closed D

theorem hamiltonian_dense : Dense ((hamiltonian ε hε h hne hb m g k).domain : Set Hilbert) :=
  KFCausalClosedGraphForm.hamiltonian_dense D

theorem hamiltonian_positive (x : (hamiltonian ε hε h hne hb m g k).domain) :
    0 ≤ (inner ℂ (hamiltonian ε hε h hne hb m g k x) (x:Hilbert)).re :=
  KFCausalClosedGraphForm.hamiltonian_positive D x

theorem hamiltonian_reference_pairing (x : (hamiltonian ε hε h hne hb m g k).domain) (u : V) :
    inner ℂ (KFCausalClosedGraphForm.energyOutput D (KFCausalClosedGraphForm.formLift D x)) (B u) =
      inner ℂ (hamiltonian ε hε h hne hb m g k x) (J u) :=
  KFCausalClosedGraphForm.hamiltonian_represents_form D x (referenceLift ε hε h hne hb m g k u)

theorem reference_domain_characterization (u : V) (y : Hilbert) :
    (∃ hx : J u ∈ (hamiltonian ε hε h hne hb m g k).domain,
      hamiltonian ε hε h hne hb m g k ⟨J u,hx⟩ = y) ↔
      ∀ v : V, inner ℂ (B u) (B v) = inner ℂ y (J v) := by
  have hc := KFCausalClosedGraphForm.hamiltonian_domain_characterization D
    (referenceLift ε hε h hne hb m g k u) y
  refine hc.trans ?_
  constructor
  · intro hp v
    exact hp (referenceLift ε hε h hne hb m g k v)
  · intro hp v
    exact congrFun ((referenceLift_dense ε hε h hne hb m g k).equalizer
      (continuous_const.inner (𝕜 := ℂ) (KFCausalClosedGraphForm.energyOutput D).continuous)
      (continuous_const.inner (𝕜 := ℂ) (KFCausalClosedGraphForm.embedding D).continuous)
      (funext hp)) v

theorem fast_time_leading_form (s u : ℝ) (w z : V) :
    KFCausalClockFloorFastTimeDynamics.leading ε hε h hne hb m g k s u w z =
      (Complex.I*((1/(2*h):ℝ):ℂ))*inner ℂ
        (KFCausalClosedGraphForm.energyOutput D (referenceLift ε hε h hne hb m g k
          (KFCausalClockFloorAveragedFormFlow.formFlow ε hε h hne hb m g k s
            (KFCausalClockFloorFastTimeEnergy.physicalTime u) w)))
        (KFCausalClosedGraphForm.energyOutput D (referenceLift ε hε h hne hb m g k z)) := rfl

theorem flow_growing_form_bound (s t : ℝ) (hst : s ≤ t) (w : V) :
    ‖referenceLift ε hε h hne hb m g k
      (KFCausalClockFloorAveragedFormFlow.formFlow ε hε h hne hb m g k s t w)‖^2 ≤
      ‖J w‖^2+KFCausalClockFloorRescaledEnergy.scaledEnergy ε hε h hne hb m g k s s w := by
  rw [referenceLift_norm,KFCausalClockFloorAveragedFormFlow.formFlow_physical_norm]
  apply add_le_add_right
  have he := KFCausalClockFloorRescaledEnergy.scaled_antitone ε hε h hne hb m g k s w hst
  change KFCausalClockFloorRescaledEnergy.scaledEnergy ε hε h hne hb m g k s t w ≤
    KFCausalClockFloorRescaledEnergy.scaledEnergy ε hε h hne hb m g k s s w at he
  rw [KFCausalClockFloorRescaledEnergy.scaled_split] at he
  have hn : 0 ≤ KFCausalClockFloorRescaledEnergy.staticLoss ε hε h hne hb m g k s t w :=
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  linarith only [he,hn]

#print axioms referenceLift_embedding
#print axioms referenceLift_output
#print axioms referenceLift_norm
#print axioms referenceLift_dense
#print axioms hamiltonian_selfAdjoint
#print axioms hamiltonian_closed
#print axioms hamiltonian_dense
#print axioms hamiltonian_positive
#print axioms hamiltonian_reference_pairing
#print axioms reference_domain_characterization
#print axioms fast_time_leading_form
#print axioms flow_growing_form_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingHamiltonian
