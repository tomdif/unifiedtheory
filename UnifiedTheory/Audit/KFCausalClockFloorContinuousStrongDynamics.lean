/- Continuous physical Hamiltonian outputs and continuous strong derivatives
on every finite forward window, for the full initial Hamiltonian domain. -/
import UnifiedTheory.Audit.KFCausalContinuousGraphOutputs
import UnifiedTheory.Audit.KFCausalClockFloorCompactGraphDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorContinuousStrongDynamics
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorPhysicalGraphEvolution
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "P" => referenceInverse ε hε h hne hh m g k
local notation "R" => shiftedResolvent ε hε h hne hh m g k
local notation "L" => liftedHamiltonian ε hε h hne hh m g k
local notation "H" => hamiltonian ε hε h hne hh m g k
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

theorem mass_output_continuous (s : ℝ) (x : V) : Continuous (fun t => Q t (F s t x)) := by
  have hQ : Continuous Q := continuous_iff_continuousAt.mpr
    (fun t => (referenceForm_derivative ε hε h hne hh m g k t).continuousAt)
  exact hQ.clm_apply (KFCausalClockFloorStrongFormEvolution.formFlow_continuous ε hε h hne hh m g k s x)

theorem exists_continuous_graph (a s r : ℝ) (ha : 0 < a) (hsr : s ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ E : (Icc s r) → Hilbert →L[ℂ] Hilbert,
      (∀ t, ‖E t‖ ≤ C) ∧ (∀ t : Icc s r, ∀ v, (U s t (R a s v),E t v) ∈ (H t).graph) ∧
      ∀ v, Continuous (fun t => E t v) :=
  KFCausalContinuousGraphOutputs.augment_uniform_graph J
    (KFCausalClockFloorAveragedFormGeometry.embedding_dense ε hε h hne hh m g k 0)
    M ((P a s).comp M) (fun t : Icc s r => Q t) (fun t : Icc s r => F s t)
    (fun t : Icc s r => L t) (fun t : Icc s r => H t)
    (fun t : Icc s r => (U s t : Hilbert →L[ℂ] Hilbert)) (R a s)
    (mass_left_pairing ε hε h hne hh m g k)
    (fun t x y hg => (lifted_graph_iff ε hε h hne hh m g k t x y).mp hg)
    (fun t x y hg => (physical_graph_iff ε hε h hne hh m g k t x y).mp hg)
    (fun t => KFCausalContinuousGraphOutputs.intertwining J
      (U s t : Hilbert →L[ℂ] Hilbert) (R a s) ((P a s).comp M) (F s t)
      (resolvent_embedding ε hε h hne hh m g k a s)
      (evolution_embedding ε hε h hne hh m g k s t))
    (fun v => KFCausalCompactLiftedGraphBound.on_subtype L (fun t => F s t (P a s (M v))) (Icc s r)
      (KFCausalClockFloorUniformLiftedOutput.uniform_lifted_graph ε hε h hne hh m g k s r hsr
        ⟨P a s (M v),shifted_lift_domain ε hε h hne hh m g k a s ha v⟩))
    (fun v => (mass_output_continuous ε hε h hne hh m g k s (P a s (M v))).comp continuous_subtype_val)
    (KFCausalClockFloorCompactGraphDynamics.exists_uniform_graph ε hε h hne hh m g k a s r ha hsr)

theorem continuous_domain_curve (s r : ℝ) (hsr : s ≤ r) (x : (H s).domain) :
    ∃ y : (Icc s r) → Hilbert, Continuous y ∧ ∀ t : Icc s r,
      (U s t x,y t) ∈ (H t).graph ∧ HasDerivAt (fun z => U s z x) (c • y t) t :=
  KFCausalContinuousGraphOutputs.continuous_domain_curve (H s) H
    (fun t => (U s t : Hilbert →L[ℂ] Hilbert)) (R 1 s) (Icc s r) c
    (fun x => by simpa only [one_smul,add_comm] using
      shiftedResolvent_left ε hε h hne hh m g k 1 s (by norm_num) x)
    (fun t ht => KFCausalClockFloorFullDomainDynamics.forward_schrodinger ε hε h hne hh m g k s t ht.1)
    (exists_continuous_graph ε hε h hne hh m g k 1 s r (by norm_num) hsr) x

theorem derivative_continuous (s r : ℝ) (hsr : s ≤ r) (x : (H s).domain) :
    Continuous (fun t : Icc s r => deriv (fun z => U s z x) t) :=
  Exists.elim (continuous_domain_curve ε hε h hne hh m g k s r hsr x) (fun y hy =>
    KFCausalContinuousGraphOutputs.derivative_continuous (fun z => U s z x) (Icc s r) c
      ⟨y,hy.1,fun t => (hy.2 t).2⟩)

#print axioms mass_output_continuous
#print axioms exists_continuous_graph
#print axioms continuous_domain_curve
#print axioms derivative_continuous
end
end UnifiedTheory.Audit.KFCausalClockFloorContinuousStrongDynamics
