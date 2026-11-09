/- One physical Hamiltonian graph bound over a whole finite forward window,
and the resulting Lipschitz estimate for every initial Hamiltonian-domain state. -/
import UnifiedTheory.Audit.KFCausalUniformPhysicalGraphAssembly
import UnifiedTheory.Audit.KFCausalUniformGraphDynamics
import UnifiedTheory.Audit.KFCausalClockFloorUniformLiftedOutput
import UnifiedTheory.Audit.KFCausalClockFloorFullDomainDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorCompactGraphDynamics
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormLinearity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorPhysicalGraphEvolution
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "A" => referenceShift ε hε h hne hh m g k
local notation "P" => referenceInverse ε hε h hne hh m g k
local notation "R" => shiftedResolvent ε hε h hne hh m g k
local notation "L" => liftedHamiltonian ε hε h hne hh m g k
local notation "H" => hamiltonian ε hε h hne hh m g k
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

theorem evolution_norm_bound (s t : ℝ) : ‖(U s t : Hilbert →L[ℂ] Hilbert)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using (evolution_norm ε hε h hne hh m g k s t x).le

theorem exists_uniform_graph (a s r : ℝ) (ha : 0 < a) (hsr : s ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ E : (Icc s r) → Hilbert →L[ℂ] Hilbert,
      (∀ t, ‖E t‖ ≤ C) ∧ ∀ t : Icc s r, ∀ v, (U s t (R a s v),E t v) ∈ (H t).graph :=
  KFCausalUniformPhysicalGraphAssembly.exists_uniform_graph J
    (embedding_injective ε hε h hne hh m g k 0)
    (KFCausalClockFloorAveragedFormGeometry.embedding_dense ε hε h hne hh m g k 0)
    M (A a s) (P a s) (fun t : Icc s r => A a t) (L s)
    (fun t : Icc s r => L t) (fun t : Icc s r => H t)
    (fun t : Icc s r => (U s t : Hilbert →L[ℂ] Hilbert)) (R a s)
    (fun t : Icc s r => formLinearMap ε hε h hne hh m g k s t) a
    (mass_left_pairing ε hε h hne hh m g k)
    (shift_symmetric ε hε h hne hh m g k a s)
    (fun t => shift_symmetric ε hε h hne hh m g k a t)
    (referenceInverse_right ε hε h hne hh m g k a s ha)
    (fun t => lifted_closed ε hε h hne hh m g k t)
    (fun t => KFCausalClockFloorAveragedHamiltonian.hamiltonian_closed ε hε h hne hh m g k t)
    (fun t => shifted_graph_mass ε hε h hne hh m g k a t)
    (fun t x y hg => (physical_graph_iff ε hε h hne hh m g k t x y).mp hg)
    (shifted_lift_domain ε hε h hne hh m g k a s ha)
    (fun x => KFCausalCompactLiftedGraphBound.on_subtype L (fun t => F s t x) (Icc s r)
      (KFCausalClockFloorUniformLiftedOutput.uniform_lifted_graph ε hε h hne hh m g k s r hsr x))
    (KFCausalUniformEmbeddedOperators.compact_pointwise (Icc s r) isCompact_Icc (F s)
      (fun x => (KFCausalClockFloorStrongFormEvolution.formFlow_continuous ε hε h hne hh m g k s x).continuousOn))
    (KFCausalUniformEmbeddedOperators.compact_norm_bound (Icc s r) isCompact_Icc (A a)
      (referenceShift_continuous ε hε h hne hh m g k a).continuousOn)
    (fun t => evolution_norm_bound ε hε h hne hh m g k s t)
    (fun t x => (evolution_embedding ε hε h hne hh m g k s t x).symm)
    (resolvent_embedding ε hε h hne hh m g k a s)

theorem uniform_output_bound (s r : ℝ) (hsr : s ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc s r, ∀ x : (H s).domain,
      ∃ hx : U s t x ∈ (H t).domain, ‖H t ⟨U s t x,hx⟩‖ ≤ C*(‖(x:Hilbert)‖+‖H s x‖) :=
  KFCausalUniformGraphDynamics.output_bound (H s) H
    (fun t => (U s t : Hilbert →L[ℂ] Hilbert)) (R 1 s) (Icc s r)
    (fun x => by simpa only [one_smul,add_comm] using
      shiftedResolvent_left ε hε h hne hh m g k 1 s (by norm_num) x)
    (exists_uniform_graph ε hε h hne hh m g k 1 s r (by norm_num) hsr)

theorem trajectory_lipschitz_bound (s r : ℝ) (hsr : s ≤ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : (H s).domain, ∀ u ∈ Icc s r, ∀ v ∈ Icc s r,
      ‖U s v x-U s u x‖ ≤ K*(‖(x:Hilbert)‖+‖H s x‖)*‖v-u‖ :=
  KFCausalUniformGraphDynamics.lipschitz_bound (H s) H
    (fun t => (U s t : Hilbert →L[ℂ] Hilbert)) c (Icc s r) (convex_Icc s r)
    (fun t ht => KFCausalClockFloorFullDomainDynamics.forward_schrodinger ε hε h hne hh m g k s t ht.1)
    (uniform_output_bound ε hε h hne hh m g k s r hsr)

#print axioms evolution_norm_bound
#print axioms exists_uniform_graph
#print axioms uniform_output_bound
#print axioms trajectory_lipschitz_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorCompactGraphDynamics
