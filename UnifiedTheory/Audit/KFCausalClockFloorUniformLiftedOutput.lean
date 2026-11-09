/- Uniform moving lifted-Hamiltonian graph outputs along actual forward
form trajectories, recovered from the fixed-coordinate graph bound. -/
import UnifiedTheory.Audit.KFCausalCompactLiftedGraphBound
import UnifiedTheory.Audit.KFCausalClockFloorLimitDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorUniformLiftedOutput
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "D" => transportDerivative ε hε h hne hh m g k
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "L" => liftedHamiltonian ε hε h hne hh m g k
local notation "F" => formFlow ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

theorem graph_transfer (a s t : ℝ) (ha : 0 < a) (x y : V) (hg : (x,y) ∈ (G a s t).graph) :
    (S a s t x,c⁻¹ • (S a s t y+D a s t x)) ∈ (L t).graph :=
  KFCausalCompactLiftedGraphBound.mass_graph M (Q t) (S a s t) (D a s t) (G a s t) (L t) c
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr (one_div_ne_zero hne)))
    (lifted_graph_iff ε hε h hne hh m g k t)
    (transported_mass_equation ε hε h hne hh m g k a s t ha) x y hg

theorem uniform_lifted_graph (s r : ℝ) (hsr : s ≤ r) (x : (L s).domain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc s r, ∃ v : V, ‖v‖ ≤ C ∧ (F s t x,v) ∈ (L t).graph := by
  have hc := KFCausalClockFloorFullApproximationStability.coefficient_continuity
    ε hε h hne hh m g k 1 s (by norm_num)
  have hu : Continuous (fun t => S 1 t s (F s t x)) := hc.2.2.1.clm_apply
    (KFCausalClockFloorStrongFormEvolution.formFlow_continuous ε hε h hne hh m g k s x)
  have hb := KFCausalCompactLiftedGraphBound.normalize_initial (G 1 s) (S 1 s) (fun t => S 1 t s)
    (F s) s r (transport_initial ε hε h hne hh m g k 1 s (by norm_num))
    (KFCausalClockFloorLimitDomain.graph_bound ε hε h hne hh m g k 1 s s r (by norm_num) hsr) x
  have ht := KFCausalCompactLiftedGraphBound.compact_transfer (G 1 s) L (S 1 s) (D 1 s)
    (fun t => S 1 t s (F s t x)) c (Icc s r) isCompact_Icc
    hc.2.1.continuousOn hc.2.2.2.2.continuousOn hu.continuousOn
    (fun t _ => graph_transfer ε hε h hne hh m g k 1 s t (by norm_num)) hb
  exact KFCausalCompactLiftedGraphBound.remove_inverse L (S 1 s) (fun t => S 1 t s)
    (fun t => F s t x) (Icc s r)
    (fun t => KFCausalClockFloorFixedDomainApproximation.transport_inverse
      ε hε h hne hh m g k 1 s t (by norm_num) (F s t x)) ht

#print axioms graph_transfer
#print axioms uniform_lifted_graph
end
end UnifiedTheory.Audit.KFCausalClockFloorUniformLiftedOutput
