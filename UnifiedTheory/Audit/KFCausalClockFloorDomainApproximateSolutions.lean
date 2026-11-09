/- Full-generator approximate solutions preserve the actual fixed domain.
The graph output is reconstructed from a bounded auxiliary equation. -/
import UnifiedTheory.Audit.KFCausalClockFloorGeneratorGraphDerivative
import UnifiedTheory.Audit.KFCausalClockFloorFullApproximateSolutions
import UnifiedTheory.Audit.KFCausalResolventDomainTrajectories

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorDomainApproximateSolutions
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFullApproximateSolutions
open UnifiedTheory.Audit.KFCausalClockFloorGeneratorGraphDerivative

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "R" => fullResolvent ε hε h hne hh m g k
local notation "D" => graphCorrection ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k

theorem approximate_solution_unique (a b s l r : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hadm : ∀ t ∈ Icc l r, q a s t < b) (u v : ℝ → V)
    (huC : ContinuousOn u (Icc l r)) (hvC : ContinuousOn v (Icc l r))
    (hu : ∀ t ∈ Icc l r, HasDerivWithinAt u (A a b s t (u t)) (Icc l r) t)
    (hv : ∀ t ∈ Icc l r, HasDerivWithinAt v (A a b s t (v t)) (Icc l r) t)
    (hi : u l = v l) : ∀ t ∈ Icc l r, u t = v t :=
  KFCausalResolventDomainTrajectories.solution_unique (A a b s) l r
    (approximation_continuousOn ε hε h hne hh m g k a b s l r ha hb hadm) u v huC hvC hu hv hi

theorem exists_domain_approximation (a lam b s l r : ℝ) (ha : 0 < a)
    (hlam : 0 < lam) (hb : 0 < b) (hlr : l ≤ r)
    (hadm : ∀ t ∈ Icc l r, q a s t < lam ∧ q a s t < b)
    (x y : V) (hxy : (x,y) ∈ (G a s l).graph) :
    ∃ w z : ℝ → V, w l = x ∧ z l = lam • x-y ∧
      ContinuousOn w (Icc l r) ∧ ContinuousOn z (Icc l r) ∧
      (∀ t ∈ Icc l r, w t = R a lam s t (z t)) ∧ ∀ t ∈ Icc l r,
        HasDerivWithinAt w (A a b s t (w t)) (Icc l r) t ∧
        HasDerivWithinAt z ((A a b s t-D a lam s t) (z t)) (Icc l r) t ∧
        (w t,lam • w t-z t) ∈ (G a s t).graph :=
  KFCausalResolventDomainTrajectories.exists_graph_solution (G a s) (A a b s) (R a lam s)
    (D a lam s) lam l r hlr
    (approximation_continuousOn ε hε h hne hh m g k a b s l r ha hb (fun t ht => (hadm t ht).2))
    ((graph_correction_continuousOn ε hε h hne hh m g k a lam s ha hlam).mono (fun t ht => (hadm t ht).1))
    (fun t ht => resolvent_factored_derivative ε hε h hne hh m g k a lam s t ha hlam (hadm t ht).1)
    (fun t ht => resolvent_approximation_commutes ε hε h hne hh m g k a lam b s t ha hlam hb
      (hadm t ht).1 (hadm t ht).2)
    (fun t ht => full_resolvent_graph ε hε h hne hh m g k a lam s t ha hlam (hadm t ht).1)
    (full_resolvent_left ε hε h hne hh m g k a lam s l ha hlam (hadm l ⟨le_rfl,hlr⟩).1) x y hxy

theorem every_approximation_preserves_domain (a lam b s l r : ℝ) (ha : 0 < a)
    (hlam : 0 < lam) (hb : 0 < b) (hlr : l ≤ r)
    (hadm : ∀ t ∈ Icc l r, q a s t < lam ∧ q a s t < b)
    (w : ℝ → V) (y : V) (hi : (w l,y) ∈ (G a s l).graph)
    (hc : ContinuousOn w (Icc l r))
    (hw : ∀ t ∈ Icc l r, HasDerivWithinAt w (A a b s t (w t)) (Icc l r) t) :
    ∃ z : ℝ → V, z l = lam • w l-y ∧ ContinuousOn z (Icc l r) ∧ ∀ t ∈ Icc l r,
      w t = R a lam s t (z t) ∧ HasDerivWithinAt z ((A a b s t-D a lam s t) (z t)) (Icc l r) t ∧
      (w t,lam • w t-z t) ∈ (G a s t).graph :=
  KFCausalResolventDomainTrajectories.every_solution_graph (G a s) (A a b s) (R a lam s)
    (D a lam s) lam l r hlr
    (approximation_continuousOn ε hε h hne hh m g k a b s l r ha hb (fun t ht => (hadm t ht).2))
    ((graph_correction_continuousOn ε hε h hne hh m g k a lam s ha hlam).mono (fun t ht => (hadm t ht).1))
    (fun t ht => resolvent_factored_derivative ε hε h hne hh m g k a lam s t ha hlam (hadm t ht).1)
    (fun t ht => resolvent_approximation_commutes ε hε h hne hh m g k a lam b s t ha hlam hb
      (hadm t ht).1 (hadm t ht).2)
    (fun t ht => full_resolvent_graph ε hε h hne hh m g k a lam s t ha hlam (hadm t ht).1)
    (full_resolvent_left ε hε h hne hh m g k a lam s l ha hlam (hadm l ⟨le_rfl,hlr⟩).1) w y hi hc hw

#print axioms approximate_solution_unique
#print axioms exists_domain_approximation
#print axioms every_approximation_preserves_domain
end
end UnifiedTheory.Audit.KFCausalClockFloorDomainApproximateSolutions
