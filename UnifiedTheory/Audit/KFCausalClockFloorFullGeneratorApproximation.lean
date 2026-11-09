/- Full-generator approximations preserve the common domain and converge
there. The connection is included inside the resolvent regularization. -/
import UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
import UnifiedTheory.Audit.KFCausalEventualResolventApproximation
import UnifiedTheory.Audit.KFCausalPartialResolventGraphRegularization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "R" => fullResolvent ε hε h hne hh m g k
local notation "K" => baseBound ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k

def fullApproximation (a b s t : ℝ) : V →L[ℂ] V := b • (b • R a b s t-1)

theorem threshold_nonnegative (a s t : ℝ) : 0 ≤ q a s t :=
  mul_nonneg (norm_nonneg _) (base_bound_nonnegative ε hε h hne hh m g k a s t)

theorem full_scaled_bound (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbq : 2*q a s t < b) (f : V) : ‖b • R a b s t f‖ ≤ (2*K a s t)*‖f‖ := by
  have hgap : q a s t < b := by
    have hq := threshold_nonnegative ε hε h hne hh m g k a s t
    linarith
  exact KFCausalEventualResolventApproximation.scaled_bound_from_gap (R a b s t) b (q a s t)
    (K a s t) hb hgap hbq.le (base_bound_nonnegative ε hε h hne hh m g k a s t)
    (full_resolvent_bound ε hε h hne hh m g k a b s t ha hb hgap) f

theorem full_scaled_strong_limit (a s t : ℝ) (ha : 0 < a) (f : V) :
    Tendsto (fun b : ℝ => b • R a b s t f) atTop (𝓝 f) := by
  apply KFCausalEventualResolventApproximation.scaled_strong_limit (G a s t) (fun b => R a b s t)
    (2*K a s t) (2*q a s t)
    (mul_nonneg (by norm_num) (base_bound_nonnegative ε hε h hne hh m g k a s t))
    (fixed_dense ε hε h hne hh m g k a s t)
  · intro b hbq hb f
    exact full_scaled_bound ε hε h hne hh m g k a b s t ha hb hbq f
  · intro b hbq hb w
    have hq := threshold_nonnegative ε hε h hne hh m g k a s t
    exact full_resolvent_left ε hε h hne hh m g k a b s t ha hb (by linarith) (w:V) (G a s t w) ((G a s t).mem_graph w)

theorem full_approximation_strong_limit (a s t : ℝ) (ha : 0 < a) (w : (G a s t).domain) :
    Tendsto (fun b : ℝ => fullApproximation ε hε h hne hh m g k a b s t (w:V))
      atTop (𝓝 (G a s t w)) := by
  apply KFCausalEventualResolventApproximation.generator_strong_limit (G a s t) (fun b => R a b s t)
    (q a s t)
  · intro b hbq x
    have hb : 0 < b := (threshold_nonnegative ε hε h hne hh m g k a s t).trans_lt hbq
    exact full_resolvent_left ε hε h hne hh m g k a b s t ha hb hbq (x:V) (G a s t x) ((G a s t).mem_graph x)
  · exact full_scaled_strong_limit ε hε h hne hh m g k a s t ha

theorem full_approximation_on_domain (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbq : q a s t < b) (w : (G a s t).domain) :
    fullApproximation ε hε h hne hh m g k a b s t (w:V) = b • R a b s t (G a s t w) :=
  KFCausalPartialResolventGraphRegularization.regularization_on_domain (G a s t) (R a b s t) b
    (fun x => full_resolvent_left ε hε h hne hh m g k a b s t ha hb hbq
      (x:V) (G a s t x) ((G a s t).mem_graph x)) w

theorem full_approximation_graph (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbq : q a s t < b) (w : (G a s t).domain) :
    (fullApproximation ε hε h hne hh m g k a b s t (w:V),
      fullApproximation ε hε h hne hh m g k a b s t (G a s t w)) ∈ (G a s t).graph :=
  KFCausalPartialResolventGraphRegularization.regularization_graph (G a s t) (R a b s t) b
    (full_resolvent_graph ε hε h hne hh m g k a b s t ha hb hbq)
    (fun x => full_resolvent_left ε hε h hne hh m g k a b s t ha hb hbq
      (x:V) (G a s t x) ((G a s t).mem_graph x)) w

theorem scaled_resolvent_graph (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbq : q a s t < b) (w : (G a s t).domain) :
    (b • R a b s t (w:V),b • R a b s t (G a s t w)) ∈ (G a s t).graph :=
  KFCausalPartialResolventGraphRegularization.scaled_graph (G a s t) (R a b s t) b
    (full_resolvent_graph ε hε h hne hh m g k a b s t ha hb hbq)
    (fun x => full_resolvent_left ε hε h hne hh m g k a b s t ha hb hbq
      (x:V) (G a s t x) ((G a s t).mem_graph x)) w

theorem scaled_resolvent_graph_limit (a s t : ℝ) (ha : 0 < a) (w : (G a s t).domain) :
    Tendsto (fun b : ℝ => (b • R a b s t (w:V),b • R a b s t (G a s t w)))
      atTop (𝓝 ((w:V),G a s t w)) :=
  (full_scaled_strong_limit ε hε h hne hh m g k a s t ha (w:V)).prodMk_nhds
    (full_scaled_strong_limit ε hε h hne hh m g k a s t ha (G a s t w))

#print axioms threshold_nonnegative
#print axioms full_scaled_bound
#print axioms full_scaled_strong_limit
#print axioms full_approximation_strong_limit
#print axioms full_approximation_on_domain
#print axioms full_approximation_graph
#print axioms scaled_resolvent_graph
#print axioms scaled_resolvent_graph_limit
end
end UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
