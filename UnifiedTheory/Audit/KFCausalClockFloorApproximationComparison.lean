/- Actual full-generator velocity and two-parameter comparison estimates.
The velocity bound is obtained from the generator graph, not assumed globally. -/
import UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorDissipation
import UnifiedTheory.Audit.KFCausalQuasiResolventVelocity
import UnifiedTheory.Audit.KFCausalWeightedCauchyPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorApproximationComparison
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorDissipation
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "R" => fullResolvent ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "W" => transportedMetric ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k
local notation "ω" => quasiRate ε hε h hne hh m g k

theorem full_velocity_energy (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbq : q a s t < b) (hbω : 2*ω a s t ≤ b) (x y : V) (hxy : (x,y) ∈ (G a s t).graph) :
    energy (W a s t) (A a b s t x) ≤ 4*energy (W a s t) y :=
  KFCausalQuasiResolventVelocity.velocity_energy (G a s t) (W a s t) (R a b s t) (A a b s t) b (ω a s t)
    (metric_symmetric ε hε h hne hh m g k a s t)
    (metric_nonnegative ε hε h hne hh m g k a s t ha) hb
    (quasi_rate_nonnegative ε hε h hne hh m g k a s t ha) hbω rfl
    (full_resolvent_graph ε hε h hne hh m g k a b s t ha hb hbq)
    (full_resolvent_left ε hε h hne hh m g k a b s t ha hb hbq)
    (full_generator_quasi_bound ε hε h hne hh m g k a s t ha) x y hxy

theorem transported_velocity_energy (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbq : q a s t < b) (hbω : 2*ω a s t ≤ b) (x y : V) (hxy : (x,y) ∈ (G a s t).graph) :
    energy (F a t) (S a s t (A a b s t x)) ≤ 4*energy (F a t) (S a s t y) :=
  KFCausalQuasiResolventVelocity.energy_transfer (W a s t) (F a t) (S a s t) (A a b s t x) y 4
    (metric_energy ε hε h hne hh m g k a s t (A a b s t x))
    (metric_energy ε hε h hne hh m g k a s t y)
    (full_velocity_energy ε hε h hne hh m g k a b s t ha hb hbq hbω x y hxy)

theorem full_smoothed_graph (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbq : q a s t < b) (x : V) : (b • R a b s t x,A a b s t x) ∈ (G a s t).graph :=
  KFCausalQuasiResolventVelocity.smoothed_graph (G a s t) (R a b s t) (A a b s t) b rfl
    (full_resolvent_graph ε hε h hne hh m g k a b s t ha hb hbq) x

theorem full_smoothed_error (a b s t : ℝ) (hb : b ≠ 0) (x : V) :
    b • R a b s t x-x = (1/b) • A a b s t x :=
  KFCausalQuasiResolventVelocity.smoothed_error (R a b s t) (A a b s t) b hb rfl x

theorem full_smoothed_complex_error (a b s t : ℝ) (hb : b ≠ 0) (x : V) :
    b • R a b s t x-x = ((1/b:ℝ):ℂ) • A a b s t x := by
  simpa only [Complex.coe_smul] using full_smoothed_error ε hε h hne hh m g k a b s t hb x

theorem graph_difference_quasi (a s t : ℝ) (ha : 0 < a) (u z v w : V)
    (hu : (u,v) ∈ (G a s t).graph) (hz : (z,w) ∈ (G a s t).graph) :
    (inner ℂ (u-z) (W a s t (v-w))).re ≤ ω a s t*energy (W a s t) (u-z) :=
  full_generator_quasi_bound ε hε h hne hh m g k a s t ha (u-z) (v-w)
    ((G a s t).graph.sub_mem hu hz)

theorem graph_comparison_pairing (a s t M p q₀ : ℝ) (ha : 0 < a) (hM : 0 ≤ M)
    (hp : 0 ≤ p) (hq₀ : 0 ≤ q₀) (hsum : 0 < p+q₀) (hsum₁ : p+q₀ ≤ 1)
    (x y u z v w : V) (hu : (u,v) ∈ (G a s t).graph) (hz : (z,w) ∈ (G a s t).graph)
    (hex : u-x = (p:ℂ) • v) (hey : z-y = (q₀:ℂ) • w)
    (hv : energy (W a s t) v ≤ M) (hw : energy (W a s t) w ≤ M) :
    2*(inner ℂ (x-y) (W a s t (v-w))).re ≤
      4*ω a s t*energy (W a s t) (x-y)+(6+8*ω a s t)*M*(p+q₀) :=
  KFCausalWeightedCauchyPairing.pairing_at_output (W a s t)
    (metric_symmetric ε hε h hne hh m g k a s t)
    (metric_nonnegative ε hε h hne hh m g k a s t ha) (ω a s t) M p q₀
    (quasi_rate_nonnegative ε hε h hne hh m g k a s t ha) hM hp hq₀ hsum hsum₁
    x y u z v w (x-y) (v-w) (u-z) rfl rfl rfl hex hey hv hw
    (graph_difference_quasi ε hε h hne hh m g k a s t ha u z v w hu hz)

theorem full_comparison_pairing (a b c s t M : ℝ) (ha : 0 < a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hbq : q a s t < b) (hcq : q a s t < c) (hM : 0 ≤ M) (x y : V)
    (hx : energy (W a s t) (A a b s t x) ≤ M) (hy : energy (W a s t) (A a c s t y) ≤ M) :
    2*(inner ℂ (x-y) (W a s t (A a b s t x-A a c s t y))).re ≤
      4*ω a s t*energy (W a s t) (x-y)+(6+8*ω a s t)*M*(1/b+1/c) := by
  have hb₀ : 0 < b := by linarith
  have hc₀ : 0 < c := by linarith
  have hsum := KFCausalWeightedCauchyPairing.reciprocal_parameters b c hb hc
  exact graph_comparison_pairing ε hε h hne hh m g k a s t M (1/b) (1/c) ha hM
    (by positivity) (by positivity) hsum.1 hsum.2 x y (b • R a b s t x) (c • R a c s t y)
    (A a b s t x) (A a c s t y)
    (full_smoothed_graph ε hε h hne hh m g k a b s t ha hb₀ hbq x)
    (full_smoothed_graph ε hε h hne hh m g k a c s t ha hc₀ hcq y)
    (full_smoothed_complex_error ε hε h hne hh m g k a b s t (ne_of_gt hb₀) x)
    (full_smoothed_complex_error ε hε h hne hh m g k a c s t (ne_of_gt hc₀) y) hx hy

theorem transported_comparison_pairing (a b c s t M : ℝ) (ha : 0 < a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hbq : q a s t < b) (hcq : q a s t < c) (hM : 0 ≤ M) (x y : V)
    (hx : energy (W a s t) (A a b s t x) ≤ M) (hy : energy (W a s t) (A a c s t y) ≤ M) :
    2*(inner ℂ (S a s t (x-y)) (F a t (S a s t (A a b s t x-A a c s t y)))).re ≤
      4*ω a s t*energy (F a t) (S a s t (x-y))+(6+8*ω a s t)*M*(1/b+1/c) :=
  KFCausalWeightedCauchyPairing.pairing_transfer (W a s t) (F a t) (S a s t) (x-y)
    (A a b s t x-A a c s t y) (ω a s t) M (1/b+1/c)
    (metric_pairing ε hε h hne hh m g k a s t (x-y) (A a b s t x-A a c s t y))
    (metric_energy ε hε h hne hh m g k a s t (x-y))
    (full_comparison_pairing ε hε h hne hh m g k a b c s t M ha hb hc hbq hcq hM x y hx hy)

#print axioms full_velocity_energy
#print axioms transported_velocity_energy
#print axioms full_smoothed_graph
#print axioms full_smoothed_error
#print axioms full_smoothed_complex_error
#print axioms graph_difference_quasi
#print axioms graph_comparison_pairing
#print axioms full_comparison_pairing
#print axioms transported_comparison_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorApproximationComparison
