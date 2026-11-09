/- The exact remaining moment-propagation criterion expressed in actual
integrated resolvent responses. No uniform bound on those responses is
postulated as an unconditional fact about the full Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalPureMomentumJointLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPureMomentumResponseCriterion
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPureMomentumCutoff
open UnifiedTheory.Audit.KFCausalPureMomentumFirstMoment
open UnifiedTheory.Audit.KFCausalPureMomentumCutoffDomain
open UnifiedTheory.Audit.KFCausalPureMomentumJointLimit
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolventEhrenfest (boundedRate)

def cutoff (n : ℕ) : ℝ := 1/((n:ℝ)+1)

theorem cutoff_positive (n : ℕ) : 0 < cutoff n := by unfold cutoff; positivity

theorem cutoff_le_one (n : ℕ) : cutoff n ≤ 1 := by
  unfold cutoff
  exact (div_le_one (by positivity : 0 < (n:ℝ)+1)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem cutoff_tendsto : Tendsto cutoff atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

theorem smoothingScale_cutoff (n : ℕ) : smoothingScale (cutoff n) = ((n:ℝ)+1)^4 := by
  simp only [smoothingScale,cutoff,one_div,inv_inv]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "U" => evolution ε hε h hne hh m g k
local notation "Q" => momentumHalf ε hε h
local notation "D" n:arg => absoluteCutoff ε hε h (cutoff n) (cutoff_positive n)

def integratedResponse (n : ℕ) (s r t : ℝ) (v : V) : ℝ :=
  (∫ z in r..t, boundedRate ε hε h hne hh m g k (smoothingScale (cutoff n)) (D n) s z v).re

def cutoffMoment (n : ℕ) (s t : ℝ) (v : V) : ℝ :=
  (inner ℂ (U s t (J v)) ((D n) (U s t (J v)))).re

local notation "I" => integratedResponse ε hε h hne hh m g k
local notation "M" => cutoffMoment ε hε h hne hh m g k
local notation "C" => remainderConstant ε hε h hne hh m g k

theorem response_remainder_bound (n : ℕ) (s r t : ℝ) (v : V) :
    |I n s r t v-(M n s t v-M n s r v)| ≤ cutoff n*C s r t v := by
  have he := (Complex.abs_re_le_norm
    (KFCausalClockFloorMovingResolventWindow.residual ε hε h hne hh m g k
      (smoothingScale (cutoff n)) (D n) s r t v)).trans
    (joint_remainder_bound ε hε h hne hh m g k (cutoff n) (cutoff_positive n) (D n)
      (operator_opNorm _ _ _ _ _) s r t v)
  simpa only [KFCausalClockFloorMovingResolventWindow.residual,
    KFCausalClockFloorResolventBalance.expectation,Complex.sub_re,integratedResponse,cutoffMoment] using he

theorem response_remainder_uniform (n : ℕ) (s r t : ℝ) (v : V) :
    |I n s r t v-(M n s t v-M n s r v)| ≤ C s r t v :=
  (response_remainder_bound ε hε h hne hh m g k n s r t v).trans
    (mul_le_of_le_one_left (remainderConstant_nonnegative ε hε h hne hh m g k s r t v) (cutoff_le_one n))

theorem domain_iff_bounded_responses (s r t : ℝ) (v : V)
    (hr : U s r (J v) ∈ (Q).domain) :
    U s t (J v) ∈ (Q).domain ↔ ∃ L : ℝ, ∀ n, I n s r t v ≤ L := by
  constructor
  · intro ht
    refine ⟨‖Q ⟨U s t (J v),ht⟩‖^2+C s r t v,?_⟩
    intro n
    have he := response_remainder_uniform ε hε h hne hh m g k n s r t v
    have hl : 0 ≤ M n s r v := absolute_cutoff_nonnegative ε hε h _ _ _
    have hu : M n s t v ≤ ‖Q ⟨U s t (J v),ht⟩‖^2 := absolute_cutoff_le_moment ε hε h _ _ _ ht
    linarith [le_abs_self (I n s r t v-(M n s t v-M n s r v))]
  · rintro ⟨L,hL⟩
    apply (domain_iff_uniform_absolute_cutoffs ε hε h _ cutoff cutoff_positive cutoff_tendsto).mpr
    refine ⟨L+‖Q ⟨U s r (J v),hr⟩‖^2+C s r t v,?_⟩
    intro n
    have he := response_remainder_uniform ε hε h hne hh m g k n s r t v
    have hu : M n s r v ≤ ‖Q ⟨U s r (J v),hr⟩‖^2 := absolute_cutoff_le_moment ε hε h _ _ _ hr
    change M n s t v ≤ _
    linarith [neg_le_abs (I n s r t v-(M n s t v-M n s r v)),hL n]

theorem unbounded_responses_of_outside_domain (s r t : ℝ) (v : V)
    (hr : U s r (J v) ∈ (Q).domain) (ht : U s t (J v) ∉ (Q).domain) (L : ℝ) :
    ∃ n, L < I n s r t v := by
  by_contra hn
  push_neg at hn
  exact ht ((domain_iff_bounded_responses ε hε h hne hh m g k s r t v hr).mpr ⟨L,hn⟩)

theorem response_upper_bound_moment_bound (s r t : ℝ) (v : V)
    (hr : U s r (J v) ∈ (Q).domain) (L : ℝ) (hL : ∀ n, I n s r t v ≤ L) :
    ∃ ht : U s t (J v) ∈ (Q).domain,
      ‖Q ⟨U s t (J v),ht⟩‖^2 ≤ ‖Q ⟨U s r (J v),hr⟩‖^2+L := by
  have ht := (domain_iff_bounded_responses ε hε h hne hh m g k s r t v hr).mpr ⟨L,hL⟩
  refine ⟨ht,?_⟩
  have hc := joint_absolute_response_limit ε hε h hne hh m g k cutoff cutoff_positive cutoff_tendsto s r t v hr ht
  have he : ‖Q ⟨U s t (J v),ht⟩‖^2-‖Q ⟨U s r (J v),hr⟩‖^2 ≤ L :=
    le_of_tendsto hc (Filter.Eventually.of_forall hL)
  linarith only [he]

#print axioms cutoff_positive
#print axioms cutoff_le_one
#print axioms cutoff_tendsto
#print axioms smoothingScale_cutoff
#print axioms response_remainder_bound
#print axioms response_remainder_uniform
#print axioms domain_iff_bounded_responses
#print axioms unbounded_responses_of_outside_domain
#print axioms response_upper_bound_moment_bound
end
end UnifiedTheory.Audit.KFCausalPureMomentumResponseCriterion
