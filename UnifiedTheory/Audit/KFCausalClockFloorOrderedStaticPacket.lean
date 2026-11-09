/- Actual ordered outputs of the clock and inverse-clock radial packet
combination that represents the three static rows. The neutral second
polynomial derivative and both shifted clock powers are retained. The
identification of this combination with the maximal static operator is a
separate attachment; no arbitrary L2 holomorphic continuation is assumed. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentHamiltonian
import UnifiedTheory.Audit.KFCausalIndependentRadialKineticOutputIdentity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorOrderedStaticPacket
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalClockFloorBoundedInverse (inverseL ordered_graph_iff)
open KFCausalIndependentRadialPacketMoments (momentState momentState_zero)
open KFCausalIndependentRadialMomentClock (weightedState inverse_state_eq)
open KFCausalClockWeightedIndependentHamiltonian (clockAction)
open KFCausalGaussianHolomorphicClockWeight (multiplier bound multiplier_analytic
  bound_nonnegative multiplier_bound)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalNeutralLinePackets (step)
open KFCausalIndependentRadialKineticOutputIdentity (kineticCombination)

variable (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR)
  (hb : |h| ≤ ε/10)
local notation "Q" => orderedExponential ε hε h

private theorem half_bound (h : ℝ) : |-h/2| ≤ |h| := by
  rw [abs_div,abs_neg,show |(2:ℝ)|=2 by norm_num]
  linarith [abs_nonneg h]

def halfMoment (m n : ℕ) : Hilbert :=
  KFCausalIndependentRadialMomentExponential.halfState
    ε h a wL wL wR C p b P m n hε hh ha hL hR le_rfl hb 0

theorem moment_ordered_graph (m n : ℕ) :
    (momentState ε a h wL wR C p b P hε ha hh hL hR m n,
      halfMoment ε a h wL wR C p b P hε ha hh hL hR hb m n) ∈ (Q).graph :=
  (ordered_graph_iff ε hε h _ _).mpr
    (KFCausalIndependentRadialMomentExponential.actual_half_graph
      ε h a wL wL wR C p b P m n hε hh ha hL hR le_rfl hb)

def clockMomentOutput (inverse : Bool) (m n : ℕ) : Hilbert :=
  clockAction ε h a hε ha hb inverse (-h/2) (half_bound h)
    (halfMoment ε (a/2) h wL wR C p b P hε (by positivity) hh hL hR hb m n)

theorem clock_moment_ordered_graph (inverse : Bool) (m n : ℕ) :
    (weightedState ε a h wL wR C p b P hε ha hh hL hR hb m n inverse,
      clockMomentOutput ε a h wL wR C p b P hε ha hh hL hR hb inverse m n) ∈ (Q).graph := by
  have hg := KFCausalAnalyticClockSecondTransport.forward_graph
    (multiplier ε a inverse) h (bound ε h a inverse)
    (multiplier_analytic ε h a inverse hε hb)
    (bound_nonnegative ε h a inverse hε)
    (multiplier_bound ε h a inverse hε hb ha) ε hε hh 7 _ _
    (moment_ordered_graph ε (a/2) h wL wR C p b P hε (by positivity) hh hL hR hb m n)
  exact hg

def combination (F : Bool → ℕ → ℕ → Polynomial ℂ → Hilbert) : Hilbert :=
  (1/2:ℂ) • F false 0 0 P +
  (2*(h:ℂ)^2*(groundWidth h:ℂ)*(1/wL:ℝ)+
    2*(h:ℂ)^2*(groundWidth h:ℂ)*(wR:ℂ)) • F true 0 0 P +
  (-2*(h:ℂ)^2*((groundWidth h:ℂ)*(1/wL:ℝ))^2) • F true 1 0 P +
  (-2*(h:ℂ)^2*((groundWidth h:ℂ)*(wR:ℂ))^2) • F true 0 1 P +
  (-(h:ℂ)^2/2) • F true 0 0 (step (neutralWidth h) b (step (neutralWidth h) b P))

def staticInput : Hilbert := combination h wL wR b P
  (fun inverse m n R => weightedState ε a h wL wR C p b R hε ha hh hL hR hb m n inverse)

def orderedOutput : Hilbert := combination h wL wR b P
  (fun inverse m n R => clockMomentOutput ε a h wL wR C p b R hε ha hh hL hR hb inverse m n)

private theorem weighted_zero (inverse : Bool) :
    weightedState ε a h wL wR C p b P hε ha hh hL hR hb 0 0 inverse =
      KFCausalClockWeightedIndependentHamiltonian.singleState
        ε h a wL wR C p b P hε hh ha hL hR hb inverse := by
  unfold weightedState KFCausalClockWeightedIndependentHamiltonian.singleState
  rw [momentState_zero]

theorem static_input_eq : staticInput ε a h wL wR C p b P hε ha hh hL hR hb =
    (1/2:ℂ) • KFCausalClockWeightedIndependentHamiltonian.singleState
      ε h a wL wR C p b P hε hh ha hL hR hb false +
    (1/2:ℂ) • inverseL ε hε (inverseL ε hε
      (kineticCombination ε a h wL wR C p b P hε ha hh hL hR 0 +
       kineticCombination ε a h wL wR C p b P hε ha hh hL hR 1)) := by
  unfold staticInput combination
  dsimp only
  rw [weighted_zero ε a h wL wR C p b P hε ha hh hL hR hb false]
  simp only [inverse_state_eq,momentState_zero,kineticCombination,
    Matrix.cons_val_zero,Matrix.cons_val_one,map_add,map_smul]
  module

theorem ordered_static_graph :
    (staticInput ε a h wL wR C p b P hε ha hh hL hR hb,
      orderedOutput ε a h wL wR C p b P hε ha hh hL hR hb) ∈ (Q).graph := by
  have hg (inverse : Bool) (m n : ℕ) (R : Polynomial ℂ) :=
    clock_moment_ordered_graph ε a h wL wR C p b R hε ha hh hL hR hb inverse m n
  have hs := (Q).graph.add_mem
    ((Q).graph.add_mem
      ((Q).graph.add_mem
        ((Q).graph.add_mem
          ((Q).graph.smul_mem (1/2:ℂ) (hg false 0 0 P))
          ((Q).graph.smul_mem (2*(h:ℂ)^2*(groundWidth h:ℂ)*(1/wL:ℝ)+
            2*(h:ℂ)^2*(groundWidth h:ℂ)*(wR:ℂ)) (hg true 0 0 P)))
        ((Q).graph.smul_mem (-2*(h:ℂ)^2*((groundWidth h:ℂ)*(1/wL:ℝ))^2)
          (hg true 1 0 P)))
      ((Q).graph.smul_mem (-2*(h:ℂ)^2*((groundWidth h:ℂ)*(wR:ℂ))^2)
        (hg true 0 1 P)))
    ((Q).graph.smul_mem (-(h:ℂ)^2/2)
      (hg true 0 0 (step (neutralWidth h) b (step (neutralWidth h) b P))))
  exact hs

theorem static_input_ordered_domain :
    staticInput ε a h wL wR C p b P hε ha hh hL hR hb ∈ (Q).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (ordered_static_graph ε a h wL wR C p b P hε ha hh hL hR hb)

#print axioms moment_ordered_graph
#print axioms clock_moment_ordered_graph
#print axioms static_input_eq
#print axioms ordered_static_graph
#print axioms static_input_ordered_domain
end
end UnifiedTheory.Audit.KFCausalClockFloorOrderedStaticPacket
