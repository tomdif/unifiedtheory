/- Full clock integration by parts for the weighted original channel
kernels. Every C1 and integrability premise is supplied from the actual
packet envelopes. Positivity and a relative response bound are separate. -/
import UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralCross
import UnifiedTheory.Audit.KFCausalFiniteMatrixWholeClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralWholeClock
noncomputable section
open MeasureTheory
open KFCausalClockResponseTransport (clock coefficient)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)

def kernels (mass2 quartic vacuum : ℝ) (N : ℕ) (ε h : ℝ) (w : Fin N → ℝ)
    (b : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (i j : Fin N) : ℝ → ℂ :=
  KFCausalWeightedReciprocalNeutralCross.actual mass2 quartic vacuum ε (-h/2)
    (groundWidth h) (neutralWidth h) (w i) (w j) (b i) (b j) (P i) (P j)

variable (mass2 quartic vacuum : ℝ) (N : ℕ) (ε h : ℝ) (a w p : Fin N → ℝ)
  (C b : Fin N → ℂ) (P : Fin N → Polynomial ℂ)
local notation "K" => kernels mass2 quartic vacuum N ε h w b P
local notation "V" => KFCausalFiniteMatrixClockTransport.value N ε (-h/2) a p C K
local notation "T" => KFCausalFiniteMatrixClockTransport.transport N ε (-h/2) a p C K
local notation "W" => KFCausalFiniteMatrixClockTransport.weak N ε (-h/2) a p C K
local notation "R" => KFCausalFiniteMatrixClockTransport.reduced N ε (-h/2) a p C K
local notation "B" => KFCausalFiniteMatrixClockTransport.boundary N ε (-h/2) a p C K

def clockPairing (s : ℝ) : ℂ := V s
def positiveSlice (s : ℝ) : ℝ := (V s).re
def transportResponse (s : ℝ) : ℝ := (T s).re
def weakResponse (s : ℝ) : ℝ := (W s).re
def reducedResponse (s : ℝ) : ℝ := (R s).re
def boundary (s : ℝ) : ℝ := (B s).re

theorem reduced_identity (s : ℝ) :
    reducedResponse mass2 quartic vacuum N ε h a w p C b P s =
      coefficient ε (-h/2) s*positiveSlice mass2 quartic vacuum N ε h a w p C b P s-
        transportResponse mass2 quartic vacuum N ε h a w p C b P s/clock ε s := by
  simp only [reducedResponse,KFCausalFiniteMatrixClockTransport.reduced,
    positiveSlice,transportResponse,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,Complex.div_ofReal_re]

variable (hε : 0 < ε) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
  (hb : |h| ≤ 2*Real.pi*ε/3)

include hε hh hw hb in
theorem kernels_contDiff (i j : Fin N) : ContDiff ℝ 1 (K i j) := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  exact KFCausalWeightedReciprocalNeutralCross.actual_contDiff ε (-h/2)
    (groundWidth h) (neutralWidth h) (w i) (w j) (b i) (b j) (P i) (P j)
    hε hy (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) (hw i) (hw j) mass2 quartic vacuum

include hε hh hw hb in
theorem kernels_bounds (i j : Fin N) :
    (∃ M : ℝ, ∀ s, ‖K i j s‖ ≤ M) ∧
      (∃ M : ℝ, ∀ s, ‖deriv (K i j) s/(clock ε s:ℂ)‖ ≤ M) := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  obtain ⟨M,_,hm⟩ := KFCausalWeightedReciprocalNeutralCross.normalized_derivative_bounds
    ε (-h/2) (groundWidth h) (neutralWidth h) (w i) (w j) (b i) (b j) (P i) (P j)
    hε hy (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) (hw i) (hw j) mass2 quartic vacuum
  exact ⟨⟨M,fun s => (hm s).1⟩,⟨(4/ε)*M,fun s => (hm s).2⟩⟩

include hε hh hw hb in
theorem boundary_derivative (s : ℝ) :
    HasDerivAt (boundary mass2 quartic vacuum N ε h a w p C b P)
      (weakResponse mass2 quartic vacuum N ε h a w p C b P s-
        reducedResponse mass2 quartic vacuum N ε h a w p C b P s) s := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
    (KFCausalFiniteMatrixClockTransport.boundary_derivative N ε (-h/2) a p C K hε hy
      (kernels_contDiff mass2 quartic vacuum N ε h w b P hε hh hw hb) s)

variable (ha : ∀ i, 0 < a i)
include hε hh hw hb ha in
theorem response_integrability :
    Integrable (weakResponse mass2 quartic vacuum N ε h a w p C b P) ∧
      Integrable (reducedResponse mass2 quartic vacuum N ε h a w p C b P) ∧
        Integrable (boundary mass2 quartic vacuum N ε h a w p C b P) := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  have hK := kernels_contDiff mass2 quartic vacuum N ε h w b P hε hh hw hb
  have hV := fun i j => (kernels_bounds mass2 quartic vacuum N ε h w b P hε hh hw hb i j).1
  have hD := fun i j => (kernels_bounds mass2 quartic vacuum N ε h w b P hε hh hw hb i j).2
  exact ⟨(KFCausalFiniteMatrixWholeClock.weak_integrable N ε (-h/2) a p C K hε hy ha hK hV).re,
    (KFCausalFiniteMatrixWholeClock.reduced_integrable N ε (-h/2) a p C K hε hy ha hK hV hD).re,
    (KFCausalFiniteMatrixWholeClock.boundary_integrable N ε (-h/2) a p C K hε hy ha hK hV).re⟩

include hε hh hw hb ha in
theorem full_clock_identity :
    (∫ s, weakResponse mass2 quartic vacuum N ε h a w p C b P s)=
      ∫ s, reducedResponse mass2 quartic vacuum N ε h a w p C b P s := by
  obtain ⟨hW,hR,hB⟩ := response_integrability mass2 quartic vacuum N ε h a w p C b P hε hh hw hb ha
  have he := integral_eq_zero_of_hasDerivAt_of_integrable
    (boundary_derivative mass2 quartic vacuum N ε h a w p C b P hε hh hw hb) (hW.sub hR) hB
  rw [integral_sub hW hR] at he
  exact sub_eq_zero.mp he

#print axioms reduced_identity
#print axioms kernels_contDiff
#print axioms kernels_bounds
#print axioms boundary_derivative
#print axioms response_integrability
#print axioms full_clock_identity
end
end UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralWholeClock
