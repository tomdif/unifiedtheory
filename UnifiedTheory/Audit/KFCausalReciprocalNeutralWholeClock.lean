/- Full clock integration by parts for the actual joint neutral/reciprocal
family. All matrix regularity and absolute bounds are discharged here;
the coupled relative transport estimate remains a separate question. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralCrossBounds
import UnifiedTheory.Audit.KFCausalFiniteMatrixWholeClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralWholeClock
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalClockResponseTransport (clock coefficient pair)
open KFCausalReciprocalNeutralPositiveEnergy (coefficients clockPairing positiveSlice)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalReciprocalNeutralCrossDifferentiation (actual)

def kernels (N : ℕ) (ε h : ℝ) (w : Fin N → ℝ) (b : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (i j : Fin N) : ℝ → ℂ :=
  actual ε (-h/2) (groundWidth h) (neutralWidth h) (w i) (w j) (b i) (b j) (P i) (P j)

variable (N : ℕ) (ε h : ℝ) (a w p : Fin N → ℝ) (C b : Fin N → ℂ) (P : Fin N → Polynomial ℂ)
local notation "K" => kernels N ε h w b P
local notation "V" => KFCausalFiniteMatrixClockTransport.value N ε (-h/2) a p C K
local notation "T" => KFCausalFiniteMatrixClockTransport.transport N ε (-h/2) a p C K
local notation "W" => KFCausalFiniteMatrixClockTransport.weak N ε (-h/2) a p C K
local notation "R" => KFCausalFiniteMatrixClockTransport.reduced N ε (-h/2) a p C K
local notation "B" => KFCausalFiniteMatrixClockTransport.boundary N ε (-h/2) a p C K

def transportResponse (s : ℝ) : ℝ := (T s).re
def weakResponse (s : ℝ) : ℝ := (W s).re
def reducedResponse (s : ℝ) : ℝ := coefficient ε (-h/2) s*positiveSlice N ε h a w p C b P s-
  transportResponse N ε h a w p C b P s/clock ε s
def boundary (s : ℝ) : ℝ := positiveSlice N ε h a w p C b P s/clock ε s

theorem value_identity (s : ℝ) : V s = clockPairing N ε h a w p C b P s := by
  unfold KFCausalFiniteMatrixClockTransport.value clockPairing KFCausalReciprocalNeutralPositiveForm.pairing
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [kernels,actual,pair,coefficients,map_mul,Complex.star_def]
  ring

variable (hε : 0 < ε) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3)

include hε hh hw hb in
theorem kernels_contDiff (i j : Fin N) : ContDiff ℝ 1 (K i j) := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  exact KFCausalReciprocalNeutralCrossDifferentiation.actual_contDiff ε (-h/2) _ _ _ _ _ _ _ _ hε hy
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) (hw i) (hw j)

include hε hh hw hb in
theorem kernels_bounds (i j : Fin N) :
    (∃ M : ℝ, ∀ s, ‖K i j s‖ ≤ M) ∧
      (∃ M : ℝ, ∀ s, ‖deriv (K i j) s/(clock ε s:ℂ)‖ ≤ M) := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  obtain ⟨M,_,hm⟩ := KFCausalReciprocalNeutralCrossBounds.normalized_derivative_bounds ε (-h/2)
    _ _ (w i) (w j) (b i) (b j) (P i) (P j) hε hy
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) (hw i) (hw j)
  exact ⟨⟨M,fun s => (hm s).1⟩,⟨(4/ε)*M,fun s => (hm s).2⟩⟩

include hε hh hw hb in
theorem boundary_identity (s : ℝ) : (B s).re = boundary N ε h a w p C b P s := by
  rw [KFCausalFiniteMatrixClockTransport.boundary,value_identity,
    KFCausalReciprocalNeutralPositiveEnergy.clockPairing_positive N ε h a w p C b P hε hh hw hb]
  simp only [boundary,Complex.div_ofReal_re,Complex.ofReal_re]

include hε hh hw hb in
theorem reduced_identity (s : ℝ) : (R s).re = reducedResponse N ε h a w p C b P s := by
  rw [KFCausalFiniteMatrixClockTransport.reduced,value_identity,
    KFCausalReciprocalNeutralPositiveEnergy.clockPairing_positive N ε h a w p C b P hε hh hw hb]
  simp only [reducedResponse,transportResponse,Complex.sub_re,← Complex.ofReal_mul,
    Complex.div_ofReal_re,Complex.ofReal_re]

include hε hh hw hb in
theorem transport_frozen_derivative (s : ℝ) : transportResponse N ε h a w p C b P s =
    KFCausalReciprocalNeutralClockDerivative.totalResponse N ε (-h/2) (groundWidth h) (neutralWidth h)
      w b P (fun _ => coefficients N ε h a p C s) s := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  let c := coefficients N ε h a p C s
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (((kernels_contDiff N ε h w b P hε hh hw hb i j).differentiable (by norm_num)).differentiableAt.hasDerivAt
        (x := s)).const_mul (conj (c i)*c j)))
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hd
  have he := hr.unique (KFCausalReciprocalNeutralKernelDerivative.fixed_pairing_derivative N ε (-h/2)
    (groundWidth h) (neutralWidth h) w b P hε hy
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hw c s)
  calc
    transportResponse N ε h a w p C b P s = (∑ i, ∑ j, (conj (c i)*c j)*deriv (K i j) s).re := by
      unfold transportResponse KFCausalFiniteMatrixClockTransport.transport
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [c,coefficients,pair,map_mul,Complex.star_def]
      ring
    _ = _ := he

include hε hh hw hb in
theorem boundary_derivative (s : ℝ) : HasDerivAt (boundary N ε h a w p C b P)
    (weakResponse N ε h a w p C b P s-reducedResponse N ε h a w p C b P s) s := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
    (KFCausalFiniteMatrixClockTransport.boundary_derivative N ε (-h/2) a p C K hε hy
      (kernels_contDiff N ε h w b P hε hh hw hb) s)
  have he : (fun t => (B t).re) = boundary N ε h a w p C b P :=
    funext (boundary_identity N ε h a w p C b P hε hh hw hb)
  change HasDerivAt (fun t => (B t).re) ((W s).re-(R s).re) s at hd
  rw [he,reduced_identity N ε h a w p C b P hε hh hw hb] at hd
  exact hd

variable (ha : ∀ i, 0 < a i)

include hε hh hw hb ha in
theorem response_integrability : Integrable (weakResponse N ε h a w p C b P) ∧
    Integrable (reducedResponse N ε h a w p C b P) ∧ Integrable (boundary N ε h a w p C b P) := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  have hK := kernels_contDiff N ε h w b P hε hh hw hb
  have hV := fun i j => (kernels_bounds N ε h w b P hε hh hw hb i j).1
  have hD := fun i j => (kernels_bounds N ε h w b P hε hh hw hb i j).2
  refine ⟨(KFCausalFiniteMatrixWholeClock.weak_integrable N ε (-h/2) a p C K hε hy ha hK hV).re, ?_, ?_⟩
  · exact (KFCausalFiniteMatrixWholeClock.reduced_integrable N ε (-h/2) a p C K hε hy ha hK hV hD).re.congr
      (Filter.Eventually.of_forall (reduced_identity N ε h a w p C b P hε hh hw hb))
  · exact (KFCausalFiniteMatrixWholeClock.boundary_integrable N ε (-h/2) a p C K hε hy ha hK hV).re.congr
      (Filter.Eventually.of_forall (boundary_identity N ε h a w p C b P hε hh hw hb))

include hε hh hw hb ha in
theorem full_clock_identity : (∫ s, weakResponse N ε h a w p C b P s) =
    ∫ s, reducedResponse N ε h a w p C b P s := by
  obtain ⟨hW,hR,hB⟩ := response_integrability N ε h a w p C b P hε hh hw hb ha
  have he := integral_eq_zero_of_hasDerivAt_of_integrable
    (boundary_derivative N ε h a w p C b P hε hh hw hb) (hW.sub hR) hB
  rw [integral_sub hW hR] at he
  exact sub_eq_zero.mp he

#print axioms value_identity
#print axioms kernels_contDiff
#print axioms kernels_bounds
#print axioms boundary_identity
#print axioms reduced_identity
#print axioms transport_frozen_derivative
#print axioms boundary_derivative
#print axioms response_integrability
#print axioms full_clock_identity
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralWholeClock
