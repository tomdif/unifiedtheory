/- A common reciprocal charged width has a response constant independent
of that width, neutral sources/degrees/counts, and independent clock
widths/frequencies. The actual full-clock ordered-potential pairing is
bounded; unequal charged-width interference remains outside this result. -/
import UnifiedTheory.Audit.KFCausalNeutralWidthUniformGrowth
import UnifiedTheory.Audit.KFCausalReciprocalNeutralCommonWidthKernel
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPotentialTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralCommonWidthResponse
noncomputable section
open MeasureTheory
open KFCausalClockFloorRelativeShift (scale)
open KFCausalClockResponseTransport (clock coefficient coefficient_lower)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalReciprocalNeutralPositiveForm (pairing)
open KFCausalNeutralFiniteResponse (realKernel realKernel_derivative)
open KFCausalReciprocalNeutralCommonWidthKernel (pairing_common_real)
open KFCausalReciprocalNeutralPositiveEnergy (coefficients clockPairing positiveSlice)
open KFCausalReciprocalNeutralWholeClock (transportResponse reducedResponse)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)

theorem exists_common_kernel_derivative (α : ℝ) (hα : 0 < α) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ β ε y w : ℝ, 0 < β → 32*β ≤ α →
      0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 → 1 ≤ w →
      ∀ (N : ℕ) (b c : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (s : ℝ),
      deriv (fun t => (pairing N α β (fun _ => w) (scale ε y t) c c
        (fun i => exponentialProfile (b i) 1 (P i))).re) s ≤
      M*(pairing N α β (fun _ => w) (scale ε y s) c c
        (fun i => exponentialProfile (b i) 1 (P i))).re := by
  obtain ⟨M,hM,hd⟩ := KFCausalNeutralWidthUniformGrowth.exists_upper_width_kernel_derivative α hα
  refine ⟨M,hM,?_⟩
  intro β ε y w hβ hwidth hε hy hy0 hw N b c P s
  have hw₀ : 0 < w := by linarith
  have hαw : α ≤ α*w := by nlinarith
  have he : (fun t => (pairing N α β (fun _ => w) (scale ε y t) c c
      (fun i => exponentialProfile (b i) 1 (P i))).re) =
      fun t => w^2*realKernel ε y (α*w) β N b c P t :=
    funext (pairing_common_real N ε y α β w b c P hα hβ hwidth hw hε hy)
  have hder := realKernel_derivative (α*w) β ε y s (by positivity) hβ
    (hwidth.trans hαw) hε hy N b c P
  have hb := mul_le_mul_of_nonneg_left
    (hd (α*w) β ε y hαw hβ (hwidth.trans hαw) hε hy hy0 N b c P s) (sq_nonneg w)
  rw [hder.deriv] at hb
  rw [he,(hder.const_mul (w^2)).deriv,
    pairing_common_real N ε y α β w b c P hα hβ hwidth hw hε hy]
  nlinarith [hb]

theorem exists_common_transport_bound (h : ℝ) (hh : h ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε w : ℝ, 0 < ε → |h| ≤ 2*Real.pi*ε/3 → 1 ≤ w →
      ∀ (N : ℕ) (a p : Fin N → ℝ) (c b : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (s : ℝ),
      transportResponse N ε h a (fun _ => w) p c b P s ≤
        M*positiveSlice N ε h a (fun _ => w) p c b P s := by
  obtain ⟨M,hM,hd⟩ := exists_common_kernel_derivative (groundWidth h) (groundWidth_positive h hh)
  refine ⟨M,hM,?_⟩
  intro ε w hε hb hw N a p c b P s
  have hy := KFCausalClockFloorShiftedOutput.shift_bound ε h hb
  have hy0 : (-h/2:ℝ) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hh) (by norm_num)
  let cs := coefficients N ε h a p c s
  have hdiff := KFCausalReciprocalNeutralKernelDerivative.fixed_pairing_derivative N ε (-h/2)
    (groundWidth h) (neutralWidth h) (fun _ => w) b P hε hy
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    (fun _ => hw) cs s
  have hbnd := hd (neutralWidth h) ε (-h/2) w (neutralWidth_positive h hh)
    (neutralWidth_bound h) hε hy hy0 hw N b cs P s
  rw [hdiff.deriv] at hbnd
  have he := congrArg Complex.re
    (KFCausalReciprocalNeutralPositiveEnergy.clockPairing_positive N ε h a (fun _ => w) p c b P
      hε hh (fun _ => hw) hb s)
  change (pairing N (groundWidth h) (neutralWidth h) (fun _ => w) (scale ε (-h/2) s)
    cs cs (fun i => exponentialProfile (b i) 1 (P i))).re =
    positiveSlice N ε h a (fun _ => w) p c b P s at he
  rw [KFCausalReciprocalNeutralWholeClock.transport_frozen_derivative
    N ε h a (fun _ => w) p c b P hε hh (fun _ => hw) hb]
  rwa [he] at hbnd

theorem exists_common_reduced_bound (h : ℝ) (hh : h ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε w : ℝ, 0 < ε → |h| ≤ 2*Real.pi*ε/3 → 1 ≤ w →
      ∀ (N : ℕ) (a p : Fin N → ℝ) (c b : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (s : ℝ),
      -((M+2)/ε)*positiveSlice N ε h a (fun _ => w) p c b P s ≤
        reducedResponse N ε h a (fun _ => w) p c b P s := by
  obtain ⟨M,hM,ht⟩ := exists_common_transport_bound h hh
  refine ⟨M,hM,?_⟩
  intro ε w hε hb hw N a p c b P s
  have hE := KFCausalReciprocalNeutralPositiveEnergy.positiveSlice_nonnegative
    N ε h a (fun _ => w) p c b P s
  have hc : 0 < clock ε s := by unfold clock; positivity
  have hec : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  have hcoef := mul_le_mul_of_nonneg_right
    (coefficient_lower ε (-h/2) s hε (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)) hE
  have hder : transportResponse N ε h a (fun _ => w) p c b P s/clock ε s ≤
      (M/ε)*positiveSlice N ε h a (fun _ => w) p c b P s := by
    calc
      _ ≤ (M*positiveSlice N ε h a (fun _ => w) p c b P s)/clock ε s :=
        div_le_div_of_nonneg_right (ht ε w hε hb hw N a p c b P s) hc.le
      _ = (M/clock ε s)*positiveSlice N ε h a (fun _ => w) p c b P s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hM hε hec) hE
  unfold reducedResponse
  have he : -((M+2)/ε)*positiveSlice N ε h a (fun _ => w) p c b P s =
      -(2/ε)*positiveSlice N ε h a (fun _ => w) p c b P s-
        (M/ε)*positiveSlice N ε h a (fun _ => w) p c b P s := by ring
  rw [he]
  linarith

theorem exists_common_potential_bound (h : ℝ) (hh : h ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε w : ℝ, ∀ hε : 0 < ε, ∀ hb : |h| ≤ 2*Real.pi*ε/3,
      ∀ hw : 1 ≤ w, ∀ (N : ℕ) (a p : Fin N → ℝ) (c b : Fin N → ℂ)
      (P : Fin N → Polynomial ℂ), ∀ ha : ∀ i, 0 < a i,
      -((M+2)/ε)*KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy
        N ε h a (fun _ => w) p c b P hε ha hh (fun _ => hw) hb ≤
      KFCausalReciprocalNeutralPotentialTransport.potentialResponse
        N ε h a (fun _ => w) p c b P hε ha hh (fun _ => hw) hb := by
  obtain ⟨M,hM,hbound⟩ := exists_common_reduced_bound h hh
  refine ⟨M,hM,?_⟩
  intro ε w hε hb hw N a p c b P ha
  rw [KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy_positive_integral,
    KFCausalReciprocalNeutralPotentialTransport.potentialResponse_reduced_integral,
    ← integral_const_mul]
  exact integral_mono
    ((KFCausalReciprocalNeutralPositiveEnergy.positiveSlice_integrable
      N ε h a (fun _ => w) p c b P hε ha hh (fun _ => hw) hb).const_mul _)
    (KFCausalReciprocalNeutralWholeClock.response_integrability
      N ε h a (fun _ => w) p c b P hε hh (fun _ => hw) hb ha).2.1
    (hbound ε w hε hb hw N a p c b P)

#print axioms exists_common_kernel_derivative
#print axioms exists_common_transport_bound
#print axioms exists_common_reduced_bound
#print axioms exists_common_potential_bound
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralCommonWidthResponse
