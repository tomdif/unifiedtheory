/-
  Canonical mean splitting and explicit determinant-phase descent.
  The actual curvature-integral transition formula is proved analytically
  in REFERENCE_PHASE_DESCENT.md and checked against independent Kato frames.
  These finite results do not certify locality of the new phase correction.
-/
import UnifiedTheory.Audit.KFCausalToronLocality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalReferencePhaseDescent
noncomputable section
open scoped BigOperators

section MeanSplit
variable {E : Type*} [Fintype E] [Nonempty E]

def mean (a : E → ℝ) : ℝ := (∑ e, a e) / Fintype.card E

theorem mean_const (r : ℝ) : mean (fun _ : E => r) = r := by
  have hc : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, hc]

omit [Nonempty E] in
theorem mean_add (a b : E → ℝ) : mean (a + b) = mean a + mean b := by
  simp [mean, Finset.sum_add_distrib, add_div]

omit [Nonempty E] in
theorem mean_sub (a b : E → ℝ) : mean (a - b) = mean a - mean b := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

def canonicalReference (b : ℝ) (a : E → ℝ) : ℝ := b + mean a
def canonicalFluctuation (a : E → ℝ) : E → ℝ := fun e => a e - mean a

omit [Nonempty E] in
theorem canonical_preserves_potential (b : ℝ) (a : E → ℝ) (e : E) :
    canonicalReference b a + canonicalFluctuation a e = b + a e := by
  unfold canonicalReference canonicalFluctuation
  ring

theorem canonical_mean_zero (a : E → ℝ) : mean (canonicalFluctuation a) = 0 := by
  change mean (a - fun _ => mean a) = 0
  rw [mean_sub, mean_const, sub_self]

/-- This is the actual reference/fluctuation redundancy, not a supplied cocycle. -/
theorem canonical_reference_shift (b r : ℝ) (a : E → ℝ) :
    canonicalReference (b + r) (a - fun _ => r) = canonicalReference b a := by
  simp only [canonicalReference, mean_sub, mean_const]
  ring

theorem canonical_fluctuation_shift (r : ℝ) (a : E → ℝ) :
    canonicalFluctuation (a - fun _ => r) = canonicalFluctuation a := by
  funext e
  simp only [canonicalFluctuation, Pi.sub_apply, mean_sub, mean_const]
  ring

theorem canonical_reference_of_same_potential (b c : ℝ) (a d : E → ℝ)
    (h : ∀ e, b + a e = c + d e) :
    canonicalReference b a = canonicalReference c d := by
  have hh : (fun _ : E => b) + a = (fun _ : E => c) + d := funext h
  have hm := congrArg mean hh
  simpa only [mean_add, mean_const, canonicalReference] using hm

theorem canonical_fluctuation_of_same_potential (b c : ℝ) (a d : E → ℝ)
    (h : ∀ e, b + a e = c + d e) :
    canonicalFluctuation a = canonicalFluctuation d := by
  have hc := canonical_reference_of_same_potential b c a d h
  funext e
  have h₁ := canonical_preserves_potential b a e
  have h₂ := canonical_preserves_potential c d e
  rw [hc, h e] at h₁
  linarith

theorem mean_bound (a : E → ℝ) (ε : ℝ) (h : ∀ e, |a e| ≤ ε) : |mean a| ≤ ε := by
  have hc : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  rw [mean, abs_div, abs_of_pos hc]
  apply (div_le_iff₀ hc).mpr
  calc
    _ ≤ ∑ e, |a e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : E, ε := Finset.sum_le_sum (fun e _ => h e)
    _ = _ := by simp [mul_comm]

theorem centered_bound (a : E → ℝ) (ε : ℝ) (h : ∀ e, |a e| ≤ ε) (e : E) :
    |canonicalFluctuation a e| ≤ 2 * ε := by
  have hm := mean_bound a ε h
  calc
    _ ≤ |a e| + |mean a| := by
      simpa [canonicalFluctuation] using (abs_sub_le (a e) 0 (mean a))
    _ ≤ ε + ε := add_le_add (h e) hm
    _ = _ := by ring

omit [Nonempty E] in
/-- Real periodic gauge gradients do not change the canonical flat reference. -/
theorem mean_periodic_gradient (ω : E → ℝ) (p : Equiv.Perm E) :
    mean (fun e => ω e - ω (p e)) = 0 := by
  simp only [mean, Finset.sum_sub_distrib, Equiv.sum_comp p ω, sub_self, zero_div]

end MeanSplit

section PhaseCorrection

def transitionPhase (flux sourceCorrection targetCorrection : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (flux + targetCorrection - sourceCorrection))

/-- The supplied curvature-integral identity fixes the sign and both endpoint terms. -/
theorem corrected_transition_formula (raw flux c₀ c₁ : ℝ) (hraw : raw = -flux) :
    Complex.exp (Complex.I * (raw + c₀ - c₁)) = transitionPhase flux c₀ c₁ := by
  unfold transitionPhase
  rw [hraw]
  congr 1
  push_cast
  ring

theorem phase_transition_composition (f₀₁ f₁₂ f₀₂ c₀ c₁ c₂ : ℝ)
    (hf : f₀₁ + f₁₂ = f₀₂) :
    transitionPhase f₀₁ c₀ c₁ * transitionPhase f₁₂ c₁ c₂ =
      transitionPhase f₀₂ c₀ c₂ := by
  unfold transitionPhase
  rw [← Complex.exp_add, ← hf]
  congr 1
  push_cast
  ring

/-- Rephasing by the integral from the canonical representative sets every
transition determinant to one; no rank-dependent root is chosen. -/
theorem canonical_phase_normalization (f₀i fij f₀j c₀ ci cj : ℝ)
    (hf : f₀i + fij = f₀j) :
    transitionPhase fij ci cj *
      Complex.exp (Complex.I * ((f₀j + cj - c₀) - (f₀i + ci - c₀))) = 1 := by
  unfold transitionPhase
  rw [← Complex.exp_add, ← hf]
  calc
    _ = Complex.exp 0 := by congr 1; push_cast; ring
    _ = 1 := Complex.exp_zero

/-- The triangle's gauge variation cancels the endpoint scalar variations. -/
theorem canonical_adjustment_gauge_invariant
    (f f' c₀ c₁ c₀' c₁' w₀ w₁ : ℝ)
    (hf : f' - f = w₁ - w₀) (h₀ : c₀' - c₀ = -w₀)
    (h₁ : c₁' - c₁ = -w₁) : f' + c₁' - c₀' = f + c₁ - c₀ := by linarith

end PhaseCorrection

section ConnectionDescent
open MeasureTheory

/-- Component form of the homotopy formula: when pulled-back curvature
vanishes in fibre directions, the derivative below is the phase gradient.
The geometric derivative identity is an explicit hypothesis here. -/
theorem fibre_connection_descent (component gradient : ℝ → ℝ)
    (hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt component (gradient s) s)
    (hint : IntervalIntegrable gradient volume 0 1) :
    component 1 - (∫ s in (0 : ℝ)..1, gradient s) = component 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

end ConnectionDescent

#print axioms mean_const
#print axioms mean_add
#print axioms mean_sub
#print axioms canonical_preserves_potential
#print axioms canonical_mean_zero
#print axioms canonical_reference_shift
#print axioms canonical_fluctuation_shift
#print axioms canonical_reference_of_same_potential
#print axioms canonical_fluctuation_of_same_potential
#print axioms mean_bound
#print axioms centered_bound
#print axioms mean_periodic_gradient
#print axioms corrected_transition_formula
#print axioms phase_transition_composition
#print axioms canonical_phase_normalization
#print axioms canonical_adjustment_gauge_invariant
#print axioms fibre_connection_descent

end
end UnifiedTheory.Audit.KFCausalReferencePhaseDescent
