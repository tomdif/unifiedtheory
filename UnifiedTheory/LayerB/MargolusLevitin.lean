/-
  LayerB/MargolusLevitin.lean
  ────────────────────────────

  The Margolus–Levitin quantum speed limit:  the time T required for
  a quantum state to evolve to an orthogonal state is bounded below
  by π/(2E), where E = ⟨H⟩ measured from the ground state.

  We work at the *spectral-decomposition level*, avoiding the full
  matrix-exponential machinery.  An `EnergySpectrum n` packages a
  probability distribution `pᵢ ≥ 0` over n non-negative energies
  `Eᵢ ≥ 0` (energies shifted so the ground state is at E = 0).  The
  survival amplitude is then

      S(T)  :=  ∑ᵢ pᵢ · exp(−i · Eᵢ · T) .

  Margolus–Levitin says:  if S(T) = 0 (the state has become fully
  orthogonal), then T · ⟨H⟩ ≥ π/2.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `EnergySpectrum n` structure.
    2. `survivalAmplitude S T` and `energyExpectation S`.
    3. `survivalAmplitude_re_eq`, `survivalAmplitude_im_eq` — extract
       Re and Im as real sums of cosines/sines.
    4. `margolus_levitin_conditional` — for any spectrum S, time T > 0,
       full orthogonality S(T) = 0, and the cos-floor trig inequality
       (passed as a hypothesis), we have T · ⟨H⟩ ≥ π/2.

  WHAT IS LEFT AS A HYPOTHESIS:
    The cos-floor trig inequality
        cos(x)  ≥  1 − (2/π) · (x + sin(x))     for x ≥ 0
    is the analytic crux of Margolus–Levitin.  We do not prove it
    here (the standard proof goes via studying the function
    f(x) := cos(x) + (2/π)(x + sin(x)) − 1 ≥ 0 on [0, ∞)).  Instead
    we pass it in as a hypothesis so the algebraic spectral-sum step
    is fully formal.  See `MathlibTrigInequality.lean` (future file)
    for the proof of the trig inequality itself.

  SCOPE:
    – Finite-dim, abstract spectrum (no matrix exponentials).
    – Units with ℏ = 1.
    – "Energy" is measured from the ground state (E_min = 0).
-/

import UnifiedTheory.LayerB.RobertsonSchrodinger
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.RobertsonSchrodinger

open Complex
open scoped ComplexOrder

/-! ## 1. Energy spectrum -/

/-- A finite energy spectrum: a probability distribution `pᵢ` over
    `n` non-negative energies `Eᵢ`.  Energies are shifted so the
    ground state sits at E = 0 (i.e., min Eᵢ = 0, but we only need
    each Eᵢ ≥ 0 for the ML bound). -/
structure EnergySpectrum (n : ℕ) where
  energies : Fin n → ℝ
  probs : Fin n → ℝ
  probs_nonneg : ∀ i, 0 ≤ probs i
  probs_sum : ∑ i, probs i = 1
  energies_nonneg : ∀ i, 0 ≤ energies i

namespace EnergySpectrum

variable {n : ℕ}

/-- The survival amplitude `S(T) = ∑ pᵢ · exp(−i Eᵢ T)`. -/
noncomputable def survivalAmplitude (S : EnergySpectrum n) (T : ℝ) : ℂ :=
  ∑ i, (S.probs i : ℂ) * Complex.exp (-Complex.I * (S.energies i : ℂ) * (T : ℂ))

/-- The energy expectation `⟨H⟩ = ∑ pᵢ · Eᵢ`. -/
noncomputable def energyExpectation (S : EnergySpectrum n) : ℝ :=
  ∑ i, S.probs i * S.energies i

theorem energyExpectation_nonneg (S : EnergySpectrum n) :
    0 ≤ S.energyExpectation := by
  unfold energyExpectation
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (S.probs_nonneg i) (S.energies_nonneg i)

/-! ## 2. Real and imaginary parts of the survival amplitude -/

/-- Real part of `-i·E·T` is zero. -/
private theorem aux_re_zero (E T : ℝ) :
    (-Complex.I * (E : ℂ) * (T : ℂ)).re = 0 := by
  simp [Complex.mul_re, Complex.I_re, Complex.I_im]

/-- Imaginary part of `-i·E·T` is `-(E·T)`. -/
private theorem aux_im_eq (E T : ℝ) :
    (-Complex.I * (E : ℂ) * (T : ℂ)).im = -(E * T) := by
  simp [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]

/-- `Re(S(T)) = ∑ pᵢ · cos(Eᵢ T)`. -/
theorem survivalAmplitude_re (S : EnergySpectrum n) (T : ℝ) :
    (S.survivalAmplitude T).re = ∑ i, S.probs i * Real.cos (S.energies i * T) := by
  unfold survivalAmplitude
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  -- (exp z).re = exp(z.re) · cos(z.im) ; here z.re = 0, z.im = -(E·T)
  rw [Complex.exp_re, aux_re_zero, aux_im_eq, Real.exp_zero, one_mul,
      Real.cos_neg]

/-- `Im(S(T)) = -∑ pᵢ · sin(Eᵢ T)`. -/
theorem survivalAmplitude_im (S : EnergySpectrum n) (T : ℝ) :
    (S.survivalAmplitude T).im = -(∑ i, S.probs i * Real.sin (S.energies i * T)) := by
  unfold survivalAmplitude
  rw [Complex.im_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  -- (exp z).im = exp(z.re) · sin(z.im) ; here z.re = 0, z.im = -(E·T)
  rw [Complex.exp_im, aux_re_zero, aux_im_eq, Real.exp_zero, one_mul,
      Real.sin_neg, mul_neg]

/-! ## 3. The Margolus–Levitin bound -/

/-- **Margolus–Levitin quantum speed limit (conditional).**

    Given an energy spectrum S with non-negative energies and a
    fully-orthogonal evolution at time T > 0 (i.e., S(T) = 0), and
    assuming the cos-floor trig inequality

        cos x  ≥  1 − (2/π) · (x + sin x)     for x ≥ 0,

    we have

        T · ⟨H⟩  ≥  π / 2 .

    The trig inequality is the analytic content; the rest is pure
    spectral algebra. -/
theorem margolus_levitin_conditional
    (S : EnergySpectrum n) (T : ℝ) (hT : 0 ≤ T)
    (h_orthogonal_re : (S.survivalAmplitude T).re = 0)
    (h_orthogonal_im : (S.survivalAmplitude T).im = 0)
    (h_trig : ∀ x : ℝ, 0 ≤ x →
                Real.cos x ≥ 1 - (2 / Real.pi) * (x + Real.sin x)) :
    T * S.energyExpectation ≥ Real.pi / 2 := by
  -- Re(S(T)) = ∑ pᵢ cos(Eᵢ T)
  have h_re := S.survivalAmplitude_re T
  have h_im := S.survivalAmplitude_im T
  rw [h_orthogonal_re] at h_re
  rw [h_orthogonal_im] at h_im
  -- From h_re: ∑ pᵢ cos(Eᵢ T) = 0
  -- From h_im: ∑ pᵢ sin(Eᵢ T) = 0
  have h_sum_cos : ∑ i, S.probs i * Real.cos (S.energies i * T) = 0 := h_re.symm
  have h_sum_sin : ∑ i, S.probs i * Real.sin (S.energies i * T) = 0 := by
    have := h_im.symm
    linarith
  -- Per-term trig bound: pᵢ · cos(Eᵢ T) ≥ pᵢ · (1 - (2/π)(Eᵢ T + sin(Eᵢ T)))
  have h_per_term : ∀ i,
      S.probs i * Real.cos (S.energies i * T)
        ≥ S.probs i
          * (1 - (2 / Real.pi) * (S.energies i * T + Real.sin (S.energies i * T))) := by
    intro i
    have h_arg_nn : 0 ≤ S.energies i * T :=
      mul_nonneg (S.energies_nonneg i) hT
    have h_trig_i := h_trig (S.energies i * T) h_arg_nn
    exact mul_le_mul_of_nonneg_left h_trig_i (S.probs_nonneg i)
  -- Sum the per-term bound
  have h_sum_bound :
      (∑ i, S.probs i * Real.cos (S.energies i * T))
        ≥ ∑ i, S.probs i
              * (1 - (2 / Real.pi) * (S.energies i * T + Real.sin (S.energies i * T))) :=
    Finset.sum_le_sum (fun i _ => h_per_term i)
  -- RHS expansion via algebraic manipulation (per-term ring + Finset distribution)
  have h_rhs_eq :
      (∑ i, S.probs i
            * (1 - (2 / Real.pi) * (S.energies i * T + Real.sin (S.energies i * T))))
        = 1 - (2 / Real.pi) * T * S.energyExpectation
          - (2 / Real.pi) * ∑ i, S.probs i * Real.sin (S.energies i * T) := by
    have h_per_i : ∀ i,
        S.probs i * (1 - (2 / Real.pi) * (S.energies i * T + Real.sin (S.energies i * T)))
          = S.probs i
            - ((2 / Real.pi) * T) * (S.probs i * S.energies i)
            - (2 / Real.pi) * (S.probs i * Real.sin (S.energies i * T)) := by
      intro i; ring
    simp_rw [h_per_i]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [S.probs_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    -- 1 - (2/π · T) · ⟨H⟩ - (2/π) · Σ sin
    unfold energyExpectation
    ring
  rw [h_rhs_eq, h_sum_sin] at h_sum_bound
  -- h_sum_bound : ∑ pᵢ cos(Eᵢ T) ≥ 1 - (2/π) · T · ⟨H⟩ - (2/π) · 0
  rw [h_sum_cos] at h_sum_bound
  -- 0 ≥ 1 - (2/π) · T · ⟨H⟩
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_step : (2 / Real.pi) * (T * S.energyExpectation) ≥ 1 := by linarith
  -- Multiply both sides by π/2 > 0 to clear the 2/π factor
  have h_pi_half_pos : (0 : ℝ) < Real.pi / 2 := by linarith
  have h_cancel : (Real.pi / 2) * ((2 / Real.pi) * (T * S.energyExpectation))
                = T * S.energyExpectation := by
    field_simp
  have h_mul : (Real.pi / 2) * ((2 / Real.pi) * (T * S.energyExpectation))
              ≥ (Real.pi / 2) * 1 :=
    mul_le_mul_of_nonneg_left h_step (le_of_lt h_pi_half_pos)
  linarith [h_cancel ▸ h_mul]

end EnergySpectrum

end UnifiedTheory.LayerB.RobertsonSchrodinger
