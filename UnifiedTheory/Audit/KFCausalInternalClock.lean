/-
  Internal free-particle clock in the canonical massless parent.
  A retained homogeneous free coordinate and a fixed total energy give
  an exact square-root relational generator on the positive-momentum
  branch. Its finite-energy error is bounded on an entire energy band.

  The stationary clock states are generalized momentum states, not
  normalized finite-spin clock preparations. The finite-R construction,
  clock readout errors and gravitational clock identification remain separate.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalInternalClock
noncomputable section
open scoped BigOperators

/-- Classical clock coordinate MT/P, conjugate to clock energy P²/(2M). -/
theorem internal_clock_canonical (M P : ℝ) (hM : M ≠ 0) (hP : P ≠ 0) :
    (M/P)*(P/M) = 1 := by field_simp

theorem internal_clock_runs (M P T : ℝ) (hM : M ≠ 0) (hP : P ≠ 0) :
    (M/P)*(P/M)+(-M*T/P^2)*0 = 1 := by
  simpa using internal_clock_canonical M P hM hP

/-- Exact rate ratio from the six-flavor coherent-block expectation
calculation in internal_clock_metric_audit.py. n=|alpha|² is the canonical
coherent parameter, not the finite-spin mean occupation. The many-spin
expectation calculation is independently symbolic, not formalized here. -/
def spinClockRatio (R n : ℝ) : ℝ := (R-1)/R*((R-n)/(R+n))-5/(4*R)

theorem spin_clock_rate_error (R n : ℝ) (hR : 1 ≤ R) (hn : 0 ≤ n) :
    0 ≤ 1-spinClockRatio R n ∧ 1-spinClockRatio R n ≤ (2*n+9/4)/R := by
  have hRp : 0 < R := by linarith
  have hden : 0 < R+n := by positivity
  have hid : 1-spinClockRatio R n = (2*n*((R-1)/(R+n))+9/4)/R := by
    unfold spinClockRatio
    field_simp
    ring
  have hf0 : 0 ≤ (R-1)/(R+n) := div_nonneg (by linarith) hden.le
  have hf1 : (R-1)/(R+n) ≤ 1 := (div_le_one₀ hden).mpr (by linarith)
  rw [hid]
  constructor
  · positivity
  · apply (div_le_div_iff_of_pos_right hRp).mpr
    nlinarith

theorem spin_clock_rate_positive (R n : ℝ) (hR : 1 ≤ R) (hn : 0 ≤ n)
    (hdilute : 2*n+9/4 < R) : 0 < spinClockRatio R n := by
  have hb := (spin_clock_rate_error R n hR hn).2
  have hfrac : (2*n+9/4)/R < 1 := (div_lt_one (by linarith)).mpr hdilute
  linarith

def clockMomentum (M E h : ℝ) : ℝ := Real.sqrt (2*M*(E-h))
def clockRate (E h : ℝ) : ℝ := 2*(E-Real.sqrt (E*(E-h)))

/-- Exact stationary total-energy equation, before any expansion. -/
theorem stationary_energy_shell (M E h : ℝ) (hM : 0 < M) (hh : h ≤ E) :
    (clockMomentum M E h)^2/(2*M)+h = E := by
  have hsub : 0 ≤ E-h := sub_nonneg.mpr hh
  rw [clockMomentum, Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-- T=sqrt(2ME)t/M is calibrated by the zero-system-energy clock speed.
Removing the common phase leaves exp(-i t clockRate E h). -/
theorem relational_frequency (M E h : ℝ) (hM : 0 < M) (hh : h ≤ E) :
    clockMomentum M E h * Real.sqrt (2*M*E)/M = 2*E-clockRate E h := by
  have hsub : 0 ≤ E-h := sub_nonneg.mpr hh
  have hm : 0 ≤ 2*M := by positivity
  rw [clockMomentum, ← Real.sqrt_mul (by positivity)]
  have he : 2*M*(E-h)*(2*M*E) = (2*M)^2*(E*(E-h)) := by ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm]
  unfold clockRate
  field_simp
  ring

theorem clock_rate_bounds (E h : ℝ) (hE : 0 < E) (hh : 0 ≤ h) (hhE : h ≤ E) :
    h ≤ clockRate E h ∧ clockRate E h ≤ 2*h := by
  have hsub : 0 ≤ E-h := sub_nonneg.mpr hhE
  have hs := Real.sq_sqrt (show 0 ≤ E*(E-h) by positivity)
  have hn := Real.sqrt_nonneg (E*(E-h))
  have hlo : E-h ≤ Real.sqrt (E*(E-h)) := by nlinarith
  have hhi : Real.sqrt (E*(E-h)) ≤ E := by nlinarith
  constructor
  · dsimp [clockRate]
    nlinarith [sq_nonneg (E-Real.sqrt (E*(E-h)))]
  · dsimp [clockRate]
    linarith

theorem clock_rate_defect_identity (E h : ℝ) (hE : 0 < E) (hhE : h ≤ E) :
    clockRate E h-h = (clockRate E h)^2/(4*E) := by
  have hsub : 0 ≤ E-h := sub_nonneg.mpr hhE
  have hs := Real.sq_sqrt (show 0 ≤ E*(E-h) by positivity)
  dsimp [clockRate]
  field_simp
  nlinarith

/-- Dimension-independent error on the entire supplied system-energy band. -/
theorem clock_rate_defect_bound (E e h : ℝ) (hE : 0 < E)
    (hh : 0 ≤ h) (hhe : h ≤ e) (heE : e ≤ E) :
    |clockRate E h-h| ≤ e^2/E := by
  have hb := clock_rate_bounds E h hE hh (hhe.trans heE)
  have hK : 0 ≤ clockRate E h := hh.trans hb.1
  have he : 0 ≤ e := hh.trans hhe
  rw [abs_of_nonneg (sub_nonneg.mpr hb.1), clock_rate_defect_identity E h hE (hhe.trans heE)]
  apply (div_le_iff₀ (show 0 < 4*E by positivity)).mpr
  have hsq : (clockRate E h)^2 ≤ (2*e)^2 := by nlinarith
  field_simp
  nlinarith

def phase (a : ℝ) : ℂ := Complex.exp (Complex.I * (a : ℂ))

theorem phase_norm (a : ℝ) : ‖phase a‖ = 1 := Complex.norm_exp_I_mul_ofReal a

theorem phase_lipschitz (a b : ℝ) : ‖phase a-phase b‖ ≤ |a-b| := by
  have he : phase a-phase b = phase b*(phase (a-b)-1) := by
    rw [mul_sub, mul_one]
    unfold phase
    rw [← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, phase_norm, one_mul]
  simpa [phase, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a-b))

theorem relational_mode_error (E e h t : ℝ) (hE : 0 < E)
    (hh : 0 ≤ h) (hhe : h ≤ e) (heE : e ≤ E) :
    ‖phase (-t*clockRate E h)-phase (-t*h)‖ ≤ |t| * e^2/E := by
  calc
    _ ≤ |-t*clockRate E h-(-t*h)| := phase_lipschitz _ _
    _ = |t| * |clockRate E h-h| := by
      rw [show -t*clockRate E h-(-t*h) = -t*(clockRate E h-h) by ring,
        abs_mul, abs_neg]
    _ ≤ |t| * (e^2/E) := mul_le_mul_of_nonneg_left
      (clock_rate_defect_bound E e h hE hh hhe heE) (abs_nonneg t)
    _ = _ := by ring

/-- Squared Hilbert-space error in an energy eigenbasis, for every state
in the band. No factor of the number of modes or states occurs. -/
theorem relational_state_error {ι : Type*} [Fintype ι]
    (energy : ι → ℝ) (ψ : ι → ℂ) (E e t : ℝ) (hE : 0 < E)
    (hpos : ∀ i, 0 ≤ energy i) (hband : ∀ i, energy i ≤ e) (heE : e ≤ E) :
    (∑ i, ‖phase (-t*clockRate E (energy i))*ψ i-phase (-t*energy i)*ψ i‖^2) ≤
      (|t| * e^2/E)^2 * ∑ i, ‖ψ i‖^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← sub_mul, norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hb := relational_mode_error E e (energy i) t hE (hpos i) (hband i) heE
  have hn : 0 ≤ |t| * e^2/E := by positivity
  nlinarith [norm_nonneg (phase (-t*clockRate E (energy i))-phase (-t*energy i))]

theorem relational_unitary {ι : Type*} [Fintype ι]
    (energy : ι → ℝ) (ψ : ι → ℂ) (E t : ℝ) :
    (∑ i, ‖phase (-t*clockRate E (energy i))*ψ i‖^2) = ∑ i, ‖ψ i‖^2 := by
  simp [phase_norm]

#print axioms internal_clock_canonical
#print axioms internal_clock_runs
#print axioms spin_clock_rate_error
#print axioms spin_clock_rate_positive
#print axioms stationary_energy_shell
#print axioms relational_frequency
#print axioms clock_rate_bounds
#print axioms clock_rate_defect_identity
#print axioms clock_rate_defect_bound
#print axioms relational_state_error
#print axioms relational_unitary

end
end UnifiedTheory.Audit.KFCausalInternalClock
