/-
  Audit/KFCausalBornQuadraturePhase.lean

  GATE THEOREMS FOR THE BI-NORMALIZED THEORY:
  THE PHASE IS QUANTIZED AT THE BORN-QUADRATURE POINT, AND
  FACT REGRESSION IS BOUNDED BY INTERFERENCE

  Context.  KFCausalBornRecordMartingale.lean proved that records are
  martingale-stable under Born completeness and that the coherent rule
  alone permits fact regression.  Two questions remained (the "gates"):
  does the ACTION-PHASED quantum structure survive bi-normalization,
  and what observable distinguishes the partially coherent theory
  (lambda < 1) from a fully dephased one?

  1. `root_phase_quantization` — an action-phased bi-normalized birth
     stage with two unit-multiplicity children at action gaps +1 and -1
     (the physical growth root: 2-antichain at gap +1, 2-chain at
     gap -1) forces
         cos phi = sqrt 2 / 2   and   rho = sqrt 2 / 2.
     With phi in [0, pi] this pins phi = pi / 4 exactly
     (`root_phase_is_pi_div_four`).  In the coherent-only wave family
     the root merely set the amplitude scale 1/(2 cos phi) and phi was
     a free parameter scanned over windows; adding the Born half of the
     double-conservation law QUANTIZES the phase at the Born-quadrature
     point.  The two solutions cos phi = 1/sqrt 2 with phi = +-pi/4 are
     conjugates: the residual freedom is exactly the orientation Z2.

  2. `fact_regression_interference_bound` — for the interpolated
     measure M_lambda = (1-lambda) Q + lambda P of the transfer audit,
     with P the Born-diagonal (martingale) channel and Q any coherent
     channel, the regression of a monotone record across a refinement
     stage is bounded by the record's own interference:
         M_lambda(F) - M_lambda(E) >= -(1-lambda) (|Q_E - P_E| + |Q_F - P_F|).
     At lambda = 1 the right side is zero (facts exactly stable); at
     lambda < 1 the theory predicts record-probability regressions of
     at most (1-lambda) times the measured interference on the record —
     the lambda-observable.  A system instantiating the record algebra
     with measured record regression EXCEEDING this bound falsifies the
     theory at every lambda; standard decoherence-based quantum
     mechanics predicts zero regression.
     `eventMass_fact_regression_bound` instantiates P via the actual
     Born-diagonal refinement using `record_accretion`.

  Numerical companion: binormalized_phase_diagram.py (per-parent
  feasibility of the action-phased bi-normalized system across phi;
  closure and records test at phi = pi/4), lambda_observable.py
  (bound tightness and per-step regression trend).

  Zero sorry.  Zero custom axioms.
-/
import UnifiedTheory.Audit.KFCausalBornRecordMartingale
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornQuadraturePhase

open UnifiedTheory.Audit.KFCausalBornRecordMartingale
open Finset

/-! ## 1. Phase quantization at the root -/

/-- An action-phased bi-normalized stage with two unit-multiplicity
children at action gaps `+1` and `-1` (the physical growth root, with
amplitudes `rho e^{i g phi}` and equal weights forced by the imaginary
part) satisfies `2 rho cos phi = 1` (coherent) and `2 rho^2 = 1`
(Born); jointly these force `cos phi = sqrt 2 / 2` and
`rho = sqrt 2 / 2`. -/
theorem root_phase_quantization (ρ φ : ℝ) (hρ : 0 < ρ)
    (hcoh : (ρ : ℂ) * Complex.exp (φ * Complex.I) +
      (ρ : ℂ) * Complex.exp (-(φ : ℂ) * Complex.I) = 1)
    (hborn : ρ ^ 2 + ρ ^ 2 = 1) :
    Real.cos φ = Real.sqrt 2 / 2 ∧ ρ = Real.sqrt 2 / 2 := by
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- extract the real coherent equation 2 rho cos phi = 1
  have hexp : Complex.exp ((φ : ℂ) * Complex.I) +
      Complex.exp (-(φ : ℂ) * Complex.I) = 2 * (Real.cos φ : ℂ) := by
    have hneg : -(φ : ℂ) * Complex.I = ((-φ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [Complex.exp_mul_I, hneg, Complex.exp_mul_I, Complex.ofReal_cos]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  have hre : 2 * ρ * Real.cos φ = 1 := by
    have h1 : (ρ : ℂ) * (Complex.exp ((φ : ℂ) * Complex.I) +
        Complex.exp (-(φ : ℂ) * Complex.I)) = 1 := by
      rw [mul_add]; exact hcoh
    rw [hexp] at h1
    have h2 : ((2 * ρ * Real.cos φ : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast at h1 ⊢
      linear_combination h1
    have := Complex.ofReal_inj.mp h2
    linarith [this]
  -- Born: rho = sqrt 2 / 2
  have hρsq : ρ ^ 2 = 1 / 2 := by linarith
  have hρval : ρ = Real.sqrt 2 / 2 := by
    have hfac : (ρ - Real.sqrt 2 / 2) * (ρ + Real.sqrt 2 / 2) = 0 := by
      have : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, hsqrt2]; norm_num
      nlinarith [hρsq, this]
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · exfalso; nlinarith [hsqrt2_pos]
  refine ⟨?_, hρval⟩
  -- cos phi = 1/(2 rho) = 1/sqrt 2 = sqrt 2 / 2
  have h2ρ : 2 * ρ = Real.sqrt 2 := by rw [hρval]; ring
  have : Real.sqrt 2 * Real.cos φ = 1 := by rw [← h2ρ]; linarith [hre]
  have hcos : Real.cos φ = 1 / Real.sqrt 2 := by
    field_simp at this ⊢
    linarith [this]
  rw [hcos]
  rw [div_eq_div_iff (by positivity) (by norm_num : (2:ℝ) ≠ 0)]
  nlinarith [hsqrt2]

/-- With `phi` in `[0, pi]`, the quantized phase is exactly `pi/4`:
the Born-quadrature point.  The conjugate branch `-pi/4` is the
orientation mirror. -/
theorem root_phase_is_pi_div_four (ρ φ : ℝ) (hρ : 0 < ρ)
    (hφ : φ ∈ Set.Icc 0 Real.pi)
    (hcoh : (ρ : ℂ) * Complex.exp (φ * Complex.I) +
      (ρ : ℂ) * Complex.exp (-(φ : ℂ) * Complex.I) = 1)
    (hborn : ρ ^ 2 + ρ ^ 2 = 1) :
    φ = Real.pi / 4 := by
  have hcos := (root_phase_quantization ρ φ hρ hcoh hborn).1
  have hπ4 : Real.pi / 4 ∈ Set.Icc 0 Real.pi := by
    constructor
    · positivity
    · linarith [Real.pi_pos]
  have : Real.cos φ = Real.cos (Real.pi / 4) := by
    rw [hcos, Real.cos_pi_div_four]
  exact Real.injOn_cos hφ hπ4 this

/-! ## 2. The lambda-observable: fact regression bounded by interference -/

/-- Arithmetic core.  If the diagonal channel is monotone
(`pE ≤ pF`, supplied by `record_accretion`), then the interpolated
measure `M_lambda = (1-lambda) Q + lambda P` of a monotone record can
regress by at most `(1-lambda)` times the total interference
`|Q - P|` on the record.  At `lambda = 1` the bound is zero. -/
theorem fact_regression_interference_bound
    (pE pF qE qF lam : ℝ) (hP : pE ≤ pF) (hlam : lam ≤ 1) :
    ((1 - lam) * qF + lam * pF) - ((1 - lam) * qE + lam * pE) ≥
      -(1 - lam) * (|qE - pE| + |qF - pF|) := by
  have hl : 0 ≤ 1 - lam := by linarith
  have h1 : -|qF - pF| ≤ qF - pF := neg_abs_le _
  have h2 : qE - pE ≤ |qE - pE| := le_abs_self _
  have hdiff : (qF - pF) - (qE - pE) ≥ -(|qE - pE| + |qF - pF|) := by
    linarith
  have hmul : (1 - lam) * ((qF - pF) - (qE - pE)) ≥
      (1 - lam) * (-(|qE - pE| + |qF - pF|)) :=
    mul_le_mul_of_nonneg_left hdiff hl
  have hkey : ((1 - lam) * qF + lam * pF) - ((1 - lam) * qE + lam * pE) =
      (pF - pE) + (1 - lam) * ((qF - pF) - (qE - pE)) := by ring
  rw [hkey]
  have : (1 - lam) * (-(|qE - pE| + |qF - pF|)) =
      -(1 - lam) * (|qE - pE| + |qF - pF|) := by ring
  linarith [hmul, hP, this.symm.le]

/-- The physical instantiation: `P` is the Born-diagonal `eventMass`
channel across one causal refinement stage, `Q` is any coherent
channel value on the same record; the interpolated measure of a
monotone record regresses by at most `(1-lambda)` times its
interference.  Standard decoherence-based quantum mechanics predicts
zero regression; measuring a larger one falsifies the law at every
`lambda`. -/
theorem eventMass_fact_regression_bound
    {Parent : Type} {Child : Type}
    [Fintype Parent] [Fintype Child] [DecidableEq Parent]
    (par : Child → Parent) (amp : Child → ℂ) (w : Parent → ℝ)
    (hB : BornComplete par amp) (hw : ∀ a, 0 ≤ w a)
    (E : Parent → Prop) (F : Child → Prop)
    (hmono : ∀ b, E (par b) → F b)
    (qE qF lam : ℝ) (hlam : lam ≤ 1) :
    ((1 - lam) * qF + lam * eventMass (refine par amp w) F) -
      ((1 - lam) * qE + lam * eventMass w E) ≥
      -(1 - lam) * (|qE - eventMass w E| +
        |qF - eventMass (refine par amp w) F|) :=
  fact_regression_interference_bound _ _ _ _ _
    (record_accretion par amp w hB hw E F hmono) hlam

#print axioms root_phase_quantization
#print axioms root_phase_is_pi_div_four
#print axioms fact_regression_interference_bound
#print axioms eventMass_fact_regression_bound

end UnifiedTheory.Audit.KFCausalBornQuadraturePhase
