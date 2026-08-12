/-
  Audit/KFCausalCoherentRecordAccretion.lean

  THE FACT-STABILITY MECHANISM: PHASES TELESCOPE, AND HEREDITARY
  EVENTS NEVER LOSE COHERENT MASS

  Context.  PI4_FIRST_PREDICTION registered the conjecture that the
  max-entropy pi/4 law has monotone coherent stem measures
  (X_minus(Q) = 0, measured then at 4 decimals).  The probe
  (factstab_probe.py, 2026-08-12) hardened the measurement to exact
  zero at 1e-15 through depth 8, REFUTED the two candidate mechanisms
  (exponential gap-family: 1/1909 parents; class factorization:
  O(1) residuals), and revealed the true structure, formalized here:

  1. `step_phase_form` — PHASE TELESCOPING.  For any action-phased law
     (edge amplitude rho * e^{i phi (S_child - S_parent)}, rho >= 0),
     a state of the form Psi(p) = e^{i phi (S_p - S_0)} R(p) with
     R >= 0 evolves to a state of the same form: the phase of every
     class amplitude is the pure class function e^{i phi Delta-S},
     because every path to a class carries the same telescoped action
     phase.  (Measured: max |arg Psi - phi Delta-S| = 3.6e-15.)
     Consequently the class-identified coherent measure |Psi|^2 = R^2
     is PHASE-FREE: interference never enters any class-diagonal
     observable of an action-phased law.
  2. `coherent_record_accretion` — with phases idle, the coherent
     evolution is a nonnegative kernel R'(c) = sum_e R(src e) a(e)
     with the labeled Born normalization sum_{e in fiber} a(e)^2 = 1.
     Labeled square-mass is exactly conserved per parent (Born), and
     aggregation of nonnegative amplitudes into classes is
     square-SUPERADDITIVE, so every hereditary event (stems: children
     of a containing parent still contain) has non-decreasing
     unnormalized coherent mass.  Facts never lose coherent weight.
  3. `coherent_total_mass_grows` — the special case EP = EC = True:
     total class-identified coherent mass is non-decreasing (the
     anti-decoherence growth of the July arc, now an inequality with
     an identified mechanism: class aggregation).
  4. `phase_free_measure` — normSq(e^{i phi t} z) = normSq z: the
     bridge from the complex state to the real accretion.

  What is NOT proven here (honest boundary): monotonicity of the
  NORMALIZED stem ratio.  It is equivalent to the A-block growth
  dominating the B-block retention; measured margin at depth 8:
  min over stems/steps = 1.0648 (factstab_probe.py part D) — a
  finite-margin numerical fact, not an identity, and the remaining
  open half of the conjecture.  The unnormalized accretion proven
  here is the exact half.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCoherentRecordAccretion

open scoped Classical
open Finset

variable {P C E : Type}
variable [Fintype P] [Fintype C] [Fintype E]
variable [DecidableEq P] [DecidableEq C]

/-! ## 0. Square superadditivity of nonnegative aggregation -/

/-- For nonnegative reals, the square of a sum dominates the sum of
squares — aggregating labeled amplitudes into a class can only gain
square-mass (all cross terms are constructive). -/
theorem sq_sum_ge_sum_sq {ι : Type} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  have hstep : ∀ i ∈ s, f i ^ 2 ≤ f i * ∑ j ∈ s, f j := by
    intro i hi
    have hle : f i ≤ ∑ j ∈ s, f j := Finset.single_le_sum hf hi
    have := mul_le_mul_of_nonneg_left hle (hf i hi)
    simpa [pow_two] using this
  calc ∑ i ∈ s, f i ^ 2 ≤ ∑ i ∈ s, f i * ∑ j ∈ s, f j :=
        Finset.sum_le_sum hstep
    _ = (∑ i ∈ s, f i) ^ 2 := by rw [← Finset.sum_mul, pow_two]

/-! ## 1. Phase telescoping -/

/-- One refinement step of an action-phased law preserves the
telescoped-phase form: if every parent amplitude is
`e^{i phi (S_p - S_0)} R p` with `R >= 0`, the child amplitude is
`e^{i phi (S_c - S_0)} R' c` with
`R' c = sum over incoming edges of R (src e) * rho e >= 0`.  The
phase is a pure class function; no path dependence survives. -/
theorem step_phase_form (φ S0 : ℝ) (SP : P → ℝ) (SC : C → ℝ)
    (src : E → P) (tgt : E → C) (ρ : E → ℝ) (R : P → ℝ) (c : C) :
    ∑ e ∈ univ.filter (fun e => tgt e = c),
      (Complex.exp ((SP (src e) - S0) * φ * Complex.I) * R (src e)) *
        (ρ e * Complex.exp
          ((SC (tgt e) - SP (src e)) * φ * Complex.I)) =
    Complex.exp ((SC c - S0) * φ * Complex.I) *
      ∑ e ∈ univ.filter (fun e => tgt e = c),
        (R (src e) * ρ e : ℝ) := by
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have htgt : tgt e = c := (Finset.mem_filter.1 he).2
  rw [htgt]
  rw [show ((SC c : ℂ) - S0) * φ * Complex.I =
      ((SP (src e) : ℂ) - S0) * φ * Complex.I +
      ((SC c : ℂ) - SP (src e)) * φ * Complex.I by ring]
  rw [Complex.exp_add]
  ring

/-- The measure bridge: a telescoped phase carries no weight —
`normSq (e^{i t} z) = normSq z` for real `t`. -/
theorem phase_free_measure (t : ℝ) (z : ℂ) :
    Complex.normSq (Complex.exp ((t : ℂ) * Complex.I) * z) =
      Complex.normSq z := by
  rw [Complex.normSq_mul]
  have h1 : Complex.exp ((t : ℂ) * Complex.I) =
      (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [h1, Complex.normSq_add_mul_I]
  have h2 : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq t
  rw [h2, one_mul]

/-! ## 2. Coherent record accretion -/

/-- THE ACCRETION THEOREM.  Coherent evolution of the (phase-stripped)
nonnegative class amplitudes: `R' c = sum_{e -> c} R (src e) * a e`,
with labeled Born completeness `sum_{e from p} (a e)^2 = 1` at every
parent.  Every hereditary event — one whose child classes inherit
membership from parent classes, as stem events do — has
non-decreasing unnormalized coherent square-mass.  Facts never lose
coherent weight; interference (which telescoping made a class
function) never subtracts. -/
theorem coherent_record_accretion
    (src : E → P) (tgt : E → C) (a : E → ℝ) (R : P → ℝ)
    (ha : ∀ e, 0 ≤ a e) (hR : ∀ p, 0 ≤ R p)
    (born : ∀ p, ∑ e ∈ univ.filter (fun e => src e = p), a e ^ 2 = 1)
    (EP : P → Prop) (EC : C → Prop)
    (hered : ∀ e, EP (src e) → EC (tgt e)) :
    ∑ p ∈ univ.filter (fun p => EP p), R p ^ 2 ≤
    ∑ c ∈ univ.filter (fun c => EC c),
      (∑ e ∈ univ.filter (fun e => tgt e = c), R (src e) * a e) ^ 2 := by
  -- Step 1: unfold the parent mass through the Born fibers.
  have h1 : ∑ p ∈ univ.filter (fun p => EP p), R p ^ 2 =
      ∑ p ∈ univ.filter (fun p => EP p),
        ∑ e ∈ univ.filter (fun e => src e = p),
          (R (src e) * a e) ^ 2 := by
    refine Finset.sum_congr rfl fun p _ => ?_
    have : ∑ e ∈ univ.filter (fun e => src e = p),
        (R (src e) * a e) ^ 2 =
        ∑ e ∈ univ.filter (fun e => src e = p),
          R p ^ 2 * a e ^ 2 := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [(Finset.mem_filter.1 he).2]; ring
    rw [this, ← Finset.mul_sum, born p, mul_one]
  -- Step 2: fiberwise collapse to a single edge sum over EP-sources.
  have h2 : ∑ p ∈ univ.filter (fun p => EP p),
      ∑ e ∈ univ.filter (fun e => src e = p),
        (R (src e) * a e) ^ 2 =
      ∑ e ∈ univ.filter (fun e => EP (src e)),
        (R (src e) * a e) ^ 2 := by
    rw [Finset.sum_fiberwise_eq_sum_filter univ
      (univ.filter (fun p => EP p)) src (fun e => (R (src e) * a e) ^ 2)]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext e
    simp [Finset.mem_filter]
  -- Step 3: heredity moves the edge sum into EC-targets (nonneg terms).
  have h3 : ∑ e ∈ univ.filter (fun e => EP (src e)),
      (R (src e) * a e) ^ 2 ≤
      ∑ e ∈ univ.filter (fun e => EC (tgt e)),
        (R (src e) * a e) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      fun e _ _ => sq_nonneg _
    intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨he.1, hered e he.2⟩
  -- Step 4: fiberwise expansion over child classes.
  have h4 : ∑ e ∈ univ.filter (fun e => EC (tgt e)),
      (R (src e) * a e) ^ 2 =
      ∑ c ∈ univ.filter (fun c => EC c),
        ∑ e ∈ univ.filter (fun e => tgt e = c),
          (R (src e) * a e) ^ 2 := by
    rw [Finset.sum_fiberwise_eq_sum_filter univ
      (univ.filter (fun c => EC c)) tgt (fun e => (R (src e) * a e) ^ 2)]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext e
    simp [Finset.mem_filter]
  -- Step 5: per class, aggregation is square-superadditive.
  have h5 : ∑ c ∈ univ.filter (fun c => EC c),
      ∑ e ∈ univ.filter (fun e => tgt e = c),
        (R (src e) * a e) ^ 2 ≤
      ∑ c ∈ univ.filter (fun c => EC c),
        (∑ e ∈ univ.filter (fun e => tgt e = c), R (src e) * a e) ^ 2 := by
    refine Finset.sum_le_sum fun c _ => ?_
    exact sq_sum_ge_sum_sq _ _
      fun e _ => mul_nonneg (hR (src e)) (ha e)
  calc ∑ p ∈ univ.filter (fun p => EP p), R p ^ 2
      = ∑ e ∈ univ.filter (fun e => EP (src e)),
          (R (src e) * a e) ^ 2 := by rw [h1, h2]
    _ ≤ ∑ e ∈ univ.filter (fun e => EC (tgt e)),
          (R (src e) * a e) ^ 2 := h3
    _ = ∑ c ∈ univ.filter (fun c => EC c),
          ∑ e ∈ univ.filter (fun e => tgt e = c),
            (R (src e) * a e) ^ 2 := h4
    _ ≤ _ := h5

/-- Total class-identified coherent mass is non-decreasing — the
anti-decoherence growth of the measure, now an inequality with an
identified mechanism (class aggregation of same-phase paths). -/
theorem coherent_total_mass_grows
    (src : E → P) (tgt : E → C) (a : E → ℝ) (R : P → ℝ)
    (ha : ∀ e, 0 ≤ a e) (hR : ∀ p, 0 ≤ R p)
    (born : ∀ p, ∑ e ∈ univ.filter (fun e => src e = p), a e ^ 2 = 1) :
    ∑ p, R p ^ 2 ≤
    ∑ c, (∑ e ∈ univ.filter (fun e => tgt e = c), R (src e) * a e) ^ 2 := by
  have h := coherent_record_accretion src tgt a R ha hR born
    (fun _ => True) (fun _ => True) (fun _ _ => trivial)
  simpa using h

#print axioms sq_sum_ge_sum_sq
#print axioms step_phase_form
#print axioms phase_free_measure
#print axioms coherent_record_accretion
#print axioms coherent_total_mass_grows

end UnifiedTheory.Audit.KFCausalCoherentRecordAccretion
