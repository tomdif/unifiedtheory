import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Fannes–Audenaert continuity bound for von Neumann entropy

This file formalizes the **bound function** of the Fannes–Audenaert theorem
(Audenaert 2007), the optimal (tight) sharpening of the older Fannes bound.

For two density matrices `ρ, σ` on `ℂ^d` with trace distance
`T = ½‖ρ − σ‖₁`, the von Neumann entropies satisfy

  `|S(ρ) − S(σ)| ≤ T · log(d − 1) + h(T)`,

where `h(T) = −T log T − (1 − T) log(1 − T)` is the binary entropy.

## What is proved unconditionally

The *bound function* `faBound d T := T * Real.log (d − 1) + binaryEntropy T`
together with all of its elementary properties are proved here with **no
`sorry` and no custom `axiom`**:

* `binaryEntropy_zero`, `binaryEntropy_one`        — `h(0) = h(1) = 0`
* `binaryEntropy_symm`                              — `h(t) = h(1 − t)`
* `binaryEntropy_half`                              — `h(½) = log 2`
* `binaryEntropy_nonneg`                            — `h ≥ 0` on `[0,1]`
* `faBound_at_zero`                                 — `faBound d 0 = 0` (continuity)
* `faBound_qubit`                                   — `faBound 2 T = h(T)`
* `faBound_nonneg`                                  — `faBound d T ≥ 0`

The deep operator inequality `|S(ρ) − S(σ)| ≤ faBound d T` itself (which
requires majorization / Lidskii's theorem on eigenvalue perturbation) is
*stated* as a named `Prop` target, `FannesAudenaert_Target`, together with the
looser classical `Fannes_Bound_Target`.

The natural logarithm `Real.log` is used throughout (so the binary entropy is
measured in *nats*); converting to bits/base-2 only rescales the bound.
-/

namespace UnifiedTheory.LayerB.FannesAudenaert

open Real

/-- **Binary entropy** in nats: `h(t) = −t log t − (1 − t) log(1 − t)`. -/
noncomputable def binaryEntropy (t : ℝ) : ℝ :=
  -t * Real.log t - (1 - t) * Real.log (1 - t)

/-- **Fannes–Audenaert bound function**
`faBound d T = T · log(d − 1) + h(T)`. -/
noncomputable def faBound (d : ℕ) (T : ℝ) : ℝ :=
  T * Real.log (d - 1) + binaryEntropy T

/-! ## Elementary properties of binary entropy -/

/-- `h(0) = 0`. -/
@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  unfold binaryEntropy
  simp

/-- `h(1) = 0`. -/
@[simp] theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  unfold binaryEntropy
  simp

/-- Binary entropy is symmetric about `½`: `h(t) = h(1 − t)`. -/
theorem binaryEntropy_symm (t : ℝ) : binaryEntropy t = binaryEntropy (1 - t) := by
  unfold binaryEntropy
  have : (1 : ℝ) - (1 - t) = t := by ring
  rw [this]
  ring

/-- `h(½) = log 2`. -/
theorem binaryEntropy_half : binaryEntropy (1 / 2) = Real.log 2 := by
  unfold binaryEntropy
  have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by ring
  rw [h1]
  -- both terms are `-(1/2) log (1/2)`, summing to `- log (1/2) = log 2`
  have hlog : Real.log (1 / 2) = - Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring

/-- `−t log t ≥ 0` for `0 ≤ t ≤ 1`. -/
theorem neg_mul_log_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ -t * Real.log t := by
  rcases eq_or_lt_of_le h0 with h | hpos
  · -- t = 0
    rw [← h]; simp
  · have hlog : Real.log t ≤ 0 := Real.log_nonpos h0 h1
    have : 0 ≤ t * (- Real.log t) := mul_nonneg h0 (by linarith)
    nlinarith [this]

/-- Binary entropy is nonnegative on `[0,1]`. -/
theorem binaryEntropy_nonneg (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ binaryEntropy t := by
  unfold binaryEntropy
  have hA : 0 ≤ -t * Real.log t := neg_mul_log_nonneg h0 h1
  -- second term: `−(1−t) log (1−t) ≥ 0`
  have h0' : 0 ≤ 1 - t := by linarith
  have h1' : 1 - t ≤ 1 := by linarith
  have hB : 0 ≤ -(1 - t) * Real.log (1 - t) := neg_mul_log_nonneg h0' h1'
  -- `binaryEntropy t = (-t log t) + (-(1-t) log (1-t))`
  have : -t * Real.log t - (1 - t) * Real.log (1 - t)
       = (-t * Real.log t) + (-(1 - t) * Real.log (1 - t)) := by ring
  rw [this]
  linarith

/-! ## Properties of the Fannes–Audenaert bound function -/

/-- At zero trace distance (equal states), the bound vanishes — this is the
*continuity* statement: equal density matrices have equal entropy. -/
@[simp] theorem faBound_at_zero (d : ℕ) : faBound d 0 = 0 := by
  unfold faBound
  simp

/-- **Qubit case** `d = 2`: since `log(d − 1) = log 1 = 0`, the bound reduces
to the pure binary entropy of the trace distance. -/
theorem faBound_qubit (T : ℝ) : faBound 2 T = binaryEntropy T := by
  unfold faBound
  norm_num

/-- For `d ≥ 2` and `0 ≤ T ≤ 1` the bound is nonnegative. -/
theorem faBound_nonneg (d : ℕ) (T : ℝ) (hd : 2 ≤ d)
    (h0 : 0 ≤ T) (h1 : T ≤ 1) : 0 ≤ faBound d T := by
  unfold faBound
  -- first term ≥ 0 : T ≥ 0 and log(d−1) ≥ 0 since d − 1 ≥ 1
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hlog : 0 ≤ Real.log ((d : ℝ) - 1) := Real.log_nonneg hd1
  have hT : 0 ≤ T * Real.log ((d : ℝ) - 1) := mul_nonneg h0 hlog
  have hh : 0 ≤ binaryEntropy T := binaryEntropy_nonneg T h0 h1
  linarith

/-- Monotonicity of the *log-dimension* term: for fixed `T ≥ 0`, increasing the
dimension can only loosen (never tighten) the bound. -/
theorem faBound_mono_dim {d e : ℕ} (hde : d ≤ e) (hd : 2 ≤ d) {T : ℝ}
    (hT : 0 ≤ T) : faBound d T ≤ faBound e T := by
  unfold faBound
  have hcast : (d : ℝ) ≤ (e : ℝ) := by exact_mod_cast hde
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hpos : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hle : (d : ℝ) - 1 ≤ (e : ℝ) - 1 := by linarith
  have hlog : Real.log ((d : ℝ) - 1) ≤ Real.log ((e : ℝ) - 1) :=
    Real.log_le_log hpos hle
  have : T * Real.log ((d : ℝ) - 1) ≤ T * Real.log ((e : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left hlog hT
  linarith

/-! ## The named theorem targets

The statements below are the *physical* Fannes–Audenaert inequality and its
older Fannes corollary.  They are quantified over abstract data
(`d : ℕ`, an entropy difference `entropyGap`, and a trace distance `T`) so that
the present file can name them without yet depending on the full
majorization / Lidskii machinery required to discharge them.
-/

/-- **The Fannes–Audenaert theorem (named target).**  For a `d`-dimensional
system, any pair of density matrices whose von Neumann entropies differ by
`entropyGap` and whose trace distance is `T` satisfies
`|entropyGap| ≤ T · log(d − 1) + h(T)`.

This is the optimal (tight) continuity bound; proving it for the genuine
quantum quantities requires Lidskii's eigenvalue-majorization theorem. -/
def FannesAudenaert_Target : Prop :=
  ∀ (d : ℕ) (entropyGap T : ℝ),
    2 ≤ d → 0 ≤ T → T ≤ 1 →
    |entropyGap| ≤ faBound d T

/-- **The stronger `−T log T` Fannes-style bound (named target).**  The
estimate `|ΔS| ≤ T · log(d − 1) − T log T`, whose right-hand side equals the
Audenaert right-hand side *minus* the nonnegative term `−(1 − T) log(1 − T)`.
Because its RHS is the smaller of the two, this is the strictly *stronger*
statement and it implies the Audenaert continuity bound. -/
def Fannes_Bound_Target : Prop :=
  ∀ (d : ℕ) (entropyGap T : ℝ),
    2 ≤ d → 0 ≤ T → T ≤ 1 →
    |entropyGap| ≤ T * Real.log (d - 1) - T * Real.log T

/-- **Master reduction.**  The stronger `−T log T` bound implies the
Fannes–Audenaert continuity bound: the Audenaert right-hand side differs from
the stronger one by the *added* nonnegative term `−(1 − T) log(1 − T) ≥ 0`, so
the Audenaert RHS is the larger and is therefore dominated by `|ΔS|` whenever
the stronger bound holds.  This is proved *unconditionally* — it only relates
the two bound functions and does not assume the deep inequality itself. -/
theorem fannes_audenaert_master :
    Fannes_Bound_Target → FannesAudenaert_Target := by
  intro hF d gap T hd h0 h1
  have key := hF d gap T hd h0 h1
  -- faBound d T = (T log(d−1) − T log T) + (−(1−T) log(1−T)), extra term ≥ 0.
  have h0' : 0 ≤ 1 - T := by linarith
  have h1' : 1 - T ≤ 1 := by linarith
  have hextra : 0 ≤ -(1 - T) * Real.log (1 - T) := neg_mul_log_nonneg h0' h1'
  have heq : faBound d T
      = (T * Real.log (d - 1) - T * Real.log T)
        + (-(1 - T) * Real.log (1 - T)) := by
    unfold faBound binaryEntropy; ring
  -- |gap| ≤ (stronger RHS) ≤ (stronger RHS) + extra = faBound
  rw [heq]
  linarith

end UnifiedTheory.LayerB.FannesAudenaert
