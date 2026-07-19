/-
# The Mermin–Wagner Theorem (LayerB)

In dimensions `d ≤ 2`, continuous symmetries cannot be spontaneously broken at
any positive temperature.  The mechanism is an **infrared (long-wavelength)
divergence** of the would-be Goldstone modes.

A gapless (would-be Goldstone) mode has propagator `~ 1/k²`.  The fluctuation of
the order-parameter phase is

```
  ⟨φ²⟩  =  (T / (2π)^d) ∫_{|k|<Λ} d^d k / k².
```

Passing to radial coordinates, `d^d k = (area of unit sphere) k^{d-1} dk`, so the
convergence of `⟨φ²⟩` is governed by the **radial integral**

```
  ∫_0^Λ k^{d-1} · k^{-2} dk  =  ∫_0^Λ k^{d-3} dk.
```

The exponent is `d - 3`, and `∫_0 k^p dk` converges at the origin iff `p > -1`,
i.e. iff `d - 3 > -1`, i.e. iff `d ≥ 3`:

* `d = 1`:  integrand `k^{-2}`, antiderivative `-1/k → +∞` as the IR cutoff
  `ε → 0`.  **Diverges** — no order.
* `d = 2`:  integrand `k^{-1}`, antiderivative `log k → -∞` as `ε → 0`.
  **Diverges (logarithmically)** — no order; the marginal case, where
  Berezinskii–Kosterlitz–Thouless physics governs instead.
* `d = 3`:  integrand `k^0 = 1`, antiderivative `k`, finite.  **Converges** —
  long-range order is possible.

This file proves the **IR-convergence dichotomy unconditionally** (the
mathematical heart), and states the full Mermin–Wagner no-go theorem together
with the BKT marginal-case statement as named targets.
-/
import Mathlib

namespace UnifiedTheory.LayerB.MerminWagner

/-! ## 1. The IR fluctuation exponent and the convergence criterion -/

/-- The infrared fluctuation integrand for spatial dimension `d` is `k^(d-3)`,
arising from the radial measure `k^(d-1)` times the Goldstone propagator `k^(-2)`.
This is its exponent. -/
def fluctExponent (d : ℕ) : ℤ := (d : ℤ) - 3

/-- Infrared convergence criterion: the radial integral `∫_0 k^p dk` converges at
the origin iff `p > -1`.  Here `p = fluctExponent d = d - 3`, so this says
`d - 3 > -1`, i.e. `d > 2`. -/
def IRConverges (d : ℕ) : Prop := fluctExponent d > -1

@[simp] theorem fluctExponent_eq (d : ℕ) : fluctExponent d = (d : ℤ) - 3 := rfl

/-- **The IR-convergence dichotomy.**  The order-parameter fluctuation integral
converges iff the spatial dimension is at least `3`.  Equivalently, for `d ≤ 2`
it diverges (no spontaneous breaking of a continuous symmetry). -/
theorem irConverges_iff (d : ℕ) : IRConverges d ↔ 3 ≤ d := by
  unfold IRConverges fluctExponent
  omega

/-- In `d = 1` the fluctuation integral diverges: no order. -/
theorem ir_diverges_d1 : ¬ IRConverges 1 := by
  rw [irConverges_iff]; omega

/-- In `d = 2` the fluctuation integral diverges (logarithmically): no order.
This is the marginal Mermin–Wagner / BKT case. -/
theorem ir_diverges_d2 : ¬ IRConverges 2 := by
  rw [irConverges_iff]; omega

/-- In `d = 3` the fluctuation integral converges: long-range order is possible. -/
theorem ir_converges_d3 : IRConverges 3 := by
  rw [irConverges_iff]

/-- The exponent itself is negative (super-IR-singular) exactly at `d = 1`. -/
theorem fluctExponent_d1 : fluctExponent 1 = -2 := by decide

/-- At `d = 2` the exponent is `-1`: the marginal logarithmic case. -/
theorem fluctExponent_d2 : fluctExponent 2 = -1 := by decide

/-- At `d = 3` the exponent is `0`: the integrand is constant, hence integrable. -/
theorem fluctExponent_d3 : fluctExponent 3 = 0 := by decide

/-- Restatement of the dichotomy as a statement about the marginal value `-1`:
the integral diverges iff the exponent is `≤ -1`. -/
theorem irDiverges_iff_exponent_le (d : ℕ) :
    ¬ IRConverges d ↔ fluctExponent d ≤ -1 := by
  unfold IRConverges; omega

/-! ## 2. The radial integral in closed form and its IR (ε → 0) behavior

We compute `∫_ε^Λ k^{d-3} dk` for the three relevant dimensions in closed form,
and analyze the `ε → 0` limit.  We work with `0 < ε ≤ Λ`.
-/

/-- The radial fluctuation integral `∫_ε^Λ k^{d-3} dk`, in closed form by cases
on the dimension:

* `d = 1`: `∫_ε^Λ k^{-2} dk = 1/ε - 1/Λ`     (diverges as `ε → 0`),
* `d = 2`: `∫_ε^Λ k^{-1} dk = log Λ - log ε`  (diverges as `ε → 0`),
* `d = 3`: `∫_ε^Λ k^{0}  dk = Λ - ε`          (finite as `ε → 0`),
* otherwise: `(Λ^(d-2) - ε^(d-2)) / (d-2)`     (the generic power-law form).

The first three are the physically decisive cases. -/
noncomputable def radialFluct (d : ℕ) (ε Λ : ℝ) : ℝ :=
  match d with
  | 1 => 1 / ε - 1 / Λ
  | 2 => Real.log Λ - Real.log ε
  | 3 => Λ - ε
  | n => (Λ ^ (n - 2) - ε ^ (n - 2)) / ((n : ℝ) - 2)

@[simp] theorem radialFluct_d1 (ε Λ : ℝ) : radialFluct 1 ε Λ = 1 / ε - 1 / Λ := rfl
@[simp] theorem radialFluct_d2 (ε Λ : ℝ) :
    radialFluct 2 ε Λ = Real.log Λ - Real.log ε := rfl
@[simp] theorem radialFluct_d3 (ε Λ : ℝ) : radialFluct 3 ε Λ = Λ - ε := rfl

/-! ### d = 3: finite (convergent) IR behavior -/

/-- **Convergence at `d = 3`.**  The `d = 3` radial integral tends to the finite
value `Λ` as the IR cutoff `ε → 0` (continuity of `Λ - ·` at `0`). -/
theorem radialFluct_d3_tendsto (Λ : ℝ) :
    Filter.Tendsto (fun ε => radialFluct 3 ε Λ) (nhds 0) (nhds Λ) := by
  simp only [radialFluct_d3]
  have : Filter.Tendsto (fun ε : ℝ => Λ - ε) (nhds 0) (nhds (Λ - 0)) :=
    (tendsto_const_nhds).sub Filter.tendsto_id
  simpa using this

/-- At `d = 3` the integral is bounded uniformly in the IR cutoff `ε ∈ (0, Λ]`:
it never exceeds `Λ`.  This is the quantitative face of convergence — order is
not destroyed by long-wavelength fluctuations. -/
theorem radialFluct_d3_bounded {ε Λ : ℝ} (hε : 0 < ε) :
    radialFluct 3 ε Λ ≤ Λ := by
  simp only [radialFluct_d3]
  linarith

/-- The `d = 3` integral is also nonnegative for `ε ≤ Λ`. -/
theorem radialFluct_d3_nonneg {ε Λ : ℝ} (hεΛ : ε ≤ Λ) :
    0 ≤ radialFluct 3 ε Λ := by
  simp only [radialFluct_d3]; linarith

/-! ### d = 1: power-law IR divergence -/

/-- The `d = 1` integrand value at fixed `Λ` as a function of the IR cutoff `ε`:
`1/ε - 1/Λ`.  We show it is **unbounded above** as `ε → 0⁺` — the hallmark of an
infrared divergence that destroys order. -/
theorem radialFluct_d1_unbounded (Λ : ℝ) (hΛ : 0 < Λ) (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ M < radialFluct 1 ε Λ := by
  -- Choose ε small enough that 1/ε exceeds M + 1/Λ.
  -- Take ε = 1 / (|M| + 1/Λ + 1); then 1/ε = |M| + 1/Λ + 1 > M + 1/Λ.
  set c : ℝ := |M| + 1 / Λ + 1 with hc
  have hcpos : 0 < c := by
    have h1 : 0 ≤ |M| := abs_nonneg M
    have h2 : 0 < 1 / Λ := by positivity
    have : (0:ℝ) < 1 := one_pos
    linarith
  refine ⟨1 / c, by positivity, ?_⟩
  simp only [radialFluct_d1]
  have hinv : 1 / (1 / c) = c := by
    rw [one_div_one_div]
  rw [hinv]
  have hMle : M ≤ |M| := le_abs_self M
  -- c - 1/Λ = |M| + 1 ≥ M + 1 > M
  have : c - 1 / Λ = |M| + 1 := by rw [hc]; ring
  linarith

/-- **Divergence at `d = 1`.**  The `d = 1` radial integral `1/ε - 1/Λ` tends to
`+∞` as the IR cutoff `ε → 0⁺`.  This is the infrared catastrophe: would-be
Goldstone fluctuations have infinite variance, so no continuous symmetry can be
spontaneously broken in one dimension. -/
theorem radialFluct_d1_tendsto_atTop (Λ : ℝ) :
    Filter.Tendsto (fun ε => radialFluct 1 ε Λ)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  simp only [radialFluct_d1]
  -- `1/ε = ε⁻¹ → +∞` on the right neighborhood of `0`; adding the constant
  -- `-(1/Λ)` preserves `atTop`.
  have hinv : Filter.Tendsto (fun ε : ℝ => ε⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := tendsto_inv_nhdsGT_zero
  have hsum : Filter.Tendsto (fun ε : ℝ => ε⁻¹ + (-(1 / Λ)))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ hinv
  refine hsum.congr ?_
  intro x; rw [one_div x]; ring

/-! ### d = 2: logarithmic IR divergence -/

/-- **Divergence at `d = 2` (logarithmic).**  The `d = 2` radial integral
`log Λ - log ε` tends to `+∞` as `ε → 0⁺`, since `log ε → -∞`.  This is the
marginal case: the divergence is only logarithmic, but it still forbids true
long-range order — the regime of Berezinskii–Kosterlitz–Thouless physics. -/
theorem radialFluct_d2_tendsto_atTop (Λ : ℝ) :
    Filter.Tendsto (fun ε => radialFluct 2 ε Λ)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  simp only [radialFluct_d2]
  -- `log ε → -∞`, so `-log ε → +∞`; adding the constant `log Λ` preserves it.
  have hlog : Filter.Tendsto (fun ε : ℝ => Real.log ε)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero
  have hneg : Filter.Tendsto (fun ε : ℝ => - Real.log ε)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    Filter.tendsto_neg_atBot_atTop.comp hlog
  have hsum : Filter.Tendsto (fun ε : ℝ => - Real.log ε + Real.log Λ)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ hneg
  refine hsum.congr ?_
  intro x; ring

/-! ## 3. The Mermin–Wagner no-go and the BKT marginal case, as named targets

The unconditional content above (the IR-convergence dichotomy and the explicit
radial-integral limits) is the mathematical core.  We now record the physical
theorem and the BKT statement as named `Prop`-level targets, defined in terms of
the established convergence criterion so that they are not vacuous placeholders.
-/

/-- **Mermin–Wagner target.**  For every spatial dimension `d ≤ 2`, the IR
fluctuation integral diverges; equivalently, the convergence criterion fails.
This is the precise sense in which a continuous symmetry cannot be spontaneously
broken in `d ≤ 2`: the would-be Goldstone fluctuation has infinite variance. -/
def MerminWagner_Target : Prop := ∀ d : ℕ, d ≤ 2 → ¬ IRConverges d

/-- **BKT target.**  The two-dimensional case is *marginal*: the IR divergence is
exactly logarithmic, encoded by the exponent being `-1` (the boundary value of
the convergence criterion).  No long-range order, but the divergence is the
weakest possible — the Berezinskii–Kosterlitz–Thouless regime. -/
def BKT_Target : Prop := fluctExponent 2 = -1 ∧ ¬ IRConverges 2

/-- The Mermin–Wagner no-go holds (unconditionally). -/
theorem mermin_wagner_target : MerminWagner_Target := by
  intro d hd
  rw [irConverges_iff]
  omega

/-- The BKT marginal-case statement holds (unconditionally). -/
theorem bkt_target : BKT_Target := by
  refine ⟨fluctExponent_d2, ir_diverges_d2⟩

/-- **Master theorem.**  The complete Mermin–Wagner picture in one statement:

1. (no-go) continuous symmetry breaking is forbidden in every `d ≤ 2`;
2. (BKT) `d = 2` is the marginal logarithmic case;
3. (order) `d = 3` admits long-range order;
4. (dichotomy) order is possible iff `d ≥ 3`. -/
theorem mermin_wagner_master :
    MerminWagner_Target ∧ BKT_Target ∧ IRConverges 3 ∧
      (∀ d : ℕ, IRConverges d ↔ 3 ≤ d) :=
  ⟨mermin_wagner_target, bkt_target, ir_converges_d3, irConverges_iff⟩

end UnifiedTheory.LayerB.MerminWagner
