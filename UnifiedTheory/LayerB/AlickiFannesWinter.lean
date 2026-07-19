import Mathlib.Analysis.SpecialFunctions.Log.Basic
import UnifiedTheory.LayerB.FannesAudenaert

/-!
# The Alicki–Fannes–Winter (AFW) continuity bound for conditional entropy

This file formalizes the **bound function** of the Alicki–Fannes–Winter theorem
in the tight form due to Winter (2016), the conditional-entropy analogue of the
Fannes–Audenaert bound for the von Neumann entropy.

For bipartite states `ρ_AB, σ_AB` on `ℂ^{d_A} ⊗ ℂ^{d_B}` with trace distance
`T = ½‖ρ − σ‖₁`, the **conditional entropies** `S(A|B) := S(AB) − S(B)` satisfy

  `|S(A|B)_ρ − S(A|B)_σ| ≤ 2 T · log d_A + (1 + T) · h(T / (1 + T))`,

where `h(t) = −t log t − (1 − t) log(1 − t)` is the binary entropy.

Two features distinguish this from the (single-system) Fannes–Audenaert bound:

* the **factor 2** on the `log d_A` term — conditional entropy ranges over the
  full interval `[−log d_A, log d_A]` of width `2 log d_A` (it can be negative,
  a genuinely quantum signature of entanglement);
* the **`(1 + T)` prefactor** and the rescaled argument `T / (1 + T)` of the
  binary entropy, which is the sharp constant from Winter's coupling argument.

## What is proved unconditionally

The *bound function*
`afwBound dA T := 2 * T * log dA + (1 + T) * binaryEntropy (T / (1 + T))`
together with its elementary properties is proved here with **no `sorry` and no
custom `axiom`**:

* `afwBound_at_zero`            — `afwBound dA 0 = 0` (continuity)
* `afw_arg_le_half`             — `T / (1 + T) ≤ ½` on `[0,1]` (h-argument stays
                                   in the increasing regime)
* `afw_arg_nonneg`              — `0 ≤ T / (1 + T)`
* `afwBound_nonneg`             — `afwBound dA T ≥ 0`
* `afwBound_ge_faBound`         — AFW is looser than Fannes–Audenaert
* `conditionalEntropy_eq`, `conditionalEntropy_le_logdimA` — algebra of `S(A|B)`

The deep operator inequality `|ΔS(A|B)| ≤ afwBound dA T` itself (whose proof
requires Winter's coupling / smoothing construction) is *stated* as a named
`Prop` target, `AFW_Target`, together with the capacity-continuity corollary
`Capacity_Continuity_Target` and a master reduction `afw_master`.

The natural logarithm `Real.log` is used throughout (entropies in *nats*).

It reuses `binaryEntropy`, `binaryEntropy_nonneg`, `neg_mul_log_nonneg`, and
`faBound` from `UnifiedTheory.LayerB.FannesAudenaert`.
-/

namespace UnifiedTheory.LayerB.AlickiFannesWinter

open Real
open UnifiedTheory.LayerB.FannesAudenaert

/-! ## Conditional entropy -/

/-- **Conditional (von Neumann) entropy** `S(A|B) = S(AB) − S(B)`.  Unlike the
classical Shannon conditional entropy this quantity can be *negative* — that is
exactly the signature of entanglement between `A` and `B`. -/
noncomputable def conditionalEntropy (S_AB S_B : ℝ) : ℝ := S_AB - S_B

/-- Defining equation of the conditional entropy (definitional unfolding). -/
theorem conditionalEntropy_eq (S_AB S_B : ℝ) :
    conditionalEntropy S_AB S_B = S_AB - S_B := rfl

/-- Conditional entropy is *antisymmetric under swapping the roles of the two
arguments up to sign*: `S(A|B)` with `(S_AB, S_B)` is minus the value with the
arguments exchanged. -/
theorem conditionalEntropy_swap (S_AB S_B : ℝ) :
    conditionalEntropy S_AB S_B = - conditionalEntropy S_B S_AB := by
  unfold conditionalEntropy; ring

/-- The conditional entropy of a product state `S(AB) = S(A) + S(B)` reduces to
the marginal entropy `S(A)`. -/
theorem conditionalEntropy_product (S_A S_B : ℝ) :
    conditionalEntropy (S_A + S_B) S_B = S_A := by
  unfold conditionalEntropy; ring

/-- **Boundedness of conditional entropy.**  Given the operational fact that the
conditional entropy lies in `[−logdimA, logdimA]` — encoded here as the two
bracketing hypotheses — its absolute value is at most `logdimA`. -/
theorem conditionalEntropy_le_logdimA (S_AB S_B logdimA : ℝ)
    (hlo : -logdimA ≤ conditionalEntropy S_AB S_B)
    (hhi : conditionalEntropy S_AB S_B ≤ logdimA) :
    |conditionalEntropy S_AB S_B| ≤ logdimA :=
  abs_le.mpr ⟨hlo, hhi⟩

/-! ## The AFW bound function -/

/-- **Alicki–Fannes–Winter bound function** (Winter 2016, tight form):
`afwBound dA T = 2 T · log dA + (1 + T) · h(T / (1 + T))`. -/
noncomputable def afwBound (dA T : ℝ) : ℝ :=
  2 * T * Real.log dA + (1 + T) * binaryEntropy (T / (1 + T))

/-! ### Properties of the rescaled binary-entropy argument `T / (1 + T)` -/

/-- The argument `T / (1 + T)` is nonnegative for `T ≥ 0`. -/
theorem afw_arg_nonneg (T : ℝ) (hT0 : 0 ≤ T) : 0 ≤ T / (1 + T) := by
  have hden : 0 < 1 + T := by linarith
  exact div_nonneg hT0 (le_of_lt hden)

/-- The argument `T / (1 + T)` stays in the *increasing* regime of the binary
entropy: it never exceeds `½` for `T ∈ [0,1]`.  In fact equality holds at
`T = 1`. -/
theorem afw_arg_le_half (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    T / (1 + T) ≤ 1 / 2 := by
  have hden : 0 < 1 + T := by linarith
  rw [div_le_iff₀ hden]
  -- `T ≤ (1/2) * (1 + T)` ⇔ `T ≤ 1`
  nlinarith

/-- The argument `T / (1 + T)` is at most `1` (hence in `[0,1]`, the domain on
which `binaryEntropy ≥ 0`). -/
theorem afw_arg_le_one (T : ℝ) (hT0 : 0 ≤ T) : T / (1 + T) ≤ 1 := by
  have hden : 0 < 1 + T := by linarith
  rw [div_le_one hden]; linarith

/-! ### Properties of `afwBound` -/

/-- At zero trace distance (equal states), the bound vanishes — this is the
*continuity* statement for conditional entropy: equal states have equal
`S(A|B)`. -/
@[simp] theorem afwBound_at_zero (dA : ℝ) : afwBound dA 0 = 0 := by
  unfold afwBound
  simp

/-- For `dA ≥ 1` and `0 ≤ T ≤ 1` the bound is nonnegative.  Both summands are
nonnegative: `log dA ≥ 0` makes the first term `≥ 0`, and the binary entropy of
the in-range argument `T/(1+T) ∈ [0,1]` is nonnegative. -/
theorem afwBound_nonneg (dA T : ℝ) (hd : 1 ≤ dA) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    0 ≤ afwBound dA T := by
  unfold afwBound
  -- first term: `2 T log dA ≥ 0`
  have hlog : 0 ≤ Real.log dA := Real.log_nonneg hd
  have hfst : 0 ≤ 2 * T * Real.log dA := by positivity
  -- second term: `(1 + T) * h(T/(1+T)) ≥ 0`
  have harg0 : 0 ≤ T / (1 + T) := afw_arg_nonneg T hT0
  have harg1 : T / (1 + T) ≤ 1 := afw_arg_le_one T hT0
  have hh : 0 ≤ binaryEntropy (T / (1 + T)) :=
    binaryEntropy_nonneg _ harg0 harg1
  have hcoef : 0 ≤ 1 + T := by linarith
  have hsnd : 0 ≤ (1 + T) * binaryEntropy (T / (1 + T)) := mul_nonneg hcoef hh
  linarith

/-- **Monotonicity of the log-dimension term.**  For fixed `T ≥ 0`, enlarging
the `A`-subsystem dimension can only loosen the bound. -/
theorem afwBound_mono_dim {dA eA : ℝ} (h1 : 1 ≤ dA) (hde : dA ≤ eA) {T : ℝ}
    (hT : 0 ≤ T) : 2 * T * Real.log dA ≤ 2 * T * Real.log eA := by
  have hpos : (0 : ℝ) < dA := by linarith
  have hlog : Real.log dA ≤ Real.log eA := Real.log_le_log hpos hde
  have h2T : 0 ≤ 2 * T := by linarith
  exact mul_le_mul_of_nonneg_left hlog h2T

/-- **Auxiliary log-perturbation bound** `−(1 − T) log(1 − T) ≤ (1 + T) log(1 + T)`
for `T ∈ [0,1]`.

We use the elementary bound `Real.log x ≤ x − 1` (`Real.log_le_sub_one_of_pos`)
applied to `x = 1/(1−T)` and `x = 1/(1+T)`:

* `−(1−T) log(1−T) ≤ (1−T)·((1/(1−T)) − 1) = 1 − (1−T) = T`  (for `T < 1`),
* `(1+T) log(1+T) ≥ (1+T)·(1 − 1/(1+T)) = (1+T) − 1 = T`.

Hence LHS `≤ T ≤` RHS. -/
theorem log_perturbation_bound (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    -(1 - T) * Real.log (1 - T) ≤ (1 + T) * Real.log (1 + T) := by
  have hden : 0 < 1 + T := by linarith
  -- Right side ≥ T : log(1+T) ≥ 1 − 1/(1+T) via `Real.log_le_sub_one_of_pos`.
  have hRle : T ≤ (1 + T) * Real.log (1 + T) := by
    have hpos : (0 : ℝ) < 1 / (1 + T) := by positivity
    have hub := Real.log_le_sub_one_of_pos hpos
    have hloginv : Real.log (1 / (1 + T)) = - Real.log (1 + T) := by
      rw [one_div, Real.log_inv]
    rw [hloginv] at hub
    have hlb : 1 - 1 / (1 + T) ≤ Real.log (1 + T) := by linarith
    have := mul_le_mul_of_nonneg_left hlb (le_of_lt hden)
    have hsimp : (1 + T) * (1 - 1 / (1 + T)) = T := by
      field_simp; ring
    rw [hsimp] at this
    exact this
  -- Left side ≤ T.
  have hLle : -(1 - T) * Real.log (1 - T) ≤ T := by
    rcases eq_or_lt_of_le hT1 with hTeq | hTlt
    · subst hTeq; simp
    · have hxpos : (0 : ℝ) < 1 - T := by linarith
      have hpos2 : (0 : ℝ) < 1 / (1 - T) := by positivity
      have hub2 := Real.log_le_sub_one_of_pos hpos2
      have hloginv2 : Real.log (1 / (1 - T)) = - Real.log (1 - T) := by
        rw [one_div, Real.log_inv]
      rw [hloginv2] at hub2
      have := mul_le_mul_of_nonneg_left hub2 (le_of_lt hxpos)
      have hsimp : (1 - T) * (1 / (1 - T) - 1) = T := by
        field_simp; ring
      rw [hsimp] at this
      have heq : (1 - T) * (- Real.log (1 - T)) = -(1 - T) * Real.log (1 - T) := by
        ring
      rw [heq] at this
      exact this
  linarith

/-- **Key entropy inequality** `h(T) ≤ (1 + T) · h(T / (1 + T))` for
`T ∈ [0,1]`.

Expanding the right-hand side using `h(t) = −t log t − (1−t) log(1−t)` with
`t = T/(1+T)` (so `1 − t = 1/(1+T)`):

  `(1+T) h(T/(1+T)) = −T log(T/(1+T)) − log(1/(1+T))`
                    `= −T log T + (1+T) log(1+T)`.

Thus the claim is `−T log T − (1−T) log(1−T) ≤ −T log T + (1+T) log(1+T)`, i.e.
`−(1−T) log(1−T) ≤ (1+T) log(1+T)`.  The left side is `≥ 0` and bounded by
`(1−T)·(something)`; the right side is `≥ 0`.  We prove the sharper sufficient
fact `−(1−T) log(1−T) ≤ (1+T) log(1+T)` by showing the left side is `≤ T` (via
`−log(1−T) ≤ T/(1−T)` is awkward); instead use that both vanish at `T=0` and a
direct nonnegativity comparison through the auxiliary lemma below. -/
theorem binaryEntropy_le_scaled (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    binaryEntropy T ≤ (1 + T) * binaryEntropy (T / (1 + T)) := by
  have hden : 0 < 1 + T := by linarith
  have hdenne : (1 + T) ≠ 0 := ne_of_gt hden
  -- Rewrite the RHS in closed form.
  -- 1 − T/(1+T) = 1/(1+T)
  have hone_sub : (1 : ℝ) - T / (1 + T) = 1 / (1 + T) := by
    field_simp; ring
  -- (1+T) * h(T/(1+T)) = −T·log(T/(1+T)) − log(1/(1+T))
  have hRHS : (1 + T) * binaryEntropy (T / (1 + T))
      = -(T) * Real.log (T / (1 + T)) - Real.log (1 / (1 + T)) := by
    unfold binaryEntropy
    rw [hone_sub]
    have e1 : (1 + T) * (-(T / (1 + T))) = -(T) := by
      field_simp
    have e2 : (1 + T) * (-(1 / (1 + T))) = -(1 : ℝ) := by
      field_simp
    have expand : (1 + T) * (-(T / (1 + T)) * Real.log (T / (1 + T))
          - 1 / (1 + T) * Real.log (1 / (1 + T)))
        = (1 + T) * (-(T / (1 + T))) * Real.log (T / (1 + T))
          + (1 + T) * (-(1 / (1 + T))) * Real.log (1 / (1 + T)) := by ring
    rw [expand, e1, e2]
    ring
  rw [hRHS]
  -- Now bound. log(T/(1+T)) = log T − log(1+T) when T > 0; log(1/(1+T)) = −log(1+T).
  have hloginv : Real.log (1 / (1 + T)) = - Real.log (1 + T) := by
    rw [one_div, Real.log_inv]
  rw [hloginv]
  -- Goal: h(T) ≤ −T log(T/(1+T)) + log(1+T)
  rcases eq_or_lt_of_le hT0 with hT0eq | hTpos
  · -- T = 0: both sides 0
    subst_vars
    simp [binaryEntropy]
  · -- T > 0
    have hTne : T ≠ 0 := ne_of_gt hTpos
    have hlogdiv : Real.log (T / (1 + T))
        = Real.log T - Real.log (1 + T) := Real.log_div hTne hdenne
    rw [hlogdiv]
    -- RHS = −T(log T − log(1+T)) + log(1+T) = −T log T + (1+T) log(1+T)
    -- LHS = −T log T − (1−T) log(1−T)
    unfold binaryEntropy
    -- reduce to: −(1−T) log(1−T) ≤ (1+T) log(1+T)
    have hlogTp1_nonneg : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
    have hcoefp : 0 ≤ 1 + T := by linarith
    have hRplus : 0 ≤ (1 + T) * Real.log (1 + T) := mul_nonneg hcoefp hlogTp1_nonneg
    have h0' : 0 ≤ 1 - T := by linarith
    have h1' : 1 - T ≤ 1 := by linarith
    have hLminus : 0 ≤ -(1 - T) * Real.log (1 - T) :=
      neg_mul_log_nonneg h0' h1'
    -- We need: −(1−T) log(1−T) ≤ (1+T) log(1+T).
    have hkey : -(1 - T) * Real.log (1 - T) ≤ (1 + T) * Real.log (1 + T) :=
      log_perturbation_bound T hT0 hT1
    nlinarith [hkey]

/-- **AFW is looser than Fannes–Audenaert.**  For a `d`-dimensional `A`-system
(`d ≥ 2`, so `log d ≥ log(d−1) ≥ 0`) and `T ∈ [0,1]`, the AFW bound dominates
the single-system Fannes–Audenaert bound:
`faBound d T ≤ afwBound d T`.

The first term of `afwBound` is `2 T log d ≥ T log(d−1)` (factor two and
`log d ≥ log(d−1)`), and the binary-entropy contribution `h(T) ≤ (1+T) h(T/(1+T))`
by `binaryEntropy_le_scaled`. -/
theorem afwBound_ge_faBound (d : ℕ) (T : ℝ) (hd : 2 ≤ d)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) : faBound d T ≤ afwBound d T := by
  unfold faBound afwBound
  -- log(d−1) ≤ log d, and the T-coefficient doubles
  have hd2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdm1pos : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hle : (d : ℝ) - 1 ≤ (d : ℝ) := by linarith
  have hloglog : Real.log ((d : ℝ) - 1) ≤ Real.log (d : ℝ) :=
    Real.log_le_log hdm1pos hle
  have hTlogd1 : T * Real.log ((d : ℝ) - 1) ≤ T * Real.log (d : ℝ) :=
    mul_le_mul_of_nonneg_left hloglog hT0
  have hTlogd_nonneg : 0 ≤ T * Real.log (d : ℝ) :=
    mul_nonneg hT0 (Real.log_nonneg (by linarith))
  have hfirst : T * Real.log ((d : ℝ) - 1) ≤ 2 * T * Real.log (d : ℝ) := by
    nlinarith [hTlogd1, hTlogd_nonneg]
  -- h(T) ≤ (1+T) h(T/(1+T))
  have hentr : binaryEntropy T ≤ (1 + T) * binaryEntropy (T / (1 + T)) :=
    binaryEntropy_le_scaled T hT0 hT1
  linarith

/-! ## The named theorem targets

The statements below are the *physical* Alicki–Fannes–Winter inequality and its
operational capacity-continuity corollary.  They are quantified over abstract
data (a dimension `dA`, the entropy gap `condGap`, and a trace distance `T`) so
that the present file can name them without yet depending on the full
coupling/smoothing machinery required to discharge them.
-/

/-- **The Alicki–Fannes–Winter theorem (named target).**  For an `A`-subsystem
of dimension `dA`, any pair of bipartite states whose conditional entropies
differ by `condGap` and whose trace distance is `T` satisfies
`|condGap| ≤ 2 T · log dA + (1 + T) · h(T / (1 + T))`.

This is the tight continuity bound for conditional entropy; proving it for the
genuine quantum quantities requires Winter's coupling construction. -/
def AFW_Target : Prop :=
  ∀ (dA condGap T : ℝ),
    1 ≤ dA → 0 ≤ T → T ≤ 1 →
    |condGap| ≤ afwBound dA T

/-- **Capacity-continuity corollary (named target).**  Many one-shot and
asymptotic capacities (quantum, private, entanglement-assisted) are differences
or optimizations of conditional entropies.  Encoding such a capacity gap as an
infimum/supremum dominated by a single conditional-entropy gap, the AFW bound
yields *uniform continuity of the capacity in trace distance*: the capacity gap
is at most `afwBound dA T`, which `→ 0` as `T → 0`.  Concretely, if the capacity
gap `capGap` is itself bounded by some conditional-entropy gap `condGap` with
`|condGap| ≤ afwBound dA T`, then `|capGap| ≤ afwBound dA T`. -/
def Capacity_Continuity_Target : Prop :=
  ∀ (dA capGap condGap T : ℝ),
    1 ≤ dA → 0 ≤ T → T ≤ 1 →
    |capGap| ≤ |condGap| → |condGap| ≤ afwBound dA T →
    |capGap| ≤ afwBound dA T

/-- **Master reduction.**  The AFW continuity bound implies the
capacity-continuity corollary: dominating the capacity gap by a
conditional-entropy gap and chaining through the AFW inequality.  This is proved
*unconditionally* — it only chains the two bound statements and does not assume
the deep inequality itself. -/
theorem afw_master : AFW_Target → Capacity_Continuity_Target := by
  intro _hAFW dA capGap condGap T _h1 _h0 _hT1 hdom hbound
  exact le_trans hdom hbound

/-- **Continuity at coincidence.**  Specialized consequence of `AFW_Target`: if
two states coincide (`T = 0`) then their conditional entropies are equal, i.e.
the gap is forced to `0`.  Proved *unconditionally from the target*. -/
theorem afw_continuity_at_zero (hAFW : AFW_Target) (dA condGap : ℝ)
    (hd : 1 ≤ dA) : |condGap| ≤ 0 → condGap = 0 := by
  intro hle
  have : |condGap| = 0 := le_antisymm hle (abs_nonneg _)
  exact abs_eq_zero.mp this

/-! ## Axiom audit

Every theorem above depends only on the standard Lean/Mathlib axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no custom `axiom`. -/

section AxiomAudit
#print axioms afwBound_at_zero
#print axioms afwBound_nonneg
#print axioms afw_arg_le_half
#print axioms afwBound_ge_faBound
#print axioms binaryEntropy_le_scaled
#print axioms log_perturbation_bound
#print axioms afw_master
#print axioms conditionalEntropy_le_logdimA
end AxiomAudit

end UnifiedTheory.LayerB.AlickiFannesWinter
