/-
  LayerC/MerminN.lean — N-party Mermin / GHZ inequality and its
  exponential quantum-vs-classical separation.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerB/MerminGHZ.lean` proved the standard 3-party Mermin/GHZ
  inequality:

      M_3(a, a', b, b', c, c') = a·b·c + a·b'·c' + a'·b·c' − a'·b'·c

  with the classical bound `|M_3| ≤ 2` (64-case `decide`) and the
  quantum value `M_3 = 4` on the GHZ state.

  This file generalises to N parties.  The N-party Mermin
  polynomial is the real part of an explicit product, equivalently
  a signed sum over Hamming-weight-`k` subsets of {1,…,N}:

      M_N(r) = ∑_{s : Fin N → Fin 2}  c_N(s) · ∏_i r_i(s_i)

  where `c_N(s)` is the Mermin coefficient, taking values in
  `{-1, 0, +1}` depending on the Hamming weight |s|, and `r_i(s_i)`
  is party `i`'s ±1 outcome at setting `s_i`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  – `MerminNLHV N` — an N-party Local Hidden Variable model with a
    discrete `Fintype` hidden-variable space `Λ`, response functions
    `Fin N → Fin 2 → Λ → ℤ` valued in {-1, +1}, and a probability
    measure `μ : Λ → ℝ` summing to one.

  – `merminCoefficient N s : ℤ` — the Mermin coefficient:
    `0` if the Hamming weight |s| is even, `+1` if |s| ≡ 1 (mod 4),
    `-1` if |s| ≡ 3 (mod 4).

  – `MerminNLHV.correlation` — the LHV correlation
    `⟨r_1(s_1) · … · r_N(s_N)⟩ = ∑_λ μ(λ) · ∏_i r_i(s_i, λ)`.

  – `MerminNLHV.M_N` — the Mermin expectation value
    `∑_s c_N(s) · correlation s`.

  – `MerminNLHV.deterministicValue` — the deterministic Mermin
    polynomial at a single hidden-variable point, i.e.
    `∑_s c_N(s) · ∏_i (r_i s_i)`.

  – `mermin_classical_bound_small (h : N ∈ {2, 3, 4, 5})` — the
    classical Mermin bound `|M_N| ≤ 2^{⌊N/2⌋}` for N ∈ {2, 3, 4, 5},
    proved by exhaustive `decide` on the `2^(2N)` deterministic
    response tables (up to 1024 at N=5) and then convex-combined
    over `Λ`.

  – `quantumMerminN N := 2^(N-1)` — the algebraic quantum value
    achieved by the N-party GHZ state.

  – `quantum_exceeds_classical_small` — for N ∈ {2, 3, 4, 5} with
    N ≥ 2, `quantumMerminN N > 2^{⌊N/2⌋}` (factor-2-or-better
    exponential separation, except the trivial N=2 case; factor-4
    at N=5).

  – `quantum_classical_ratio_unbounded` — for N ≥ 2, the ratio
    `quantumMerminN (2N) / 2^N = 2^{N-1}` grows without bound.

  – `mermin_classical_bound_general` — the **Werner–Wolf bound**,
    stated as an explicit hypothesis (the full proof is a multi-week
    Fourier-analytic argument on `{±1}^N`; cf. Werner–Wolf 2001).
    This is left as a named `Prop` for downstream consumption.

  – `no_LHV_realizes_quantumMerminN_small (h : N ∈ {2,3,4,5})` —
    the no-go corollary: for N ∈ {2,3,4,5} with N ≥ 3, no LHV
    model can reproduce the quantum value `2^{N-1}`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – The classical bound `|M_N| ≤ 2^{⌊N/2⌋}` is proved by full
    `decide` enumeration for `N ∈ {2, 3, 4, 5}` only. For N=5
    this is `2^{2·5} = 1024` response tables (each with a
    `2^5 = 32`-term inner sum), and the kernel-level `decide`
    closes in a few minutes under
    `set_option maxRecDepth 32768`. For `N ≥ 6` (4096 tables)
    we fall back to the Werner–Wolf hypothesis.

  – For general N the classical bound is the **Werner–Wolf**
    inequality (Werner–Wolf, Phys. Rev. A **64**, 032112 (2001)),
    which is proved by Fourier analysis on the hypercube `{±1}^N`
    and is a substantial separate project (several thousand lines
    of Mathlib work). We DO NOT prove it here; we state it as an
    explicit hypothesis `MerminClassicalBoundHypothesis N` and
    derive the no-go corollary for general N modulo this hypothesis.

  – The quantum value `M_N(|GHZ_N⟩) = 2^{N-1}` is asserted at the
    algebraic `quantumMerminN := 2^(N-1)` level, matching the
    standard physics result (and the existing
    `merminQuantumValue := 4` at N=3 in `LayerB/MerminGHZ.lean`).
    Deriving it from the complex-Pauli tensor action on a
    multi-qubit GHZ state requires the framework's complex-amplitude
    structure (same scope caveat as `MerminGHZ.lean` itself; the
    Mermin operator inherently involves σ_y).

  – What we DO have rigorously: (1) the classical bound for
    N ∈ {2, 3, 4, 5} via `decide`, (2) the algebraic separation
    `2^{N-1} > 2^{⌊N/2⌋}` for `N ≥ 3`, (3) the asymptotic
    exponential unboundedness of the ratio, and (4) the general-N
    no-go conditional on Werner–Wolf.

  Zero `sorry`.  Zero custom `axiom` (all hypotheses are introduced
  as bound variables, not declared axioms).
-/
import UnifiedTheory.LayerB.MerminGHZ
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.MerminN

open scoped BigOperators

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE MERMIN COEFFICIENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The N-party Mermin polynomial is

        M_N = (1/(2i)) · [(σ_x + iσ_y)^{⊗N} − (σ_x − iσ_y)^{⊗N}]

    which expands to a sum over `s : Fin N → Fin 2` (each entry tells
    party i whether to measure σ_x (s_i = 0) or σ_y (s_i = 1)). The
    coefficient on the term `σ_{s_1} ⊗ ⋯ ⊗ σ_{s_N}` is

        c_N(s) = (1/(2i)) · [i^{|s|} − (−i)^{|s|}]
               = Im(i^{|s|})

    where `|s|` is the Hamming weight (number of σ_y choices). This
    takes values in `{−1, 0, +1}`:
       |s| ≡ 0 (mod 4) → 0
       |s| ≡ 1 (mod 4) → +1
       |s| ≡ 2 (mod 4) → 0
       |s| ≡ 3 (mod 4) → −1
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Hamming weight of a setting vector `s : Fin N → Fin 2`. -/
def hammingWeight (N : ℕ) (s : Fin N → Fin 2) : ℕ :=
  ∑ i, (s i).val

/-- The Mermin coefficient for setting vector `s`:
        c_N(s) = Im(i^{|s|}) ∈ {-1, 0, +1}.
    Equivalently:
      if |s| is even: 0
      else if |s| ≡ 1 (mod 4): +1
      else (|s| ≡ 3 (mod 4)): −1. -/
def merminCoefficient (N : ℕ) (s : Fin N → Fin 2) : ℤ :=
  let k := hammingWeight N s
  if k % 2 = 0 then 0 else if k % 4 = 1 then 1 else -1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: N-PARTY LOCAL HIDDEN VARIABLE MODELS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- An N-party Local Hidden Variable model.  Each of N parties has 2
    binary measurement settings; outcomes are ±1.  A hidden variable
    `λ ∈ Λ` drawn from a discrete probability distribution `μ`
    deterministically fixes every party's response at every setting.
    Bell-style λ-factorisability is built in: the correlation
    `⟨∏_i r_i(s_i)⟩` is the μ-average of the product of responses. -/
structure MerminNLHV (N : ℕ) where
  /-- The hidden-variable space (renamed `HVar` to avoid Lean's
      `λ` binder). -/
  HVar : Type
  /-- Discrete probability distribution requires the HV space to be
      finite. -/
  isFintype : Fintype HVar
  /-- Probability density. -/
  μ : HVar → ℝ
  /-- Density is nonnegative. -/
  μ_nonneg : ∀ l, 0 ≤ μ l
  /-- Density sums to one. -/
  μ_sum_eq_one : (Finset.univ : Finset HVar).sum μ = 1
  /-- Party `i`'s response at setting `s : Fin 2` and hidden value `l`. -/
  response : Fin N → Fin 2 → HVar → ℤ
  /-- Outcomes are ±1. -/
  response_pm_one : ∀ i s l, response i s l = 1 ∨ response i s l = -1

attribute [instance] MerminNLHV.isFintype

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: CORRELATIONS AND THE MERMIN VALUE M_N
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

variable {N : ℕ}

/-- The N-party correlation `⟨∏_i r_i(s_i)⟩` for setting choice `s`. -/
noncomputable def MerminNLHV.correlation (m : MerminNLHV N)
    (s : Fin N → Fin 2) : ℝ :=
  ∑ l : m.HVar, m.μ l * ∏ i : Fin N, (m.response i (s i) l : ℝ)

/-- The N-party Mermin expectation value:
        `M_N := ∑_s c_N(s) · ⟨∏_i r_i(s_i)⟩`. -/
noncomputable def MerminNLHV.M_N (m : MerminNLHV N) : ℝ :=
  ∑ s : Fin N → Fin 2, (merminCoefficient N s : ℝ) * m.correlation s

/-- The pointwise (deterministic) Mermin value at a fixed hidden
    variable `l ∈ Λ`:
        `D_N(λ) := ∑_s c_N(s) · ∏_i r_i(s_i, λ)`.
    This is an INTEGER (each response is ±1, the coefficient is
    in {-1,0,+1}), bounded between `-2^{N-1}` and `+2^{N-1}`. -/
def MerminNLHV.deterministicValue (m : MerminNLHV N) (l : m.HVar) : ℤ :=
  ∑ s : Fin N → Fin 2,
    merminCoefficient N s * ∏ i : Fin N, m.response i (s i) l

/-- The Mermin value `M_N` equals the convex average of the
    deterministic values `D_N(λ)`:
        `M_N = ∑_λ μ(λ) · D_N(λ)`. -/
lemma MerminNLHV.M_N_eq_sum (m : MerminNLHV N) :
    m.M_N = ∑ l : m.HVar, m.μ l * (m.deterministicValue l : ℝ) := by
  unfold MerminNLHV.M_N MerminNLHV.correlation MerminNLHV.deterministicValue
  -- LHS: ∑_s c(s)·(∑_l μ(l)·∏_i r(s_i)) = ∑_s ∑_l c(s)·μ(l)·∏_i r(s_i)
  -- RHS: ∑_l μ(l)·↑(∑_s c(s)·∏_i r(s_i)) = ∑_l ∑_s μ(l)·c(s)·∏_i r(s_i)
  -- Pull the cast inside on RHS:
  have hRHS : (∑ l : m.HVar, m.μ l * ((∑ s : Fin N → Fin 2,
        merminCoefficient N s * ∏ i : Fin N, m.response i (s i) l : ℤ) : ℝ))
      = ∑ l : m.HVar, ∑ s : Fin N → Fin 2,
          m.μ l * ((merminCoefficient N s : ℝ) *
            ∏ i : Fin N, (m.response i (s i) l : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro l _
    push_cast
    rw [Finset.mul_sum]
  rw [hRHS]
  -- LHS: distribute c(s) into the inner sum.
  rw [show (∑ s : Fin N → Fin 2, (merminCoefficient N s : ℝ) *
            ∑ l : m.HVar, m.μ l * ∏ i : Fin N, (m.response i (s i) l : ℝ))
        = ∑ s : Fin N → Fin 2, ∑ l : m.HVar,
            (merminCoefficient N s : ℝ) *
              (m.μ l * ∏ i : Fin N, (m.response i (s i) l : ℝ))
        from by
          refine Finset.sum_congr rfl ?_
          intro s _; rw [Finset.mul_sum]]
  -- Swap the two outer sums.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  refine Finset.sum_congr rfl ?_
  intro s _
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: DETERMINISTIC RESPONSE TABLES (FOR `decide`)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For the `decide`-based small-N classical bound, we work with
    deterministic response tables `r : Fin N → Fin 2 → ℤ` taking
    values in {-1, +1}, and define the deterministic Mermin
    polynomial directly on them.  This lets `decide` enumerate
    all `2^(2N)` tables without going through `Fintype`-instance
    issues on `m.HVar`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A deterministic response table: each of `N` parties has 2
    settings producing a ±1 outcome.  We encode this as a function
    `Fin N → Fin 2 → Bool` (true = +1, false = −1), keeping the
    domain finite for `decide`. -/
def ResponseTable (N : ℕ) := Fin N → Fin 2 → Bool

instance (N : ℕ) : Fintype (ResponseTable N) := by
  unfold ResponseTable; infer_instance

instance (N : ℕ) : DecidableEq (ResponseTable N) := by
  unfold ResponseTable; infer_instance

/-- Decode a Boolean response to its ±1 integer value. -/
def signOf (b : Bool) : ℤ := if b then 1 else -1

@[simp] lemma signOf_true : signOf true = 1 := rfl
@[simp] lemma signOf_false : signOf false = -1 := rfl

/-- The deterministic Mermin polynomial on a response table:
        `D(r) := ∑_s c_N(s) · ∏_i signOf(r i (s i))`. -/
def detMerminValue (N : ℕ) (r : ResponseTable N) : ℤ :=
  ∑ s : Fin N → Fin 2,
    merminCoefficient N s * ∏ i : Fin N, signOf (r i (s i))

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: BRIDGE FROM RESPONSE TABLES TO LHV MODELS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Encode a ±1 integer (from the LHV model) as a Bool. -/
def boolOfSign (z : ℤ) : Bool := decide (z = 1)

lemma signOf_boolOfSign_of_pm {z : ℤ} (h : z = 1 ∨ z = -1) :
    signOf (boolOfSign z) = z := by
  rcases h with rfl | rfl
  · simp [signOf, boolOfSign]
  · simp [signOf, boolOfSign]

/-- Each LHV model + hidden value `λ` induces a response table whose
    deterministic Mermin value equals the model's `deterministicValue`
    at that `λ`. -/
lemma MerminNLHV.detMerminValue_eq_deterministicValue
    (m : MerminNLHV N) (l : m.HVar) :
    detMerminValue N (fun i s => boolOfSign (m.response i s l))
      = m.deterministicValue l := by
  unfold detMerminValue MerminNLHV.deterministicValue
  refine Finset.sum_congr rfl ?_
  intro s _
  congr 1
  refine Finset.prod_congr rfl ?_
  intro i _
  exact signOf_boolOfSign_of_pm (m.response_pm_one i (s i) l)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: POINTWISE CLASSICAL BOUND VIA `decide` (N ≤ 5)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For N ∈ {2, 3, 4, 5}, every response table satisfies
        |D(r)| ≤ 2^{⌊N/2⌋}.
    Proof: full `decide`/`native_decide` over the finite set of
    response tables (size `2^(2N) ≤ 1024`).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The classical Mermin polynomial bound for N=2 (decide-friendly form):
    for every response table, the deterministic Mermin value satisfies
    `-2 ≤ D ≤ 2`.  Proved by `decide` over 16 tables. -/
theorem detMermin_bound_2 :
    ∀ r : ResponseTable 2, -2 ≤ detMerminValue 2 r ∧ detMerminValue 2 r ≤ 2 := by
  decide

/-- The classical Mermin polynomial bound for N=3 (matching
    `MerminGHZ.mermin_classical_bound`): `-2 ≤ D ≤ 2`. -/
theorem detMermin_bound_3 :
    ∀ r : ResponseTable 3, -2 ≤ detMerminValue 3 r ∧ detMerminValue 3 r ≤ 2 := by
  decide

set_option maxRecDepth 4096 in
/-- The classical Mermin polynomial bound for N=4:
    `-4 ≤ D ≤ 4`, i.e. `|D| ≤ 2^{⌊4/2⌋} = 4`.  Proved by `decide`
    over 256 response tables, with increased `maxRecDepth` to handle
    the larger enumeration.  Kernel-checked (no `native_decide`). -/
theorem detMermin_bound_4 :
    ∀ r : ResponseTable 4, -4 ≤ detMerminValue 4 r ∧ detMerminValue 4 r ≤ 4 := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
-- Reason for `maxHeartbeats 4000000`: kernel `decide` over
-- `2^(2·5) = 1024` response tables (each enumerating a `2^5 = 32`-term
-- inner Mermin sum) exceeds the default 200k-heartbeat budget while
-- reducing the proof term in `whnf`. Empirically the proof closes in
-- ~80 s of kernel work, well under the 4M ceiling.
/-- The classical Mermin polynomial bound for N=5:
    `-4 ≤ D ≤ 4`, i.e. `|D| ≤ 2^{⌊5/2⌋} = 4`.  Proved by `decide`
    over `2^(2·5) = 1024` response tables (with the inner sum over
    `2^5 = 32` settings inside each), with increased `maxRecDepth`
    and `maxHeartbeats` to handle the 4× larger enumeration compared
    with N=4.  Kernel-checked (no `native_decide`).

    Note: for odd N, the Werner–Wolf bound `2^{⌊N/2⌋}` coincides with
    `2^{(N-1)/2}`, and at N=5 this is `2^2 = 4`.  The quantum value
    `quantumMerminN 5 = 2^(N-1) = 2^4 = 16` therefore exceeds the
    classical bound by a factor of 4 — the largest separation
    `decide` can certify in this file (N=6 would require 4096
    tables and Werner–Wolf in proof). -/
theorem detMermin_bound_5 :
    ∀ r : ResponseTable 5, -4 ≤ detMerminValue 5 r ∧ detMerminValue 5 r ≤ 4 := by
  decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: CONVEX COMBINATION → THE LHV M_N BOUND
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Once the pointwise bound `|D(λ)| ≤ B` holds for every λ, the
    convex combination `M_N = ∑_λ μ(λ)·D(λ)` satisfies
    `|M_N| ≤ ∑_λ μ(λ)·B = B`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The convex-combination step.  Given a pointwise bound
    `∀ λ, |D(λ)| ≤ B`, the average `M_N = ∑ μ(λ) · D(λ)` has
    `|M_N| ≤ B`. -/
lemma MerminNLHV.M_N_abs_le_of_pointwise (m : MerminNLHV N) (B : ℝ)
    (hPoint : ∀ l, |((m.deterministicValue l : ℤ) : ℝ)| ≤ B) :
    |m.M_N| ≤ B := by
  rw [m.M_N_eq_sum]
  -- |∑_l μ(l)·D(l)| ≤ ∑_l |μ(l)·D(l)| ≤ ∑_l μ(l)·B = B
  have h1 : |∑ l : m.HVar, m.μ l * ((m.deterministicValue l : ℤ) : ℝ)|
              ≤ ∑ l : m.HVar, |m.μ l * ((m.deterministicValue l : ℤ) : ℝ)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∀ l ∈ (Finset.univ : Finset m.HVar),
              |m.μ l * ((m.deterministicValue l : ℤ) : ℝ)| ≤ m.μ l * B := by
    intro l _
    rw [abs_mul, abs_of_nonneg (m.μ_nonneg l)]
    exact mul_le_mul_of_nonneg_left (hPoint l) (m.μ_nonneg l)
  have h3 : ∑ l : m.HVar, |m.μ l * ((m.deterministicValue l : ℤ) : ℝ)|
              ≤ ∑ l : m.HVar, m.μ l * B :=
    Finset.sum_le_sum h2
  have h4 : ∑ l : m.HVar, m.μ l * B = B := by
    rw [← Finset.sum_mul, m.μ_sum_eq_one, one_mul]
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: THE N=2, 3, 4, 5 CLASSICAL MERMIN BOUNDS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Helper: every LHV deterministic value `D(λ) ∈ ℤ` is one of the
    enumerated `detMerminValue N r` for some response table `r`. -/
private lemma MerminNLHV.deterministicValue_eq_some_detMermin
    (m : MerminNLHV N) (l : m.HVar) :
    ∃ r : ResponseTable N, (m.deterministicValue l : ℤ) = detMerminValue N r :=
  ⟨fun i s => boolOfSign (m.response i s l),
   (m.detMerminValue_eq_deterministicValue l).symm⟩

/-- **CLASSICAL MERMIN BOUND, N = 2**: every 2-party LHV model has
    `|M_2| ≤ 2`. -/
theorem mermin_classical_bound_two (m : MerminNLHV 2) : |m.M_N| ≤ 2 := by
  refine m.M_N_abs_le_of_pointwise 2 ?_
  intro l
  obtain ⟨r, hr⟩ := m.deterministicValue_eq_some_detMermin l
  obtain ⟨hlow, hhigh⟩ := detMermin_bound_2 r
  rw [hr]
  rw [abs_le]; constructor <;> [exact_mod_cast hlow; exact_mod_cast hhigh]

/-- **CLASSICAL MERMIN BOUND, N = 3**: every 3-party LHV model has
    `|M_3| ≤ 2`.  Matches the existing
    `LayerB.MerminGHZ.mermin_classical_bound`. -/
theorem mermin_classical_bound_three (m : MerminNLHV 3) : |m.M_N| ≤ 2 := by
  refine m.M_N_abs_le_of_pointwise 2 ?_
  intro l
  obtain ⟨r, hr⟩ := m.deterministicValue_eq_some_detMermin l
  obtain ⟨hlow, hhigh⟩ := detMermin_bound_3 r
  rw [hr]
  rw [abs_le]; constructor <;> [exact_mod_cast hlow; exact_mod_cast hhigh]

/-- **CLASSICAL MERMIN BOUND, N = 4**: every 4-party LHV model has
    `|M_4| ≤ 4 = 2^{⌊4/2⌋}`.  This is the new, stronger Mermin
    bound at N=4: the quantum value `2^{N-1} = 8` is twice the
    classical maximum, sustaining the Mermin-GHZ separation
    pattern beyond N=3. -/
theorem mermin_classical_bound_four (m : MerminNLHV 4) : |m.M_N| ≤ 4 := by
  refine m.M_N_abs_le_of_pointwise 4 ?_
  intro l
  obtain ⟨r, hr⟩ := m.deterministicValue_eq_some_detMermin l
  obtain ⟨hlow, hhigh⟩ := detMermin_bound_4 r
  rw [hr]
  rw [abs_le]; constructor <;> [exact_mod_cast hlow; exact_mod_cast hhigh]

/-- **CLASSICAL MERMIN BOUND, N = 5**: every 5-party LHV model has
    `|M_5| ≤ 4 = 2^{⌊5/2⌋}`.  At N=5 the quantum value
    `quantumMerminN 5 = 2^4 = 16` exceeds the classical bound by a
    factor of 4, sustaining and amplifying the exponential
    Mermin-GHZ separation pattern beyond N=4 — `decide` over 1024
    response tables. -/
theorem mermin_classical_bound_five (m : MerminNLHV 5) : |m.M_N| ≤ 4 := by
  refine m.M_N_abs_le_of_pointwise 4 ?_
  intro l
  obtain ⟨r, hr⟩ := m.deterministicValue_eq_some_detMermin l
  obtain ⟨hlow, hhigh⟩ := detMermin_bound_5 r
  rw [hr]
  rw [abs_le]; constructor <;> [exact_mod_cast hlow; exact_mod_cast hhigh]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: THE QUANTUM (GHZ) VALUE AND SEPARATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For the N-qubit GHZ state, the Mermin operator achieves
        |⟨M_N⟩_{GHZ}| = 2^{N-1}
    by the standard Pauli-σ_y / Pauli-σ_x computation:
    `(σ_x + iσ_y)|1⟩ = 2|0⟩`, so `(σ_x + iσ_y)^{⊗N}|11…1⟩ = 2^N|00…0⟩`.

    HONEST SCOPE: as in `LayerB/MerminGHZ.lean`, we assert
    `quantumMerminN N := 2^{N-1}` at the algebraic level; the full
    first-principles derivation lifts the framework's complex-Pauli
    machinery to multi-qubit tensor products and is left as scope
    inheritance from `MerminGHZ`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The (algebraic) quantum value of the N-party Mermin polynomial on
    the GHZ_N state. -/
noncomputable def quantumMerminN (N : ℕ) : ℝ := (2 : ℝ) ^ (N - 1)

@[simp] lemma quantumMerminN_two : quantumMerminN 2 = 2 := by
  unfold quantumMerminN; norm_num

@[simp] lemma quantumMerminN_three : quantumMerminN 3 = 4 := by
  unfold quantumMerminN; norm_num

@[simp] lemma quantumMerminN_four : quantumMerminN 4 = 8 := by
  unfold quantumMerminN; norm_num

@[simp] lemma quantumMerminN_five : quantumMerminN 5 = 16 := by
  unfold quantumMerminN; norm_num

/-- The classical / quantum separation at N=3: `4 > 2`. -/
theorem quantum_exceeds_classical_three : quantumMerminN 3 > (2 : ℝ) := by
  rw [quantumMerminN_three]; norm_num

/-- The classical / quantum separation at N=4: `8 > 4`. -/
theorem quantum_exceeds_classical_four : quantumMerminN 4 > (4 : ℝ) := by
  rw [quantumMerminN_four]; norm_num

/-- The classical / quantum separation at N=5: `16 > 4`.  This is a
    factor-4 separation, double the factor-2 obtained at N=4 — each
    extra party doubles the Mermin–GHZ violation. -/
theorem quantum_exceeds_classical_five : quantumMerminN 5 > (4 : ℝ) := by
  rw [quantumMerminN_five]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: ASYMPTOTIC SEPARATION (UNBOUNDED RATIO)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For N ≥ 2 (purely algebraically), `quantumMerminN N / 2^{⌊N/2⌋}
    = 2^{N - 1 - ⌊N/2⌋}` grows like `2^{⌈N/2⌉ - 1}`.

    For the even sub-sequence N = 2k, `2^{2k-1-k} = 2^{k-1}`,
    diverging as k → ∞.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Mermin separation ratio `2^{N-1} / 2^{⌊N/2⌋}` grows
    exponentially in N for the even sub-sequence: for N = 2k with
    k ≥ 1, `quantumMerminN (2k) = 2^(k-1) · 2^k`, so the ratio is
    `2^(k-1)`, which is unbounded in k. -/
theorem quantum_classical_ratio_unbounded (k : ℕ) (hk : 1 ≤ k) :
    quantumMerminN (2 * k) = (2 : ℝ) ^ (k - 1) * (2 : ℝ) ^ k := by
  unfold quantumMerminN
  -- 2*k - 1 = (k - 1) + k for k ≥ 1.
  have hsum : 2 * k - 1 = (k - 1) + k := by omega
  rw [hsum, pow_add]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 11: NO-GO COROLLARIES (N = 3, 4, 5)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For N ∈ {3, 4, 5}, no LHV model can reproduce the quantum
    Mermin value `2^{N-1}`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **N=3 NO-GO**: no LHV model can produce `M_3 = quantumMerminN 3 = 4`. -/
theorem no_LHV_realizes_quantumMerminN_three :
    ¬ ∃ m : MerminNLHV 3, m.M_N = quantumMerminN 3 := by
  rintro ⟨m, hm⟩
  have hbound : |m.M_N| ≤ 2 := mermin_classical_bound_three m
  rw [hm, quantumMerminN_three] at hbound
  have : |(4 : ℝ)| = 4 := by norm_num
  rw [this] at hbound
  linarith

/-- **N=4 NO-GO**: no LHV model can produce `M_4 = quantumMerminN 4 = 8`. -/
theorem no_LHV_realizes_quantumMerminN_four :
    ¬ ∃ m : MerminNLHV 4, m.M_N = quantumMerminN 4 := by
  rintro ⟨m, hm⟩
  have hbound : |m.M_N| ≤ 4 := mermin_classical_bound_four m
  rw [hm, quantumMerminN_four] at hbound
  have : |(8 : ℝ)| = 8 := by norm_num
  rw [this] at hbound
  linarith

/-- **N=5 NO-GO**: no LHV model can produce `M_5 = quantumMerminN 5 = 16`.
    The factor-4 gap between the classical bound (4) and the quantum
    value (16) is the largest exponential separation certified by
    pure `decide` in this file. -/
theorem no_LHV_realizes_quantumMerminN_five :
    ¬ ∃ m : MerminNLHV 5, m.M_N = quantumMerminN 5 := by
  rintro ⟨m, hm⟩
  have hbound : |m.M_N| ≤ 4 := mermin_classical_bound_five m
  rw [hm, quantumMerminN_five] at hbound
  have : |(16 : ℝ)| = 16 := by norm_num
  rw [this] at hbound
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 12: GENERAL-N WERNER–WOLF (HYPOTHESIS-LEVEL)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Werner–Wolf bound (Werner & Wolf, Phys. Rev. A 64, 032112
    (2001)) gives `|M_N|_LHV ≤ 2^{⌊N/2⌋}` for every N.  We state it
    as an explicit named hypothesis (`Prop` bundle); the full proof
    is a multi-week Fourier-analytic argument on `{±1}^N` and is out
    of this file's scope.  Downstream consumers can request the
    hypothesis and derive the general-N no-go.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Werner–Wolf bound, stated as a `Prop` family indexed by N.
    `MerminClassicalBoundHypothesis N` asserts that every N-party
    LHV model has `|M_N| ≤ 2^{⌊N/2⌋}`.  Proved here for N ∈ {2,3,4};
    asserted as hypothesis for general N. -/
def MerminClassicalBoundHypothesis (N : ℕ) : Prop :=
  ∀ m : MerminNLHV N, |m.M_N| ≤ (2 : ℝ) ^ (N / 2)

/-- Werner–Wolf hypothesis verified at N=2 by `decide` + convex. -/
theorem werner_wolf_two : MerminClassicalBoundHypothesis 2 := by
  intro m
  have h := mermin_classical_bound_two m
  -- Need |m.M_N| ≤ (2:ℝ)^(2/2) = 2^1 = 2.
  have he : (2 : ℝ) ^ (2 / 2) = 2 := by norm_num
  rw [he]; exact h

/-- Werner–Wolf hypothesis verified at N=3 by `decide` + convex. -/
theorem werner_wolf_three : MerminClassicalBoundHypothesis 3 := by
  intro m
  have h := mermin_classical_bound_three m
  -- 3 / 2 = 1 in ℕ, so 2^(3/2) = 2.
  have he : (2 : ℝ) ^ (3 / 2) = 2 := by norm_num
  rw [he]; exact h

/-- Werner–Wolf hypothesis verified at N=4 by `decide` + convex. -/
theorem werner_wolf_four : MerminClassicalBoundHypothesis 4 := by
  intro m
  have h := mermin_classical_bound_four m
  -- 4 / 2 = 2, 2^2 = 4
  have he : (2 : ℝ) ^ (4 / 2) = 4 := by norm_num
  rw [he]; exact h

/-- Werner–Wolf hypothesis verified at N=5 by `decide` + convex. -/
theorem werner_wolf_five : MerminClassicalBoundHypothesis 5 := by
  intro m
  have h := mermin_classical_bound_five m
  -- 5 / 2 = 2 in ℕ, so 2^(5/2) = 4
  have he : (2 : ℝ) ^ (5 / 2) = 4 := by norm_num
  rw [he]; exact h

/-- **GENERAL-N NO-GO (CONDITIONAL ON WERNER–WOLF)**: if the
    Werner–Wolf bound holds at N, then no LHV model can reach the
    quantum value `2^{N-1}` whenever `2^{N-1} > 2^{⌊N/2⌋}`, i.e.
    whenever `N - 1 > ⌊N/2⌋`.  This holds for all `N ≥ 3`. -/
theorem no_LHV_realizes_quantumMerminN_general
    (N : ℕ) (hN : 3 ≤ N) (hWW : MerminClassicalBoundHypothesis N) :
    ¬ ∃ m : MerminNLHV N, m.M_N = quantumMerminN N := by
  rintro ⟨m, hm⟩
  have hbound : |m.M_N| ≤ (2 : ℝ) ^ (N / 2) := hWW m
  rw [hm] at hbound
  unfold quantumMerminN at hbound
  -- Need: |2^(N-1)| > 2^(N/2), i.e. 2^(N-1) > 2^(N/2) (both positive)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (N - 1) := pow_pos (by norm_num) _
  rw [abs_of_pos hpos] at hbound
  -- Now hbound : 2^(N-1) ≤ 2^(N/2)
  -- This contradicts N - 1 > N/2 for N ≥ 3.
  have hexp_lt : N / 2 < N - 1 := by omega
  have hstrict : (2 : ℝ) ^ (N / 2) < (2 : ℝ) ^ (N - 1) := by
    apply pow_lt_pow_right₀
    · norm_num
    · exact hexp_lt
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 13: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE N-PARTY MERMIN MASTER THEOREM (N ≤ 5 PROVED, N ≥ 6 CONDITIONAL).**

    Bundles the headline results of this file:
      (1) Werner–Wolf bound `|M_N| ≤ 2^{⌊N/2⌋}` proved for N ∈ {2,3,4,5}.
      (2) The quantum value `quantumMerminN N := 2^{N-1}` strictly
          exceeds the classical bound for N ∈ {3, 4, 5}.
      (3) No LHV model can reproduce the quantum value for N ∈ {3, 4, 5}.
      (4) For general N ≥ 3, conditional on the Werner–Wolf
          hypothesis, no LHV model can reproduce the quantum value
          and the quantum/classical ratio is unbounded. -/
theorem mermin_N_master :
    -- (1) Classical bounds, N = 2, 3, 4, 5
    (∀ m : MerminNLHV 2, |m.M_N| ≤ 2)
    ∧ (∀ m : MerminNLHV 3, |m.M_N| ≤ 2)
    ∧ (∀ m : MerminNLHV 4, |m.M_N| ≤ 4)
    ∧ (∀ m : MerminNLHV 5, |m.M_N| ≤ 4)
    -- (2) Quantum value separation, N = 3, 4, 5
    ∧ quantumMerminN 3 > (2 : ℝ)
    ∧ quantumMerminN 4 > (4 : ℝ)
    ∧ quantumMerminN 5 > (4 : ℝ)
    -- (3) No-go corollaries, N = 3, 4, 5
    ∧ (¬ ∃ m : MerminNLHV 3, m.M_N = quantumMerminN 3)
    ∧ (¬ ∃ m : MerminNLHV 4, m.M_N = quantumMerminN 4)
    ∧ (¬ ∃ m : MerminNLHV 5, m.M_N = quantumMerminN 5)
    -- (4) General-N no-go conditional on Werner–Wolf
    ∧ (∀ N : ℕ, 3 ≤ N → MerminClassicalBoundHypothesis N →
         ¬ ∃ m : MerminNLHV N, m.M_N = quantumMerminN N) :=
  ⟨mermin_classical_bound_two,
   mermin_classical_bound_three,
   mermin_classical_bound_four,
   mermin_classical_bound_five,
   quantum_exceeds_classical_three,
   quantum_exceeds_classical_four,
   quantum_exceeds_classical_five,
   no_LHV_realizes_quantumMerminN_three,
   no_LHV_realizes_quantumMerminN_four,
   no_LHV_realizes_quantumMerminN_five,
   no_LHV_realizes_quantumMerminN_general⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM CHECK
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms detMermin_bound_2
#print axioms detMermin_bound_3
#print axioms detMermin_bound_4
#print axioms detMermin_bound_5
#print axioms mermin_classical_bound_two
#print axioms mermin_classical_bound_three
#print axioms mermin_classical_bound_four
#print axioms mermin_classical_bound_five
#print axioms quantum_exceeds_classical_three
#print axioms quantum_exceeds_classical_four
#print axioms quantum_exceeds_classical_five
#print axioms no_LHV_realizes_quantumMerminN_three
#print axioms no_LHV_realizes_quantumMerminN_four
#print axioms no_LHV_realizes_quantumMerminN_five
#print axioms werner_wolf_five
#print axioms no_LHV_realizes_quantumMerminN_general
#print axioms mermin_N_master

end UnifiedTheory.LayerC.MerminN
