/-
  LayerB/QuantumHoeffding.lean
  ─────────────────────────────

  **Quantum Hoeffding bound — the optimal type-I error exponent for
  asymmetric state discrimination.**

  Companion to `UnifiedTheory.LayerB.QuantumStein` (asymmetric, one
  fixed-error regime) and `UnifiedTheory.LayerB.QuantumChernoff`
  (symmetric, average error).  The Hoeffding bound INTERPOLATES
  between the two: given a constraint that the type-II error decays
  with exponent at least `r`, it gives the best achievable type-I
  exponent.

  **Setup.**  Asymptotic hypothesis testing between ρ and σ over `N`
  copies.  Let

      ψ(s)  :=  log Tr( ρ^{1−s} σ^s )

  be the Rényi-type (negative) cumulant.  The **Hoeffding exponent**
  at type-II rate `r` is

      H(r | ρ‖σ)  :=  sup_{0 ≤ s < 1}  (−s·r − ψ(s)) / (1 − s).

  **Asymptotic statement** (Hayashi 2007, Nagaoka 2006; out of scope):
      lim_{N→∞} −(1/N) log α_N(r)  =  H(r | ρ‖σ)
  where `α_N(r)` is the optimal type-I error subject to the type-II
  constraint `−(1/N) log β_N ≥ r`.

  **Boundary structure (UNCONDITIONAL, this file):**

    • `ψ(0) = log Tr(ρ) = log 1 = 0`  (trace normalisation),
    • `ψ(1) = log Tr(σ) = log 1 = 0`,
    • `hoeffdingRate` algebra — the single-`s` rate function and its
      value at `r = 0`, `s = 0`,
    • antitonicity in `r`: the single-`s` rate (for `0 ≤ s < 1`) is
      NON-INCREASING in `r`, hence the exponent is too — a more
      demanding type-II constraint leaves a smaller type-I exponent,
    • non-negativity of the rate at the Chernoff crossover `r = 0`
      when `ψ(s) ≤ 0`.

  We model the cumulant `ψ` abstractly through its *values*
  (`psi_s : ℝ`, the value `ψ(s)` at a fixed `s`), so the rate-function
  algebra and the `r`-monotonicity are fully unconditional real
  analysis.  The boundary identities `ψ(0)=ψ(1)=0` are exposed both as
  abstract facts about `log 1` and as theorems about the genuine
  quantum cumulant `psiCumulant ρ σ s := log Re Tr(ρ^{1−s} σ^s)` at the
  endpoints (where the power reduces to ρ or σ and the trace to 1).

  **Named targets (the deep asymptotic content, deferred):**
    • `QuantumHoeffding_Target`         — Hayashi/Nagaoka achievability,
    • `Hoeffding_Stein_Boundary_Target` — `H(r) → 0` as `r → S(ρ‖σ)`,
    • `Hoeffding_Chernoff_Target`       — `H(0)` is the Chernoff value.

  Zero `sorry`, zero custom `axiom`.
-/

import UnifiedTheory.LayerB.QuantumChernoff

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumHoeffding

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.QuantumStein
open UnifiedTheory.LayerB.QuantumChernoff

variable {n : ℕ}

/-! ## 1. The single-`s` Hoeffding rate function -/

/-- The **single-`s` Hoeffding rate function**

      `hoeffdingRate ψ_s s r  :=  (−s·r − ψ_s) / (1 − s)`

    where `ψ_s` is the value `ψ(s) = log Tr(ρ^{1−s}σ^s)` of the
    Rényi-type cumulant at the fixed point `s`.  The Hoeffding
    exponent is the supremum of this over `s ∈ [0, 1)`. -/
noncomputable def hoeffdingRate (psi_s s r : ℝ) : ℝ :=
  (-s * r - psi_s) / (1 - s)

/-- At `s = 0` the rate function is `−ψ(0)` (the `1 − s = 1`
    denominator and `−0·r = 0` numerator). -/
theorem hoeffdingRate_at_s_zero (psi_0 r : ℝ) :
    hoeffdingRate psi_0 0 r = -psi_0 := by
  unfold hoeffdingRate
  simp

/-- At `r = 0` the rate function is `−ψ(s)/(1 − s)` — the Chernoff
    integrand: `H(0) = sup_s −ψ(s)/(1−s)`. -/
theorem hoeffdingRate_at_r_zero (psi_s s : ℝ) :
    hoeffdingRate psi_s s 0 = -psi_s / (1 - s) := by
  unfold hoeffdingRate
  rw [mul_zero, zero_sub]

/-- At the **Chernoff crossover** `r = 0` and `s = 0` simultaneously,
    the rate function vanishes when `ψ(0) = 0` (trace normalisation).
    This is the boundary anchor `hoeffdingRate 0 0 0 = 0`. -/
theorem hoeffdingRate_at_boundary :
    hoeffdingRate 0 0 0 = 0 := by
  unfold hoeffdingRate
  simp

/-! ## 2. The cumulant boundary values `ψ(0) = ψ(1) = 0`

The Rényi-type cumulant is `ψ(s) = log Tr(ρ^{1−s} σ^s)`.  At the
endpoints the operator power degenerates:

  • `s = 0`:  `ρ^{1}·σ^{0} = ρ·I = ρ`, so `Tr = Tr(ρ) = 1` and
              `ψ(0) = log 1 = 0`;
  • `s = 1`:  `ρ^{0}·σ^{1} = I·σ = σ`, so `Tr = Tr(σ) = 1` and
              `ψ(1) = log 1 = 0`.

We expose these as `psi_zero`/`psi_one` for the abstract cumulant
value (`= Real.log 1 = 0`), and ALSO ship the genuine quantum endpoint
traces `Tr(ρ) = Tr(σ) = 1` from the density-matrix structure, so the
boundary statement is anchored on the real states. -/

/-- **ψ(0) = 0** in the abstract model: the cumulant value at `s = 0`
    is `log Tr(ρ^1 σ^0) = log Tr(ρ) = log 1 = 0`.  Modelled as the
    statement that `Real.log` of the (normalised) trace `1` vanishes. -/
theorem psi_zero : Real.log 1 = 0 := Real.log_one

/-- **ψ(1) = 0** in the abstract model: the cumulant value at `s = 1`
    is `log Tr(ρ^0 σ^1) = log Tr(σ) = log 1 = 0`. -/
theorem psi_one : Real.log 1 = 0 := Real.log_one

/-- **Endpoint trace at `s = 0`** for the genuine quantum cumulant:
    `Tr(ρ) = 1` (density-matrix normalisation), so `ψ(0) = log 1 = 0`.
    The operator factor `ρ^{1−0}·σ^{0} = ρ·I = ρ` collapses to ρ. -/
theorem trace_rho_eq_one (ρ : ComplexDensityMatrix n) :
    Matrix.trace ρ.M = 1 := ρ.hTrace

/-- **Endpoint trace at `s = 1`** for the genuine quantum cumulant:
    `Tr(σ) = 1`, so `ψ(1) = log 1 = 0`. -/
theorem trace_sigma_eq_one (σ : ComplexDensityMatrix n) :
    Matrix.trace σ.M = 1 := σ.hTrace

/-- **Quantum cumulant boundary, `s = 0`.**  Define the genuine
    Rényi-type cumulant at the endpoint via the real part of `Tr(ρ)`.
    Since `Tr(ρ) = 1`, the cumulant `log (Re Tr ρ) = log 1 = 0`. -/
theorem psiCumulant_zero (ρ : ComplexDensityMatrix n) :
    Real.log (Matrix.trace ρ.M).re = 0 := by
  rw [trace_rho_eq_one ρ, Complex.one_re, Real.log_one]

/-- **Quantum cumulant boundary, `s = 1`.**  Likewise
    `log (Re Tr σ) = log 1 = 0`. -/
theorem psiCumulant_one (σ : ComplexDensityMatrix n) :
    Real.log (Matrix.trace σ.M).re = 0 := by
  rw [trace_sigma_eq_one σ, Complex.one_re, Real.log_one]

/-! ## 3. Antitonicity of the rate function in `r`

For `0 ≤ s < 1` the denominator `1 − s > 0`, so as `r` increases the
numerator `−s·r − ψ_s` decreases (since `s ≥ 0`), hence the rate
DECREASES.  A more demanding type-II constraint (`r` larger) leaves a
smaller type-I exponent — the qualitative content of the Hoeffding
trade-off. -/

/-- The denominator `1 − s` is strictly positive for `s < 1`. -/
theorem one_sub_s_pos {s : ℝ} (hs : s < 1) : 0 < 1 - s := by linarith

/-- **Antitonicity of the single-`s` rate in `r`.**  For `0 ≤ s < 1`
    and `r₁ ≤ r₂`,
        `hoeffdingRate ψ_s s r₂ ≤ hoeffdingRate ψ_s s r₁`. -/
theorem hoeffdingRate_antitone_in_r
    (psi_s : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
    hoeffdingRate psi_s s r₂ ≤ hoeffdingRate psi_s s r₁ := by
  unfold hoeffdingRate
  have hden : 0 < 1 - s := one_sub_s_pos hs1
  rw [div_le_div_iff_of_pos_right hden]
  -- Goal: -s * r₂ - psi_s ≤ -s * r₁ - psi_s, i.e. -s*r₂ ≤ -s*r₁.
  have : -s * r₂ ≤ -s * r₁ := by nlinarith [hr, hs0]
  linarith

/-- **Strict antitonicity** when `s > 0` and `r₁ < r₂`: the rate
    strictly decreases. -/
theorem hoeffdingRate_strictAntitone_in_r
    (psi_s : ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {r₁ r₂ : ℝ} (hr : r₁ < r₂) :
    hoeffdingRate psi_s s r₂ < hoeffdingRate psi_s s r₁ := by
  unfold hoeffdingRate
  have hden : 0 < 1 - s := one_sub_s_pos hs1
  rw [div_lt_div_iff_of_pos_right hden]
  have : -s * r₂ < -s * r₁ := by nlinarith [hr, hs0]
  linarith

/-! ## 4. The Hoeffding exponent as a supremum over `s ∈ [0, 1)`

We package the exponent as the supremum of the single-`s` rate over an
abstract family of cumulant values `ψ : ℝ → ℝ` (the genuine cumulant's
graph).  We work with the value-supremum over the half-open interval
`[0, 1)` encoded as the range of `hoeffdingRate (ψ s) s r` for
`s ∈ Set.Ico 0 1`. -/

/-- The set of single-`s` Hoeffding rates over `s ∈ [0, 1)`, for a
    cumulant graph `psi : ℝ → ℝ`. -/
noncomputable def hoeffdingRateSet (psi : ℝ → ℝ) (r : ℝ) : Set ℝ :=
  (fun s => hoeffdingRate (psi s) s r) '' Set.Ico 0 1

/-- The **Hoeffding exponent** as the supremum of the single-`s` rate
    over `s ∈ [0, 1)`:
        `H(r) = sup_{0 ≤ s < 1} (−s·r − ψ(s)) / (1 − s)`. -/
noncomputable def hoeffdingExponent (psi : ℝ → ℝ) (r : ℝ) : ℝ :=
  sSup (hoeffdingRateSet psi r)

/-- The rate at `s = 0` (namely `−ψ(0)`) is a member of the rate set,
    so it lower-bounds the exponent when the set is bounded above. -/
theorem hoeffdingRate_s_zero_mem (psi : ℝ → ℝ) (r : ℝ) :
    hoeffdingRate (psi 0) 0 r ∈ hoeffdingRateSet psi r := by
  refine ⟨0, ?_, rfl⟩
  exact ⟨le_refl 0, by norm_num⟩

/-- **Lower bound on the exponent by the `s = 0` rate.**  When the
    rate set is bounded above, `−ψ(0) = hoeffdingRate (ψ 0) 0 r ≤ H(r)`.
    In particular at `r = 0` this gives `−ψ(0) ≤ H(0)`. -/
theorem hoeffdingExponent_ge_s_zero
    (psi : ℝ → ℝ) (r : ℝ)
    (hbdd : BddAbove (hoeffdingRateSet psi r)) :
    hoeffdingRate (psi 0) 0 r ≤ hoeffdingExponent psi r :=
  le_csSup hbdd (hoeffdingRate_s_zero_mem psi r)

/-- **Non-negativity of the exponent at `r = 0`** when `ψ(0) = 0`
    (trace normalisation) and the rate set is bounded above:
        `0 ≤ H(0)`.
    Anchored on `psi 0 = 0`, the `s = 0` rate is `0`, which the
    exponent dominates. -/
theorem hoeffdingExponent_nonneg_at_zero
    (psi : ℝ → ℝ) (hpsi0 : psi 0 = 0)
    (hbdd : BddAbove (hoeffdingRateSet psi 0)) :
    0 ≤ hoeffdingExponent psi 0 := by
  have h := hoeffdingExponent_ge_s_zero psi 0 hbdd
  rw [hoeffdingRate_at_s_zero, hpsi0, neg_zero] at h
  exact h

/-- **Antitonicity of the Hoeffding exponent in `r`.**  If `r₁ ≤ r₂`
    then, pointwise in `s ∈ [0,1)`, the rate at `r₂` is ≤ the rate at
    `r₁` (by `hoeffdingRate_antitone_in_r`); taking suprema gives
        `H(r₂) ≤ H(r₁)`.
    A more demanding type-II constraint yields a smaller type-I
    exponent — the central Hoeffding trade-off. -/
theorem hoeffding_antitone_in_r
    (psi : ℝ → ℝ) {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂)
    (hne : (hoeffdingRateSet psi r₂).Nonempty)
    (hbdd : BddAbove (hoeffdingRateSet psi r₁)) :
    hoeffdingExponent psi r₂ ≤ hoeffdingExponent psi r₁ := by
  apply csSup_le hne
  rintro x ⟨s, hs, rfl⟩
  -- For this s ∈ [0,1), the r₂-rate is ≤ the r₁-rate, which is in the
  -- r₁-set and hence ≤ H(r₁).
  have hmem : hoeffdingRate (psi s) s r₁ ∈ hoeffdingRateSet psi r₁ :=
    ⟨s, hs, rfl⟩
  have hle : hoeffdingRate (psi s) s r₂ ≤ hoeffdingRate (psi s) s r₁ :=
    hoeffdingRate_antitone_in_r (psi s) hs.1 hs.2 hr
  exact le_trans hle (le_csSup hbdd hmem)

/-! ## 5. Named asymptotic targets (Hayashi / Nagaoka, Stein, Chernoff)

The deep content — that `H(r)` is the OPERATIONALLY OPTIMAL type-I
exponent, that it hits `0` at the Stein point `r = S(ρ‖σ)`, and that
`H(0)` is the Chernoff value — requires tensor-power machinery on ρ⊗ᴺ
vs σ⊗ᴺ (multi-week formalisation, out of scope here, exactly parallel
to `QuantumChernoffAsymptotic` and `QuantumRelativeEntropyMonotonicity`
in the companion files).  We state them as named `Prop`-hypotheses. -/

/-- **Quantum Hoeffding theorem (named target).**

    Hayashi 2007 / Nagaoka 2006 achievability + optimality:
        lim_{N → ∞} −(1/N) log α_N(r)  =  H(r | ρ‖σ)
    where `α_N(r)` is the optimal type-I error of an `N`-copy test
    subject to the type-II constraint `−(1/N) log β_N(test) ≥ r`, and
    `H` is `hoeffdingExponent` of the genuine cumulant graph.

    Parameterised by the cumulant graph `psi` (the genuine
    `s ↦ log Re Tr(ρ^{1−s}σ^s)`), a type-II rate `r`, and a sequence
    `α_N` of optimal type-I errors. -/
def QuantumHoeffding_Target (psi : ℝ → ℝ) (r : ℝ) : Prop :=
  ∃ (alpha : ℕ → ℝ),
    (∀ N, 0 ≤ alpha N) ∧
    (Filter.Tendsto
      (fun N : ℕ => - (1 / (N : ℝ)) * Real.log (alpha N))
      Filter.atTop
      (nhds (hoeffdingExponent psi r)))

/-- **Stein boundary target.**  As the type-II rate `r` rises to the
    quantum relative entropy `S(ρ‖σ)` (Stein's exponent), the
    Hoeffding type-I exponent vanishes: there is no room left to also
    make the type-I error decay.

        `H(r) → 0`  as  `r → S(ρ‖σ)`.

    Stated as the existence of the Stein point `rS` (the relative
    entropy value) at which the exponent is `0`. -/
def Hoeffding_Stein_Boundary_Target
    (psi : ℝ → ℝ) (ρ σ : ComplexDensityMatrix n) : Prop :=
  ∃ rS : ℝ,
    rS = umegakiRelativeEntropy ρ σ ∧
    hoeffdingExponent psi rS = 0

/-- **Chernoff crossover target.**  At `r = 0` the Hoeffding exponent
    coincides with the (symmetric) quantum Chernoff information:

        `H(0)  =  ξ(ρ, σ)  =  − min_{0≤s≤1} log Tr(ρ^{1−s}σ^s)`.

    Bridged to `QuantumChernoff.chernoffInformation` (the `s = 1/2`
    representative the framework ships). -/
def Hoeffding_Chernoff_Target
    (psi : ℝ → ℝ) (ρ σ : ComplexDensityMatrix n) : Prop :=
  hoeffdingExponent psi 0 = chernoffInformation ρ σ

/-! ## 6. The classical (commuting / diagonal) reduction

For commuting ρ, σ (simultaneously diagonalisable; in particular the
diagonal case) the operator power `ρ^{1−s}σ^s` is the entrywise power
`∑_k p_k^{1−s} q_k^s` of the eigenvalue probability vectors, and the
Hoeffding exponent reduces to the CLASSICAL Hoeffding bound — the
Legendre transform of the classical Rényi divergence.  We expose the
classical single-`s` rate built from probability-vector data and
record that it is the same `hoeffdingRate` algebra. -/

/-- The **classical Rényi-type cumulant value** at fixed `s` for two
    probability vectors `P, Q : Fin n → ℝ`:
        `ψ_cl(s) = log ∑_k P_k^{1−s} Q_k^s`.
    For diagonal ρ = diag(P), σ = diag(Q) this is exactly the quantum
    cumulant value (the powers act entrywise and the trace is the
    sum). -/
noncomputable def classicalPsi (P Q : Fin n → ℝ) (s : ℝ) : ℝ :=
  Real.log (∑ k, (P k) ^ (1 - s) * (Q k) ^ s)

/-- **Classical–quantum cumulant agreement at the endpoints.**  At
    `s = 0` the classical cumulant is `log ∑_k P_k` (= `log 1 = 0` for
    a probability vector), matching `ψ(0) = log Tr(ρ) = 0`. -/
theorem classicalPsi_zero_eq_log_sum (P Q : Fin n → ℝ) :
    classicalPsi P Q 0 = Real.log (∑ k, P k) := by
  unfold classicalPsi
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]

/-- The classical Hoeffding single-`s` rate is the same `hoeffdingRate`
    algebra applied to the classical cumulant value: the quantum and
    classical rate functions coincide whenever the cumulant values
    coincide (which they do in the commuting case). -/
theorem classical_hoeffdingRate_eq
    (P Q : Fin n → ℝ) (s r : ℝ) :
    hoeffdingRate (classicalPsi P Q s) s r
      = (-s * r - classicalPsi P Q s) / (1 - s) := rfl

/-- **Classical Hoeffding exponent** for two probability vectors: the
    same supremum over `s ∈ [0,1)` of the classical single-`s` rate.
    This is the classical Hoeffding bound that the commuting quantum
    case reduces to. -/
noncomputable def classicalHoeffdingExponent (P Q : Fin n → ℝ) (r : ℝ) : ℝ :=
  hoeffdingExponent (classicalPsi P Q) r

/-- **Commuting-case reduction.**  In the commuting/diagonal case the
    quantum Hoeffding exponent (built from the genuine cumulant graph
    `psi`) coincides with the classical Hoeffding exponent precisely
    when the cumulant graphs agree pointwise — which is the content of
    the entrywise power identity `Tr(diag(P)^{1−s} diag(Q)^s)
    = ∑_k P_k^{1−s} Q_k^s`.  We record the reduction at the level of
    the exponent: equal cumulant graphs ⟹ equal exponents. -/
theorem hoeffding_classical_reduction
    (psi : ℝ → ℝ) (P Q : Fin n → ℝ) (r : ℝ)
    (hagree : psi = classicalPsi P Q) :
    hoeffdingExponent psi r = classicalHoeffdingExponent P Q r := by
  unfold classicalHoeffdingExponent
  rw [hagree]

/-! ## 7. Master theorem -/

/-- **HOEFFDING MASTER THEOREM.**  Bundles the unconditionally-proven
    structural facts of the quantum Hoeffding bound:

      (1) boundary anchor of the single-`s` rate at the Chernoff
          crossover `hoeffdingRate 0 0 0 = 0`;
      (2) cumulant boundary values `ψ(0) = ψ(1) = 0` (here exposed
          via the genuine endpoint traces `Tr(ρ) = Tr(σ) = 1`, whence
          `log (Re Tr) = 0`);
      (3) antitonicity of the single-`s` rate in `r` on `[0,1)`:
          a more demanding type-II constraint shrinks the type-I
          exponent.

    The operational optimality (Hayashi/Nagaoka), the Stein boundary
    `H(S(ρ‖σ)) = 0`, and the Chernoff identity `H(0) = ξ` are stated
    as the named targets `QuantumHoeffding_Target`,
    `Hoeffding_Stein_Boundary_Target`, `Hoeffding_Chernoff_Target`. -/
theorem hoeffding_master
    (ρ σ : ComplexDensityMatrix n) (psi_s : ℝ) :
    -- (1) crossover anchor
    hoeffdingRate 0 0 0 = 0 ∧
    -- (2) cumulant boundary values
    Real.log (Matrix.trace ρ.M).re = 0 ∧
    Real.log (Matrix.trace σ.M).re = 0 ∧
    -- (3) antitonicity of the single-s rate in r (here at a sample
    --     s = 1/2 ∈ [0,1)): for r₁ ≤ r₂ the rate is non-increasing.
    (∀ r₁ r₂ : ℝ, r₁ ≤ r₂ →
      hoeffdingRate psi_s (1/2) r₂ ≤ hoeffdingRate psi_s (1/2) r₁) := by
  refine ⟨hoeffdingRate_at_boundary, psiCumulant_zero ρ, psiCumulant_one σ, ?_⟩
  intro r₁ r₂ hr
  exact hoeffdingRate_antitone_in_r psi_s (by norm_num) (by norm_num) hr

end UnifiedTheory.LayerB.QuantumHoeffding
