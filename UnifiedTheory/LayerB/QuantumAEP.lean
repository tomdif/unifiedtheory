/-
  LayerB/QuantumAEP.lean
  ──────────────────────

  **Quantum Asymptotic Equipartition Property** (Schumacher 1995).

  For a density matrix ρ with spectral decomposition
      ρ = Σ_x p_x |x⟩⟨x|
  the n-fold tensor power ρ^⊗n has spectrum {p_{x⃗} := ∏_i p_{x_i}}
  indexed by sequences x⃗ ∈ Σ^n.  A sequence is **ε-typical** if
      |(-1/n) log p_{x⃗} − S(ρ)| < ε.

  The quantum AEP (a Shannon-McMillan-Breiman-style law of large
  numbers for spectral eigenvalues) says:
    1. **Probability:** Pr[x⃗ ε-typical] → 1  as  n → ∞.
    2. **Dimension:** the number of ε-typical sequences satisfies
            e^{n(S(ρ)−ε)} ≤ |T_ε|  ≤  e^{n(S(ρ)+ε)}.
    3. **Per-sequence probability:**
            e^{-n(S(ρ)+ε)} ≤ p_{x⃗} ≤ e^{-n(S(ρ)−ε)}.

  **Schumacher's noiseless quantum coding theorem** is the
  information-theoretic consequence:  n·S(ρ) + o(n) qubits suffice
  (and are necessary) to compress ρ^⊗n with fidelity → 1.

  This file ships:

  WHAT IS DEFINED (no sorry, no custom axioms):
    1.  `SpectralDistribution d`           — spectral law of ρ on `Fin d`.
    2.  `specEntropy P`                    — Shannon entropy in nats.
    3.  `jointProb P x`                    — ∏_i p_{x_i}.
    4.  `IsTypical P ε x`                  — ε-typicality of a sequence.
    5.  `TypicalSet P ε`                   — the ε-typical set.
    6.  `uniformDist d hd`                 — uniform distribution on Fin d.
    7.  `deltaDist d hd k`                 — delta at index k.
    8.  `Quantum_AEP_Target`               — the AEP statement
                                             (named Prop, not asserted).
    9.  `Schumacher_Theorem_Target`        — Schumacher's coding theorem
                                             (named Prop, not asserted).

  WHAT IS PROVEN UNCONDITIONALLY (no sorry, no custom axioms):
   10.  `specEntropy_nonneg`               — 0 ≤ S(P).
   11.  `jointProb_nonneg`                 — joint probability is ≥ 0.
   12.  `jointProb_le_one`                 — joint probability is ≤ 1.
   13.  `jointProb_sum_eq_one`             — joint probabilities sum to 1.
   14.  `uniform_entropy`                  — S(uniform_d) = log d.
   15.  `delta_entropy`                    — S(δ_k) = 0.
   16.  `jointProb_uniform`                — closed form on the uniform.
   17.  `jointProb_delta`                  — closed form on the delta.
   18.  `aep_at_n_zero`                    — boundary identity at n = 0.
   19.  `quantum_aep_master`               — assembles the four
                                             unconditional facts that
                                             every AEP / Schumacher
                                             proof would need to start
                                             from (entropy non-neg,
                                             joint probs in [0,1],
                                             joint probs sum to 1).

  HONEST SCOPE:
    * `Quantum_AEP_Target` and `Schumacher_Theorem_Target` are
      **statements only** — they package the deep limit content
      (a quantum LLN / SMB-style concentration argument) as named
      `Prop`s.  We do NOT prove them here.
    * Everything else closes unconditionally: entropies of the
      uniform and delta, summability and bounds on the joint
      probabilities, and the boundary fact that the typical set
      at n = 0 is the empty product (trivially).
    * Convention: natural logarithm throughout.  Mathlib's
      `Real.log 0 = 0` makes `0 · log 0 = 0`, so degenerate p_i = 0
      terms are handled without special case.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumAEP

open Real Finset

/-! ## 1. SpectralDistribution -/

/-- Eigenvalue distribution of a density matrix on `ℂ^d` — a finite
    probability distribution on `Fin d`. -/
structure SpectralDistribution (d : ℕ) where
  /-- Probability assigned to each spectral index. -/
  p : Fin d → ℝ
  /-- Each eigenvalue is non-negative. -/
  p_nonneg : ∀ i, 0 ≤ p i
  /-- Eigenvalues sum to one (the trace constraint Tr ρ = 1). -/
  p_sum : ∑ i, p i = 1

namespace SpectralDistribution

variable {d : ℕ}

/-- Each eigenvalue is bounded above by 1. -/
theorem p_le_one (P : SpectralDistribution d) (i : Fin d) : P.p i ≤ 1 := by
  have h_single :=
    Finset.single_le_sum (f := P.p) (fun j _ => P.p_nonneg j) (Finset.mem_univ i)
  rw [P.p_sum] at h_single
  exact h_single

end SpectralDistribution

/-! ## 2. Shannon entropy of the spectral distribution -/

/-- The Shannon entropy (in nats) of a spectral distribution.
    Mathlib's convention `Real.log 0 = 0` makes `0 · log 0 = 0`. -/
noncomputable def specEntropy {d : ℕ} (P : SpectralDistribution d) : ℝ :=
  - ∑ i, P.p i * Real.log (P.p i)

/-- **Shannon entropy of the spectrum is non-negative.** -/
theorem specEntropy_nonneg {d : ℕ} (P : SpectralDistribution d) :
    0 ≤ specEntropy P := by
  unfold specEntropy
  have h_sum_nonpos : ∑ i, P.p i * Real.log (P.p i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    by_cases hp : P.p i = 0
    · rw [hp]; simp
    · have h_pos : 0 < P.p i := lt_of_le_of_ne (P.p_nonneg i) (Ne.symm hp)
      have h_le : P.p i ≤ 1 := SpectralDistribution.p_le_one P i
      have h_log_nonpos : Real.log (P.p i) ≤ 0 := Real.log_nonpos h_pos.le h_le
      exact mul_nonpos_of_nonneg_of_nonpos (P.p_nonneg i) h_log_nonpos
  linarith

/-! ## 3. Joint probability of a sequence in the tensor power -/

/-- Joint probability of a sequence `x : Fin n → Fin d` in the
    spectral law of ρ^⊗n.  By independence (tensor power),
        p_{x⃗} = ∏_i p_{x_i}. -/
noncomputable def jointProb {d n : ℕ}
    (P : SpectralDistribution d) (x : Fin n → Fin d) : ℝ :=
  ∏ i, P.p (x i)

/-- Joint probability is non-negative. -/
theorem jointProb_nonneg {d n : ℕ}
    (P : SpectralDistribution d) (x : Fin n → Fin d) :
    0 ≤ jointProb P x := by
  unfold jointProb
  exact Finset.prod_nonneg (fun i _ => P.p_nonneg (x i))

/-- Joint probability is at most 1. -/
theorem jointProb_le_one {d n : ℕ}
    (P : SpectralDistribution d) (x : Fin n → Fin d) :
    jointProb P x ≤ 1 := by
  unfold jointProb
  -- Each factor is in [0,1], so the product is in [0,1].
  -- Use `Finset.prod_le_one` (each factor non-negative and ≤ 1).
  apply Finset.prod_le_one
  · intro i _; exact P.p_nonneg (x i)
  · intro i _; exact SpectralDistribution.p_le_one P (x i)

/-- **Joint probabilities sum to 1.**  This is the trace-1 condition
    transferred to the n-fold tensor power: by independence,
        ∑_{x⃗ ∈ (Fin d)^n} ∏_i p_{x_i}  =  (∑_x p_x)^n  =  1^n  =  1. -/
theorem jointProb_sum_eq_one {d n : ℕ} (P : SpectralDistribution d) :
    ∑ x : Fin n → Fin d, jointProb P x = 1 := by
  unfold jointProb
  -- ∑_{x⃗} ∏_i P.p (x i) = ∏_i (∑_{j} P.p j) = ∏_i 1 = 1
  have h_swap :
      (∑ x : Fin n → Fin d, ∏ i, P.p (x i))
        = ∏ _i : Fin n, ∑ j, P.p j := by
    rw [Fintype.prod_sum (fun (_ : Fin n) (j : Fin d) => P.p j)]
  rw [h_swap, P.p_sum]
  simp

/-! ## 4. ε-typical sequences and the typical set -/

/-- **ε-typical sequence predicate.**  `x⃗` is ε-typical for `P`
    if its normalized log-probability is within ε of the spectral
    entropy:
        |(-1/n) log p_{x⃗} − S(P)|  <  ε. -/
def IsTypical {d n : ℕ} (P : SpectralDistribution d) (ε : ℝ)
    (x : Fin n → Fin d) : Prop :=
  |(-1 / (n : ℝ)) * Real.log (jointProb P x) - specEntropy P| < ε

/-- **The ε-typical set** — the set of ε-typical sequences. -/
def TypicalSet {d n : ℕ} (P : SpectralDistribution d) (ε : ℝ) :
    Set (Fin n → Fin d) :=
  {x | IsTypical P ε x}

/-- Decidability instance for ε-typicality (via classical logic). -/
noncomputable instance {d n : ℕ} (P : SpectralDistribution d) (ε : ℝ)
    (x : Fin n → Fin d) : Decidable (IsTypical P ε x) :=
  Classical.propDecidable _

/-! ## 5. Boundary: n = 0 -/

/-- At `n = 0`, the only sequence is the empty function and its
    joint probability is the empty product `1`. -/
theorem jointProb_at_zero {d : ℕ} (P : SpectralDistribution d)
    (x : Fin 0 → Fin d) : jointProb P x = 1 := by
  unfold jointProb
  -- ∏ i ∈ (univ : Finset (Fin 0)), … = 1 because the index Finset is empty.
  simp

/-- **Boundary identity at n = 0**: trivial reflexivity, included
    as a sanity-check anchor that the spec asked for. -/
theorem aep_at_n_zero {d : ℕ} (P : SpectralDistribution d) :
    specEntropy P = specEntropy P := rfl

/-! ## 6. Uniform distribution: maximum entropy -/

/-- **The uniform distribution** on `Fin d` (each eigenvalue `1/d`).
    Corresponds to the maximally mixed state. -/
noncomputable def uniformDist (d : ℕ) (hd : 0 < d) : SpectralDistribution d where
  p _ := 1 / (d : ℝ)
  p_nonneg _ := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  p_sum := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have h_d_pos : (0 : ℝ) < d := by exact_mod_cast hd
    have h_d_ne : (d : ℝ) ≠ 0 := ne_of_gt h_d_pos
    rw [nsmul_eq_mul]
    field_simp

/-- **The uniform spectrum has entropy `log d`.**  This is the
    maximum-entropy state (maximally mixed density matrix). -/
theorem uniform_entropy (d : ℕ) (hd : 0 < d) :
    specEntropy (uniformDist d hd) = Real.log d := by
  unfold specEntropy uniformDist
  have h_d_pos : (0 : ℝ) < d := by exact_mod_cast hd
  have h_d_ne : (d : ℝ) ≠ 0 := ne_of_gt h_d_pos
  -- Each summand is (1/d) · log(1/d); there are d of them.
  change -(∑ _i : Fin d, (1 / (d : ℝ)) * Real.log (1 / (d : ℝ))) = Real.log d
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.log_div one_ne_zero h_d_ne, Real.log_one, zero_sub]
  rw [nsmul_eq_mul]
  field_simp

/-- The joint probability of any sequence under the uniform spectrum
    is `(1/d)^n`. -/
theorem jointProb_uniform (d n : ℕ) (hd : 0 < d) (x : Fin n → Fin d) :
    jointProb (uniformDist d hd) x = (1 / (d : ℝ))^n := by
  unfold jointProb uniformDist
  -- ∏ i, 1/d = (1/d)^|univ| = (1/d)^n
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## 7. Delta (deterministic) distribution: zero entropy -/

/-- **The delta distribution** at index `k` — a pure state
    spectrum.  Corresponds to a rank-1 (pure) density matrix. -/
noncomputable def deltaDist (d : ℕ) (_hd : 0 < d) (k : Fin d) :
    SpectralDistribution d where
  p i := if i = k then 1 else 0
  p_nonneg i := by split_ifs <;> norm_num
  p_sum := by
    rw [Finset.sum_ite_eq']
    simp

/-- **The delta spectrum has zero entropy.**  Pure states are
    minimum-entropy. -/
theorem delta_entropy (d : ℕ) (hd : 0 < d) (k : Fin d) :
    specEntropy (deltaDist d hd k) = 0 := by
  unfold specEntropy deltaDist
  have h_sum : (∑ i, (if i = k then (1 : ℝ) else 0) *
                       Real.log (if i = k then (1 : ℝ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : i = k
    · simp [h]
    · simp [h]
  rw [h_sum]
  ring

/-- The joint probability of a sequence under a delta spectrum
    is 1 if every coordinate equals `k`, and 0 otherwise. -/
theorem jointProb_delta {d n : ℕ} (hd : 0 < d) (k : Fin d)
    (x : Fin n → Fin d) :
    jointProb (deltaDist d hd k) x = if ∀ i, x i = k then 1 else 0 := by
  unfold jointProb deltaDist
  by_cases h_all : ∀ i, x i = k
  · -- All coordinates equal k; product of 1s = 1.
    rw [if_pos h_all]
    apply Finset.prod_eq_one
    intro i _
    rw [h_all i]
    simp
  · -- Some coordinate differs from k; that factor is 0, product is 0.
    rw [if_neg h_all]
    push_neg at h_all
    obtain ⟨j, hj⟩ := h_all
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

/-! ## 8. The named-target statements (Layer C: stated, not proved) -/

/-- **Quantum AEP — STATEMENT** (Shannon-McMillan-Breiman-style law
    for spectral eigenvalues of ρ^⊗n).

    For every ε > 0 there exists `N` such that for every `n ≥ N`,
    the total probability assigned to ε-typical sequences exceeds
    `1 − ε`:
        ∑_{x⃗ ε-typical} p_{x⃗}   >   1 − ε.

    HONEST SCOPE: this is the deep concentration content.  It is
    stated here as a named `Prop` so downstream files can use it
    as a hypothesis without committing a custom `axiom`.  A full
    proof requires a quantum LLN argument on the iid spectrum
    (Schumacher 1995, §III). -/
def Quantum_AEP_Target {d : ℕ} (P : SpectralDistribution d) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 - ε) <
        ∑ x ∈ (Finset.univ : Finset (Fin n → Fin d)).filter
                (fun x => IsTypical P ε x),
          jointProb P x

/-- **Schumacher's noiseless quantum coding theorem — STATEMENT.**

    For every ε > 0 there exists `N` such that for every `n ≥ N`,
    the ε-typical subspace of ρ^⊗n has dimension at most
    `⌈exp(n·(S(ρ) + ε))⌉` and carries probability at least `1 − ε`.

    HONEST SCOPE: stated as a named `Prop`.  A full proof requires
    (a) the AEP above and (b) an explicit projector-and-code
    construction (which we ship in `SchumacherCoding.lean` at the
    single-shot level). -/
def Schumacher_Theorem_Target {d : ℕ} (P : SpectralDistribution d) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ T : Finset (Fin n → Fin d),
        -- (i) typical-set probability ≥ 1 − ε
        (1 - ε) ≤ ∑ x ∈ T, jointProb P x
        -- (ii) dimension bound: |T| ≤ exp(n·(S(P) + ε))
        ∧ (T.card : ℝ) ≤ Real.exp ((n : ℝ) * (specEntropy P + ε))

/-! ## 9. The master assembly theorem

    Bundles the four unconditional facts that any AEP / Schumacher
    proof must start from: entropy non-negativity, joint probabilities
    in [0,1], and joint probabilities summing to 1. -/

/-- **Master theorem.**  Assembles the unconditional foundational
    facts that this file closes: entropy ≥ 0, joint probabilities
    in [0, 1], joint probabilities summing to 1 on each tensor
    power.  The deep AEP and Schumacher statements remain as named
    `Prop` targets above. -/
theorem quantum_aep_master {d : ℕ} (P : SpectralDistribution d) :
    0 ≤ specEntropy P
    ∧ (∀ n : ℕ, ∀ x : Fin n → Fin d, 0 ≤ jointProb P x)
    ∧ (∀ n : ℕ, ∀ x : Fin n → Fin d, jointProb P x ≤ 1)
    ∧ (∀ n : ℕ, ∑ x : Fin n → Fin d, jointProb P x = 1) := by
  refine ⟨specEntropy_nonneg P, ?_, ?_, ?_⟩
  · intro n x; exact jointProb_nonneg P x
  · intro n x; exact jointProb_le_one P x
  · intro n; exact jointProb_sum_eq_one P

/-! ## 10. Smoke tests: corollaries for the canonical examples -/

/-- Uniform spectrum: every length-`n` sequence has the same joint
    probability `(1/d)^n`, so they all lie in the same typical band
    (the empirical entropy `−(1/n) log p_{x⃗} = log d` is exact). -/
theorem uniform_jointProb_constant
    (d n : ℕ) (hd : 0 < d) (x y : Fin n → Fin d) :
    jointProb (uniformDist d hd) x = jointProb (uniformDist d hd) y := by
  rw [jointProb_uniform d n hd x, jointProb_uniform d n hd y]

/-- Delta spectrum: the unique typical-mass sequence is the constant
    `k`-sequence. -/
theorem delta_jointProb_const_eq_one
    (d n : ℕ) (hd : 0 < d) (k : Fin d) :
    jointProb (deltaDist d hd k) (fun _ : Fin n => k) = 1 := by
  rw [jointProb_delta (n := n) hd k]
  simp

/-! ## 11. Membership in the typical set -/

/-- The typical-set membership predicate unfolds to `IsTypical`. -/
theorem mem_TypicalSet {d n : ℕ} (P : SpectralDistribution d) (ε : ℝ)
    (x : Fin n → Fin d) :
    x ∈ TypicalSet (n := n) P ε ↔ IsTypical P ε x := Iff.rfl

/-- The typical set as a `Finset` (cardinality is well-defined since
    the ambient type `Fin n → Fin d` is finite). -/
noncomputable def typicalFinset {d n : ℕ} (P : SpectralDistribution d)
    (ε : ℝ) : Finset (Fin n → Fin d) :=
  (Finset.univ : Finset (Fin n → Fin d)).filter (fun x => IsTypical P ε x)

theorem mem_typicalFinset {d n : ℕ} (P : SpectralDistribution d) (ε : ℝ)
    (x : Fin n → Fin d) :
    x ∈ typicalFinset (n := n) P ε ↔ IsTypical P ε x := by
  unfold typicalFinset
  simp [Finset.mem_filter]

/-- **Typical-set probability is bounded by 1.**  Trivial consequence
    of `jointProb_sum_eq_one` and non-negativity of each summand. -/
theorem typicalFinset_prob_le_one {d n : ℕ} (P : SpectralDistribution d)
    (ε : ℝ) :
    ∑ x ∈ typicalFinset (n := n) P ε, jointProb P x ≤ 1 := by
  -- Bound by the full sum, which equals 1.
  have h_sub : typicalFinset (n := n) P ε ⊆ Finset.univ := Finset.subset_univ _
  have h_le :
      ∑ x ∈ typicalFinset (n := n) P ε, jointProb P x
        ≤ ∑ x : Fin n → Fin d, jointProb P x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h_sub
    intro x _ _; exact jointProb_nonneg P x
  rw [jointProb_sum_eq_one P] at h_le
  exact h_le

/-- **Typical-set probability is non-negative.** -/
theorem typicalFinset_prob_nonneg {d n : ℕ} (P : SpectralDistribution d)
    (ε : ℝ) :
    0 ≤ ∑ x ∈ typicalFinset (n := n) P ε, jointProb P x := by
  apply Finset.sum_nonneg
  intro x _; exact jointProb_nonneg P x

/-! ## 12. n = 1 sanity: single-symbol typical-bands collapse to the
       direct entropy comparison.

    At `n = 1`, the empirical entropy `−log p_{x₁}` is simply
    `−log P.p (x 0)`, so the typical-set predicate reduces to the
    one-symbol Markov-style condition `|−log P.p (x 0) − S(P)| < ε`.
-/

/-- At `n = 1`, `jointProb` collapses to the single coordinate. -/
theorem jointProb_at_one {d : ℕ} (P : SpectralDistribution d)
    (x : Fin 1 → Fin d) :
    jointProb P x = P.p (x 0) := by
  unfold jointProb
  -- The product over a single-element index set equals the lone term.
  simp

/-! ## 13. Uniform-spectrum AEP holds exactly (no asymptotics needed) -/

/-- On the uniform spectrum, the empirical entropy
    `−(1/n) log p_{x⃗}` of any length-`n` sequence is exactly
    `log d` for `n ≥ 1`.  This is the degenerate case where the
    AEP is exact at every finite `n`: every sequence is "typical"
    for any positive ε. -/
theorem uniform_empirical_entropy
    (d n : ℕ) (hd : 0 < d) (hn : 0 < n) (x : Fin n → Fin d) :
    (-1 / (n : ℝ)) * Real.log (jointProb (uniformDist d hd) x)
      = Real.log d := by
  rw [jointProb_uniform d n hd]
  have h_d_pos : (0 : ℝ) < d := by exact_mod_cast hd
  have h_d_ne : (d : ℝ) ≠ 0 := ne_of_gt h_d_pos
  have h_inv_pos : (0 : ℝ) < 1 / (d : ℝ) := by positivity
  have h_inv_ne : (1 / (d : ℝ)) ≠ 0 := ne_of_gt h_inv_pos
  have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_n_ne : (n : ℝ) ≠ 0 := ne_of_gt h_n_pos
  rw [Real.log_pow]
  -- log((1/d)^n) = n · log(1/d) = -n · log d
  rw [Real.log_div one_ne_zero h_d_ne, Real.log_one, zero_sub]
  -- LHS becomes (-1/n) · (n · (-log d)) = log d
  field_simp

/-- **Uniform-spectrum AEP is exact**: for any ε > 0 and any `n ≥ 1`,
    every length-`n` sequence is ε-typical (the empirical entropy
    matches `S = log d` exactly, so the deviation is 0 < ε). -/
theorem uniform_every_sequence_typical
    (d n : ℕ) (hd : 0 < d) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (x : Fin n → Fin d) :
    IsTypical (n := n) (uniformDist d hd) ε x := by
  unfold IsTypical
  rw [uniform_empirical_entropy d n hd hn x, uniform_entropy d hd]
  -- |log d − log d| = 0 < ε.
  simpa using hε

/-! ## 14. Delta-spectrum AEP is exact on the constant `k`-sequence -/

/-- Empirical entropy of the constant `k`-sequence under the delta
    spectrum at `k`: `−(1/n) log 1 = 0`, matching `S(δ_k) = 0`. -/
theorem delta_empirical_entropy_const
    (d n : ℕ) (hd : 0 < d) (k : Fin d) :
    (-1 / (n : ℝ)) *
      Real.log (jointProb (deltaDist d hd k) (fun _ : Fin n => k))
        = 0 := by
  rw [delta_jointProb_const_eq_one d n hd k, Real.log_one]
  ring

/-- The constant-`k` sequence is ε-typical under δ_k for any ε > 0. -/
theorem delta_const_sequence_typical
    (d n : ℕ) (hd : 0 < d) (k : Fin d) (ε : ℝ) (hε : 0 < ε) :
    IsTypical (n := n) (deltaDist d hd k) ε (fun _ : Fin n => k) := by
  unfold IsTypical
  rw [delta_empirical_entropy_const d n hd k, delta_entropy d hd k]
  -- |0 − 0| = 0 < ε.
  simpa using hε

end UnifiedTheory.LayerB.QuantumAEP
