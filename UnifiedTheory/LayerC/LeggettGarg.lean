/-
  LayerC/LeggettGarg.lean — Leggett-Garg inequality and its quantum violation

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  The framework already formalises several "no-go" theorems for quantum
  mechanics in the spatial / structural directions:

    – `LayerB/BellTheorem.lean`              CHSH (spatial, 2-party)
    – `LayerB/SeparableCHSH.lean`            factorizable-CHSH classical bound
    – `LayerB/MerminGHZ.lean`                3-party Mermin-GHZ
    – `LayerC/...`                           Kochen-Specker (structural)

  This file adds the TEMPORAL no-go: the **Leggett-Garg inequality**,
  which constrains correlations of a single observable at successive
  times under the assumptions of (a) macroscopic realism per se and
  (b) noninvasive measurability.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  (1) `MRModel`: a structure encoding a macrorealistic model on three
      times — a fintype hidden-variable space `Λ`, a probability
      distribution `μ` on `Λ`, and a ±1-valued response function
      `Q : Fin 3 → Λ → ℤ`.

  (2) `MRModel.correlation` and `MRModel.K3` : the two-time correlator
      `C(t_i, t_j) = Σ μ(λ)·Q_i(λ)·Q_j(λ)` and the three-time
      Leggett-Garg quantity `K_3 = C(0,1) + C(1,2) − C(0,2)`.

  (3) `pointwise_K3_le_one` : for any ±1 triple `q : Fin 3 → ℤ`,
      `q 0·q 1 + q 1·q 2 − q 0·q 2 ≤ 1`. Combinatorial bound, proved
      by `decide`-style case analysis on the 8 possibilities.

  (4) `MRModel.K3_le_one` : **THE LEGGETT-GARG INEQUALITY.** Every
      macrorealistic model satisfies `K_3 ≤ 1`. Proved by integrating
      the pointwise bound against `μ`.

  (5) `quantumK3 = 2·cos(π/3) − cos(2π/3) = 3/2` : the quantum value
      at the optimal angle `ωτ = π/3` for a qubit with Hamiltonian
      `H = (ω/2) σ_z` measuring `Q = σ_z` in the state `(I + σ_x)/2`.

  (6) `quantumK3_eq_three_halves` : `quantumK3 = 3/2`, proved from
      `cos(π/3) = 1/2`, `cos(2π/3) = -1/2`, and arithmetic.

  (7) `quantumK3_violates_LG` : `1 < quantumK3` (i.e. 1 < 3/2).

  (8) `no_MR_realizes_quantum` : **THE LEGGETT-GARG NO-GO.** There is
      NO macrorealistic model whose K_3 equals the quantum value. Same
      shape as the CHSH-style "no LHV realises the singlet" theorems.

  (9) `leggett_garg_master` : bundle of (4)+(6)+(7)+(8) as a single
      citable conjunction.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – The classical bound (`MRModel.K3_le_one`) is proved at the abstract
    level: for ANY hidden-variable model with ±1 outcomes and a
    probability distribution, no matter how the dynamics is realised.
    This is the strongest possible "macrorealism" assumption.

  – The quantum value `quantumK3 = 3/2` is computed at the ANGLE
    level: the input is the formula `2·cos(ωτ) − cos(2ωτ)` evaluated
    at `ωτ = π/3`. We do NOT derive that formula here from the
    Hamiltonian / dephasing semigroup. Such a derivation would require
    a continuous-time correlation function on `DensityMatrix2Honest`,
    which the framework's `LayerB/LindbladDephasing` and
    `LayerB/LindbladContinuous` provide at the channel level but not
    yet as the explicit `Tr(ρ_0 · σ_z(t_1) · σ_z(t_2))` integrand. The
    formula `cos(ω(t_2 − t_1)) · e^{-Γ(t_2 − t_1)}` for the qubit
    two-time correlator is standard and matches the framework's
    dephasing semigroup with `Γ = 0`; we postulate it as the
    angle-level input to the no-go, exactly as the singlet correlation
    `-cos(θ_a − θ_b)` is the input to the CHSH no-go (cf.
    `LayerB/BellTheorem.bell_violation` style).

  – Three times, qubit observable. The standard `K_n` family (n ≥ 4)
    requires more cases in `pointwise_K3_le_one`; we stick to n = 3,
    which is the canonical Leggett-Garg form.

  – No custom axioms. Zero `sorry`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.LeggettGarg

open Real Finset

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: MACROREALIST MODELS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **A macrorealistic model** for a single observable at three times.

    `Λ` is the hidden-variable space (assumed finite for clean
    integration; the proof generalises to any probability space, but
    the finite case suffices for the no-go). `μ` is the probability
    distribution on `Λ`. `Q i λ ∈ {−1, +1}` is the (predetermined)
    value of the observable at time `t_i ∈ {t_0, t_1, t_2}` when the
    hidden variable is `λ`. Macrorealism = the value `Q i λ` is
    defined SIMULTANEOUSLY for all three times; noninvasive measurement
    = the value at time `t_j` does not change when `t_i` is also
    measured (this is the OPERATIONAL content; here it is BUILT IN by
    assigning a single `Q i λ` for each `i, λ`). -/
structure MRModel where
  /-- The hidden-variable space. -/
  Λ : Type
  /-- `Λ` is finite. -/
  fintype : Fintype Λ
  /-- `μ` is the probability density on `Λ`. -/
  μ : Λ → ℝ
  /-- `μ` is non-negative. -/
  μ_nonneg : ∀ l, 0 ≤ μ l
  /-- `μ` sums to 1. -/
  μ_sum : (∑ l, μ l) = 1
  /-- `Q i λ ∈ ℤ` is the predetermined value of the observable
      at time `t_i` given hidden variable `λ`. -/
  Q : Fin 3 → Λ → ℤ
  /-- `Q i λ ∈ {−1, +1}`. -/
  Q_pm : ∀ i l, Q i l = 1 ∨ Q i l = -1

attribute [instance] MRModel.fintype

/-- **Two-time correlator** `C(t_i, t_j) := Σ_λ μ(λ)·Q_i(λ)·Q_j(λ)`. -/
noncomputable def MRModel.correlation (m : MRModel) (i j : Fin 3) : ℝ :=
  ∑ l, m.μ l * (m.Q i l : ℝ) * (m.Q j l : ℝ)

/-- **The Leggett-Garg quantity** `K_3 := C(0,1) + C(1,2) − C(0,2)`. -/
noncomputable def MRModel.K3 (m : MRModel) : ℝ :=
  m.correlation 0 1 + m.correlation 1 2 - m.correlation 0 2

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: POINTWISE BOUND ON ±1 TRIPLES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Pointwise K_3 bound.** For any three numbers `q 0, q 1, q 2 ∈
    {−1, +1}`, the LG combination `q 0·q 1 + q 1·q 2 − q 0·q 2 ≤ 1`.

    Proof: 8 cases on `(q 0, q 1, q 2) ∈ {−1,+1}³`. In each case the
    expression evaluates to ±1, −3, −3, +1, +1, −3, −3, +1 (or
    permutation thereof); the maximum is exactly 1. -/
theorem pointwise_K3_le_one (q : Fin 3 → ℤ) (hq : ∀ i, q i = 1 ∨ q i = -1) :
    q 0 * q 1 + q 1 * q 2 - q 0 * q 2 ≤ 1 := by
  rcases hq 0 with h0 | h0 <;>
    rcases hq 1 with h1 | h1 <;>
      rcases hq 2 with h2 | h2 <;>
        · rw [h0, h1, h2]; decide

/-- **Companion lower bound** (not used in the no-go, but the natural
    counterpart): `−3 ≤ q 0·q 1 + q 1·q 2 − q 0·q 2`. The minimum is
    attained when two of the products are `−1` and the third is `+1`. -/
theorem pointwise_K3_ge_neg_three (q : Fin 3 → ℤ)
    (hq : ∀ i, q i = 1 ∨ q i = -1) :
    -3 ≤ q 0 * q 1 + q 1 * q 2 - q 0 * q 2 := by
  rcases hq 0 with h0 | h0 <;>
    rcases hq 1 with h1 | h1 <;>
      rcases hq 2 with h2 | h2 <;>
        · rw [h0, h1, h2]; decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE LEGGETT-GARG INEQUALITY K_3 ≤ 1
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A scalar identity used in the lift: for each `λ`,
    `μ(λ)·Q_0·Q_1 + μ(λ)·Q_1·Q_2 − μ(λ)·Q_0·Q_2
       = μ(λ)·(Q_0·Q_1 + Q_1·Q_2 − Q_0·Q_2)`. -/
private theorem μ_distrib (μ q01 q12 q02 : ℝ) :
    μ * q01 + μ * q12 - μ * q02 = μ * (q01 + q12 - q02) := by ring

/-- **K_3 written as a single sum over `λ`** of `μ(λ)·(...)`. -/
private theorem K3_sum_form (m : MRModel) :
    m.K3 = ∑ l, m.μ l *
      ((m.Q 0 l : ℝ) * (m.Q 1 l : ℝ)
        + (m.Q 1 l : ℝ) * (m.Q 2 l : ℝ)
        - (m.Q 0 l : ℝ) * (m.Q 2 l : ℝ)) := by
  unfold MRModel.K3 MRModel.correlation
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The pointwise bound, transported to the real numbers: for any
    `λ`, `Q_0·Q_1 + Q_1·Q_2 − Q_0·Q_2 ≤ 1` as reals. -/
private theorem pointwise_K3_le_one_real (m : MRModel) (l : m.Λ) :
    ((m.Q 0 l : ℝ) * (m.Q 1 l : ℝ)
      + (m.Q 1 l : ℝ) * (m.Q 2 l : ℝ)
      - (m.Q 0 l : ℝ) * (m.Q 2 l : ℝ))
    ≤ 1 := by
  have hq : ∀ i, m.Q i l = 1 ∨ m.Q i l = -1 := fun i => m.Q_pm i l
  have hint :
      m.Q 0 l * m.Q 1 l + m.Q 1 l * m.Q 2 l - m.Q 0 l * m.Q 2 l ≤ 1 :=
    pointwise_K3_le_one (fun i => m.Q i l) hq
  have : ((m.Q 0 l * m.Q 1 l + m.Q 1 l * m.Q 2 l
            - m.Q 0 l * m.Q 2 l : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by
    exact_mod_cast hint
  push_cast at this
  linarith

/-- **THE LEGGETT-GARG INEQUALITY.** Every macrorealistic model
    satisfies `K_3 ≤ 1`.

    Proof: write `K_3` as a single sum `Σ_λ μ(λ)·R(λ)` where
    `R(λ) = Q_0(λ)·Q_1(λ) + Q_1(λ)·Q_2(λ) − Q_0(λ)·Q_2(λ)`. By
    `pointwise_K3_le_one`, `R(λ) ≤ 1` pointwise. Since `μ(λ) ≥ 0`,
    `μ(λ)·R(λ) ≤ μ(λ)·1 = μ(λ)`. Summing and using `Σ μ = 1`
    gives `K_3 ≤ 1`. -/
theorem MRModel.K3_le_one (m : MRModel) : m.K3 ≤ 1 := by
  rw [K3_sum_form]
  -- Each summand bounded by μ(λ) using R(λ) ≤ 1 and μ(λ) ≥ 0.
  have h_each : ∀ l ∈ (Finset.univ : Finset m.Λ),
      m.μ l * ((m.Q 0 l : ℝ) * (m.Q 1 l : ℝ)
        + (m.Q 1 l : ℝ) * (m.Q 2 l : ℝ)
        - (m.Q 0 l : ℝ) * (m.Q 2 l : ℝ))
      ≤ m.μ l * 1 := by
    intro l _
    exact mul_le_mul_of_nonneg_left
      (pointwise_K3_le_one_real m l) (m.μ_nonneg l)
  -- Sum the pointwise bounds.
  have h_sum :
      (∑ l, m.μ l * ((m.Q 0 l : ℝ) * (m.Q 1 l : ℝ)
        + (m.Q 1 l : ℝ) * (m.Q 2 l : ℝ)
        - (m.Q 0 l : ℝ) * (m.Q 2 l : ℝ)))
      ≤ (∑ l, m.μ l * 1) :=
    Finset.sum_le_sum h_each
  -- Σ μ(l)·1 = Σ μ(l) = 1.
  have h_simp : (∑ l, m.μ l * (1 : ℝ)) = 1 := by
    simp [m.μ_sum]
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE QUANTUM VALUE AT ωτ = π/3
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The quantum K_3 value at the optimal angle ωτ = π/3.**

    Standard textbook derivation (e.g. Emary-Lambert-Nori 2014):
    for a qubit initially in `ρ_0 = (I + σ_x)/2` with Hamiltonian
    `H = (ω/2)·σ_z` and observable `Q = σ_z`, the two-time
    correlator is `C(t_i, t_j) = cos(ω·(t_j − t_i))`. Evenly spaced
    times `t_2 − t_1 = t_3 − t_2 = τ` give

        K_3 = cos(ωτ) + cos(ωτ) − cos(2ωτ) = 2·cos(ωτ) − cos(2ωτ).

    Maximising over `ωτ` (derivative `−2·sin(ωτ) + 2·sin(2ωτ) = 0`
    ⇒ `cos(ωτ) = 1/2` ⇒ `ωτ = π/3`) gives the maximum value below. -/
noncomputable def quantumK3 : ℝ :=
  2 * Real.cos (Real.pi / 3) - Real.cos (2 * Real.pi / 3)

/-- `cos(2π/3) = -cos(π/3)` (from `cos(π − x) = −cos x`). -/
theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -Real.cos (Real.pi / 3) := by
  have h : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub]

/-- **`quantumK3 = 3/2`.** From `cos(π/3) = 1/2` and
    `cos(2π/3) = −cos(π/3) = −1/2`:
    `2·(1/2) − (−1/2) = 1 + 1/2 = 3/2`. -/
theorem quantumK3_eq_three_halves : quantumK3 = 3 / 2 := by
  unfold quantumK3
  rw [cos_two_pi_div_three, Real.cos_pi_div_three]
  ring

/-- **THE QUANTUM VIOLATION.** `1 < quantumK3`, i.e. `1 < 3/2`. -/
theorem quantumK3_violates_LG : 1 < quantumK3 := by
  rw [quantumK3_eq_three_halves]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE LEGGETT-GARG NO-GO
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE LEGGETT-GARG NO-GO.** No macrorealistic model can reproduce
    the quantum K_3 value of 3/2.

    This is the temporal analogue of `BellTheorem.bell_violation` /
    `SeparableCHSH.singlet_correlations_not_factorizable` (spatial)
    and of the Kochen-Specker-style no-gos (structural). It rules out
    the possibility that quantum observables at successive times have
    predetermined ±1 values that are independent of measurement
    arrangement. -/
theorem no_MR_realizes_quantum :
    ¬ ∃ m : MRModel, m.K3 = quantumK3 := by
  rintro ⟨m, hm⟩
  have h1 : m.K3 ≤ 1 := m.K3_le_one
  have h2 : 1 < m.K3 := by rw [hm]; exact quantumK3_violates_LG
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: A WITNESS — THE EQUAL-WEIGHT TRIVIAL MR MODEL HAS K_3 = 1
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Showing the LG bound is TIGHT — there exists a macrorealistic
    model that saturates `K_3 = 1`. The simplest is the deterministic
    "always +1" model: one hidden variable, Q ≡ +1. Then
    C(i,j) = 1 for all i,j, and K_3 = 1 + 1 − 1 = 1.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The trivial macrorealistic model with one hidden value λ = ()
    and Q ≡ +1 at every time. -/
noncomputable def trivialMRModel : MRModel where
  Λ := Unit
  fintype := inferInstance
  μ _ := 1
  μ_nonneg _ := by norm_num
  μ_sum := by simp
  Q _ _ := 1
  Q_pm _ _ := Or.inl rfl

/-- The trivial MR model has every two-time correlator equal to 1. -/
theorem trivialMRModel_correlation (i j : Fin 3) :
    trivialMRModel.correlation i j = 1 := by
  unfold MRModel.correlation trivialMRModel
  simp

/-- **The trivial MR model saturates the LG bound** `K_3 = 1`. So the
    inequality `K_3 ≤ 1` is tight. -/
theorem trivialMRModel_K3 : trivialMRModel.K3 = 1 := by
  unfold MRModel.K3
  rw [trivialMRModel_correlation, trivialMRModel_correlation,
      trivialMRModel_correlation]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM (LEGGETT-GARG).** Bundled headline:

    (1) **LG inequality** — every macrorealistic model satisfies
        `K_3 ≤ 1`.
    (2) **Quantum value** — the qubit / dephasing-free quantum
        prediction at `ωτ = π/3` is `K_3 = 3/2`.
    (3) **Violation** — the quantum value exceeds the LG bound:
        `1 < 3/2`.
    (4) **No-go** — no macrorealistic model can produce the quantum
        value.
    (5) **Tightness** — the LG bound is achieved by the trivial
        "always +1" model. -/
theorem leggett_garg_master :
    -- (1) Classical LG bound
    (∀ m : MRModel, m.K3 ≤ 1)
    -- (2) Quantum value
    ∧ quantumK3 = 3 / 2
    -- (3) Quantum violates classical
    ∧ 1 < quantumK3
    -- (4) No macrorealistic model reproduces quantum
    ∧ (¬ ∃ m : MRModel, m.K3 = quantumK3)
    -- (5) Classical bound is tight
    ∧ trivialMRModel.K3 = 1 :=
  ⟨MRModel.K3_le_one,
   quantumK3_eq_three_halves,
   quantumK3_violates_LG,
   no_MR_realizes_quantum,
   trivialMRModel_K3⟩

end UnifiedTheory.LayerC.LeggettGarg
