/-
  LayerB/EntanglementOfFormation.lean — Wootters' entanglement of formation
  for two-qubit pure states.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  For a bipartite pure state |ψ⟩ ∈ H_A ⊗ H_B the **entanglement of
  formation** (Bennett–DiVincenzo–Smolin–Wootters 1996, Wootters 1998)
  is defined as the von Neumann entropy of the reduced density matrix
  ρ_A = Tr_B(|ψ⟩⟨ψ|):

      EoF(|ψ⟩) := S(ρ_A) = - Σ_k λ_k² · log(λ_k²)

  where {λ_k} are the Schmidt coefficients of |ψ⟩.  For a two-qubit pure
  state with Schmidt coefficients (λ_0, λ_1), λ_0² ≥ λ_1², and
  normalization λ_0² + λ_1² = 1, this collapses to the **binary entropy**

      EoF(|ψ⟩) = h(λ_0²) := - λ_0² log(λ_0²) - (1 - λ_0²) log(1 - λ_0²).

  **Wootters' formula** (1998) expresses EoF entirely in terms of the
  concurrence C:

      EoF(|ψ⟩) = h( (1 + √(1 - C²)) / 2 ).

  The two formulas are equivalent: from `C = 2 λ_0 λ_1` and the
  normalization `λ_0² + λ_1² = 1` we get

      (λ_0² - λ_1²)² = (λ_0² + λ_1²)² - 4 λ_0² λ_1²
                     = 1 - C²,

  so when λ_0² ≥ λ_1²,  λ_0² - λ_1² = √(1 - C²)  and therefore
  λ_0² = (1 + √(1 - C²)) / 2.  The two forms of h(·) then receive the
  same argument.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  – `binaryEntropy x := -x log x - (1-x) log(1-x)` — direct definition
    matching the QM/IT literature.
  – `binaryEntropy_eq_mathlib`         : agrees with `Real.binEntropy`.
  – `binaryEntropy_nonneg`             : h(x) ≥ 0 on [0, 1].
  – `binaryEntropy_le_log_two`         : h(x) ≤ log 2 (max at 1/2).
  – `binaryEntropy_zero`, `binaryEntropy_one`, `binaryEntropy_half`.
  – `binaryEntropy_one_sub`            : h(1-x) = h(x) (symmetry).
  – `eofViaSchmidt`                    : EoF in Schmidt form.
  – `eofViaConcurrence`                : EoF in Wootters/concurrence form.
  – `IsSchmidtNormalized`              : λ_0² + λ_1² = 1.
  – `wootters_arg_eq`                  : the **algebraic identity** that
                                        (1 + √(1 - C²)) / 2 = λ_0²
                                        under normalization + ordering.
  – `eof_schmidt_eq_concurrence`       : the Wootters EoF equivalence.
  – `eof_zero_iff_separable`           : EoF = 0 ⟺ ψ is separable.
  – `eof_singlet_eq_log_two`           : the singlet saturates the upper
                                        bound EoF = log 2 (= 1 bit).
  – `eof_master`                       : aggregator.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – Pure two-qubit states only.  Mixed-state EoF is Wootters' celebrated
    convex-roof construction using the spin-flipped density matrix; that
    is a substantial separate development and is out of scope.

  – Real amplitudes only, following the framework's convention
    (`TwoParticleState n := Matrix (Fin n) (Fin n) ℝ`).  The Schmidt
    decomposition and concurrence are already established in this
    convention by `SchmidtDecomposition.lean` and `Concurrence.lean`.

  – The "Schmidt normalisation" λ_0² + λ_1² = 1 is taken as an
    explicit hypothesis on the decomposition (`IsSchmidtNormalized`).
    It is the standard QM normalisation tr(ρ_A) = 1; for the singlet
    `singletDecomp` it is satisfied with both coefficients equal to
    1/√2.

  Zero `sorry`. Zero custom axioms.
-/

import UnifiedTheory.LayerB.Concurrence
import UnifiedTheory.LayerB.SchmidtDecomposition
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.EntanglementOfFormation

open UnifiedTheory.LayerB.Entanglement
open UnifiedTheory.LayerB.QuantumEntanglement
open UnifiedTheory.LayerB.SchmidtDecomposition
open UnifiedTheory.LayerB.BellTheorem
open UnifiedTheory.LayerB.Concurrence

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE BINARY ENTROPY FUNCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    h(x) := -x log x - (1 - x) log(1 - x), the Shannon entropy of a
    Bernoulli(x) random variable, in nats (natural log).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The **binary entropy function**:
    `binaryEntropy x := -x log x - (1 - x) log (1 - x)`.

    For x ∈ [0, 1] this is the Shannon entropy of a Bernoulli(x) variable
    (in nats).  Outside [0, 1] it agrees with Mathlib's `Real.binEntropy`
    by the convention `log p = log |p|`. -/
noncomputable def binaryEntropy (x : ℝ) : ℝ :=
  - x * Real.log x - (1 - x) * Real.log (1 - x)

/-- Our `binaryEntropy` equals Mathlib's `Real.binEntropy` everywhere.
    This lets us reuse Mathlib's entropy lemmas. -/
theorem binaryEntropy_eq_mathlib (x : ℝ) :
    binaryEntropy x = Real.binEntropy x := by
  unfold binaryEntropy Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  ring

/-- `binaryEntropy 0 = 0`. -/
@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  rw [binaryEntropy_eq_mathlib]
  exact Real.binEntropy_zero

/-- `binaryEntropy 1 = 0`. -/
@[simp] theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  rw [binaryEntropy_eq_mathlib]
  exact Real.binEntropy_one

/-- `binaryEntropy (1/2) = log 2`. -/
theorem binaryEntropy_half : binaryEntropy (1 / 2) = Real.log 2 := by
  rw [binaryEntropy_eq_mathlib]
  have h : (1 : ℝ) / 2 = (2 : ℝ)⁻¹ := by norm_num
  rw [h]
  exact Real.binEntropy_two_inv

/-- **Symmetry**: `h(1 - x) = h(x)`. -/
theorem binaryEntropy_one_sub (x : ℝ) :
    binaryEntropy (1 - x) = binaryEntropy x := by
  rw [binaryEntropy_eq_mathlib, binaryEntropy_eq_mathlib]
  exact Real.binEntropy_one_sub x

/-- **Non-negativity** on `[0, 1]`. -/
theorem binaryEntropy_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ binaryEntropy x := by
  rw [binaryEntropy_eq_mathlib]
  exact Real.binEntropy_nonneg hx0 hx1

/-- **Upper bound**: `h(x) ≤ log 2`, with equality iff `x = 1/2`. -/
theorem binaryEntropy_le_log_two (x : ℝ) :
    binaryEntropy x ≤ Real.log 2 := by
  rw [binaryEntropy_eq_mathlib]
  exact Real.binEntropy_le_log_two

/-- The bound `h(x) ≤ log 2` specialised to `[0, 1]` (matches the
    interface requested in the task spec). -/
theorem binaryEntropy_le_log_two_on_unitInterval
    (x : ℝ) (_hx0 : 0 ≤ x) (_hx1 : x ≤ 1) :
    binaryEntropy x ≤ Real.log 2 :=
  binaryEntropy_le_log_two x

/-- `binaryEntropy x > 0` for `x ∈ (0, 1)`. -/
theorem binaryEntropy_pos (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    0 < binaryEntropy x := by
  rw [binaryEntropy_eq_mathlib]
  exact Real.binEntropy_pos hx0 hx1

/-- `binaryEntropy x = 0` ⟺ `x ∈ {0, 1}`. -/
theorem binaryEntropy_eq_zero_iff (x : ℝ) :
    binaryEntropy x = 0 ↔ x = 0 ∨ x = 1 := by
  rw [binaryEntropy_eq_mathlib]
  exact Real.binEntropy_eq_zero

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: EOF VIA THE LARGER SCHMIDT EIGENVALUE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Given Schmidt coefficients (λ_0, λ_1) of a 2-qubit pure state with
    λ_0² ≥ λ_1², the reduced density matrix has eigenvalues (λ_0², λ_1²)
    and von Neumann entropy

        EoF(ψ) = - λ_0² log λ_0² - λ_1² log λ_1²
               = - λ_0² log λ_0² - (1 - λ_0²) log (1 - λ_0²)
               = h(λ_0²)

    (using normalisation λ_0² + λ_1² = 1 in the second line).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **EoF via the larger Schmidt eigenvalue**: as a function of `λ_0²`
    (the larger of the two squared Schmidt coefficients) this is just the
    binary entropy. -/
noncomputable def eofViaSchmidt (l0sq : ℝ) : ℝ := binaryEntropy l0sq

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: WOOTTERS FORMULA — EOF VIA CONCURRENCE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Wootters' celebrated formula:
        EoF(ψ) = h( (1 + √(1 - C²)) / 2 ).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **EoF via the concurrence** (Wootters 1998).  As a function of the
    concurrence C ∈ [0, 1] of a pure two-qubit state. -/
noncomputable def eofViaConcurrence (C : ℝ) : ℝ :=
  binaryEntropy ((1 + Real.sqrt (1 - C ^ 2)) / 2)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: SCHMIDT NORMALISATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The standard QM normalisation of a Schmidt decomposition is
        Σ_k λ_k² = 1
    (so that tr(ρ_A) = 1).  For two qubits this is λ_0² + λ_1² = 1.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A two-qubit Schmidt decomposition is **normalised** if its squared
    coefficients sum to 1.  This is the standard QM condition
    tr(ρ_A) = 1. -/
def IsSchmidtNormalized {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ) : Prop :=
  S.coeffs 0 ^ 2 + S.coeffs 1 ^ 2 = 1

/-- The singlet's canonical Schmidt decomposition is normalised. -/
theorem singletDecomp_isSchmidtNormalized :
    IsSchmidtNormalized singletDecomp := by
  unfold IsSchmidtNormalized
  rw [singletDecomp_coeffs 0, singletDecomp_coeffs 1]
  -- Goal: (1/√2)² + (1/√2)² = 1
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, sq]; rw [hsq]
  rw [h]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE WOOTTERS ALGEBRAIC IDENTITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    With  λ_0² + λ_1² = 1  and  C = 2 λ_0 λ_1  (and λ_0, λ_1 ≥ 0,
    λ_0² ≥ λ_1²),

        (1 + √(1 - C²)) / 2 = λ_0².

    Proof.  (λ_0² - λ_1²)² = (λ_0² + λ_1²)² - 4 λ_0² λ_1²
                          = 1 - C².
    Since λ_0² ≥ λ_1², √((λ_0² - λ_1²)²) = λ_0² - λ_1².
    Hence  √(1 - C²) = λ_0² - λ_1²,  and adding λ_0² + λ_1² = 1
    gives  1 + √(1 - C²) = 2 λ_0².
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The Wootters algebraic identity** at the level of bare reals.

    Given non-negative λ_0, λ_1 with λ_0² + λ_1² = 1 and λ_0² ≥ λ_1²,
    the Wootters argument simplifies:

        (1 + √(1 - (2 λ_0 λ_1)²)) / 2 = λ_0². -/
theorem wootters_arg_eq_real
    (l0 l1 : ℝ) (_hl0 : 0 ≤ l0) (_hl1 : 0 ≤ l1)
    (hnorm : l0 ^ 2 + l1 ^ 2 = 1)
    (hord : l1 ^ 2 ≤ l0 ^ 2) :
    (1 + Real.sqrt (1 - (2 * l0 * l1) ^ 2)) / 2 = l0 ^ 2 := by
  -- Step 1: 1 - (2 l0 l1)² = (l0² - l1²)².
  have hdiff_sq : 1 - (2 * l0 * l1) ^ 2 = (l0 ^ 2 - l1 ^ 2) ^ 2 := by
    have : (l0 ^ 2 - l1 ^ 2) ^ 2
         = (l0 ^ 2 + l1 ^ 2) ^ 2 - (2 * l0 * l1) ^ 2 := by ring
    rw [this, hnorm]; ring
  -- Step 2: l0² - l1² ≥ 0 (from hord).
  have hdiff_nn : 0 ≤ l0 ^ 2 - l1 ^ 2 := sub_nonneg.mpr hord
  -- Step 3: √((l0² - l1²)²) = l0² - l1².
  have hsqrt : Real.sqrt (1 - (2 * l0 * l1) ^ 2) = l0 ^ 2 - l1 ^ 2 := by
    rw [hdiff_sq]
    exact Real.sqrt_sq hdiff_nn
  -- Step 4: combine with normalisation.
  rw [hsqrt]
  -- Goal: (1 + (l0² - l1²)) / 2 = l0²
  -- Since l0² + l1² = 1, l1² = 1 - l0², so 1 + l0² - l1² = 2 l0².
  have hl1sq : l1 ^ 2 = 1 - l0 ^ 2 := by linarith
  rw [hl1sq]; ring

/-- **The Wootters algebraic identity** specialised to a SchmidtDecomp.

    For a normalised Schmidt decomposition of a two-qubit pure state
    with `S.coeffs 1 ^ 2 ≤ S.coeffs 0 ^ 2`, the Wootters argument equals
    the larger squared Schmidt coefficient. -/
theorem wootters_arg_eq
    {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ)
    (hnorm : IsSchmidtNormalized S)
    (hord : S.coeffs 1 ^ 2 ≤ S.coeffs 0 ^ 2) :
    (1 + Real.sqrt (1 - concurrence ψ ^ 2)) / 2 = S.coeffs 0 ^ 2 := by
  -- Rewrite concurrence via Schmidt: C = 2 λ_0 λ_1.
  rw [concurrence_via_schmidt S]
  -- Now goal: (1 + √(1 - (2 λ_0 λ_1)²)) / 2 = λ_0².
  exact wootters_arg_eq_real (S.coeffs 0) (S.coeffs 1)
          (S.coeffs_nonneg 0) (S.coeffs_nonneg 1) hnorm hord

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: WOOTTERS EQUIVALENCE — SCHMIDT FORM = CONCURRENCE FORM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Wootters equivalence** (the headline theorem).

    For a normalised Schmidt decomposition with the larger squared
    coefficient labelled `0`,

        eofViaSchmidt (λ_0²) = eofViaConcurrence (C(ψ)).

    Both are just `binaryEntropy` evaluated at the same number, by the
    algebraic identity `(1 + √(1 - C²)) / 2 = λ_0²`. -/
theorem eof_schmidt_eq_concurrence
    {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ)
    (hnorm : IsSchmidtNormalized S)
    (hord : S.coeffs 1 ^ 2 ≤ S.coeffs 0 ^ 2) :
    eofViaSchmidt (S.coeffs 0 ^ 2) = eofViaConcurrence (concurrence ψ) := by
  unfold eofViaSchmidt eofViaConcurrence
  rw [wootters_arg_eq S hnorm hord]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: EOF = 0 ⟺ SEPARABLE (via concurrence)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `eofViaConcurrence C = 0` ⟺ argument is 0 or 1 ⟺ C = 0
    (provided 0 ≤ C ≤ 1, which holds for any normalised state).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **EoF = 0 ⟺ concurrence = 0** (vanishing-EoF characterisation).

    Under the standard pure-state assumption 0 ≤ C ≤ 1, the Wootters EoF
    vanishes iff the concurrence vanishes.  Combined with
    `concurrence_eq_zero_iff_separable` from `Concurrence.lean` this is
    the statement "EoF = 0 ⟺ ψ is separable". -/
theorem eofViaConcurrence_eq_zero_iff_C_eq_zero
    (C : ℝ) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    eofViaConcurrence C = 0 ↔ C = 0 := by
  unfold eofViaConcurrence
  -- The argument of binaryEntropy.
  set x : ℝ := (1 + Real.sqrt (1 - C ^ 2)) / 2 with hx_def
  -- Frame: 1 - C² ∈ [0, 1].
  have hCsq_le_one : C ^ 2 ≤ 1 := by nlinarith
  have hCsq_nn : 0 ≤ C ^ 2 := sq_nonneg _
  have h1mCsq_nn : 0 ≤ 1 - C ^ 2 := by linarith
  have h1mCsq_le_one : 1 - C ^ 2 ≤ 1 := by linarith
  have hsqrt_nn : 0 ≤ Real.sqrt (1 - C ^ 2) := Real.sqrt_nonneg _
  have hsqrt_le_one : Real.sqrt (1 - C ^ 2) ≤ 1 := by
    have := Real.sqrt_le_sqrt h1mCsq_le_one
    rwa [Real.sqrt_one] at this
  -- x ∈ [1/2, 1].
  have hx_ge_half : (1 / 2 : ℝ) ≤ x := by
    rw [hx_def]; linarith [hsqrt_nn]
  have hx_le_one : x ≤ 1 := by
    rw [hx_def]; linarith [hsqrt_le_one]
  have hx_pos : 0 < x := by linarith [hx_ge_half]
  -- Now apply binaryEntropy_eq_zero_iff: x = 0 or x = 1.
  -- Since x > 0, only x = 1 is possible.
  constructor
  · intro heof
    rw [binaryEntropy_eq_zero_iff] at heof
    rcases heof with hx0 | hx1
    · exact absurd hx0 (ne_of_gt hx_pos)
    · -- x = 1 ⟹ √(1 - C²) = 1 ⟹ 1 - C² = 1 ⟹ C² = 0 ⟹ C = 0.
      have hsqrt1 : Real.sqrt (1 - C ^ 2) = 1 := by
        have : (1 + Real.sqrt (1 - C ^ 2)) / 2 = 1 := hx1
        linarith
      have h1mCsq_eq : 1 - C ^ 2 = 1 := by
        have h2 : Real.sqrt (1 - C ^ 2) ^ 2 = 1 - C ^ 2 :=
          Real.sq_sqrt h1mCsq_nn
        -- Substitute √(1 - C²) = 1 into h2 to get 1² = 1 - C².
        rw [hsqrt1] at h2
        -- h2 : 1 ^ 2 = 1 - C ^ 2
        linarith [h2]
      have hCsq : C ^ 2 = 0 := by linarith
      -- C² = 0 ⟹ C = 0.
      have habs : |C| = 0 := by
        have := sq_abs C
        nlinarith [sq_nonneg (|C|), abs_nonneg C, this, hCsq]
      exact abs_eq_zero.mp habs
  · intro hC
    -- C = 0 ⟹ √(1 - 0) = 1 ⟹ x = 1 ⟹ h(x) = 0.
    have : x = 1 := by
      rw [hx_def, hC]; simp [Real.sqrt_one]
    rw [this]
    exact binaryEntropy_one

/-- **EoF vanishes iff the state is separable** (the qualitative
    characterisation).  Combines
    `eofViaConcurrence_eq_zero_iff_C_eq_zero` with the concurrence-
    separability bridge from `Concurrence.lean`.

    Note: stated for normalised states (`IsNormalized ψ`) so that
    0 ≤ C(ψ) ≤ 1. -/
theorem eof_zero_iff_separable
    (ψ : TwoParticleState 2) (h : IsNormalized ψ) :
    eofViaConcurrence (concurrence ψ) = 0 ↔ IsQuantumSeparable ψ := by
  have hC_nn : 0 ≤ concurrence ψ := concurrence_nonneg ψ
  have hC_le_one : concurrence ψ ≤ 1 := concurrence_le_one_of_normalized ψ h
  rw [eofViaConcurrence_eq_zero_iff_C_eq_zero _ hC_nn hC_le_one]
  exact concurrence_eq_zero_iff_separable ψ

/-- **EoF vanishes iff concurrence vanishes** (the structural form, no
    normalisation hypothesis on ψ — the equivalence is purely about the
    real-valued functions, requiring only that the numeric argument C
    satisfy 0 ≤ C ≤ 1). -/
theorem eof_zero_iff_C_zero
    (ψ : TwoParticleState 2) (h : IsNormalized ψ) :
    eofViaConcurrence (concurrence ψ) = 0 ↔ concurrence ψ = 0 :=
  eofViaConcurrence_eq_zero_iff_C_eq_zero _
    (concurrence_nonneg ψ)
    (concurrence_le_one_of_normalized ψ h)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: THE SINGLET HAS EOF = log 2 (= 1 BIT)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The singlet is maximally entangled: its concurrence is 1 and
    EoF = h((1 + 0) / 2) = h(1/2) = log 2  (= 1 bit).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The singlet saturates the upper bound**: EoF(singlet) = log 2.

    Via the concurrence form: C(singlet) = 1, so
    `eofViaConcurrence 1 = h((1 + √0)/2) = h(1/2) = log 2`. -/
theorem eof_singlet_eq_log_two :
    eofViaConcurrence (concurrence (singletState : TwoParticleState 2)) = Real.log 2 := by
  rw [concurrence_singlet_eq_one]
  unfold eofViaConcurrence
  -- 1 - 1² = 0, √0 = 0, (1 + 0)/2 = 1/2.
  have h1 : (1 : ℝ) - (1 : ℝ) ^ 2 = 0 := by ring
  rw [h1, Real.sqrt_zero]
  have h2 : ((1 : ℝ) + 0) / 2 = 1 / 2 := by norm_num
  rw [h2]
  exact binaryEntropy_half

/-- **The singlet via the Schmidt form**: EoF(singlet) = h(1/2) = log 2,
    using the explicit singletDecomp with coefficients (1/√2, 1/√2). -/
theorem eof_singlet_via_schmidt :
    eofViaSchmidt ((singletDecomp.coeffs 0) ^ 2) = Real.log 2 := by
  unfold eofViaSchmidt
  rw [singletDecomp_coeffs 0]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, sq]; rw [hsq]
  rw [h]
  exact binaryEntropy_half

/-- The Wootters equivalence checked on the singlet — both forms produce
    `log 2`. -/
theorem eof_schmidt_eq_concurrence_singlet :
    eofViaSchmidt ((singletDecomp.coeffs 0) ^ 2)
      = eofViaConcurrence (concurrence (singletState : TwoParticleState 2)) := by
  rw [eof_singlet_via_schmidt, eof_singlet_eq_log_two]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: EOF BOUNDS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For any normalised pure two-qubit state,
        0 ≤ EoF(ψ) ≤ log 2.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **EoF non-negativity** (Wootters form): for any pure two-qubit state
    with concurrence in `[0, 1]`,  `EoF(ψ) ≥ 0`. -/
theorem eofViaConcurrence_nonneg
    (C : ℝ) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    0 ≤ eofViaConcurrence C := by
  unfold eofViaConcurrence
  have hCsq_nn : 0 ≤ C ^ 2 := sq_nonneg C
  have hCsq_le_one : C ^ 2 ≤ 1 := by nlinarith
  have h1mCsq_nn : 0 ≤ 1 - C ^ 2 := by linarith
  have hsqrt_nn : 0 ≤ Real.sqrt (1 - C ^ 2) := Real.sqrt_nonneg _
  have hsqrt_le_one : Real.sqrt (1 - C ^ 2) ≤ 1 := by
    have h1mCsq_le_one : 1 - C ^ 2 ≤ 1 := by linarith
    have := Real.sqrt_le_sqrt h1mCsq_le_one
    rwa [Real.sqrt_one] at this
  have hx_nn : 0 ≤ (1 + Real.sqrt (1 - C ^ 2)) / 2 := by linarith
  have hx_le_one : (1 + Real.sqrt (1 - C ^ 2)) / 2 ≤ 1 := by linarith
  exact binaryEntropy_nonneg _ hx_nn hx_le_one

/-- **EoF upper bound** (Wootters form): for any pure two-qubit state,
    `EoF(ψ) ≤ log 2`. -/
theorem eofViaConcurrence_le_log_two (C : ℝ) :
    eofViaConcurrence C ≤ Real.log 2 := by
  unfold eofViaConcurrence
  exact binaryEntropy_le_log_two _

/-- **EoF non-negativity** (Schmidt form): for any `x ∈ [0, 1]`,
    `eofViaSchmidt x ≥ 0`. -/
theorem eofViaSchmidt_nonneg
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ eofViaSchmidt x :=
  binaryEntropy_nonneg x hx0 hx1

/-- **EoF upper bound** (Schmidt form): `eofViaSchmidt x ≤ log 2`. -/
theorem eofViaSchmidt_le_log_two (x : ℝ) :
    eofViaSchmidt x ≤ Real.log 2 :=
  binaryEntropy_le_log_two x

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **ENTANGLEMENT OF FORMATION — WOOTTERS' PURE-STATE BUNDLE.**

    For real-amplitude pure two-qubit states, the entanglement of
    formation is

        EoF(ψ) = h(λ_0²)  =  h( (1 + √(1 - C(ψ)²)) / 2 ),

    where h is the binary entropy and λ_0² is the larger of the two
    squared Schmidt coefficients.  This file proves:

    (1) `binaryEntropy_nonneg`            : 0 ≤ h(x) for x ∈ [0, 1].
    (2) `binaryEntropy_le_log_two`        : h(x) ≤ log 2.
    (3) `binaryEntropy_half`              : h(1/2) = log 2.
    (4) `wootters_arg_eq`                 : the algebraic core
            (1 + √(1 - C²)) / 2 = λ_0² under λ_0² + λ_1² = 1, λ_1² ≤ λ_0².
    (5) `eof_schmidt_eq_concurrence`      : the Wootters equivalence
            eofViaSchmidt λ_0² = eofViaConcurrence C(ψ).
    (6) `eof_zero_iff_separable`          : qualitative — EoF = 0 ⟺ separable.
    (7) `eof_singlet_eq_log_two`          : the singlet saturates the bound.
    (8) `eofViaConcurrence_nonneg`        : 0 ≤ EoF for pure two-qubit ψ.
    (9) `eofViaConcurrence_le_log_two`    : EoF ≤ log 2 (= 1 bit).

    Honest scope: pure states only.  Mixed-state EoF (Wootters' convex
    roof on the spin-flipped density matrix) is a separate development. -/
theorem eof_master :
    -- (1) Non-negativity of h
    (∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ binaryEntropy x)
    -- (2) Upper bound of h
    ∧ (∀ x : ℝ, binaryEntropy x ≤ Real.log 2)
    -- (3) Maximum at 1/2
    ∧ binaryEntropy (1 / 2) = Real.log 2
    -- (4) Wootters algebraic identity at the real level
    ∧ (∀ (l0 l1 : ℝ), 0 ≤ l0 → 0 ≤ l1 →
        l0 ^ 2 + l1 ^ 2 = 1 → l1 ^ 2 ≤ l0 ^ 2 →
        (1 + Real.sqrt (1 - (2 * l0 * l1) ^ 2)) / 2 = l0 ^ 2)
    -- (5) Wootters equivalence (Schmidt = Concurrence)
    ∧ (∀ {ψ : TwoParticleState 2} (S : SchmidtDecomp ψ),
        IsSchmidtNormalized S →
        S.coeffs 1 ^ 2 ≤ S.coeffs 0 ^ 2 →
        eofViaSchmidt (S.coeffs 0 ^ 2) = eofViaConcurrence (concurrence ψ))
    -- (6) EoF = 0 ⟺ separable (for normalised ψ)
    ∧ (∀ ψ : TwoParticleState 2, IsNormalized ψ →
        (eofViaConcurrence (concurrence ψ) = 0 ↔ IsQuantumSeparable ψ))
    -- (7) Singlet has EoF = log 2
    ∧ eofViaConcurrence (concurrence (singletState : TwoParticleState 2))
      = Real.log 2
    -- (8) EoF ≥ 0 on pure two-qubit states (C ∈ [0, 1])
    ∧ (∀ C : ℝ, 0 ≤ C → C ≤ 1 → 0 ≤ eofViaConcurrence C)
    -- (9) EoF ≤ log 2 for all real C (the argument is always in [0, 1]
    -- and h is bounded everywhere)
    ∧ (∀ C : ℝ, eofViaConcurrence C ≤ Real.log 2) :=
  ⟨binaryEntropy_nonneg,
   fun x => binaryEntropy_le_log_two x,
   binaryEntropy_half,
   wootters_arg_eq_real,
   @eof_schmidt_eq_concurrence,
   eof_zero_iff_separable,
   eof_singlet_eq_log_two,
   eofViaConcurrence_nonneg,
   eofViaConcurrence_le_log_two⟩

end UnifiedTheory.LayerB.EntanglementOfFormation
