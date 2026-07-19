/-
  UnifiedTheory/LayerB/QuantumWalk.lean
  ──────────────────────────────────────

  **Grover's algorithm: reflections, oracle, diffusion, iteration.**

  Extends the quantum-computing pillar opened by
  `LayerB/UniversalGates.lean`.  Where `UniversalGates.lean` formalises
  the *finite* universal-gate scaffolding (gate sets, words,
  reachability) and the Pauli group, this file formalises the
  building blocks of the canonical *amplitude-amplification* quantum
  algorithm:

    1. The **uniform superposition** `|+⟩ = (1/√N) Σ_i |i⟩` on
       a database of `N` items.
    2. The **reflection** about a state `ψ`,
          `R_ψ := I − 2 |ψ⟩⟨ψ| / ⟨ψ|ψ⟩`,
       which is the involution that fixes `ψ`'s line and negates the
       orthogonal complement.
    3. The **Grover oracle** `O_t := R_{|t⟩}`, the reflection about
       the marked basis vector `|t⟩`.
    4. The **Grover diffusion operator** `D := R_{|+⟩}`, the reflection
       about the uniform superposition.
    5. The **Grover iteration**
          `G := − O_t · D`,
       which rotates the state in the 2-D Grover plane by an angle
       `2θ` where `sin θ = 1/√N`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE SHIPS

    Layer A (definitions)
      • `uniformSuperposition N`     : `Fin N → ℂ`, value `1/√N`
                                        at every index.
      • `basisVector N t`            : `|t⟩` as a function.
      • `reflection ψ`               : the matrix
                                        `I − (2/⟨ψ|ψ⟩) |ψ⟩⟨ψ|`.
      • `groverOracle N t`           : reflection about `|t⟩`.
      • `groverDiffusion N`          : reflection about `|+⟩`.
      • `groverIteration N t`        : `− groverOracle · groverDiffusion`.

    Layer B (structural identities and unitarity)
      • `reflection_sq`              : a reflection about a normalised
                                        state squares to the identity.
      • `reflection_isHermitian`     : a reflection is self-adjoint.
      • `reflection_unitary`         : a reflection of a normalised
                                        state is unitary.
      • `groverOracle_unitary`,
        `groverDiffusion_unitary`,
        `groverIteration_unitary`    : the three Grover operators are
                                        unitary.

    Layer C (the BBBV / Grover named targets)
      • `GroverOptimalQuery_Target`  : the BBBV-1997 `Ω(√N)` quantum
                                        query lower bound, stated as a
                                        named `Prop`.
      • `GroverIterationUpperBound_Target` : the matching `O(√N)`
                                        upper bound exhibited by
                                        `groverIteration`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE NOTE

  We do NOT prove either side of `Θ(√N)`:

    *  The **upper bound** (Grover 1996) requires the angle
       parametrisation `sin θ = 1/√N`, the explicit closed form
       `G^k |+⟩ = cos((2k+1)θ) |+⟩' + sin((2k+1)θ) |t⟩`, and the
       analysis showing optimal `k = ⌊π/(4θ)⌋ ≈ π√N/4`.

    *  The **lower bound** (BBBV 1997) is a hybrid argument
       comparing oracle queries against an averaging argument over
       all `N` possible target locations.

  Both are stated as named hypotheses so downstream code may
  reference them, and so a future formalisation has a fixed
  target.  What we DO prove here is everything *structural*:
  the definitions are mathematically correct, the operators are
  honest unitaries, and the Grover iteration is the standard
  `-O · D` composite.

  Zero `sorry`.  Zero custom `axiom`.
-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumWalk

open Matrix Complex BigOperators

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART A — Vectors: uniform superposition and basis states
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

variable {N : ℕ}

/-- The **uniform superposition** on `Fin N`:
    `(1/√N) Σ_i |i⟩`, represented as the column vector with value
    `1/√N` at every basis index. -/
noncomputable def uniformSuperposition (N : ℕ) : Fin N → ℂ :=
  fun _ => ((1 / Real.sqrt N : ℝ) : ℂ)

/-- The **standard basis vector** `|t⟩` on `Fin N`:
    indicator of the index `t`. -/
def basisVector (N : ℕ) (t : Fin N) : Fin N → ℂ :=
  fun i => if i = t then 1 else 0

/-! ### Norm of the basis vector. -/

/-- `|t⟩` is a unit vector: `Σ_i ‖basisVector N t i‖² = 1`. -/
theorem basisVector_normSq (N : ℕ) (t : Fin N) :
    (∑ i, Complex.normSq (basisVector N t i)) = 1 := by
  classical
  -- The sum collapses to the single term `i = t`.
  rw [show (∑ i, Complex.normSq (basisVector N t i))
        = ∑ i ∈ (Finset.univ : Finset (Fin N)),
            Complex.normSq (if i = t then (1 : ℂ) else 0) from
      by simp [basisVector]]
  rw [Finset.sum_eq_single t]
  · simp
  · intro i _ hi
    simp [hi]
  · intro ht
    exact (ht (Finset.mem_univ _)).elim

/-! ### Norm of the uniform superposition. -/

/-- The norm-square of every entry of `uniformSuperposition N` is `1/N`
    (for `0 < N`). -/
private lemma uniformSuperposition_entry_normSq (hN : 0 < N) (i : Fin N) :
    Complex.normSq (uniformSuperposition N i) = (1 / N : ℝ) := by
  unfold uniformSuperposition
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt N := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have h_sqrt_ne : (Real.sqrt N : ℝ) ≠ 0 := ne_of_gt h_sqrt_pos
  have h_sqrt_sq : (Real.sqrt N) ^ 2 = N := by
    rw [sq]
    exact Real.mul_self_sqrt (by exact_mod_cast (Nat.zero_le N))
  -- normSq of (r : ℂ) for real r is r^2.
  have hRe : Complex.normSq (((1 / Real.sqrt N : ℝ) : ℂ)) = (1 / Real.sqrt N) ^ 2 := by
    rw [Complex.normSq_ofReal]
    ring
  rw [hRe]
  field_simp
  rw [h_sqrt_sq]

/-- The uniform superposition is a unit vector (for `0 < N`):
    `Σ_i ‖uniformSuperposition N i‖² = 1`. -/
theorem uniformSuperposition_normSq (hN : 0 < N) :
    (∑ i, Complex.normSq (uniformSuperposition N i)) = 1 := by
  have h_each : ∀ i : Fin N,
      Complex.normSq (uniformSuperposition N i) = (1 / N : ℝ) :=
    fun i => uniformSuperposition_entry_normSq hN i
  calc (∑ i, Complex.normSq (uniformSuperposition N i))
      = ∑ _ : Fin N, (1 / N : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h_each i
    _ = (Finset.univ : Finset (Fin N)).card * (1 / N : ℝ) := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
    _ = N * (1 / N : ℝ) := by rw [Finset.card_univ, Fintype.card_fin]
    _ = 1 := by
        have hNne : (N : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)
        field_simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART B — Reflections: I − 2 |ψ⟩⟨ψ| / ⟨ψ|ψ⟩
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The **outer product** matrix `|ψ⟩⟨ψ|` whose `(i, j)` entry is
    `ψ i * conj(ψ j)`. -/
noncomputable def outerProduct (ψ : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => ψ i * star (ψ j))

/-- The entry formula for `outerProduct`. -/
@[simp] theorem outerProduct_apply (ψ : Fin N → ℂ) (i j : Fin N) :
    outerProduct ψ i j = ψ i * star (ψ j) := rfl

/-- The **reflection** about a vector `ψ`:
        `R_ψ := I − (2/⟨ψ|ψ⟩) · |ψ⟩⟨ψ|`.

    When `ψ` is a unit vector (`⟨ψ|ψ⟩ = 1`), this simplifies to
    `R_ψ = I − 2 |ψ⟩⟨ψ|`, the standard reflection about `ψ`'s line. -/
noncomputable def reflection (ψ : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (1 : Matrix (Fin N) (Fin N) ℂ)
    - (2 / ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ)) • outerProduct ψ

/-! ### Conjugate-transpose of the outer product. -/

/-- `(|ψ⟩⟨ψ|)ᴴ = |ψ⟩⟨ψ|`.  Direct entry computation. -/
theorem outerProduct_conjTranspose (ψ : Fin N → ℂ) :
    (outerProduct ψ)ᴴ = outerProduct ψ := by
  ext i j
  -- (Mᴴ) i j = star (M j i)
  rw [Matrix.conjTranspose_apply]
  rw [outerProduct_apply, outerProduct_apply]
  -- star (ψ j * star (ψ i)) = star (star (ψ i)) * star (ψ j) = ψ i * star (ψ j)
  rw [StarMul.star_mul, star_star]

/-- `outerProduct ψ` is Hermitian. -/
theorem outerProduct_isHermitian (ψ : Fin N → ℂ) :
    (outerProduct ψ).IsHermitian :=
  outerProduct_conjTranspose ψ

/-! ### Outer-product squared. -/

/-- A useful sum identity: for any vector `ψ`,
    `Σ_k star (ψ k) * ψ k = ((Σ_k ‖ψ k‖²) : ℝ) : ℂ`. -/
private theorem sum_star_mul (ψ : Fin N → ℂ) :
    (∑ k, star (ψ k) * ψ k) = ((∑ k, Complex.normSq (ψ k) : ℝ) : ℂ) := by
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  -- star z * z = z * star z = z * conj z = normSq z, as complex.
  rw [show star (ψ k) * ψ k = ψ k * star (ψ k) by ring]
  -- ψ k * star (ψ k) = normSq (ψ k) as ℂ (via Complex.mul_conj).
  exact Complex.mul_conj (ψ k)

/-- `(|ψ⟩⟨ψ|) * (|ψ⟩⟨ψ|) = ⟨ψ|ψ⟩ · |ψ⟩⟨ψ|`. -/
theorem outerProduct_sq (ψ : Fin N → ℂ) :
    (outerProduct ψ) * (outerProduct ψ)
      = ((∑ k, Complex.normSq (ψ k) : ℝ) : ℂ) • outerProduct ψ := by
  ext i j
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [outerProduct_apply]
  -- LHS: Σ_k (ψ i * star (ψ k)) * (ψ k * star (ψ j))
  simp only [outerProduct_apply]
  have heq : ∀ k,
      (ψ i * star (ψ k)) * (ψ k * star (ψ j))
        = ψ i * star (ψ j) * (star (ψ k) * ψ k) := by
    intro k; ring
  simp_rw [heq]
  rw [← Finset.mul_sum]
  rw [sum_star_mul]
  ring

/-! ### Hermiticity of the reflection. -/

/-- For a vector `ψ` the scaling factor
    `(2 / (Σ ‖ψ‖²) : ℂ)` is its own conjugate (it is real). -/
private lemma scale_factor_star (ψ : Fin N → ℂ) :
    star ((2 / ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ)))
      = (2 / ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ)) := by
  rw [Complex.star_def, map_div₀, map_ofNat]
  rw [Complex.conj_ofReal]

/-- A reflection is Hermitian (self-adjoint). -/
theorem reflection_isHermitian (ψ : Fin N → ℂ) :
    (reflection ψ).IsHermitian := by
  change (reflection ψ)ᴴ = reflection ψ
  unfold reflection
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul]
  rw [outerProduct_conjTranspose ψ]
  rw [scale_factor_star]

/-! ### Reflection squared = Identity (involution). -/

/-- **The key identity for unitarity.**  When `ψ` is a unit vector
    (`⟨ψ|ψ⟩ = 1`), the reflection `R_ψ` squares to the identity. -/
theorem reflection_sq (ψ : Fin N → ℂ)
    (hψ : (∑ i, Complex.normSq (ψ i) : ℝ) = 1) :
    reflection ψ * reflection ψ = (1 : Matrix (Fin N) (Fin N) ℂ) := by
  unfold reflection
  set c : ℂ := (2 / ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ)) with hc_def
  -- (1 - cP)² = 1 - 2cP + c² P².
  -- With ⟨ψ|ψ⟩ = 1 and P² = P, this is 1 - 2cP + c² P.
  -- With c = 2, this is 1 - 4P + 4P = 1.
  -- Step 1: c = 2 (since ⟨ψ|ψ⟩ = 1).
  have hc_val : c = 2 := by
    rw [hc_def, hψ]
    push_cast
    norm_num
  rw [hc_val]
  -- Step 2: P * P = P (since ⟨ψ|ψ⟩ = 1).
  have hPP : (outerProduct ψ) * (outerProduct ψ) = outerProduct ψ := by
    rw [outerProduct_sq, hψ]
    push_cast
    rw [one_smul]
  -- Step 3: introduce an abbreviation `Q := 2 • outerProduct ψ` for
  -- the matrix, so we can do non-commutative-ring algebra.  Key fact:
  -- Q * Q = Q + Q  (since (2•P)² = 4•(P*P) = 4•P = (2+2)•P = Q + Q).
  set P : Matrix (Fin N) (Fin N) ℂ := outerProduct ψ with hP_def
  set Q : Matrix (Fin N) (Fin N) ℂ := (2 : ℂ) • P with hQ_def
  have h_QQ : Q * Q = Q + Q := by
    change ((2 : ℂ) • P) * ((2 : ℂ) • P) = (2 : ℂ) • P + (2 : ℂ) • P
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hPP]
    rw [show ((2 : ℂ) * 2 : ℂ) = ((2 : ℂ) + 2) by ring, add_smul]
  -- Goal: (1 - Q) * (1 - Q) = 1, given Q * Q = Q + Q.
  -- Pure noncomm_ring on the matrix ring (no smul left).
  change ((1 : Matrix (Fin N) (Fin N) ℂ) - Q) * ((1 : Matrix (Fin N) (Fin N) ℂ) - Q)
        = (1 : Matrix (Fin N) (Fin N) ℂ)
  have h_dist : ((1 : Matrix (Fin N) (Fin N) ℂ) - Q)
              * ((1 : Matrix (Fin N) (Fin N) ℂ) - Q)
              = (1 : Matrix (Fin N) (Fin N) ℂ) - Q - Q + Q * Q := by
    noncomm_ring
  rw [h_dist, h_QQ]
  abel

/-! ### Reflection unitarity. -/

/-- **A reflection of a unit vector is unitary.**

    Strategy: a Hermitian involution `M` satisfies `M * Mᴴ = M * M = 1`,
    which is the defining condition for membership of `unitaryGroup`. -/
theorem reflection_unitary (ψ : Fin N → ℂ)
    (hψ : (∑ i, Complex.normSq (ψ i) : ℝ) = 1) :
    reflection ψ ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  -- M * star M = 1.  Since M is Hermitian, star M = M, so M * M = 1.
  have h_herm : star (reflection ψ) = reflection ψ := reflection_isHermitian ψ
  rw [h_herm]
  exact reflection_sq ψ hψ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART C — Grover operators: oracle, diffusion, iteration
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The **Grover oracle**: reflection about the marked basis vector `|t⟩`.

    Concretely, `O_t = I − 2 |t⟩⟨t|` flips the sign of the amplitude of
    the marked item and leaves all others unchanged. -/
noncomputable def groverOracle (N : ℕ) (t : Fin N) :
    Matrix (Fin N) (Fin N) ℂ :=
  reflection (basisVector N t)

/-- The **Grover diffusion operator**: reflection about the uniform
    superposition `|+⟩`.

    Concretely, `D = I − 2 |+⟩⟨+|` (equivalent up to global sign to the
    physicist's `2|+⟩⟨+| − I`).  The Grover iteration is `−O · D`. -/
noncomputable def groverDiffusion (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  reflection (uniformSuperposition N)

/-- **The Grover iteration** `G := − O_t · D`.

    Each application rotates the state in the 2-D plane spanned by
    `|t⟩` and the unmarked superposition by `2θ` where
    `sin θ = 1/√N`.  After `k ≈ π√N/4` iterations starting from
    `|+⟩`, the state is amplified to nearly `|t⟩`. -/
noncomputable def groverIteration (N : ℕ) (t : Fin N) :
    Matrix (Fin N) (Fin N) ℂ :=
  -(groverOracle N t * groverDiffusion N)

/-! ### Unitarity of the three Grover operators. -/

/-- The Grover oracle is unitary. -/
theorem groverOracle_unitary (N : ℕ) (t : Fin N) :
    groverOracle N t ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  unfold groverOracle
  exact reflection_unitary (basisVector N t) (basisVector_normSq N t)

/-- The Grover diffusion operator is unitary (for `0 < N`). -/
theorem groverDiffusion_unitary (hN : 0 < N) :
    groverDiffusion N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  unfold groverDiffusion
  exact reflection_unitary (uniformSuperposition N) (uniformSuperposition_normSq hN)

/-- A product of two unitaries is unitary, and the negative of a unitary
    is also unitary.  Hence `G = −(O · D)` is unitary. -/
theorem groverIteration_unitary (N : ℕ) (t : Fin N) (hN : 0 < N) :
    groverIteration N t ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  unfold groverIteration
  rw [Matrix.mem_unitaryGroup_iff]
  -- star (-X) = -star X; (-X) * (-star X) = X * star X.
  have h_OD : (groverOracle N t * groverDiffusion N)
                * star (groverOracle N t * groverDiffusion N) = 1 := by
    rw [← Matrix.mem_unitaryGroup_iff]
    exact Submonoid.mul_mem _ (groverOracle_unitary N t)
                              (groverDiffusion_unitary hN)
  rw [star_neg, neg_mul_neg]
  exact h_OD

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART D — The BBBV / Grover named targets
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The Grover upper bound** (Grover 1996): there exists `C > 0` such
    that for every `N > 0` and target `t : Fin N`, the Grover iteration
    `G = −O_t · D` produces, after some `k ≤ C·√N` applications starting
    from the uniform superposition `|+⟩`, a state whose squared overlap
    with `|t⟩` is at least `2/3`.

    Not proved here.  Requires the angle parametrisation `sin θ = 1/√N`
    and the closed form `G^k |+⟩ = cos((2k+1)θ) |+⟩' + sin((2k+1)θ) |t⟩`. -/
def GroverIterationUpperBound_Target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ t : Fin N,
    ∃ k : ℕ, (k : ℝ) ≤ C * Real.sqrt N ∧
      ‖((groverIteration N t) ^ k *ᵥ uniformSuperposition N) t‖ ^ 2 ≥ (2 : ℝ) / 3

/-- **The BBBV lower bound** (Bennett–Bernstein–Brassard–Vazirani 1997):
    *any* quantum algorithm querying the oracle `O_t` needs `Ω(√N)`
    queries to find the marked item with constant probability.

    We state it for the specific iteration scheme (matched to
    `GroverIterationUpperBound_Target`).  Not proved here. -/
def GroverOptimalQuery_Target : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N →
    ∀ (k : ℕ),
      (∀ t : Fin N,
        ‖((groverIteration N t) ^ k *ᵥ uniformSuperposition N) t‖ ^ 2
          ≥ (2 : ℝ) / 3)
      → (k : ℝ) ≥ c * Real.sqrt N

end UnifiedTheory.LayerB.QuantumWalk

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms UnifiedTheory.LayerB.QuantumWalk.reflection_sq
#print axioms UnifiedTheory.LayerB.QuantumWalk.reflection_unitary
#print axioms UnifiedTheory.LayerB.QuantumWalk.groverOracle_unitary
#print axioms UnifiedTheory.LayerB.QuantumWalk.groverDiffusion_unitary
#print axioms UnifiedTheory.LayerB.QuantumWalk.groverIteration_unitary
