/-
  LayerB/StinespringDephasing.lean — Explicit Stinespring dilation for
  the framework's dephasing channel.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerB/LindbladDephasing.lean` proves the dephasing channel
      Φ(ρ) = (1+γ)/2 · ρ + (1-γ)/2 · σ_z ρ σ_z
  is CPTP at the state level (preserves trace and PSD on
  `DensityMatrix2Honest`). What is NOT proved there is the *structural*
  Stinespring statement: every CPTP map factors as
      Φ(ρ) = Tr_E (V ρ V*)
  with V : H → H ⊗ H_E an isometry into a system+environment dilation.

  This file gives the explicit dilation for the dephasing channel in
  the real-amplitude qubit case.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONSTRUCTION

  Hilbert spaces are real:
      H   = ℝ² (basis indexed by `Fin 2`)
      H_E = ℝ² (basis indexed by `Fin 2`, environment ancilla qubit)
      H ⊗ H_E = ℝ⁴ (basis indexed by `Fin 2 × Fin 2`)

  Density matrices are 2 × 2 real symmetric trace-1 PSD matrices,
  parametrized by the four scalars `(p₁, p₂, c, c)` of
  `DensityMatrix2Honest` with `coh_im = 0` (real-amplitude restriction).
  We work directly with the **scalar** representation.

  Kraus operators of the dephasing channel:
      K₁ = α · I,        α = √((1+γ)/2)
      K₂ = β · σ_z,      β = √((1-γ)/2)

  The fixed identity `α² + β² = 1` says V is an isometry.

  Stinespring isometry V : H → H ⊗ H_E
      V|ψ⟩ = (K₁ |ψ⟩) ⊗ |0⟩_E + (K₂ |ψ⟩) ⊗ |1⟩_E
           = α · |ψ⟩ ⊗ |0⟩_E + β · (σ_z |ψ⟩) ⊗ |1⟩_E

  As a 4 × 2 matrix, V[(i, e), j] is:
      e = 0 :   α · δ_{i,j}                  (K₁ = α · I)
      e = 1 :   β · σ_z[i, j]                (K₂ = β · σ_z)

  Partial trace over the environment:
      (Tr_E M)[i, i'] := Σ_e M[(i, e), (i', e)]

  The Stinespring equation
      (Tr_E (V ρ V^T))[i, i']
        = (K₁ ρ K₁^T + K₂ ρ K₂^T)[i, i']
        = α² · ρ[i, i'] + β² · (σ_z ρ σ_z)[i, i']
  holds for every 2 × 2 real symmetric ρ. With α² = (1+γ)/2,
  β² = (1-γ)/2 this is exactly the dephasing channel:
      diagonal (i = i') :  α² · p + β² · p = p
      off-diag (i ≠ i') :  α² · c + β² · (-c) = (α² - β²) · c = γ · c.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  (1) `kraus_norm_unit`: α² + β² = 1 from γ ∈ [0, 1].
  (2) `pauli_z`, `pauli_z_sq_eq_id`: σ_z and σ_z² = I.
  (3) `stinespringV`: the explicit 4 × 2 isometry matrix V.
  (4) `stinespringV_isIsometry`: V^T V = I (column-orthonormal).
  (5) `partialTraceE`: partial trace over the environment.
  (6) `partialTrace_VρVt_eq_kraus_sum`: Tr_E(V ρ V^T) equals the
      Kraus sum K₁ ρ K₁^T + K₂ ρ K₂^T.
  (7) `kraus_sum_eq_dephasing_action`: the Kraus sum acts on a 2 × 2
      real symmetric ρ by preserving the diagonal and contracting
      the off-diagonal by γ — i.e. the dephasing channel.
  (8) `stinespring_equation`: Tr_E(V ρ V^T) = Φ(ρ) at the scalar
      level for every `DensityMatrix2Honest` ρ with `coh_im = 0`.
  (9) `stinespring_master`: bundle of the above.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – Real-amplitude qubit only. Genuine quantum dephasing is over ℂ;
    here the channel acts on the real (`coh_re`) component of the
    coherence. The imaginary component would be handled identically
    by adjoining an `i`-factor to the Kraus operators, which is a
    purely formal extension.
  – Specific channel only. **Stinespring's theorem in full generality**
    (for an arbitrary CPTP map on an arbitrary Hilbert space) requires
    the GNS construction and is a substantial piece of operator-algebra
    machinery NOT formalized here. We give the explicit dilation for
    *this* channel — verifying the theorem in our specific case.
  – Matrices are represented as scalar-valued functions
    `Fin 2 → Fin 2 → ℝ` (and similarly `Fin 2 × Fin 2 → ...` for the
    dilated 4 × 4 case). This avoids importing the full
    `Matrix (Fin n) (Fin n) ℝ` library and keeps the proofs purely
    scalar / `decide`-friendly. The mathematical content is identical.
  – Parameters: we encode the Kraus weights as `α, β : ℝ` with
    `α² + β² = 1`, `α² = (1+γ)/2`, `β² = (1-γ)/2`. This avoids
    importing `Real.sqrt`; the existence of `α, β` for any
    `γ ∈ [0, 1]` is demonstrated separately via `Real.sqrt`.

  Zero `sorry`. Zero custom axioms.
-/
import UnifiedTheory.LayerB.LindbladDephasing
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.StinespringDephasing

open UnifiedTheory.LayerB.DensityMatrixHonest
open UnifiedTheory.LayerB.LindbladDephasing

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: KRAUS WEIGHTS AND THEIR NORMALIZATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Kraus weights of the dephasing channel:
    `α = √((1+γ)/2)`, `β = √((1-γ)/2)`. We package the *squared*
    weights `α²` and `β²` together with the fact that they sum to 1.
    Existence of suitable `α, β ≥ 0` is provided by `kraus_weights`. -/
structure KrausWeights (γ : ℝ) where
  α : ℝ
  β : ℝ
  α_sq : α ^ 2 = (1 + γ) / 2
  β_sq : β ^ 2 = (1 - γ) / 2

/-- Existence of Kraus weights for any `γ ∈ [0, 1]`. The construction
    uses `Real.sqrt` on the manifestly non-negative quantities
    `(1+γ)/2` and `(1-γ)/2`. -/
noncomputable def krausWeights (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1) :
    KrausWeights γ where
  α := Real.sqrt ((1 + γ) / 2)
  β := Real.sqrt ((1 - γ) / 2)
  α_sq := by
    have h_nn : (0 : ℝ) ≤ (1 + γ) / 2 := by linarith
    rw [sq, Real.mul_self_sqrt h_nn]
  β_sq := by
    have h_nn : (0 : ℝ) ≤ (1 - γ) / 2 := by linarith
    rw [sq, Real.mul_self_sqrt h_nn]

/-- **Normalization of the Kraus weights.** `α² + β² = 1`. This is the
    isometry condition `V^T V = I` reduced to a scalar equality. -/
theorem kraus_norm_unit (γ : ℝ) (w : KrausWeights γ) :
    w.α ^ 2 + w.β ^ 2 = 1 := by
  rw [w.α_sq, w.β_sq]; ring

/-- The dephasing parameter γ is recovered as `α² - β²`. -/
theorem kraus_diff_eq_gamma (γ : ℝ) (w : KrausWeights γ) :
    w.α ^ 2 - w.β ^ 2 = γ := by
  rw [w.α_sq, w.β_sq]; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: PAULI-Z AS A 2 × 2 MATRIX
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Pauli-Z matrix `σ_z = diag(1, -1)`. -/
def pauli_z : Fin 2 → Fin 2 → ℝ
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 0
  | 1, 1 => -1

/-- The 2 × 2 identity matrix. -/
def id2 : Fin 2 → Fin 2 → ℝ
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 0
  | 1, 1 => 1

/-- σ_z² = I.  Verified by case analysis on the four entries. -/
theorem pauli_z_sq_eq_id (i j : Fin 2) :
    (pauli_z i 0 * pauli_z 0 j + pauli_z i 1 * pauli_z 1 j) = id2 i j := by
  fin_cases i <;> fin_cases j <;> simp [pauli_z, id2]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: 2 × 2 SYMMETRIC MATRIX REPRESENTATION OF A DENSITY MATRIX
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A `DensityMatrix2Honest` ρ with `coh_im = 0` is represented as the
    2 × 2 real symmetric matrix
        ⎡ p₁   c ⎤
        ⎣ c    p₂⎦
    with `c = ρ.coh_re`. We expose the entries explicitly to keep the
    proofs scalar.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The 2 × 2 real symmetric matrix associated with a real-amplitude
    density matrix ρ (using only the real part of the coherence). -/
def rhoMatrix (ρ : DensityMatrix2Honest) : Fin 2 → Fin 2 → ℝ
  | 0, 0 => ρ.p₁
  | 0, 1 => ρ.coh_re
  | 1, 0 => ρ.coh_re
  | 1, 1 => ρ.p₂

/-- σ_z ρ σ_z, computed entrywise on the 2 × 2 representation. The
    diagonal is unchanged; the off-diagonal is negated. -/
def pauliZConj (ρ : DensityMatrix2Honest) : Fin 2 → Fin 2 → ℝ
  | 0, 0 => ρ.p₁
  | 0, 1 => -ρ.coh_re
  | 1, 0 => -ρ.coh_re
  | 1, 1 => ρ.p₂

/-- **σ_z ρ σ_z is computed correctly** by `pauliZConj` for any 2 × 2
    real symmetric ρ. This is the matrix identity
        (σ_z ρ σ_z)[i, j]
          = Σ_{k,ℓ} σ_z[i,k] · ρ[k,ℓ] · σ_z[ℓ,j]
    expanded by case analysis. -/
theorem pauli_z_conj_correct (ρ : DensityMatrix2Honest) (i j : Fin 2) :
    (pauli_z i 0 * (rhoMatrix ρ 0 0 * pauli_z 0 j + rhoMatrix ρ 0 1 * pauli_z 1 j)
      + pauli_z i 1 * (rhoMatrix ρ 1 0 * pauli_z 0 j + rhoMatrix ρ 1 1 * pauli_z 1 j))
        = pauliZConj ρ i j := by
  fin_cases i <;> fin_cases j <;>
    simp [pauli_z, rhoMatrix, pauliZConj]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE STINESPRING ISOMETRY V : ℝ² → ℝ² ⊗ ℝ²
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    V : H → H ⊗ H_E acts on basis state |j⟩ as
        V|j⟩ = K₁|j⟩ ⊗ |0⟩_E + K₂|j⟩ ⊗ |1⟩_E.
    With H = H_E = ℝ² and basis index in `Fin 2`, V is a 4 × 2 matrix
    indexed by `((i, e), j)` with `(i, e) ∈ Fin 2 × Fin 2` the
    system+environment composite index and `j ∈ Fin 2` the input index.
    The matrix entry is K_e[i, j] (with K_0 = α·I, K_1 = β·σ_z).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The Stinespring isometry V** for the dephasing channel. As a
    4 × 2 matrix indexed by composite system-environment pair `(i, e)`
    and input system index `j`. -/
def stinespringV (γ : ℝ) (w : KrausWeights γ) :
    Fin 2 → Fin 2 → Fin 2 → ℝ
  | i, 0, j => w.α * id2 i j         -- environment in |0⟩, K₁ = α·I
  | i, 1, j => w.β * pauli_z i j     -- environment in |1⟩, K₂ = β·σ_z

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: V IS AN ISOMETRY (V^T V = I)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The (j, j') entry of V^T V is
        Σ_{i, e} V[(i, e), j] · V[(i, e), j']
          = Σ_i (α² · I[i,j] · I[i,j'] + β² · σ_z[i,j] · σ_z[i,j'])
          = α² · I[j, j'] + β² · (σ_z² )[j, j']
          = (α² + β²) · I[j, j']
          = I[j, j'].
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- V^T V at entry (j, j'): explicit sum over the composite (i, e) index. -/
def vtv (γ : ℝ) (w : KrausWeights γ) (j j' : Fin 2) : ℝ :=
  -- Sum over i ∈ {0, 1} and e ∈ {0, 1} of V[(i, e), j] · V[(i, e), j'].
  (stinespringV γ w 0 0 j) * (stinespringV γ w 0 0 j') +
  (stinespringV γ w 0 1 j) * (stinespringV γ w 0 1 j') +
  (stinespringV γ w 1 0 j) * (stinespringV γ w 1 0 j') +
  (stinespringV γ w 1 1 j) * (stinespringV γ w 1 1 j')

/-- **The isometry equation V^T V = I.** Verified entrywise on
    `(j, j') ∈ Fin 2 × Fin 2`, using the Kraus normalization
    `α² + β² = 1`. -/
theorem stinespringV_isIsometry (γ : ℝ) (w : KrausWeights γ) (j j' : Fin 2) :
    vtv γ w j j' = id2 j j' := by
  have hsum : w.α ^ 2 + w.β ^ 2 = 1 := kraus_norm_unit γ w
  fin_cases j <;> fin_cases j' <;>
    simp [vtv, stinespringV, id2, pauli_z] <;> nlinarith [hsum]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: V ρ V^T ON THE DILATED 4 × 4 SPACE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For ρ a 2 × 2 real symmetric matrix and V the 4 × 2 isometry above,
    the (i, e), (i', e') entry of V ρ V^T is
        (V ρ V^T)[(i, e), (i', e')]
           = Σ_{j, j'} V[(i, e), j] · ρ[j, j'] · V[(i', e'), j'].
    We expand this entrywise.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The dilated state `V ρ V^T` as a 4 × 4 matrix indexed by composite
    `(i, e)` and `(i', e')`. -/
def vRhoVt (γ : ℝ) (w : KrausWeights γ) (ρ : DensityMatrix2Honest)
    (i e i' e' : Fin 2) : ℝ :=
  (stinespringV γ w i e 0) * (rhoMatrix ρ 0 0) * (stinespringV γ w i' e' 0) +
  (stinespringV γ w i e 0) * (rhoMatrix ρ 0 1) * (stinespringV γ w i' e' 1) +
  (stinespringV γ w i e 1) * (rhoMatrix ρ 1 0) * (stinespringV γ w i' e' 0) +
  (stinespringV γ w i e 1) * (rhoMatrix ρ 1 1) * (stinespringV γ w i' e' 1)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: PARTIAL TRACE OVER THE ENVIRONMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For M a 4 × 4 matrix indexed by (system, env), the partial trace
    over the environment is
        (Tr_E M)[i, i'] := Σ_e M[(i, e), (i', e)].
    With env = `Fin 2`, the sum is two terms.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Partial trace over the environment** of a generic 4 × 4 matrix
    indexed by composite (system, env) pairs. -/
def partialTraceE (M : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  fun i i' => M i 0 i' 0 + M i 1 i' 1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: KRAUS SUM AND PARTIAL TRACE OF V ρ V^T
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The structural identity at the heart of Stinespring:
        Tr_E(V ρ V^T) = K₁ ρ K₁^T + K₂ ρ K₂^T.
    Splitting the partial-trace sum on `e` into the two summands gives
    exactly the two Kraus terms.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The **Kraus sum** `Φ_K(ρ) := K₁ ρ K₁^T + K₂ ρ K₂^T` at entry
    `(i, i')`. With `K₁ = α·I` and `K₂ = β·σ_z` this is
    `α² · ρ[i, i'] + β² · (σ_z ρ σ_z)[i, i']`. -/
def krausSum (γ : ℝ) (w : KrausWeights γ) (ρ : DensityMatrix2Honest)
    (i i' : Fin 2) : ℝ :=
  w.α ^ 2 * rhoMatrix ρ i i' + w.β ^ 2 * pauliZConj ρ i i'

/-- **The partial trace of V ρ V^T equals the Kraus sum.**

    Proof outline: the partial-trace sum splits the (i, e), (i', e)
    entry of V ρ V^T into e = 0 (contributing α² · ρ[i, i'] from
    K₁ = α·I) and e = 1 (contributing β² · (σ_z ρ σ_z)[i, i'] from
    K₂ = β·σ_z). All four entries (i, i') are verified
    by case analysis. -/
theorem partialTrace_VρVt_eq_kraus_sum (γ : ℝ) (w : KrausWeights γ)
    (ρ : DensityMatrix2Honest) (i i' : Fin 2) :
    partialTraceE (vRhoVt γ w ρ) i i' = krausSum γ w ρ i i' := by
  fin_cases i <;> fin_cases i' <;>
    simp [partialTraceE, vRhoVt, krausSum, stinespringV, id2,
          pauli_z, rhoMatrix, pauliZConj] <;> ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: THE KRAUS SUM IS THE DEPHASING CHANNEL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Kraus sum α² · ρ + β² · σ_z ρ σ_z, on a 2 × 2 real symmetric
    ρ, has:
       diagonal  : α² · p + β² · p  = (α² + β²) · p  = p
       off-diag  : α² · c + β² · (-c)  = (α² - β²) · c  = γ · c.
    This is exactly the action of `dephasingChannel γ` on the
    `(p₁, p₂, coh_re)`-subspace.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The 2 × 2 representation of the dephased density matrix
    `dephasingChannel γ ρ`. This is `rhoMatrix` applied to the output;
    we expose it explicitly for the comparison theorem. -/
def dephasedRhoMatrix (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ : DensityMatrix2Honest) : Fin 2 → Fin 2 → ℝ :=
  rhoMatrix (dephasingChannel γ hγ_nn hγ_le_one ρ)

/-- The 2 × 2 representation of `dephasingChannel γ ρ` is what one
    would expect: diagonal preserved, off-diagonal multiplied by γ. -/
theorem dephasedRhoMatrix_entries (γ : ℝ) (hγ_nn : 0 ≤ γ)
    (hγ_le_one : γ ≤ 1) (ρ : DensityMatrix2Honest) (i j : Fin 2) :
    dephasedRhoMatrix γ hγ_nn hγ_le_one ρ i j =
      (if i = j then rhoMatrix ρ i j else γ * rhoMatrix ρ i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [dephasedRhoMatrix, rhoMatrix, dephasingChannel, dephase]

/-- **Kraus sum equals the dephasing channel action.** For every
    `DensityMatrix2Honest` ρ, every entry (i, j) ∈ Fin 2 × Fin 2:
        krausSum γ w ρ i j  =  rhoMatrix (dephasingChannel γ ρ) i j.
    This uses both `α² + β² = 1` (diagonal) and `α² - β² = γ`
    (off-diagonal). -/
theorem kraus_sum_eq_dephasing_action (γ : ℝ) (hγ_nn : 0 ≤ γ)
    (hγ_le_one : γ ≤ 1) (w : KrausWeights γ) (ρ : DensityMatrix2Honest)
    (i j : Fin 2) :
    krausSum γ w ρ i j = dephasedRhoMatrix γ hγ_nn hγ_le_one ρ i j := by
  have hsum : w.α ^ 2 + w.β ^ 2 = 1 := kraus_norm_unit γ w
  have hdiff : w.α ^ 2 - w.β ^ 2 = γ := kraus_diff_eq_gamma γ w
  -- Diagonal case: α²·p + β²·p = (α² + β²)·p = 1·p = p
  -- Off-diag case: α²·c + β²·(-c) = (α² - β²)·c = γ·c
  fin_cases i <;> fin_cases j <;>
    simp [krausSum, rhoMatrix, pauliZConj, dephasedRhoMatrix,
          dephasingChannel, dephase]
  · -- (0,0): w.α^2 * ρ.p₁ + w.β^2 * ρ.p₁ = ρ.p₁
    have : w.α ^ 2 * ρ.p₁ + w.β ^ 2 * ρ.p₁ = (w.α ^ 2 + w.β ^ 2) * ρ.p₁ := by ring
    rw [this, hsum]; ring
  · -- (0,1): w.α^2 * ρ.coh_re + -(w.β^2 * ρ.coh_re) = γ * ρ.coh_re
    have key : w.α ^ 2 * ρ.coh_re + -(w.β ^ 2 * ρ.coh_re)
        = (w.α ^ 2 - w.β ^ 2) * ρ.coh_re := by ring
    rw [key, hdiff]
  · -- (1,0): w.α^2 * ρ.coh_re + -(w.β^2 * ρ.coh_re) = γ * ρ.coh_re
    have key : w.α ^ 2 * ρ.coh_re + -(w.β ^ 2 * ρ.coh_re)
        = (w.α ^ 2 - w.β ^ 2) * ρ.coh_re := by ring
    rw [key, hdiff]
  · -- (1,1): w.α^2 * ρ.p₂ + w.β^2 * ρ.p₂ = ρ.p₂
    have : w.α ^ 2 * ρ.p₂ + w.β ^ 2 * ρ.p₂ = (w.α ^ 2 + w.β ^ 2) * ρ.p₂ := by ring
    rw [this, hsum]; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: THE STINESPRING EQUATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Putting Parts 6, 8, 9 together:
        Tr_E(V ρ V^T)  =  K₁ ρ K₁^T + K₂ ρ K₂^T  =  Φ(ρ).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **STINESPRING EQUATION FOR THE DEPHASING CHANNEL.** For every
    `DensityMatrix2Honest` ρ (real-amplitude case) and every Kraus
    weight pair w with α² = (1+γ)/2, β² = (1-γ)/2:
        Tr_E (V ρ V^T) = dephasingChannel γ ρ
    at every entry (i, j) of the 2 × 2 representation. -/
theorem stinespring_equation (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (w : KrausWeights γ) (ρ : DensityMatrix2Honest) (i j : Fin 2) :
    partialTraceE (vRhoVt γ w ρ) i j =
      dephasedRhoMatrix γ hγ_nn hγ_le_one ρ i j := by
  rw [partialTrace_VρVt_eq_kraus_sum γ w ρ i j,
      kraus_sum_eq_dephasing_action γ hγ_nn hγ_le_one w ρ i j]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 11: SCALAR-LEVEL CONSEQUENCES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Reading off the diagonal and off-diagonal entries from the
    Stinespring equation reproduces the dephasing-channel update at
    the scalar level: populations preserved, real coherence multiplied
    by γ.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Diagonal entry (population p₁) preserved by the dilation.** -/
theorem stinespring_p1 (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (w : KrausWeights γ) (ρ : DensityMatrix2Honest) :
    partialTraceE (vRhoVt γ w ρ) 0 0 = ρ.p₁ := by
  have h := stinespring_equation γ hγ_nn hγ_le_one w ρ 0 0
  simp [dephasedRhoMatrix, rhoMatrix, dephasingChannel, dephase] at h
  exact h

/-- **Diagonal entry (population p₂) preserved by the dilation.** -/
theorem stinespring_p2 (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (w : KrausWeights γ) (ρ : DensityMatrix2Honest) :
    partialTraceE (vRhoVt γ w ρ) 1 1 = ρ.p₂ := by
  have h := stinespring_equation γ hγ_nn hγ_le_one w ρ 1 1
  simp [dephasedRhoMatrix, rhoMatrix, dephasingChannel, dephase] at h
  exact h

/-- **Off-diagonal entry (coherence) contracted by γ.** -/
theorem stinespring_coh (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (w : KrausWeights γ) (ρ : DensityMatrix2Honest) :
    partialTraceE (vRhoVt γ w ρ) 0 1 = γ * ρ.coh_re := by
  have h := stinespring_equation γ hγ_nn hγ_le_one w ρ 0 1
  simp [dephasedRhoMatrix, rhoMatrix, dephasingChannel, dephase] at h
  exact h

/-- **Off-diagonal entry symmetry: same as `stinespring_coh` for the
    transposed entry, reflecting Hermiticity of ρ.** -/
theorem stinespring_coh_transposed (γ : ℝ) (hγ_nn : 0 ≤ γ)
    (hγ_le_one : γ ≤ 1) (w : KrausWeights γ) (ρ : DensityMatrix2Honest) :
    partialTraceE (vRhoVt γ w ρ) 1 0 = γ * ρ.coh_re := by
  have h := stinespring_equation γ hγ_nn hγ_le_one w ρ 1 0
  simp [dephasedRhoMatrix, rhoMatrix, dephasingChannel, dephase] at h
  exact h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 12: TRACE-PRESERVATION FROM STINESPRING (CHECK)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Stinespring's theorem implies trace preservation as a corollary,
    via Tr(Tr_E(V ρ V^T)) = Tr(V^T V ρ) = Tr(I · ρ) = Tr(ρ).
    We verify this *concretely* on our 2 × 2 channel: summing the
    diagonal of `Tr_E(V ρ V^T)` reproduces the trace `p₁ + p₂` of ρ.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Trace preservation, as a corollary of the Stinespring identity.**
    The trace of `Tr_E(V ρ V^T)` (sum of diagonal entries) equals
    the trace of ρ (`p₁ + p₂ = 1`). -/
theorem stinespring_trace_preserving (γ : ℝ) (hγ_nn : 0 ≤ γ)
    (hγ_le_one : γ ≤ 1) (w : KrausWeights γ) (ρ : DensityMatrix2Honest) :
    partialTraceE (vRhoVt γ w ρ) 0 0 + partialTraceE (vRhoVt γ w ρ) 1 1
      = ρ.p₁ + ρ.p₂ := by
  rw [stinespring_p1 γ hγ_nn hγ_le_one w ρ,
      stinespring_p2 γ hγ_nn hγ_le_one w ρ]

/-- **Trace = 1**, using the type-level `htrace` field. -/
theorem stinespring_trace_one (γ : ℝ) (hγ_nn : 0 ≤ γ)
    (hγ_le_one : γ ≤ 1) (w : KrausWeights γ) (ρ : DensityMatrix2Honest) :
    partialTraceE (vRhoVt γ w ρ) 0 0 + partialTraceE (vRhoVt γ w ρ) 1 1
      = 1 := by
  rw [stinespring_trace_preserving γ hγ_nn hγ_le_one w ρ]
  exact ρ.htrace

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 13: SPECIAL CASES (γ = 1 IDENTITY DILATION, γ = 0 FULL DEPHASING)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **At γ = 1 the channel is the identity** and the dilation reduces
    to V|ψ⟩ = |ψ⟩ ⊗ |0⟩_E (only K₁ contributes; K₂ has coefficient
    β = 0). The off-diagonal Stinespring equation gives `1 * coh_re`. -/
theorem stinespring_identity_case (w : KrausWeights 1)
    (ρ : DensityMatrix2Honest) :
    partialTraceE (vRhoVt 1 w ρ) 0 1 = ρ.coh_re := by
  have h := stinespring_coh 1 (by norm_num) le_rfl w ρ
  linarith

/-- **At γ = 0 the channel zeros out the coherence.** Now α = β = √(1/2),
    both Kraus operators contribute equally, and the off-diagonal cancels:
    `α² · c + β² · (-c) = 0`. -/
theorem stinespring_full_dephasing_case (w : KrausWeights 0)
    (ρ : DensityMatrix2Honest) :
    partialTraceE (vRhoVt 0 w ρ) 0 1 = 0 := by
  have h := stinespring_coh 0 le_rfl (by norm_num) w ρ
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 14: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM (STINESPRING DILATION FOR DEPHASING).**

    The dephasing channel `Φ(ρ) = (1+γ)/2 · ρ + (1-γ)/2 · σ_z ρ σ_z`
    on the real-amplitude qubit admits an EXPLICIT Stinespring dilation:

    (1) **Kraus normalization:** for any γ ∈ [0, 1] there exist
        non-negative `α, β` with α² = (1+γ)/2, β² = (1-γ)/2, hence
        α² + β² = 1 (`kraus_norm_unit`).

    (2) **Isometry:** the explicit 4 × 2 matrix V with entries
        `V[(i, 0), j] = α · I[i, j]` and
        `V[(i, 1), j] = β · σ_z[i, j]` satisfies V^T V = I
        (`stinespringV_isIsometry`).

    (3) **Stinespring equation:** for every density matrix ρ and
        every entry (i, j),
            (Tr_E (V ρ V^T))[i, j] = (Φ(ρ))[i, j]
        (`stinespring_equation`).

    (4) **Trace preservation as a corollary:** summing the diagonal
        of `Tr_E (V ρ V^T)` recovers `p₁ + p₂ = 1`
        (`stinespring_trace_one`).
-/
theorem stinespring_master :
    -- (1) Kraus normalization
    (∀ γ : ℝ, ∀ w : KrausWeights γ, w.α ^ 2 + w.β ^ 2 = 1)
    -- (2) Kraus weights exist for any γ ∈ [0, 1]
    ∧ (∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 → Nonempty (KrausWeights γ))
    -- (3) Isometry V^T V = I
    ∧ (∀ γ : ℝ, ∀ w : KrausWeights γ, ∀ j j' : Fin 2,
        vtv γ w j j' = id2 j j')
    -- (4) Stinespring equation Tr_E(V ρ V^T) = Φ(ρ)
    ∧ (∀ γ : ℝ, ∀ hγ_nn : 0 ≤ γ, ∀ hγ_le_one : γ ≤ 1,
        ∀ w : KrausWeights γ, ∀ ρ : DensityMatrix2Honest,
          ∀ i j : Fin 2,
            partialTraceE (vRhoVt γ w ρ) i j =
              dephasedRhoMatrix γ hγ_nn hγ_le_one ρ i j)
    -- (5) Trace preservation = 1 from the dilation (γ ∈ [0, 1] needed
    --     by `htrace`-corollary route via `stinespring_trace_one`)
    ∧ (∀ γ : ℝ, ∀ _hγ_nn : 0 ≤ γ, ∀ _hγ_le_one : γ ≤ 1,
        ∀ w : KrausWeights γ, ∀ ρ : DensityMatrix2Honest,
          partialTraceE (vRhoVt γ w ρ) 0 0
            + partialTraceE (vRhoVt γ w ρ) 1 1 = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro γ w; exact kraus_norm_unit γ w
  · intro γ hγ_nn hγ_le_one
    exact ⟨krausWeights γ hγ_nn hγ_le_one⟩
  · intro γ w j j'; exact stinespringV_isIsometry γ w j j'
  · intro γ hγ_nn hγ_le_one w ρ i j
    exact stinespring_equation γ hγ_nn hγ_le_one w ρ i j
  · intro γ hγ_nn hγ_le_one w ρ
    exact stinespring_trace_one γ hγ_nn hγ_le_one w ρ

end UnifiedTheory.LayerB.StinespringDephasing
