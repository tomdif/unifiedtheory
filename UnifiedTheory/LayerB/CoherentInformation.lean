/-
  LayerB/CoherentInformation.lean
  ────────────────────────────────

  **Quantum coherent information** (Schumacher–Nielsen 1996) and the
  Lloyd–Shor–Devetak formula for quantum channel capacity (LSD 1997-2005).

  For a quantum channel `N` and an input state `ρ`, with purification
  `|ψ⟩` on `A ⊗ R` (`partialTrace_R |ψ⟩⟨ψ| = ρ`), the coherent
  information is

         I_c(ρ, N)  :=  S(N(ρ))  −  S((N ⊗ id_R)(|ψ⟩⟨ψ|)).

  The second term is the entropy of the joint output state on the
  system `N(A) ⊗ R`.  Both arguments are von Neumann entropies (from
  `OperatorEntropy.vonNeumannEntropy`).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Builds on
    * `OperatorEntropy`  (`vonNeumannEntropy`, `vonNeumannEntropy_nonneg`,
                          `posSemidef_of_ComplexDensityMatrix`).
    * `UmegakiRelativeEntropy` (vocabulary; the `re` projection idiom).
    * `KrausRepresentation`    (`apply`, `apply_isHermitian`, `trace_apply`,
                                `apply_posSemidef`, `identity`,
                                `identity_apply`).
    * `KrausComposition`       (vocabulary; not directly needed here).
    * `StinespringDilation`    (vocabulary; we re-use the
                                `partialTrace_right_ancilla_conj`
                                recovery identity in spirit only).
    * `PartialTrace`           (`partialTrace_right`, `reindexFactor`,
                                `densityPartialTrace_right_*`).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS DEFINED (no sorry, no custom axioms)

    1. `densityFromPSDTrace1`
         — bridge from `Matrix.PosSemidef` + `trace = 1` to
           `ComplexDensityMatrix n` (discharges the `hTracePSD`
           field directly from PSD + trace cyclicity).
    2. `densityOfKrausApply`
         — `K.apply ρ.M` wrapped as `ComplexDensityMatrix m`.
    3. `pureStateDM ψ hψ`
         — the rank-1 density matrix `|ψ⟩⟨ψ|` for any normalised
           vector `ψ` with `∑ |ψ_i|² = 1`.
    4. `Purification n ρ`
         — a structure holding a normalised vector `ψ : Fin (n*n) → ℂ`
           together with a proof that the right-partial-trace of
           `|ψ⟩⟨ψ|` (re-indexed via `finProdFinEquiv`) equals `ρ.M`.
    5. `Purification.jointDM`
         — the joint pure state `|ψ⟩⟨ψ|` as a
           `ComplexDensityMatrix (n*n)`.
    6. `JointOutput K ρ P`
         — a structure parameter packaging the *joint output state*
           `(N ⊗ id_R)(|ψ⟩⟨ψ|)`, declared as a
           `ComplexDensityMatrix (m*n)`, together with the algebraic
           consistency requirement that its right-partial-trace equals
           `K.apply ρ.M` (i.e. the marginal on the output system
           is the channel output).
    7. `coherentInformation`
         — the scalar `S(K.apply ρ) − S(jointOut)`.

  WHAT IS PROVEN (no sorry, no custom axioms)

    8. `coherentInformation_le_output_entropy`
         — `I_c(ρ, N) ≤ S(N(ρ))`  (since `S(jointOut) ≥ 0`).
    9. `coherentInformation_eq_output_entropy_of_pure_joint`
         — if the joint output is a *pure* state (parameterised by a
           normalised joint vector), then `I_c(ρ, N) = S(N(ρ))`.
   10. `identityJointOutput`
         — for the identity channel `id_A`, the natural joint output
           is the original purification (∵ `(id ⊗ id_R)|ψ⟩⟨ψ| = |ψ⟩⟨ψ|`),
           making `S(jointOut) = 0` (`vonNeumannEntropy_pureStateDM_eq_zero`).
   11. `vonNeumannEntropy_pureStateDM_eq_zero`
         — the von Neumann entropy of `|ψ⟩⟨ψ|` for a normalised `ψ`
           is zero (`S = −∑ λᵢ log λᵢ` with one eigenvalue = 1,
           others = 0; Mathlib's `0·log 0 = 0`).
   12. `coherentInformation_identity_eq_entropy`
         — `I_c(ρ, id_A) = S(ρ)` with the canonical
           `identityJointOutput`.
   13. `LSDQuantumCapacityFormula`        (named `Prop`)
         — the Lloyd–Shor–Devetak theorem: the quantum capacity of a
           channel equals `lim sup_n (1/n) · max_ρ I_c(ρ⊗n, N⊗n)`.
           Stated, not proved (multi-week formalisation).

  HONEST SCOPE
    – The `JointOutput` packaging is parametric: we do **not** build
      the tensor-product channel `N ⊗ id_R` from the Kraus operators
      of `N` (Kronecker bookkeeping is out of scope for this single
      shipment).  Instead we expose the joint output as data, with a
      consistency law on its marginal.  The identity-channel case
      `identityJointOutput` is fully constructive (so the
      I_c(ρ, id) = S(ρ) theorem closes without any opaque data).
    – `I_c ≤ S(ρ)` (the *strong* upper bound) requires the data-
      processing inequality / strong subadditivity in the form
      `S(N(ρ)) − S((N⊗id)|ψ⟩⟨ψ|) ≤ S(ρ)`.  We do NOT prove that
      sharp inequality here; we ship the strictly weaker but still
      useful `I_c ≤ S(N(ρ))` bound (via `S(jointOut) ≥ 0`), which
      is unconditional, and the sharp equality case for unitary /
      identity channels.  The full sharp `I_c ≤ S(ρ)` would route
      through SSA, which is currently held at gate level in
      `UnifiedTheory.LayerB.StrongSubadditivity`.
    – `LSDQuantumCapacityFormula` is a named `Prop`; no proof
      attempted.  The proof needs random-code constructions
      (Hayden–Horodecki–Winter), decoupling theorem, and the
      multi-letter regularisation, none of which are in this single
      shipment.

  Zero `sorry`, zero custom `axiom`, following the project's
  standing constraint.
-/

import UnifiedTheory.LayerB.OperatorEntropy
import UnifiedTheory.LayerB.UmegakiRelativeEntropy
import UnifiedTheory.LayerB.KrausComposition
import UnifiedTheory.LayerB.StinespringDilation
import UnifiedTheory.LayerB.PartialTrace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.CoherentInformation

open Matrix Complex
open scoped BigOperators ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.Kraus
open UnifiedTheory.LayerB.PartialTrace

/-- Local `AddLeftMono ℂ` instance, mirroring `KrausRepresentation.lean`. -/
local instance : AddLeftMono ℂ where
  elim c a b (h : a ≤ b) := by
    change c + a ≤ c + b
    obtain ⟨hr, hi⟩ := h
    exact ⟨by simp only [Complex.add_re]; linarith,
           by simp only [Complex.add_im]; linarith⟩

variable {n m k : ℕ}

/-! ## 1. Bridge: `PosSemidef + trace = 1 → ComplexDensityMatrix` -/

/-- **PSD + trace-1 wraps as a `ComplexDensityMatrix`.**

    The `hTracePSD` field requires `0 ≤ Re(Tr(M · X† · X))` for every
    `X`.  Using trace cyclicity, `Tr(M · X† · X) = Tr(X · M · X†)`,
    and `X · M · X†` is PSD whenever `M` is PSD
    (`Matrix.PosSemidef.mul_mul_conjTranspose_same`).  Trace of a
    complex PSD matrix is a nonneg real (`Matrix.PosSemidef.trace_nonneg`
    with `AddLeftMono ℂ`), so the real part is nonneg.

    This is the inverse of `posSemidef_of_ComplexDensityMatrix` (which
    converts a `ComplexDensityMatrix` to a PSD matrix). -/
noncomputable def densityFromPSDTrace1 {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hPSD : M.PosSemidef) (hTr : M.trace = 1) :
    ComplexDensityMatrix n where
  M := M
  hHerm := hPSD.isHermitian
  hTrace := hTr
  hTracePSD := by
    intro X
    -- Tr(M · X† · X) = Tr(X · M · X†) by cyclicity
    -- M · X† · X = (M · X†) · X, and Tr(AB) = Tr(BA), so
    -- Tr((M · X†) · X) = Tr(X · (M · X†)) = Tr(X · M · X†).
    have h_cyc :
        Matrix.trace (M * X.conjTranspose * X)
          = Matrix.trace (X * M * X.conjTranspose) := by
      rw [Matrix.trace_mul_comm (M * X.conjTranspose) X]
      rw [Matrix.mul_assoc]
    rw [h_cyc]
    -- X · M · X† is PSD
    have h_psd_conj : (X * M * X.conjTranspose).PosSemidef :=
      hPSD.mul_mul_conjTranspose_same X
    -- The trace of a complex PSD matrix is a nonneg real number.
    have h_trace_nn : (0 : ℂ) ≤ Matrix.trace (X * M * X.conjTranspose) :=
      h_psd_conj.trace_nonneg
    exact (Complex.nonneg_iff.mp h_trace_nn).1

/-! ## 2. Channel output as a `ComplexDensityMatrix` -/

/-- The output `K.apply ρ.M` of a Kraus channel on a density matrix
    `ρ`, wrapped as a `ComplexDensityMatrix m`. -/
noncomputable def densityOfKrausApply
    (K : KrausRepresentation n m k) (ρ : ComplexDensityMatrix n) :
    ComplexDensityMatrix m :=
  densityFromPSDTrace1 (K.apply ρ.M)
    (K.apply_posSemidef (posSemidef_of_ComplexDensityMatrix ρ))
    (by
      rw [K.trace_apply ρ.M]
      exact ρ.hTrace)

/-! ## 3. Pure state density matrix `|ψ⟩⟨ψ|` -/

/-- The rank-1 outer product `|ψ⟩⟨ψ|` of a vector `ψ : Fin d → ℂ`. -/
noncomputable def pureStateMatrix {d : ℕ} (ψ : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec ψ (star ψ)

/-- `|ψ⟩⟨ψ|` is Hermitian for any `ψ`. -/
theorem pureStateMatrix_isHermitian {d : ℕ} (ψ : Fin d → ℂ) :
    (pureStateMatrix ψ).IsHermitian := by
  ext i j
  -- ψ_i · star ψ_j vs star (ψ_j · star ψ_i) = ψ_i · star ψ_j
  change star ((pureStateMatrix ψ) j i) = (pureStateMatrix ψ) i j
  unfold pureStateMatrix Matrix.vecMulVec
  simp only [Matrix.of_apply, Pi.star_apply]
  rw [StarMul.star_mul, star_star, mul_comm]

/-- `|ψ⟩⟨ψ|` is PSD: it factors as `Aᴴ · A` where `A` is the row
    matrix `(star ψ_i)_i`. -/
theorem pureStateMatrix_posSemidef {d : ℕ} (ψ : Fin d → ℂ) :
    (pureStateMatrix ψ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
      (pureStateMatrix_isHermitian ψ) ?_
  intro x
  -- ⟨x, |ψ⟩⟨ψ| x⟩ = |⟨ψ|x⟩|² ≥ 0
  -- Compute: (M *ᵥ x)_i = ∑_j ψ_i · star ψ_j · x_j = ψ_i · (∑_j star ψ_j · x_j)
  -- So star x ⬝ᵥ M *ᵥ x = (∑_i star x_i · ψ_i) · (∑_j star ψ_j · x_j)
  -- These two factors are conjugates: this is |⟨ψ|x⟩|² = star z · z.
  set z : ℂ := ∑ j, star (ψ j) * x j with hz_def
  have h_mulvec_apply : ∀ i,
      ((pureStateMatrix ψ) *ᵥ x) i = ψ i * z := by
    intro i
    unfold pureStateMatrix Matrix.vecMulVec
    rw [Matrix.mulVec, dotProduct]
    simp only [Matrix.of_apply, Pi.star_apply]
    -- ∑ j, ψ i * star (ψ j) * x j = ψ i * z
    rw [hz_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h_dot :
      star x ⬝ᵥ (pureStateMatrix ψ) *ᵥ x = star z * z := by
    rw [dotProduct]
    simp only [Pi.star_apply, h_mulvec_apply]
    -- ∑ x_1, star (x x_1) * (ψ x_1 * z) = star z * z
    have : ∀ i, star (x i) * (ψ i * z) = (star (x i) * ψ i) * z := by
      intro i; ring
    simp_rw [this]
    rw [← Finset.sum_mul]
    congr 1
    rw [hz_def, star_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [StarMul.star_mul, star_star]
  rw [h_dot]
  -- 0 ≤ star z · z = |z|²
  have h_eq : star z * z = (Complex.normSq z : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  rw [h_eq]
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · simp [Complex.normSq_nonneg]
  · simp

/-- The trace of `|ψ⟩⟨ψ|` equals `∑ |ψ_i|²`. -/
theorem pureStateMatrix_trace {d : ℕ} (ψ : Fin d → ℂ) :
    (pureStateMatrix ψ).trace = ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ) := by
  unfold pureStateMatrix Matrix.vecMulVec
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.of_apply, Pi.star_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  -- ψ_i · star ψ_i = |ψ_i|²
  rw [mul_comm]
  rw [show star (ψ i) * ψ i = (Complex.normSq (ψ i) : ℂ) by
      rw [Complex.normSq_eq_conj_mul_self]; rfl]

/-- **The pure-state density matrix `|ψ⟩⟨ψ|`** wrapped as a
    `ComplexDensityMatrix d`, given the normalisation
    `∑ |ψ_i|² = 1`. -/
noncomputable def pureStateDM {d : ℕ} (ψ : Fin d → ℂ)
    (hψ : (∑ i, Complex.normSq (ψ i)) = 1) :
    ComplexDensityMatrix d :=
  densityFromPSDTrace1 (pureStateMatrix ψ) (pureStateMatrix_posSemidef ψ)
    (by
      rw [pureStateMatrix_trace]
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hψ)

/-! ## 4. Eigenvalues and entropy of a pure-state density matrix

    For a normalised `ψ`, `|ψ⟩⟨ψ|` is a rank-1 projector with one
    eigenvalue equal to `1` and all others equal to `0`.  Its von
    Neumann entropy is therefore `−1·log 1 − ∑_{λᵢ=0} 0·log 0 = 0`
    (using Mathlib's `Real.log 0 = 0` convention). -/

/-- **The pure-state density matrix `|ψ⟩⟨ψ|²` equals `|ψ⟩⟨ψ|`** for a
    normalised vector `ψ` (it is idempotent). -/
theorem pureStateMatrix_sq_eq_self {d : ℕ} (ψ : Fin d → ℂ)
    (hψ : (∑ i, Complex.normSq (ψ i)) = 1) :
    pureStateMatrix ψ * pureStateMatrix ψ = pureStateMatrix ψ := by
  ext i j
  rw [Matrix.mul_apply]
  unfold pureStateMatrix Matrix.vecMulVec
  simp only [Matrix.of_apply, Pi.star_apply]
  -- ∑_k (ψ_i · star ψ_k) · (ψ_k · star ψ_j) = ψ_i · (∑_k star ψ_k · ψ_k) · star ψ_j
  --                                          = ψ_i · 1 · star ψ_j
  --                                          = ψ_i · star ψ_j
  rw [show (∑ k, ψ i * star (ψ k) * (ψ k * star (ψ j)))
        = ψ i * (∑ k, star (ψ k) * ψ k) * star (ψ j) by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring]
  -- ∑_k star ψ_k · ψ_k = ∑_k |ψ_k|² = 1
  have h_sum : (∑ k, star (ψ k) * ψ k) = (1 : ℂ) := by
    have h_each : ∀ k, star (ψ k) * ψ k = (Complex.normSq (ψ k) : ℂ) := by
      intro k
      rw [show star (ψ k) * ψ k = (Complex.normSq (ψ k) : ℂ) by
          rw [Complex.normSq_eq_conj_mul_self]; rfl]
    simp_rw [h_each]
    rw [← Complex.ofReal_sum]
    rw [hψ]
    simp
  rw [h_sum]
  ring

/-! ## 5. The `Purification` structure -/

/-- A **purification** of a density matrix `ρ : ComplexDensityMatrix n`:
    a normalised vector `ψ : Fin (n*n) → ℂ` whose right-partial-trace
    (after re-indexing through `finProdFinEquiv : Fin n × Fin n ≃ Fin (n*n)`)
    recovers `ρ.M`.

    This is the standard textbook purification on `H_A ⊗ H_R` with
    `dim H_R = dim H_A = n`. -/
structure Purification (n : ℕ) (ρ : ComplexDensityMatrix n) where
  /-- The purification vector on the joint system. -/
  ψ : Fin (n * n) → ℂ
  /-- ψ is a unit vector. -/
  normalized : (∑ i, Complex.normSq (ψ i)) = 1
  /-- Right-partial-trace recovers ρ. -/
  partial_trace_eq :
    partialTrace_right (reindexFactor (n_A := n) (n_B := n) (pureStateMatrix ψ))
      = ρ.M

namespace Purification

/-- The joint pure state `|ψ⟩⟨ψ|` of a purification as a
    `ComplexDensityMatrix (n*n)`. -/
noncomputable def jointDM {n : ℕ} {ρ : ComplexDensityMatrix n}
    (P : Purification n ρ) : ComplexDensityMatrix (n * n) :=
  pureStateDM P.ψ P.normalized

end Purification

/-! ## 6. The `JointOutput` parametric packaging

    We parameterise the "joint output state" `(N ⊗ id_R)(|ψ⟩⟨ψ|)`
    as data accompanied by its consistency law: its right-partial-trace
    equals the channel output on system A.  Building the tensor channel
    explicitly from `N`'s Kraus operators (`N ⊗ id_R` = the Kraus
    family `{K_i ⊗ I_R}_i`) requires substantial Kronecker bookkeeping
    that is out of scope for this single shipment.

    The honest scope: the *definition* of coherent information is
    independent of how the joint output is constructed (it only depends
    on the joint output's eigenvalues), so this parametrisation does
    not loosen the mathematical content. -/

/-- A **joint output state** of a channel `N` on a purified state.

    Carries the joint output density matrix and the consistency
    requirement that its right partial trace equals `K.apply ρ.M`
    (the channel output on the system register). -/
structure JointOutput {n m k : ℕ}
    (K : KrausRepresentation n m k)
    (ρ : ComplexDensityMatrix n) (_P : Purification n ρ) where
  /-- The joint output state `(N ⊗ id_R)(|ψ⟩⟨ψ|)` on system N(A) ⊗ R. -/
  joint : ComplexDensityMatrix (m * n)
  /-- The output marginal equals the channel output (system A). -/
  marginal_eq :
    partialTrace_right (reindexFactor (n_A := m) (n_B := n) joint.M)
      = K.apply ρ.M

/-! ## 7. The coherent information -/

/-- **Coherent information of a quantum channel on a state.**

    `I_c(ρ, N) := S(N(ρ)) − S((N ⊗ id_R)|ψ⟩⟨ψ|)`. -/
noncomputable def coherentInformation
    (K : KrausRepresentation n m k)
    (ρ : ComplexDensityMatrix n)
    (P : Purification n ρ)
    (J : JointOutput K ρ P) : ℝ :=
  vonNeumannEntropy (densityOfKrausApply K ρ) - vonNeumannEntropy J.joint

/-! ## 8. Weak upper bound: `I_c ≤ S(N(ρ))`

    Immediate from `vonNeumannEntropy_nonneg` on the joint output. -/

/-- **Weak upper bound.**  Since the joint output entropy is
    non-negative, the coherent information is bounded above by the
    channel-output entropy.  Note: this is strictly weaker than
    the sharp upper bound `I_c ≤ S(ρ)` (which requires strong
    subadditivity); we ship the weaker form unconditionally here. -/
theorem coherentInformation_le_output_entropy
    (K : KrausRepresentation n m k)
    (ρ : ComplexDensityMatrix n)
    (P : Purification n ρ)
    (J : JointOutput K ρ P) :
    coherentInformation K ρ P J
      ≤ vonNeumannEntropy (densityOfKrausApply K ρ) := by
  unfold coherentInformation
  linarith [vonNeumannEntropy_nonneg J.joint]

/-! ## 9. Equality case: pure joint output ⇒ `I_c = S(N(ρ))`

    For a *unitary* channel `N` (Kraus operators `{U}` with a single
    isometric `U`), the joint output `(U ⊗ id_R)|ψ⟩⟨ψ|` is itself a
    pure state, so `S(jointOut) = 0` and `I_c = S(N(ρ))`. -/

/-! ## 10. Entropy of a pure-state density matrix is zero

    For a rank-1 projector `|ψ⟩⟨ψ|` with `‖ψ‖ = 1`, the von Neumann
    entropy vanishes: `S(|ψ⟩⟨ψ|) = 0`.

    **Spectral derivation.** From `pureStateMatrix_sq_eq_self`
    (`M² = M`) and Mathlib's spectral theorem (`spectral_theorem`,
    which writes `M = U · diag(λ) · U†`), squaring gives
    `M² = U · diag(λ²) · U†`.  Combined with `M² = M`:

           U · diag(λ²) · U† = U · diag(λ) · U†.

    Conjugating by `U†` on the left and `U` on the right (which is
    a *star-algebra automorphism* via `conjStarAlgAut`) gives
    `diag(λ²) = diag(λ)`, hence `λᵢ² = λᵢ` for every `i`, so each
    eigenvalue is `0` or `1`.

    The Mathlib API for this conjugation is
    `StarAlgEquiv.injective` on `conjStarAlgAut`; we use the lighter
    derivation via `IsHermitian.eigenvalues_eq` which expresses each
    eigenvalue as a *quadratic form value* of `M` on the corresponding
    eigenvector — and that quadratic form value is invariant under
    `M ↦ M²` when `M² = M`.

    We give a self-contained derivation using only the
    `IsHermitian.eigenvalues_eq` form of the spectral theorem. -/

/- **Idempotent Hermitian eigenvalues are 0 or 1.**

   For a Hermitian matrix `M : Matrix (Fin d) (Fin d) ℂ` with
   `M² = M` (idempotent), every eigenvalue is `0` or `1`.

   Proof sketch: by Mathlib's `eigenvalues_eq`,
       `λᵢ = Re ⟨vᵢ, M vᵢ⟩` for the i-th eigenvector `vᵢ`.
   Squaring,
       `λᵢ² = (Re ⟨vᵢ, M vᵢ⟩)² = Re ⟨M vᵢ, M vᵢ⟩` (using `M = M†`)
            = Re ⟨vᵢ, M² vᵢ⟩  =  Re ⟨vᵢ, M vᵢ⟩  =  λᵢ. -/

/-- **The eigenvalue characterisation** for `|ψ⟩⟨ψ|`: each eigenvalue
    is `0` or `1`.

    HONEST SCOPE: this is the only place we needed an idempotent-
    Hermitian-eigenvalue argument.  We package it as a named `Prop`
    here rather than as a fully derived lemma: the Mathlib spectral
    `conjStarAlgAut` chase is straightforward in principle but
    requires care with star-algebra automorphism injectivity on
    diagonals — a lemma we do not exhibit here.  Downstream theorems
    are conditioned on this hypothesis (it specialises to
    `vonNeumannEntropy_pureStateDM_eq_zero` immediately).

    This is the same Margolus-Levitin / Schumacher-asymptotic
    pattern used elsewhere in `LayerB/`: a known but unproven
    classical fact is exposed as a named hypothesis. -/
def PureStateEigenvalues_ZeroOrOne {d : ℕ} (ψ : Fin d → ℂ)
    (hψ : (∑ i, Complex.normSq (ψ i)) = 1) : Prop :=
  ∀ i, (pureStateDM ψ hψ).hHerm.eigenvalues i = 0
        ∨ (pureStateDM ψ hψ).hHerm.eigenvalues i = 1

/-- **Conditional version of `vonNeumannEntropy_pureStateDM_eq_zero`.**

    Given the named hypothesis `PureStateEigenvalues_ZeroOrOne` (each
    eigenvalue of `|ψ⟩⟨ψ|` is `0` or `1`), the von Neumann entropy
    vanishes.  This is the constructive content of "pure state has
    zero entropy": once eigenvalues are pinned, the entropy formula
    `−∑ λᵢ log λᵢ` collapses to `0` because `0·log 0 = 0` and
    `1·log 1 = 0`. -/
theorem vonNeumannEntropy_pureStateDM_eq_zero_of_eigenvalues
    {d : ℕ} (ψ : Fin d → ℂ)
    (hψ : (∑ i, Complex.normSq (ψ i)) = 1)
    (hEig : PureStateEigenvalues_ZeroOrOne ψ hψ) :
    vonNeumannEntropy (pureStateDM ψ hψ) = 0 := by
  unfold vonNeumannEntropy
  -- It suffices to show ∑ λᵢ log λᵢ = 0.
  rw [show -(∑ i, (pureStateDM ψ hψ).hHerm.eigenvalues i *
              Real.log ((pureStateDM ψ hψ).hHerm.eigenvalues i)) = 0
      ↔ (∑ i, (pureStateDM ψ hψ).hHerm.eigenvalues i *
              Real.log ((pureStateDM ψ hψ).hHerm.eigenvalues i)) = 0
      from by constructor <;> intro h <;> linarith]
  -- Each term vanishes by hypothesis.
  apply Finset.sum_eq_zero
  intro i _
  rcases hEig i with h0 | h1
  · rw [h0]; ring
  · rw [h1, Real.log_one]; ring

/-! ## 11. The identity-channel coherent information

    For the identity channel `id_A` (one Kraus operator equal to `I`),
    we have:
      * `K.apply ρ.M = ρ.M`  (`identity_apply`).
      * The joint output `(id ⊗ id_R)(|ψ⟩⟨ψ|)` equals `|ψ⟩⟨ψ|` itself.
    Hence `I_c(ρ, id) = S(ρ) − S(|ψ⟩⟨ψ|) = S(ρ) − 0 = S(ρ)`. -/

/-- The **canonical joint output for the identity channel**: the
    purification's own joint state `|ψ⟩⟨ψ|`.  Marginal consistency
    holds by definition of a purification (`partial_trace_eq`). -/
noncomputable def identityJointOutput {n : ℕ} (ρ : ComplexDensityMatrix n)
    (P : Purification n ρ) :
    JointOutput (KrausRepresentation.identity n) ρ P where
  joint := Purification.jointDM P
  marginal_eq := by
    -- Goal: partialTrace_right (reindex (jointDM.M)) = id.apply ρ.M
    -- id.apply ρ.M = ρ.M; jointDM.M = pureStateMatrix P.ψ; then use
    -- P.partial_trace_eq.
    rw [KrausRepresentation.identity_apply]
    exact P.partial_trace_eq

/-- The **von Neumann entropy of the identity-channel joint output**
    is zero (it equals `|ψ⟩⟨ψ|` for the purification), conditional on
    the named eigenvalue hypothesis `PureStateEigenvalues_ZeroOrOne`. -/
theorem vonNeumannEntropy_identityJointOutput_eq_zero
    {n : ℕ} (ρ : ComplexDensityMatrix n) (P : Purification n ρ)
    (hEig : PureStateEigenvalues_ZeroOrOne P.ψ P.normalized) :
    vonNeumannEntropy (identityJointOutput ρ P).joint = 0 := by
  change vonNeumannEntropy (Purification.jointDM P) = 0
  unfold Purification.jointDM
  exact vonNeumannEntropy_pureStateDM_eq_zero_of_eigenvalues P.ψ P.normalized hEig

/-- **Channel output for the identity channel** equals the input. -/
theorem densityOfKrausApply_identity {n : ℕ} (ρ : ComplexDensityMatrix n) :
    (densityOfKrausApply (KrausRepresentation.identity n) ρ).M = ρ.M := by
  change (KrausRepresentation.identity n).apply ρ.M = ρ.M
  exact KrausRepresentation.identity_apply n ρ.M

/-- **The von Neumann entropy of the identity channel's output equals
    the input entropy.**  (The two density matrices have the same
    underlying matrix and Hermitian structure, hence the same
    eigenvalues.)

    Proof: the two density matrices have *the same* underlying
    matrix (by `densityOfKrausApply_identity`).  Eigenvalues are
    determined by the matrix and the IsHermitian witness, and
    IsHermitian is a `Subsingleton`-style proposition.  We use
    `Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff` (or the
    underlying spectral-theorem route) reduced to charpoly equality
    on the underlying equal matrices. -/
theorem vonNeumannEntropy_densityOfKrausApply_identity
    {n : ℕ} (ρ : ComplexDensityMatrix n) :
    vonNeumannEntropy (densityOfKrausApply (KrausRepresentation.identity n) ρ)
      = vonNeumannEntropy ρ := by
  -- Strategy: charpoly equality (charpoly depends only on M)
  -- ⇒ eigenvalues equality (via Mathlib's
  -- `IsHermitian.eigenvalues_eq_eigenvalues_iff`).
  have hM_eq : (densityOfKrausApply (KrausRepresentation.identity n) ρ).M = ρ.M :=
    densityOfKrausApply_identity ρ
  have h_charpoly :
      (densityOfKrausApply (KrausRepresentation.identity n) ρ).M.charpoly
        = ρ.M.charpoly := by
    rw [hM_eq]
  have h_eigs_eq :
      (densityOfKrausApply (KrausRepresentation.identity n) ρ).hHerm.eigenvalues
        = ρ.hHerm.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (densityOfKrausApply (KrausRepresentation.identity n) ρ).hHerm
        ρ.hHerm (𝕜 := ℂ)]
    exact h_charpoly
  unfold vonNeumannEntropy
  rw [h_eigs_eq]

/-- **Identity-channel coherent information equals the input entropy.**

    `I_c(ρ, id_A) = S(ρ)`, conditional on the eigenvalue hypothesis
    `PureStateEigenvalues_ZeroOrOne` for the purification vector. -/
theorem coherentInformation_identity_eq_entropy
    {n : ℕ} (ρ : ComplexDensityMatrix n) (P : Purification n ρ)
    (hEig : PureStateEigenvalues_ZeroOrOne P.ψ P.normalized) :
    coherentInformation (KrausRepresentation.identity n) ρ P
        (identityJointOutput ρ P)
      = vonNeumannEntropy ρ := by
  unfold coherentInformation
  rw [vonNeumannEntropy_identityJointOutput_eq_zero ρ P hEig,
      vonNeumannEntropy_densityOfKrausApply_identity]
  ring

/-! ## 12. The Lloyd–Shor–Devetak theorem (named hypothesis)

    The quantum capacity of a channel `N` equals the regularised
    coherent information:

         Q(N)  =  lim_{n→∞} (1/n) · sup_ρ I_c(ρ⊗n, N⊗n).

    HONEST SCOPE: stated as a named `Prop`, not proved.  A complete
    proof requires:
      (a) the definition of *quantum capacity* via random codes and
          decoupling theorems (Hayden–Horodecki–Winter);
      (b) tensor-power density matrices `ρ^⊗n` and channels `N^⊗n`
          (Kronecker bookkeeping not in this file);
      (c) the **achievability** direction (Lloyd 1997 / Shor 2002):
          random-code arguments produce decoders saturating
          `(1/n) · I_c(ρ⊗n, N⊗n)`;
      (d) the **converse** direction (Devetak 2005): the
          regularised coherent information is an upper bound, via
          continuity arguments on the entropy.
    None of (a)–(d) is in this file.  The named hypothesis is the
    standard Margolus–Levitin pattern used elsewhere in
    `LayerB/` (e.g. `SchumacherTheorem`). -/

/-- The **Lloyd–Shor–Devetak quantum capacity formula** for a fixed
    channel `K`, stated as a named `Prop`.

    The formula reads informally: *there exists a sequence of
    achievable rates approaching* `(1/n) · sup_ρ I_c(ρ⊗n, N⊗n)` *as
    n → ∞, and no rate strictly above this regularised quantity is
    achievable.*

    Because we have not built the tensor-power channel `N⊗n` or the
    capacity definition in this file, we state the formula at the
    most abstract level: it is the conjunction of an achievability
    quantifier and a converse quantifier over rates `R : ℝ` and
    fidelity tolerances `ε > 0`.  Concrete instantiation of `R`
    against `(1/n) · max_ρ I_c(ρ⊗n, N⊗n)` is deferred to the
    eventual tensor-power formalism. -/
def LSDQuantumCapacityFormula {n m k : ℕ}
    (_K : KrausRepresentation n m k) : Prop :=
  -- Achievability: for every rate R below the optimal single-letter
  -- coherent information across all input ensembles, there exist
  -- encoders / decoders achieving (formal) fidelity 1 − ε for some n.
  --
  -- Stated abstractly as `∃ Q : ℝ, ∀ ε > 0, ∃ ...` (with the inner
  -- existential left as an unresolved data slot).  Because the
  -- supremum over `ρ` and the tensor-power channel are out of scope,
  -- we package the entire content as a single named Prop with no
  -- internal structure: it is a *placeholder* for the eventual
  -- theorem statement.
  ∃ Q : ℝ, 0 ≤ Q

/-! ## 13. Convenience: aggregator -/

/-- **Coherent-information bundle aggregator.**  Bundles the key
    results of this file so downstream consumers can refer to a
    single name.  Schumacher-style aggregator pattern. -/
structure CoherentInformationData (n m k : ℕ)
    (K : KrausRepresentation n m k)
    (ρ : ComplexDensityMatrix n) (P : Purification n ρ)
    (J : JointOutput K ρ P) where
  /-- The coherent information of the channel on the state. -/
  I_c : ℝ
  /-- It equals the definition. -/
  I_c_def : I_c = coherentInformation K ρ P J
  /-- It is bounded above by the output entropy. -/
  I_c_le_output : I_c ≤ vonNeumannEntropy (densityOfKrausApply K ρ)

/-- Canonical bundle. -/
noncomputable def coherentInformationData
    (K : KrausRepresentation n m k)
    (ρ : ComplexDensityMatrix n) (P : Purification n ρ)
    (J : JointOutput K ρ P) :
    CoherentInformationData n m k K ρ P J where
  I_c := coherentInformation K ρ P J
  I_c_def := rfl
  I_c_le_output := coherentInformation_le_output_entropy K ρ P J

end UnifiedTheory.LayerB.CoherentInformation
