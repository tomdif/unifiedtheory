/-
  LayerB/BlochO3Classification.lean — SU(2) → SO(3) cover and the
  O(3) classification of Bloch-sphere isometries (named-target form).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  GOAL OF THIS FILE

  Reduce `BlochO3_classification` (the named subgate in
  `WignerHardQubit.lean`) to a SHARP, SINGLE-POINT structural
  hypothesis: that every Wigner symmetry of the qubit, viewed
  as an isometry of the Bloch sphere `S² ⊂ ℝ³`, decomposes as

      (SU(2) rotation)  ∘  (optional coordinatewise complex
                            conjugation on the underlying qubit).

  This is the standard textbook recipe:

    • SU(2) double-covers SO(3) via Pauli conjugation
        R_U(v) := U · (v · σ) · U†,                  (1)
      sending the unit Bloch vector
        v_ψ = b̂(ψ) ∈ S²
      of a qubit state ψ to the unit Bloch vector of `U·ψ`.
      Both U and -U give the same R_U, so SO(3) = SU(2)/Z₂.

    • Coordinatewise complex conjugation of the qubit `ψ ↦ ψ̄`
      acts on the Bloch vector by FLIPPING the y-component
      (and leaving x, z fixed):
        b̂(ψ̄) = (v_x, -v_y, v_z).
      This is a reflection across the xz-plane (det -1 ∈ O(3)).

    • Every O(3) element factors as SO(3) ∘ (1 or reflection),
      so every Bloch-sphere isometry comes from SU(2) or
      SU(2) ∘ (complex conjugation) acting on the qubit.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED UNCONDITIONALLY

  - `paulVecToMatrix`        : the linear map  ℝ³ → Mat₂(ℂ)
                                v ↦ vₓ·σₓ + vᵧ·σᵧ + v_z·σ_z.
  - `paulVecToMatrix_zero`   : zero vector ↦ zero matrix.
  - `paulVecToMatrix_blochVector_diag`  : diagonal entries
                                are exactly `±b_z(ψ)`.
  - `conjVec_flips_bloch_y`  : `b̂(ψ̄) = (b_x, -b_y, b_z)`,
                                the explicit y-flip identity.
  - `conjVec_rnormSq_blochUnit` : the y-flipped vector still
                                has unit norm.

  WHAT IS GATED (named target)

  - `O3_decomposition_Target`        : "Every Bloch-sphere
                                Wigner symmetry equals SU(2)
                                conjugation possibly preceded
                                by coordinatewise conjugation,
                                at the level of rays."
                                A single sharp Prop bundling
                                (i) the SU(2)→SO(3) cover
                                (ii) the O(3) = SO(3) ⊔ −SO(3)
                                splitting
                                (iii) "complex conjugation = y-flip".

  - `blochO3_classification_holds` :
                                Conditional discharge of
                                `BlochO3_classification` from
                                `O3_decomposition_Target`. By
                                construction (the target is the
                                statement of the gate), this is
                                immediate.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  This file does NOT formalise the SU(2)→SO(3) two-fold cover
  (Pauli triple-conjugation identity, det-preserving action)
  or the O(3) = SO(3) ⊔ −SO(3) splitting. Those are themselves
  multi-day Lean projects against current Mathlib. They are
  bundled into the single named target
  `O3_decomposition_Target`, which is verbatim the conclusion
  of the gate `BlochO3_classification`. The reduction is therefore
  PROVABLE BY DEFINITION — but the named target now packages a
  precise, structurally minimal statement that downstream work
  can discharge.

  Zero `sorry`.  Zero custom `axiom`.
-/

import UnifiedTheory.LayerB.WignerHardQubit
import UnifiedTheory.LayerC.BipartiteQubitCHSH

set_option relaxedAutoImplicit false
set_option linter.style.show false

namespace UnifiedTheory.LayerB.BlochO3Classification

open Matrix Complex
open scoped ComplexConjugate
open UnifiedTheory.LayerB.WignerTheorem
open UnifiedTheory.LayerB.WignerHardQubit
open UnifiedTheory.LayerC.BipartiteQubitCHSH

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: PAULI Y (the third Pauli matrix)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    σx and σz live in `LayerC.BipartiteQubitCHSH`; we add σy for
    the Pauli-vector construction.  σy = !![0, -i; i, 0]. -/

/-- Pauli Y. -/
def σy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- σy is Hermitian. -/
theorem σy_isHermitian : σy.IsHermitian := by
  unfold Matrix.IsHermitian σy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Complex.conj_I]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: PAULI-VECTOR MATRIX  v ↦ v·σ
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Pauli-vector matrix associated to `v ∈ ℝ³`:

        paulVecToMatrix v := vₓ·σₓ + vᵧ·σᵧ + v_z·σ_z.

    This is a Hermitian 2×2 matrix of trace 0; its eigenvalues
    are ±‖v‖. The map v ↦ v·σ is an ℝ-linear isomorphism from
    ℝ³ onto the traceless Hermitian 2×2 matrices.

    Under it, SU(2) acts on ℝ³ by conjugation
        R_U(v) := the unique vector with U·(v·σ)·U† = R_U(v)·σ,
    realising the standard two-fold cover SU(2) → SO(3). -/
noncomputable def paulVecToMatrix (v : Fin 3 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (v 0 : ℂ) • σx + (v 1 : ℂ) • σy + (v 2 : ℂ) • σz

/-- `paulVecToMatrix` sends the zero vector to the zero matrix. -/
theorem paulVecToMatrix_zero :
    paulVecToMatrix (fun _ => (0 : ℝ)) = 0 := by
  unfold paulVecToMatrix
  simp

/-- Explicit entries of `paulVecToMatrix v`. -/
theorem paulVecToMatrix_entries (v : Fin 3 → ℝ) :
    paulVecToMatrix v 0 0 = (v 2 : ℂ)
  ∧ paulVecToMatrix v 0 1 = (v 0 : ℂ) - Complex.I * (v 1 : ℂ)
  ∧ paulVecToMatrix v 1 0 = (v 0 : ℂ) + Complex.I * (v 1 : ℂ)
  ∧ paulVecToMatrix v 1 1 = -(v 2 : ℂ) := by
  unfold paulVecToMatrix σx σy σz
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.add_apply, smul_eq_mul] <;> ring

/-- `paulVecToMatrix v` is Hermitian. -/
theorem paulVecToMatrix_isHermitian (v : Fin 3 → ℝ) :
    (paulVecToMatrix v).IsHermitian := by
  have h_real_smul : ∀ (c : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ),
      M.IsHermitian → ((c : ℂ) • M).IsHermitian := by
    intro c M hM
    unfold Matrix.IsHermitian at hM ⊢
    rw [Matrix.conjTranspose_smul, hM]
    rw [show star (c : ℂ) = (c : ℂ) from by
          rw [Complex.star_def, Complex.conj_ofReal]]
  unfold paulVecToMatrix
  exact ((h_real_smul _ _ σx_isHermitian).add (h_real_smul _ _ σy_isHermitian)).add
        (h_real_smul _ _ σz_isHermitian)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: DIAGONAL ENTRIES OF  b(ψ)·σ
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a qubit  ψ ∈ ℂ²,  the diagonal entries of the Pauli-vector
    matrix of the Bloch vector  b(ψ)  recover  ±b_z(ψ). -/

/-- The (0,0) and (1,1) entries of `paulVecToMatrix (blochVector ψ)`
    are `+b_z(ψ)` and `-b_z(ψ)` respectively. -/
theorem paulVecToMatrix_blochVector_diag (ψ : Fin 2 → ℂ) :
    paulVecToMatrix (blochVector ψ) 0 0 = (blochVector ψ 2 : ℂ)
  ∧ paulVecToMatrix (blochVector ψ) 1 1 = -(blochVector ψ 2 : ℂ) := by
  obtain ⟨h00, _, _, h11⟩ := paulVecToMatrix_entries (blochVector ψ)
  exact ⟨h00, h11⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: COMPLEX CONJUGATION ↔ y-REFLECTION ON THE BLOCH SPHERE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Coordinatewise complex conjugation of the qubit
        K : ψ = (ψ₀, ψ₁) ↦ (conj ψ₀, conj ψ₁)
    acts on the Bloch vector by flipping the y-component:
        b̂(K ψ) = (b_x, -b_y, b_z).

    Computational proof:
      b_x : Re(conj ψ₀ · ψ₁)  invariant under  K  (Re unchanged
                                                   when both args
                                                   are conjugated;
                                                   star ∘ star = id).
      b_z : |ψ₀|² - |ψ₁|²    invariant under K (|conj z| = |z|).
      b_y : Im(conj ψ₀ · ψ₁) NEGATES under K
            (Im(conj(conj a)·conj b) = Im(a · conj b)
             = -Im(conj a · b)).
-/

/-- `blochVector` entries on the conjugated vector.  Direct
    computation: x and z are invariant, y NEGATES. -/
theorem conjVec_flips_bloch_y (ψ : Fin 2 → ℂ) :
    blochVector (conjVec ψ) 0 = blochVector ψ 0
  ∧ blochVector (conjVec ψ) 1 = -(blochVector ψ 1)
  ∧ blochVector (conjVec ψ) 2 = blochVector ψ 2 := by
  -- Common step: conjVec ψ k = conj (ψ k) (definitional under `star = conj` on ℂ).
  have hcv : ∀ k, conjVec ψ k = conj (ψ k) := fun k => rfl
  refine ⟨?_, ?_, ?_⟩
  · -- x: 2 · Re(conj(conj ψ₀) · conj ψ₁) = 2 · Re(ψ₀ · conj ψ₁)
    --      = 2 · Re(star(conj ψ₀ · ψ₁)) = 2 · Re(conj ψ₀ · ψ₁).
    rw [blochVector_zero, blochVector_zero, hcv 0, hcv 1]
    -- Goal: 2 * (conj (conj (ψ 0)) * conj (ψ 1)).re = 2 * (conj (ψ 0) * ψ 1).re
    rw [Complex.conj_conj]
    -- Goal: 2 * (ψ 0 * conj (ψ 1)).re = 2 * (conj (ψ 0) * ψ 1).re
    -- (ψ 0 * conj (ψ 1)) = conj (conj (ψ 0) * ψ 1), so .re is preserved.
    have hcalc : ψ 0 * conj (ψ 1) = conj (conj (ψ 0) * ψ 1) := by
      rw [map_mul, Complex.conj_conj]
    rw [hcalc, Complex.conj_re]
  · -- y: 2 · Im(conj(conj ψ₀) · conj ψ₁) = 2 · Im(ψ₀ · conj ψ₁) = -2·Im(conj ψ₀ · ψ₁).
    rw [blochVector_one, blochVector_one, hcv 0, hcv 1]
    rw [Complex.conj_conj]
    -- Goal: 2 * (ψ 0 * conj (ψ 1)).im = -(2 * (conj (ψ 0) * ψ 1).im)
    have hcalc : ψ 0 * conj (ψ 1) = conj (conj (ψ 0) * ψ 1) := by
      rw [map_mul, Complex.conj_conj]
    rw [hcalc, Complex.conj_im]
    ring
  · -- z: |conj ψ₀|² - |conj ψ₁|² = |ψ₀|² - |ψ₁|²  (normSq invariant under conjugation).
    rw [blochVector_two, blochVector_two, hcv 0, hcv 1]
    rw [Complex.normSq_conj, Complex.normSq_conj]

/-! ### Bloch-unit version of the y-flip identity. -/

/-- The y-flip on a unit Bloch vector preserves unit norm.

    The flipped vector `(v_x, -v_y, v_z)` has the same `rnormSq`
    as `v`, because `(-v_y)² = v_y²`. -/
theorem rnormSq_yflip (v : Fin 3 → ℝ) :
    rnormSq (fun k => if k = 1 then -(v k) else v k) = rnormSq v := by
  rw [rnormSq_expand, rnormSq_expand]
  -- The three entries: k = 0 (unchanged), k = 1 (negated), k = 2 (unchanged).
  -- The `if` reduces by `decide` at each value.
  simp only [show ((0 : Fin 3) = 1) = False from by decide,
             show ((2 : Fin 3) = 1) = False from by decide,
             if_true, if_false]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: SU(2) ROTATION = PAULI-VECTOR CONJUGATION
            (STATED AS NAMED PROPERTY OF EACH UNITARY)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For each U ∈ SU(2) (or more generally each unitary U ∈ U(2)),
    there exists R_U ∈ SO(3) such that

        U · (v·σ) · U†  =  (R_U v) · σ                  (*)

    for every v ∈ ℝ³.  This is the SU(2)/U(2) → SO(3) homomorphism;
    its kernel on U(2) is the U(1) center, and on SU(2) is Z₂.

    We state (*) as a named PROPERTY of a single unitary, packaged
    so the gate `O3_decomposition_Target` can quote it. -/

/-- Property: U conjugation acts as a rotation on the Pauli vector. -/
def IsSu2RotationOf (U : Matrix (Fin 2) (Fin 2) ℂ)
    (R : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : Prop :=
  ∀ v : Fin 3 → ℝ,
    U * paulVecToMatrix v * Uᴴ = paulVecToMatrix (R v)

/-- Property: R is an isometry of `S²` (preserves the unit norm
    and Euclidean dot product). -/
def IsBlochSphereIsometry (R : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : Prop :=
  (∀ v : Fin 3 → ℝ, rnormSq v = 1 → rnormSq (R v) = 1) ∧
  (∀ v w : Fin 3 → ℝ, rnormSq v = 1 → rnormSq w = 1 →
      rdot (R v) (R w) = rdot v w)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE NAMED O(3)-DECOMPOSITION TARGET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The structural-mathematics statement that consolidates

        (i)   SU(2) → SO(3) is surjective via Pauli conjugation;
        (ii)  O(3) = SO(3) ⊔ (SO(3) ∘ y-reflection);
        (iii) coordinatewise complex conjugation of the qubit
              realises the y-reflection on the Bloch sphere
              (proved in `conjVec_flips_bloch_y` above).

    Bundling them gives a single Prop: every Wigner symmetry of
    the qubit is, on rays, either

       ψ  ↦  U *ᵥ ψ                       (unitary case, SO(3))
       ψ  ↦  V *ᵥ (conj ψ)                (antiunitary case, O(3) \ SO(3))

    for some unitary U or V ∈ U(2). -/

/-- **Named target**: every Wigner symmetry of the qubit decomposes
    as a unitary or antiunitary action on the underlying ℂ² rays.

    By construction, this is verbatim the statement of
    `BlochO3_classification` — but we package it under a memorable
    name so downstream work (the multi-day SU(2)→SO(3) cover + O(3)
    decomposition formalisation) targets a sharp, single-point gate. -/
def O3_decomposition_Target : Prop :=
  ∀ T : Ray 2 → Ray 2, IsWignerSymmetry T →
    (∃ U : Matrix (Fin 2) (Fin 2) ℂ,
        U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        ∀ ψ : Ray 2, VecRayEquiv (T ψ).val (U *ᵥ ψ.val))
    ∨
    (∃ V : Matrix (Fin 2) (Fin 2) ℂ,
        V ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        ∀ ψ : Ray 2, VecRayEquiv (T ψ).val (V *ᵥ (conjVec ψ.val)))

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: CONDITIONAL DISCHARGE OF `BlochO3_classification`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Conditional discharge of `BlochO3_classification`.**

    By construction `O3_decomposition_Target` is the same Prop as
    `BlochO3_classification` — the named target was chosen to be
    EXACTLY the conclusion of the gate.  This is a `def`-level
    equality of propositions, closed by `id`. -/
theorem blochO3_classification_holds
    (h : O3_decomposition_Target) :
    BlochO3_classification := h

/-- The converse direction: `BlochO3_classification` reduces to
    `O3_decomposition_Target`. Together with the forward
    direction, this records that the named target is structurally
    minimal — it does not strengthen or weaken the gate. -/
theorem O3_decomposition_Target_of_BlochO3
    (h : BlochO3_classification) :
    O3_decomposition_Target := h

/-- Equivalence form: the named target IS the gate. -/
theorem O3_decomposition_Target_iff_BlochO3 :
    O3_decomposition_Target ↔ BlochO3_classification :=
  Iff.rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: COMPOSITE — WIGNER HARD QUBIT FROM THE TARGET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Wigner hard direction at n = 2 from the O(3) decomposition target.**

    Composes `blochO3_classification_holds` with the existing
    `wigner_hard_qubit` to discharge `WignerHardDirection 2` from
    the single named structural hypothesis
    `O3_decomposition_Target`. -/
theorem wigner_hard_qubit_from_target
    (h : O3_decomposition_Target) : WignerHardDirection 2 :=
  wigner_hard_qubit (blochO3_classification_holds h)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: HEADLINE SUMMARY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    What this file ships:

    (1) `paulVecToMatrix v := vₓ·σx + vᵧ·σy + v_z·σz`,
        the standard ℝ-linear map ℝ³ → traceless Hermitian 2×2
        complex matrices that powers the SU(2)→SO(3) cover.

    (2) `paulVecToMatrix_zero`, `paulVecToMatrix_entries`,
        `paulVecToMatrix_isHermitian`,
        `paulVecToMatrix_blochVector_diag`:
        explicit computational facts about the map.

    (3) `conjVec_flips_bloch_y` (THE KEY POSITIVE CONTENT):
        coordinatewise qubit conjugation flips the y-component
        of the Bloch vector and leaves x, z fixed — proved by
        direct calculation on `(conj ψ₀, conj ψ₁) ∈ ℂ²`.

    (4) `rnormSq_yflip`: y-flip preserves unit norm on ℝ³.

    (5) `IsSu2RotationOf` and `IsBlochSphereIsometry`:
        named properties packaging (i) the Pauli-conjugation
        identity for SU(2)→SO(3), (ii) the isometry property
        of a Bloch-sphere map. These are SHAPES into which the
        full SU(2)→SO(3) and O(3) classification theorems would
        be inserted.

    (6) `O3_decomposition_Target` (NAMED GATE):
        the single sharp Prop expressing the textbook O(3)
        classification of Bloch isometries, lifted to rays.

    (7) `blochO3_classification_holds`, `O3_decomposition_Target_iff_BlochO3`:
        equivalence with the existing named gate
        `BlochO3_classification`.

    (8) `wigner_hard_qubit_from_target`:
        composite — `WignerHardDirection 2` from the target.

    Zero `sorry`. Zero custom `axiom`. -/
theorem bloch_O3_classification_master :
    -- (a) paulVecToMatrix is well-defined and Hermitian.
    (∀ v : Fin 3 → ℝ, (paulVecToMatrix v).IsHermitian)
    -- (b) Complex conjugation flips the y-component.
  ∧ (∀ ψ : Fin 2 → ℂ,
        blochVector (conjVec ψ) 0 = blochVector ψ 0
      ∧ blochVector (conjVec ψ) 1 = -(blochVector ψ 1)
      ∧ blochVector (conjVec ψ) 2 = blochVector ψ 2)
    -- (c) y-flip preserves unit norm.
  ∧ (∀ v : Fin 3 → ℝ, rnormSq v = 1 →
        rnormSq (fun k => if k = 1 then -(v k) else v k) = 1)
    -- (d) The named target discharges the gate.
  ∧ (O3_decomposition_Target → BlochO3_classification)
    -- (e) The composite discharges `WignerHardDirection 2`.
  ∧ (O3_decomposition_Target → WignerHardDirection 2) :=
  ⟨paulVecToMatrix_isHermitian,
   conjVec_flips_bloch_y,
   fun v hv => by rw [rnormSq_yflip]; exact hv,
   blochO3_classification_holds,
   wigner_hard_qubit_from_target⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms paulVecToMatrix_isHermitian
#print axioms conjVec_flips_bloch_y
#print axioms rnormSq_yflip
#print axioms blochO3_classification_holds
#print axioms wigner_hard_qubit_from_target
#print axioms bloch_O3_classification_master

end UnifiedTheory.LayerB.BlochO3Classification
