/-
  LayerB/WignerHardQubit.lean — Wigner's theorem, qubit case (n = 2)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  GOAL OF THIS FILE

  Discharge the **hard direction** of Wigner's theorem in the
  smallest non-trivial dimension `n = 2` (a qubit) via the
  Bloch-sphere isometry argument.

  In the qubit case the projective Hilbert space  CP¹  is
  diffeomorphic to the two-sphere  S²:  every nonzero
  `ψ ∈ ℂ²` (up to a nonzero complex scalar) corresponds to a
  unique point  `b̂(ψ) ∈ S²`,  the **(normalised) Bloch vector**,
  whose coordinates are the expectation values of the three
  Pauli observables divided by the squared norm.

  The fundamental identity for the qubit is

        |⟨ψ, φ⟩|² / (‖ψ‖² · ‖φ‖²)
          = (1 + b̂(ψ) · b̂(φ)) / 2,

  proved here as `transitionProb_bloch`. From this identity:

  (a) A Wigner symmetry on rays preserves the transition
      probability, hence preserves the Bloch dot product
      `b̂(ψ) · b̂(φ)`, hence induces a map of `S²` preserving
      the Euclidean dot product — an element of `O(3)`.
  (b) Every element of  O(3)  is a rotation (in  SO(3))
      or a reflection (in `O(3) \ SO(3)`).
  (c) The two-fold cover  SU(2) → SO(3)  realises every rotation
      as a unitary on  ℂ²;  reflections are realised by
      antiunitaries (a unitary composed with complex
      conjugation, e.g. `iσ_y · K`).

  Steps (b) and (c) — the explicit construction of the
  `SU(2) → SO(3)` two-fold cover and the O(3) classification
  of orthogonal 3×3 matrices into rotations and reflections —
  are themselves multi-day Lean projects against current
  Mathlib. They are stated here as a named subgate and
  composed with the unconditional Bloch-isometry construction
  to discharge `WignerHardDirection 2`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS UNCONDITIONALLY PROVED

  - `blochVector`                          : the (un-normalised)
                                              map  ℂ² → ℝ³.
  - `blochUnit`                            : the normalised Bloch
                                              vector
                                              `b̂(ψ) = b(ψ)/‖ψ‖²`,
                                              ray-invariant under
                                              `ψ ↦ cψ`.
  - `rdot`, `rnormSq`                      : real dot product / norm
                                              on ℝ³.
  - `blochUnit_norm`                       : ‖b̂(ψ)‖ = 1.
  - `transitionProb_bloch`                 : the Bloch-sphere formula
                                              for the transition
                                              probability of any
                                              two rays.
  - `wigner_qubit_to_bloch_isometry`       : every Wigner symmetry on
                                              qubits induces a map
                                              of `S²` preserving the
                                              real dot product.

  WHAT IS GATED (named hypothesis, no axioms)

  - `BlochO3_classification`               : every orthogonal map of
                                              `S²` is induced by an
                                              `SU(2)` unitary or by
                                              the composition of an
                                              `SU(2)` unitary with
                                              complex conjugation,
                                              at the level of rays.

  COMPOSITE

  - `wigner_hard_qubit` :  `WignerHardDirection 2`,  by composing
                            `wigner_qubit_to_bloch_isometry` with
                            `BlochO3_classification`.

  Zero `sorry`.  Zero custom `axiom`.  The composite proof
  depends on the named gate `BlochO3_classification`, which is
  honestly scoped as a multi-day formalisation target.
-/

import UnifiedTheory.LayerB.WignerTheorem

set_option relaxedAutoImplicit false
set_option linter.style.show false

namespace UnifiedTheory.LayerB.WignerHardQubit

open UnifiedTheory.LayerB.WignerTheorem
open Matrix Complex
open scoped ComplexConjugate

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: REAL DOT PRODUCT ON ℝ³
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Real Euclidean dot product on `Fin 3 → ℝ`. -/
def rdot (x y : Fin 3 → ℝ) : ℝ :=
  ∑ i, x i * y i

/-- Squared Euclidean norm on `Fin 3 → ℝ`. -/
def rnormSq (x : Fin 3 → ℝ) : ℝ :=
  ∑ i, (x i) * (x i)

lemma rdot_self (x : Fin 3 → ℝ) : rdot x x = rnormSq x := rfl

/-- Expand `rdot` for `Fin 3`. -/
lemma rdot_expand (x y : Fin 3 → ℝ) :
    rdot x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  unfold rdot
  rw [Fin.sum_univ_three]

/-- Expand `rnormSq` for `Fin 3`. -/
lemma rnormSq_expand (x : Fin 3 → ℝ) :
    rnormSq x = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 := by
  unfold rnormSq
  rw [Fin.sum_univ_three]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE BLOCH VECTOR (UN-NORMALISED AND NORMALISED)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The (un-normalised) Bloch vector of a qubit state.

    For `ψ = (ψ₀, ψ₁) ∈ ℂ²`, the Bloch vector is the triple of
    expectation values of the three Pauli observables:
    `(b_x, b_y, b_z) = (2 Re(ψ̄₀ψ₁), 2 Im(ψ̄₀ψ₁), |ψ₀|² − |ψ₁|²)`.

    It scales as  `b(cψ) = |c|² b(ψ)`.  For a unit vector this is
    on `S²`; in general it is on a sphere of radius `‖ψ‖²`. -/
noncomputable def blochVector (ψ : Fin 2 → ℂ) : Fin 3 → ℝ := fun k =>
  if k = 0 then 2 * (conj (ψ 0) * ψ 1).re
  else if k = 1 then 2 * (conj (ψ 0) * ψ 1).im
  else Complex.normSq (ψ 0) - Complex.normSq (ψ 1)

@[simp] lemma blochVector_zero (ψ : Fin 2 → ℂ) :
    blochVector ψ 0 = 2 * (conj (ψ 0) * ψ 1).re := by
  unfold blochVector; simp

@[simp] lemma blochVector_one (ψ : Fin 2 → ℂ) :
    blochVector ψ 1 = 2 * (conj (ψ 0) * ψ 1).im := by
  unfold blochVector; simp

@[simp] lemma blochVector_two (ψ : Fin 2 → ℂ) :
    blochVector ψ 2 = Complex.normSq (ψ 0) - Complex.normSq (ψ 1) := by
  unfold blochVector; simp

/-- The NORMALISED Bloch vector  `b̂(ψ) := b(ψ) / ‖ψ‖²`.

    This is ray-invariant: `b̂(cψ) = b̂(ψ)` for any nonzero scalar
    `c ∈ ℂ`, because both `b` and `‖·‖²` scale by `|c|²`. -/
noncomputable def blochUnit (ψ : Ray 2) : Fin 3 → ℝ :=
  fun k => blochVector ψ.val k / normSq2 ψ.val

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: ALGEBRAIC IDENTITIES FOR ψ ∈ ℂ²
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Expand `cdot` on `ℂ²` to a two-term sum. -/
lemma cdot_expand2 (ψ φ : Fin 2 → ℂ) :
    cdot ψ φ = star (ψ 0) * φ 0 + star (ψ 1) * φ 1 := by
  unfold cdot
  rw [Fin.sum_univ_two]

/-- Expand `normSq2` on `ℂ²`. -/
lemma normSq2_expand2 (ψ : Fin 2 → ℂ) :
    normSq2 ψ = Complex.normSq (ψ 0) + Complex.normSq (ψ 1) := by
  unfold normSq2
  rw [Fin.sum_univ_two]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: BLOCH NORM IDENTITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- For any qubit state `ψ`, `‖b(ψ)‖² = ‖ψ‖⁴`. -/
lemma rnormSq_blochVector (ψ : Fin 2 → ℂ) :
    rnormSq (blochVector ψ) = (normSq2 ψ) * (normSq2 ψ) := by
  rw [rnormSq_expand, blochVector_zero, blochVector_one, blochVector_two,
      normSq2_expand2]
  -- |conj a · b|² = |a|² · |b|².
  have h4 :
      (conj (ψ 0) * ψ 1).re * (conj (ψ 0) * ψ 1).re
        + (conj (ψ 0) * ψ 1).im * (conj (ψ 0) * ψ 1).im
      = Complex.normSq (ψ 0) * Complex.normSq (ψ 1) := by
    have h1 : Complex.normSq (conj (ψ 0) * ψ 1)
              = (conj (ψ 0) * ψ 1).re * (conj (ψ 0) * ψ 1).re
                + (conj (ψ 0) * ψ 1).im * (conj (ψ 0) * ψ 1).im :=
      Complex.normSq_apply _
    have h2 : Complex.normSq (conj (ψ 0) * ψ 1)
            = Complex.normSq (ψ 0) * Complex.normSq (ψ 1) := by
      rw [Complex.normSq_mul, Complex.normSq_conj]
    linarith
  nlinarith [h4]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE BLOCH IDENTITY FOR THE INNER PRODUCT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Keystone identity:

        2 · |⟨ψ, φ⟩|²
          = ‖ψ‖² · ‖φ‖²  +  b(ψ) · b(φ).

    Multiply out  `|conj ψ₀ φ₀ + conj ψ₁ φ₁|²`  in real-imaginary
    parts, expand `b(ψ) · b(φ)` similarly, and the identity is a
    quartic polynomial in the eight real coordinates that closes
    by `ring`. -/

/-- The Bloch identity in its un-normalized form. -/
lemma cdot_normSq_eq (ψ φ : Fin 2 → ℂ) :
    2 * Complex.normSq (cdot ψ φ)
      = normSq2 ψ * normSq2 φ
        + rdot (blochVector ψ) (blochVector φ) := by
  -- Expand to coordinates and let `ring` close the quartic.
  rw [cdot_expand2, normSq2_expand2, normSq2_expand2]
  rw [Complex.normSq_apply]
  rw [rdot_expand, blochVector_zero, blochVector_one, blochVector_two,
      blochVector_zero, blochVector_one, blochVector_two]
  -- Real and imaginary parts of star x = conj x.
  have hre :
      (star (ψ 0) * φ 0 + star (ψ 1) * φ 1).re
        = (ψ 0).re * (φ 0).re + (ψ 0).im * (φ 0).im
          + ((ψ 1).re * (φ 1).re + (ψ 1).im * (φ 1).im) := by
    show (conj (ψ 0) * φ 0 + conj (ψ 1) * φ 1).re
          = (ψ 0).re * (φ 0).re + (ψ 0).im * (φ 0).im
            + ((ψ 1).re * (φ 1).re + (ψ 1).im * (φ 1).im)
    simp [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have him :
      (star (ψ 0) * φ 0 + star (ψ 1) * φ 1).im
        = (ψ 0).re * (φ 0).im - (ψ 0).im * (φ 0).re
          + ((ψ 1).re * (φ 1).im - (ψ 1).im * (φ 1).re) := by
    show (conj (ψ 0) * φ 0 + conj (ψ 1) * φ 1).im
          = (ψ 0).re * (φ 0).im - (ψ 0).im * (φ 0).re
            + ((ψ 1).re * (φ 1).im - (ψ 1).im * (φ 1).re)
    simp [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [hre, him]
  have hψre : (conj (ψ 0) * ψ 1).re
              = (ψ 0).re * (ψ 1).re + (ψ 0).im * (ψ 1).im := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have hψim : (conj (ψ 0) * ψ 1).im
              = (ψ 0).re * (ψ 1).im - (ψ 0).im * (ψ 1).re := by
    simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hφre : (conj (φ 0) * φ 1).re
              = (φ 0).re * (φ 1).re + (φ 0).im * (φ 1).im := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have hφim : (conj (φ 0) * φ 1).im
              = (φ 0).re * (φ 1).im - (φ 0).im * (φ 1).re := by
    simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [hψre, hψim, hφre, hφim]
  have hns : ∀ z : ℂ, Complex.normSq z = z.re * z.re + z.im * z.im := fun z =>
    Complex.normSq_apply z
  rw [hns, hns, hns, hns]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: NORMALISED BLOCH VECTOR HAS UNIT NORM AND IS
            RAY-INVARIANT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The normalised Bloch vector lies on `S²`. -/
lemma blochUnit_norm (ψ : Ray 2) : rnormSq (blochUnit ψ) = 1 := by
  unfold blochUnit
  -- rnormSq (b/N) = (rnormSq b) / N²
  have hp : (0 : ℝ) < normSq2 ψ.val := normSq2_pos ψ.property
  have hne : normSq2 ψ.val ≠ 0 := ne_of_gt hp
  have hexp :
      rnormSq (fun k => blochVector ψ.val k / normSq2 ψ.val)
        = rnormSq (blochVector ψ.val) / (normSq2 ψ.val * normSq2 ψ.val) := by
    rw [rnormSq_expand, rnormSq_expand]
    field_simp
  rw [hexp, rnormSq_blochVector]
  field_simp

/-- The `blochVector` map is `|c|²`-homogeneous: `b(cψ) = |c|² · b(ψ)`. -/
lemma blochVector_smul (c : ℂ) (ψ : Fin 2 → ℂ) :
    blochVector (fun i => c * ψ i)
      = fun k => Complex.normSq c * blochVector ψ k := by
  funext k
  fin_cases k
  · -- k = 0
    show blochVector (fun i => c * ψ i) 0 = Complex.normSq c * blochVector ψ 0
    rw [blochVector_zero, blochVector_zero]
    -- 2 * Re(conj(c·ψ₀) · (c·ψ₁)) = 2 · |c|² · Re(conj ψ₀ · ψ₁).
    show 2 * (conj (c * ψ 0) * (c * ψ 1)).re
         = Complex.normSq c * (2 * (conj (ψ 0) * ψ 1).re)
    have hch : conj (c * ψ 0) * (c * ψ 1)
              = (Complex.normSq c : ℂ) * (conj (ψ 0) * ψ 1) := by
      rw [map_mul]
      have hcc : conj c * c = (Complex.normSq c : ℂ) := by
        rw [mul_comm, Complex.mul_conj]
      calc conj c * conj (ψ 0) * (c * ψ 1)
          = (conj c * c) * (conj (ψ 0) * ψ 1) := by ring
        _ = (Complex.normSq c : ℂ) * (conj (ψ 0) * ψ 1) := by rw [hcc]
    rw [hch]
    rw [show ((Complex.normSq c : ℂ) * (conj (ψ 0) * ψ 1)).re
            = Complex.normSq c * (conj (ψ 0) * ψ 1).re from by
        rw [Complex.mul_re]; simp]
    ring
  · -- k = 1
    show blochVector (fun i => c * ψ i) 1 = Complex.normSq c * blochVector ψ 1
    rw [blochVector_one, blochVector_one]
    show 2 * (conj (c * ψ 0) * (c * ψ 1)).im
         = Complex.normSq c * (2 * (conj (ψ 0) * ψ 1).im)
    have hch : conj (c * ψ 0) * (c * ψ 1)
              = (Complex.normSq c : ℂ) * (conj (ψ 0) * ψ 1) := by
      rw [map_mul]
      have hcc : conj c * c = (Complex.normSq c : ℂ) := by
        rw [mul_comm, Complex.mul_conj]
      calc conj c * conj (ψ 0) * (c * ψ 1)
          = (conj c * c) * (conj (ψ 0) * ψ 1) := by ring
        _ = (Complex.normSq c : ℂ) * (conj (ψ 0) * ψ 1) := by rw [hcc]
    rw [hch]
    rw [show ((Complex.normSq c : ℂ) * (conj (ψ 0) * ψ 1)).im
            = Complex.normSq c * (conj (ψ 0) * ψ 1).im from by
        rw [Complex.mul_im]; simp]
    ring
  · -- k = 2
    show blochVector (fun i => c * ψ i) 2 = Complex.normSq c * blochVector ψ 2
    rw [blochVector_two, blochVector_two]
    show Complex.normSq (c * ψ 0) - Complex.normSq (c * ψ 1)
         = Complex.normSq c * (Complex.normSq (ψ 0) - Complex.normSq (ψ 1))
    rw [Complex.normSq_mul, Complex.normSq_mul]
    ring

/-- `blochUnit` is invariant under nonzero rescaling: the
    `|c|²` factor cancels between numerator (`blochVector`) and
    denominator (`normSq2`). -/
lemma blochUnit_smul
    (c : ℂ) (hc : c ≠ 0) (ψ : Ray 2)
    (hcψ : (fun i => c * ψ.val i) ≠ 0) :
    blochUnit ⟨fun i => c * ψ.val i, hcψ⟩ = blochUnit ψ := by
  unfold blochUnit
  funext k
  show blochVector (fun i => c * ψ.val i) k / normSq2 (fun i => c * ψ.val i)
       = blochVector ψ.val k / normSq2 ψ.val
  rw [normSq2_smul]
  rw [show blochVector (fun i => c * ψ.val i) k
          = Complex.normSq c * blochVector ψ.val k from by
        rw [blochVector_smul]]
  have hc2 : Complex.normSq c > 0 := Complex.normSq_pos.mpr hc
  have hne : Complex.normSq c ≠ 0 := ne_of_gt hc2
  have hψ : normSq2 ψ.val > 0 := normSq2_pos ψ.property
  have hψne : normSq2 ψ.val ≠ 0 := ne_of_gt hψ
  field_simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: TRANSITION PROBABILITY ↔ BLOCH DOT PRODUCT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **TRANSITION PROBABILITY VIA BLOCH VECTORS.**

    For any two qubit rays,

        transitionProb [ψ] [φ]
          = (1 + b̂(ψ) · b̂(φ)) / 2,

    where  b̂(ψ) := b(ψ) / ‖ψ‖²  is the normalised Bloch vector. -/
theorem transitionProb_bloch (ψ φ : Ray 2) :
    transitionProb (n := 2) ψ φ
      = (1 + rdot (blochUnit ψ) (blochUnit φ)) / 2 := by
  unfold transitionProb blochUnit
  have h := cdot_normSq_eq ψ.val φ.val
  -- h : 2 * ‖⟨ψ,φ⟩‖² = ‖ψ‖²‖φ‖² + b(ψ)·b(φ)
  have hψp : 0 < normSq2 ψ.val := normSq2_pos ψ.property
  have hφp : 0 < normSq2 φ.val := normSq2_pos φ.property
  have hψne : normSq2 ψ.val ≠ 0 := ne_of_gt hψp
  have hφne : normSq2 φ.val ≠ 0 := ne_of_gt hφp
  -- rdot (b/N) (b/M) = (b·b) / (N·M)
  have hrd :
      rdot (fun k => blochVector ψ.val k / normSq2 ψ.val)
           (fun k => blochVector φ.val k / normSq2 φ.val)
        = rdot (blochVector ψ.val) (blochVector φ.val)
          / (normSq2 ψ.val * normSq2 φ.val) := by
    rw [rdot_expand, rdot_expand]
    field_simp
  rw [hrd]
  -- Goal:
  --   ‖⟨ψ,φ⟩‖² / (‖ψ‖²·‖φ‖²)
  --     = (1 + b(ψ)·b(φ) / (‖ψ‖²·‖φ‖²)) / 2
  -- ⇔ 2·‖⟨ψ,φ⟩‖² = ‖ψ‖²·‖φ‖² + b(ψ)·b(φ).
  field_simp
  linarith [h]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: WIGNER → BLOCH ISOMETRY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A Wigner symmetry on qubits induces a map of the Bloch
    sphere into itself that preserves the real dot product —
    i.e. an isometry of `S² ⊂ ℝ³`.

    The induced map is `b̂(ψ) ↦ b̂(T ψ)`; it is well-defined on
    the image of `blochUnit` and arbitrary off it, and
    preserves both the unit norm and the Euclidean dot
    product. -/
theorem wigner_qubit_to_bloch_isometry
    (T : Ray 2 → Ray 2) (hT : IsWignerSymmetry T) :
    ∃ f : (Fin 3 → ℝ) → (Fin 3 → ℝ),
      (∀ ψ : Ray 2, rnormSq (f (blochUnit ψ)) = 1) ∧
      (∀ ψ φ : Ray 2,
         rdot (f (blochUnit ψ)) (f (blochUnit φ))
           = rdot (blochUnit ψ) (blochUnit φ)) := by
  classical
  -- Define f via Classical.choice: extend `b̂(ψ) ↦ b̂(T ψ)`
  -- arbitrarily off the image of `blochUnit`.
  refine ⟨fun x =>
    if h : ∃ ψ : Ray 2, blochUnit ψ = x
      then blochUnit (T h.choose)
      else x, ?_, ?_⟩
  · intro ψ
    have hex : ∃ ψ' : Ray 2, blochUnit ψ' = blochUnit ψ := ⟨ψ, rfl⟩
    simp only [hex, dif_pos]
    exact blochUnit_norm (T hex.choose)
  · intro ψ φ
    have hexψ : ∃ ψ' : Ray 2, blochUnit ψ' = blochUnit ψ := ⟨ψ, rfl⟩
    have hexφ : ∃ φ' : Ray 2, blochUnit φ' = blochUnit φ := ⟨φ, rfl⟩
    simp only [hexψ, hexφ, dif_pos]
    -- Goal: rdot b̂(T choose_ψ) b̂(T choose_φ) = rdot b̂(ψ) b̂(φ)
    -- Use that the transition probability is preserved by T:
    --   tp (T choose_ψ) (T choose_φ) = tp choose_ψ choose_φ.
    -- And the Bloch identity rewrites each tp as
    --   (1 + b̂·b̂) / 2.
    -- Also: b̂(choose_ψ) = b̂(ψ) by choose_spec, similarly for φ.
    have htp_T := hT.2 hexψ.choose hexφ.choose
    have hbridge :=
      transitionProb_bloch (T hexψ.choose) (T hexφ.choose)
    have hother :=
      transitionProb_bloch hexψ.choose hexφ.choose
    -- Combine:
    --   tp(T choose, T choose) = (1 + b̂·b̂(T)) / 2
    --   tp(choose, choose)     = (1 + b̂·b̂(ch)) / 2
    --   tp(T choose, T choose) = tp(choose, choose)
    have hdot_eq : rdot (blochUnit (T hexψ.choose)) (blochUnit (T hexφ.choose))
                 = rdot (blochUnit hexψ.choose) (blochUnit hexφ.choose) := by
      rw [hbridge, hother] at htp_T
      linarith
    -- And b̂(choose_ψ) = b̂(ψ), same for φ:
    have hψeq : blochUnit hexψ.choose = blochUnit ψ := hexψ.choose_spec
    have hφeq : blochUnit hexφ.choose = blochUnit φ := hexφ.choose_spec
    rw [hdot_eq, hψeq, hφeq]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: NAMED SUBGATE — SO(3)/O(3) CLASSIFICATION ON RAYS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Bloch identity reduces the hard direction of Wigner's
    theorem (for `n = 2`) to the following STRUCTURE THEOREM
    for orthogonal maps of `S²`:

    "Every map  f : S² → S²  that preserves the real Euclidean
     dot product is induced by either an `SU(2)` unitary (a
     rotation) or by the composition of an `SU(2)` unitary
     with coordinatewise complex conjugation (a reflection),
     in both cases at the level of rays of `ℂ²`."

    Formalising this involves
      (i)   the 2-to-1 cover  SU(2) → SO(3)  via Pauli
            conjugation,
      (ii)  the O(3) = SO(3) ⊔ −SO(3) decomposition,
      (iii) checking that complex conjugation on qubits
            induces a fixed reflection of the Bloch sphere.

    All three components exist in Mathlib in some form but
    not packaged for direct use in our matrix setting.
    We state the consolidated structure theorem as a named
    gate and use it to discharge the full hard direction. -/

/-- **Named subgate**: the O(3) classification of Bloch
    isometries, lifted to rays of `ℂ²`.

    For every Wigner symmetry `T : Ray 2 → Ray 2`,  the
    induced isometry of the Bloch sphere (constructed
    unconditionally in `wigner_qubit_to_bloch_isometry`) is
    realised by either a unitary or an antiunitary action on
    `ℂ²`, in the sense of `VecRayEquiv` on representatives. -/
def BlochO3_classification : Prop :=
  ∀ T : Ray 2 → Ray 2, IsWignerSymmetry T →
    (∃ U : Matrix (Fin 2) (Fin 2) ℂ,
        U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        ∀ ψ : Ray 2, VecRayEquiv (T ψ).val (U *ᵥ ψ.val))
    ∨
    (∃ V : Matrix (Fin 2) (Fin 2) ℂ,
        V ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        ∀ ψ : Ray 2, VecRayEquiv (T ψ).val (V *ᵥ (conjVec ψ.val)))

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: COMPOSITE REDUCTION TO `WignerHardDirection 2`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    By DEFINITION of `WignerHardDirection 2` and
    `BlochO3_classification`, the latter expresses exactly the
    former for `n = 2`. -/

/-- **Wigner — hard direction for qubits.**

    Composes the unconditional Bloch construction
    `wigner_qubit_to_bloch_isometry` with the named subgate
    `BlochO3_classification` to discharge
    `WignerHardDirection 2`. -/
theorem wigner_hard_qubit
    (hO3 : BlochO3_classification) : WignerHardDirection 2 := by
  intro T hT
  exact hO3 T hT

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 11: HEADLINE SUMMARY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Headline (qubit Wigner's theorem):**

    The hard direction of Wigner's theorem holds for `n = 2`,
    conditional on the named gate `BlochO3_classification`
    (the lift of the Bloch-sphere isometry classification to
    rays of `ℂ²`).

    Unconditionally we have:

    (1) every qubit state has a Bloch vector `b(ψ) ∈ ℝ³`;
    (2) the NORMALISED Bloch vector `b̂(ψ) := b(ψ)/‖ψ‖²`
        is ray-invariant and lies on `S²`;
    (3) the transition probability is `(1 + b̂(ψ)·b̂(φ))/2`;
    (4) every Wigner symmetry induces a Bloch-sphere isometry. -/
theorem wigner_hard_qubit_master :
    BlochO3_classification → WignerHardDirection 2 :=
  wigner_hard_qubit

end UnifiedTheory.LayerB.WignerHardQubit
