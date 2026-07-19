/-
  LayerB/WignerTheorem.lean — Wigner's theorem on quantum symmetries

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  In quantum mechanics, pure states are RAYS in a Hilbert space:
  a nonzero vector  ψ ∈ ℂⁿ  modulo the equivalence  ψ ∼ c·ψ  for any
  nonzero scalar  c.  The physical observable attached to a pair of
  rays is the TRANSITION PROBABILITY

      P([ψ], [φ]) = |⟨ψ, φ⟩|² / (‖ψ‖² · ‖φ‖²),

  invariant under rescaling of either argument (numerator and
  denominator both pick up the same `|c|²`).

  A WIGNER SYMMETRY is a bijection of the ray space that preserves
  all transition probabilities.  Wigner's 1931 theorem asserts that
  every such symmetry is induced by either a UNITARY or an ANTIUNITARY
  operator on  ℂⁿ.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED (this file)

  – `Ray n`                  : the type of nonzero vectors of  ℂⁿ
                              (we work with representatives; ray
                              equality enters only via the
                              probability formula, which is
                              rescaling-invariant).
  – `transitionProb ψ φ`     : the probability defined above.
  – `transitionProb_smul_left` : invariance under rescaling, witnessing
                              the well-definedness on rays.
  – `IsWignerSymmetry T`     : bijectivity + preservation of every
                              transition probability.
  – `unitary_induces_wigner` : EVERY unitary  U : Matrix (Fin n)
                              (Fin n) ℂ  induces a Wigner symmetry
                              (constructively built, bijection +
                              preservation).  This is the EASY
                              DIRECTION of Wigner's theorem.
  – `antiunitary_induces_wigner` : Same for an "antiunitary"
                              operator (unitary composed with complex
                              conjugation).
  – `WignerHardDirection n`  : the converse, stated as a named Prop
                              (out of present scope; multi-week
                              formalization).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – The unitary direction (`unitary_induces_wigner`) is proved
    UNCONDITIONALLY, including bijectivity of the induced ray map.
  – The antiunitary direction (`antiunitary_induces_wigner`) is
    likewise unconditional.
  – The HARD direction — that every Wigner symmetry comes from a
    unitary or antiunitary — is the deep content of Wigner's 1931
    theorem (Bargmann 1964 gave a modern proof).  It is OUT OF
    SCOPE for this file and stated as a named hypothesis
    `WignerHardDirection`.

  Zero `sorry`. Zero custom axioms.
-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Matrix.Mul

set_option relaxedAutoImplicit false
set_option linter.style.show false

namespace UnifiedTheory.LayerB.WignerTheorem

open Matrix Complex
open scoped ComplexConjugate

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: RAYS AND TRANSITION PROBABILITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A **ray** is a nonzero vector in ℂⁿ; we work with representatives
    and observe rescaling-invariance via `transitionProb_smul_left`. -/
def Ray (n : ℕ) := {ψ : Fin n → ℂ // ψ ≠ 0}

/-- Coerce a `Ray n` to its underlying vector. -/
instance {n : ℕ} : CoeFun (Ray n) (fun _ => Fin n → ℂ) where
  coe ψ := ψ.val

/-- Inner product of two complex vectors: ⟨ψ, φ⟩ = Σᵢ star(ψᵢ) · φᵢ. -/
def cdot {n : ℕ} (ψ φ : Fin n → ℂ) : ℂ :=
  ∑ i, star (ψ i) * φ i

/-- Squared norm of a complex vector: ‖ψ‖² = Σᵢ |ψᵢ|². -/
def normSq2 {n : ℕ} (ψ : Fin n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (ψ i)

lemma normSq2_nonneg {n : ℕ} (ψ : Fin n → ℂ) : 0 ≤ normSq2 ψ := by
  unfold normSq2
  exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (ψ i))

lemma normSq2_eq_zero {n : ℕ} {ψ : Fin n → ℂ} :
    normSq2 ψ = 0 ↔ ψ = 0 := by
  classical
  unfold normSq2
  constructor
  · intro h
    funext i
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ Complex.normSq (ψ j) :=
      fun j _ => Complex.normSq_nonneg _
    have hi : Complex.normSq (ψ i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.mp hi
  · intro h
    subst h
    simp

lemma normSq2_pos {n : ℕ} {ψ : Fin n → ℂ} (hψ : ψ ≠ 0) :
    0 < normSq2 ψ :=
  lt_of_le_of_ne (normSq2_nonneg ψ) (fun h => hψ (normSq2_eq_zero.mp h.symm))

/-- **Transition probability** between two rays. -/
noncomputable def transitionProb {n : ℕ} (ψ φ : Ray n) : ℝ :=
  Complex.normSq (cdot ψ.val φ.val) / (normSq2 ψ.val * normSq2 φ.val)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: BASIC INNER-PRODUCT IDENTITIES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `cdot` equals the dotProduct of `star ψ` and `φ`. -/
lemma cdot_eq_dotProduct {n : ℕ} (ψ φ : Fin n → ℂ) :
    cdot ψ φ = (star ψ : Fin n → ℂ) ⬝ᵥ φ := by
  unfold cdot
  rfl

/-- `normSq2 ψ` equals the complex inner product of `ψ` with itself. -/
lemma normSq2_eq_dotProduct {n : ℕ} (ψ : Fin n → ℂ) :
    (normSq2 ψ : ℂ) = (star ψ : Fin n → ℂ) ⬝ᵥ ψ := by
  show ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ) = ∑ i, star (ψ i) * ψ i
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  show (Complex.normSq (ψ i) : ℂ) = star (ψ i) * ψ i
  have hstar : star (ψ i) = conj (ψ i) := rfl
  rw [hstar, Complex.normSq_eq_conj_mul_self]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: RESCALING INVARIANCE — RAYS ARE WELL DEFINED
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

lemma cdot_smul_left {n : ℕ} (c : ℂ) (ψ φ : Fin n → ℂ) :
    cdot (fun i => c * ψ i) φ = star c * cdot ψ φ := by
  unfold cdot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  show star (c * ψ i) * φ i = star c * (star (ψ i) * φ i)
  rw [StarMul.star_mul]
  ring

lemma cdot_smul_right {n : ℕ} (c : ℂ) (ψ φ : Fin n → ℂ) :
    cdot ψ (fun i => c * φ i) = c * cdot ψ φ := by
  unfold cdot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma normSq2_smul {n : ℕ} (c : ℂ) (ψ : Fin n → ℂ) :
    normSq2 (fun i => c * ψ i) = Complex.normSq c * normSq2 ψ := by
  unfold normSq2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.normSq_mul]

/-- **Rescaling invariance of the transition probability** (left argument).
    This is the well-definedness check for the ray formulation. -/
lemma transitionProb_smul_left {n : ℕ} (c : ℂ) (hc : c ≠ 0)
    (ψ φ : Ray n) (hcψ : (fun i => c * ψ.val i) ≠ 0) :
    transitionProb ⟨fun i => c * ψ.val i, hcψ⟩ φ = transitionProb ψ φ := by
  unfold transitionProb
  show Complex.normSq (cdot (fun i => c * ψ.val i) φ.val) /
        (normSq2 (fun i => c * ψ.val i) * normSq2 φ.val)
       = Complex.normSq (cdot ψ.val φ.val) / (normSq2 ψ.val * normSq2 φ.val)
  rw [cdot_smul_left, Complex.normSq_mul, normSq2_smul]
  have hstar_eq : (star c : ℂ) = conj c := rfl
  rw [hstar_eq, Complex.normSq_conj]
  have hψ : normSq2 ψ.val > 0 := normSq2_pos ψ.property
  have hφ : normSq2 φ.val > 0 := normSq2_pos φ.property
  have hc2 : Complex.normSq c > 0 := Complex.normSq_pos.mpr hc
  field_simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: WIGNER SYMMETRY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `T : Ray n → Ray n` is a **Wigner symmetry** if it is a bijection
    that preserves the transition probability between every pair of
    rays. -/
def IsWignerSymmetry {n : ℕ} (T : Ray n → Ray n) : Prop :=
  Function.Bijective T ∧
    ∀ ψ φ : Ray n, transitionProb (T ψ) (T φ) = transitionProb ψ φ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: UNITARY ACTION ON RAYS

    Throughout, given  U ∈ unitaryGroup (Fin n) ℂ,  i.e. star U * U = 1,
    we obtain
      (i)   U *ᵥ ψ ≠ 0   whenever  ψ ≠ 0   (because Uᴴ is a left inverse),
      (ii)  ⟨Uψ, Uφ⟩ = ⟨ψ, φ⟩,
      (iii) ‖Uψ‖² = ‖ψ‖².
    From these the transition probability is preserved.

    The induced map on rays is therefore a well-defined function;
    bijectivity follows from the unitary group structure (the map
    induced by  star U  is the two-sided inverse).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

variable {n : ℕ}

/-- A unitary matrix sends nonzero vectors to nonzero vectors. -/
lemma unitary_mulVec_ne_zero
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    {ψ : Fin n → ℂ} (hψ : ψ ≠ 0) :
    U *ᵥ ψ ≠ 0 := by
  intro h
  apply hψ
  have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hcalc : (star U) *ᵥ (U *ᵥ ψ) = ψ := by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [h, Matrix.mulVec_zero] at hcalc
  exact hcalc.symm

/-- Inner product is preserved by a unitary action:
        ⟨Uψ, Uφ⟩ = ⟨ψ, φ⟩. -/
lemma cdot_unitary_invariant
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ψ φ : Fin n → ℂ) :
    cdot (U *ᵥ ψ) (U *ᵥ φ) = cdot ψ φ := by
  have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [cdot_eq_dotProduct, cdot_eq_dotProduct]
  rw [Matrix.star_mulVec]
  -- ((star ψ) ᵥ* Uᴴ) ⬝ᵥ (U *ᵥ φ)
  rw [← Matrix.dotProduct_mulVec]
  -- star ψ ⬝ᵥ (Uᴴ *ᵥ (U *ᵥ φ))
  have hstar : (star U : Matrix (Fin n) (Fin n) ℂ) = Uᴴ :=
    Matrix.star_eq_conjTranspose U
  rw [Matrix.mulVec_mulVec, ← hstar, h1, Matrix.one_mulVec]

/-- Squared norm is preserved by a unitary action. -/
lemma normSq2_unitary_invariant
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : Fin n → ℂ) :
    normSq2 (U *ᵥ ψ) = normSq2 ψ := by
  have h := cdot_unitary_invariant hU ψ ψ
  have hL : cdot (U *ᵥ ψ) (U *ᵥ ψ) = (normSq2 (U *ᵥ ψ) : ℂ) := by
    rw [cdot_eq_dotProduct]
    exact (normSq2_eq_dotProduct (U *ᵥ ψ)).symm
  have hR : cdot ψ ψ = (normSq2 ψ : ℂ) := by
    rw [cdot_eq_dotProduct]
    exact (normSq2_eq_dotProduct ψ).symm
  rw [hL, hR] at h
  exact_mod_cast h

/-- Action of a unitary on a ray (well-defined: produces a nonzero vector). -/
noncomputable def unitaryActionRay
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : Ray n) : Ray n :=
  ⟨U *ᵥ ψ.val, unitary_mulVec_ne_zero hU ψ.property⟩

/-- The unitary ray action preserves transition probability. -/
lemma unitaryActionRay_preserves_transitionProb
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ψ φ : Ray n) :
    transitionProb (unitaryActionRay hU ψ) (unitaryActionRay hU φ)
      = transitionProb ψ φ := by
  unfold transitionProb unitaryActionRay
  show Complex.normSq (cdot (U *ᵥ ψ.val) (U *ᵥ φ.val)) /
        (normSq2 (U *ᵥ ψ.val) * normSq2 (U *ᵥ φ.val))
       = Complex.normSq (cdot ψ.val φ.val) / (normSq2 ψ.val * normSq2 φ.val)
  rw [cdot_unitary_invariant hU, normSq2_unitary_invariant hU,
      normSq2_unitary_invariant hU]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: BIJECTIVITY OF THE UNITARY RAY MAP
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The conjugate transpose of a unitary is also unitary. -/
lemma star_mem_unitaryGroup
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    star U ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_star]
  exact Matrix.mem_unitaryGroup_iff'.mp hU

/-- `unitaryActionRay` with `star U` is a left inverse of
    `unitaryActionRay` with `U`. -/
lemma unitaryActionRay_left_inverse
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : Ray n) :
    unitaryActionRay (star_mem_unitaryGroup hU) (unitaryActionRay hU ψ) = ψ := by
  apply Subtype.ext
  show (star U) *ᵥ (U *ᵥ ψ.val) = ψ.val
  rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.mp hU,
      Matrix.one_mulVec]

/-- And a right inverse. -/
lemma unitaryActionRay_right_inverse
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : Ray n) :
    unitaryActionRay hU (unitaryActionRay (star_mem_unitaryGroup hU) ψ) = ψ := by
  apply Subtype.ext
  show U *ᵥ ((star U) *ᵥ ψ.val) = ψ.val
  rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff.mp hU,
      Matrix.one_mulVec]

/-- The unitary ray map is a bijection of `Ray n`. -/
lemma unitaryActionRay_bijective
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Function.Bijective (unitaryActionRay hU) := by
  refine ⟨?_, ?_⟩
  · intro ψ φ h
    have := congrArg (unitaryActionRay (star_mem_unitaryGroup hU)) h
    rw [unitaryActionRay_left_inverse hU,
        unitaryActionRay_left_inverse hU] at this
    exact this
  · intro φ
    exact ⟨unitaryActionRay (star_mem_unitaryGroup hU) φ,
           unitaryActionRay_right_inverse hU φ⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: THE EASY DIRECTION — UNITARIES INDUCE WIGNER SYMMETRIES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Wigner — unitary direction (easy half).**

    Every unitary matrix  U ∈ unitaryGroup (Fin n) ℂ  induces a
    Wigner symmetry of the ray space, given on representatives by
    ψ ↦ U *ᵥ ψ. -/
theorem unitary_induces_wigner
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ T : Ray n → Ray n, IsWignerSymmetry T ∧
      ∀ ψ : Ray n, (T ψ).val = U *ᵥ ψ.val := by
  refine ⟨unitaryActionRay hU, ?_, ?_⟩
  · exact ⟨unitaryActionRay_bijective hU,
           unitaryActionRay_preserves_transitionProb hU⟩
  · intro _
    rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: COMPLEX CONJUGATION ON VECTORS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Coordinatewise complex conjugation of a vector. -/
def conjVec {n : ℕ} (ψ : Fin n → ℂ) : Fin n → ℂ := fun i => star (ψ i)

@[simp] lemma conjVec_zero : conjVec (0 : Fin n → ℂ) = 0 := by
  funext i; simp [conjVec]

@[simp] lemma conjVec_conjVec (ψ : Fin n → ℂ) : conjVec (conjVec ψ) = ψ := by
  funext i; show star (star (ψ i)) = ψ i; rw [star_star]

/-- Coordinatewise conjugation sends nonzero vectors to nonzero vectors. -/
lemma conjVec_ne_zero {ψ : Fin n → ℂ} (hψ : ψ ≠ 0) : conjVec ψ ≠ 0 := by
  intro h
  apply hψ
  have := congrArg conjVec h
  rw [conjVec_conjVec, conjVec_zero] at this
  exact this

/-- `cdot` after coordinate conjugation: ⟨ψ̄, φ̄⟩ = star ⟨ψ, φ⟩. -/
lemma cdot_conjVec (ψ φ : Fin n → ℂ) :
    cdot (conjVec ψ) (conjVec φ) = star (cdot ψ φ) := by
  unfold cdot conjVec
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  show star (star (ψ i)) * star (φ i) = star (star (ψ i) * φ i)
  rw [StarMul.star_mul, star_star]
  ring

/-- Squared norm after coordinate conjugation. -/
lemma normSq2_conjVec (ψ : Fin n → ℂ) :
    normSq2 (conjVec ψ) = normSq2 ψ := by
  unfold normSq2 conjVec
  refine Finset.sum_congr rfl ?_
  intro i _
  exact Complex.normSq_conj (ψ i)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: ANTIUNITARY ACTION ON RAYS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Antiunitary action on rays: ψ ↦ V *ᵥ (ψ̄). -/
noncomputable def antiunitaryActionRay
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : Ray n) : Ray n :=
  ⟨V *ᵥ conjVec ψ.val, unitary_mulVec_ne_zero hV (conjVec_ne_zero ψ.property)⟩

/-- The antiunitary ray action preserves transition probability:
    the inner product picks up a `star`, but `|·|²` is invariant under `star`. -/
lemma antiunitaryActionRay_preserves_transitionProb
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ψ φ : Ray n) :
    transitionProb (antiunitaryActionRay hV ψ) (antiunitaryActionRay hV φ)
      = transitionProb ψ φ := by
  unfold transitionProb antiunitaryActionRay
  show Complex.normSq (cdot (V *ᵥ conjVec ψ.val) (V *ᵥ conjVec φ.val)) /
        (normSq2 (V *ᵥ conjVec ψ.val) * normSq2 (V *ᵥ conjVec φ.val))
       = Complex.normSq (cdot ψ.val φ.val) / (normSq2 ψ.val * normSq2 φ.val)
  rw [cdot_unitary_invariant hV, normSq2_unitary_invariant hV,
      normSq2_unitary_invariant hV, cdot_conjVec,
      normSq2_conjVec, normSq2_conjVec]
  -- Remaining: |star z|² = |z|²
  have hstar_eq : ∀ z : ℂ, (star z : ℂ) = conj z := fun _ => rfl
  rw [hstar_eq, Complex.normSq_conj]

/-! Bijectivity of the antiunitary ray map.

    The map  ψ ↦ V *ᵥ ψ̄  has inverse  φ ↦ (star V) *ᵥ φ  conjugated.
    More precisely, the inverse is  φ ↦ conjVec ((star V) *ᵥ φ).

    We construct it via the antiunitary action of `star V` followed
    by the unitary action of `star V`-style argument. Concretely we
    just give the inverse function directly and check the two
    composition identities. -/

/-- The inverse map for the antiunitary action: ψ ↦ conjVec ((star V) *ᵥ ψ). -/
noncomputable def antiunitaryActionRayInv
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : Ray n) : Ray n :=
  ⟨conjVec ((star V) *ᵥ ψ.val),
    conjVec_ne_zero (unitary_mulVec_ne_zero (star_mem_unitaryGroup hV) ψ.property)⟩

/-- `antiunitaryActionRayInv hV` is a left inverse of `antiunitaryActionRay hV`. -/
lemma antiunitaryActionRay_left_inverse
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : Ray n) :
    antiunitaryActionRayInv hV (antiunitaryActionRay hV ψ) = ψ := by
  apply Subtype.ext
  show conjVec ((star V) *ᵥ (V *ᵥ conjVec ψ.val)) = ψ.val
  rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.mp hV,
      Matrix.one_mulVec]
  show conjVec (conjVec ψ.val) = ψ.val
  rw [conjVec_conjVec]

/-- `antiunitaryActionRayInv hV` is a right inverse of `antiunitaryActionRay hV`. -/
lemma antiunitaryActionRay_right_inverse
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : Ray n) :
    antiunitaryActionRay hV (antiunitaryActionRayInv hV ψ) = ψ := by
  apply Subtype.ext
  show V *ᵥ conjVec (conjVec ((star V) *ᵥ ψ.val)) = ψ.val
  rw [conjVec_conjVec, Matrix.mulVec_mulVec,
      Matrix.mem_unitaryGroup_iff.mp hV, Matrix.one_mulVec]

/-- The antiunitary ray action is a bijection of `Ray n`. -/
lemma antiunitaryActionRay_bijective
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Function.Bijective (antiunitaryActionRay hV) := by
  refine ⟨?_, ?_⟩
  · intro ψ φ h
    have := congrArg (antiunitaryActionRayInv hV) h
    rw [antiunitaryActionRay_left_inverse hV,
        antiunitaryActionRay_left_inverse hV] at this
    exact this
  · intro φ
    exact ⟨antiunitaryActionRayInv hV φ,
           antiunitaryActionRay_right_inverse hV φ⟩

/-- **Wigner — antiunitary direction (easy half).**

    Every "antiunitary" — a unitary `V` composed with coordinatewise
    complex conjugation — induces a Wigner symmetry of the ray space:
    ψ ↦ V *ᵥ (ψ̄). -/
theorem antiunitary_induces_wigner
    (V : Matrix (Fin n) (Fin n) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ T : Ray n → Ray n, IsWignerSymmetry T ∧
      ∀ ψ : Ray n, (T ψ).val = V *ᵥ (conjVec ψ.val) := by
  refine ⟨antiunitaryActionRay hV, ?_, ?_⟩
  · exact ⟨antiunitaryActionRay_bijective hV,
           antiunitaryActionRay_preserves_transitionProb hV⟩
  · intro _
    rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: THE HARD DIRECTION — STATEMENT ONLY (OUT OF SCOPE)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `WignerHardDirection n` is the deep content of Wigner's 1931
    theorem.  We state it here as a named Prop so it can be cited
    elsewhere without being proved.  A formal proof is a multi-week
    undertaking (Bargmann's modern argument requires complex
    projective geometry and a delicate phase analysis).

    Note: with our representative-level definitions, ray equality
    in the conclusion is encoded as "same vector up to nonzero scalar".
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Two vectors are PROJECTIVELY EQUAL if they differ by a nonzero
    complex scalar — i.e. they project to the same point of complex
    projective space. -/
def VecRayEquiv {n : ℕ} (ψ φ : Fin n → ℂ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ψ = fun i => c * φ i

/-- **The hard direction of Wigner's theorem**, stated as a named
    proposition. Out of scope for this file: a formal proof requires
    Bargmann-style complex projective geometry, several hundred
    additional lines of Lean. -/
def WignerHardDirection (n : ℕ) : Prop :=
  ∀ T : Ray n → Ray n, IsWignerSymmetry T →
    (∃ U : Matrix (Fin n) (Fin n) ℂ,
        U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
        ∀ ψ : Ray n, VecRayEquiv (T ψ).val (U *ᵥ ψ.val))
    ∨
    (∃ V : Matrix (Fin n) (Fin n) ℂ,
        V ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
        ∀ ψ : Ray n, VecRayEquiv (T ψ).val (V *ᵥ (conjVec ψ.val)))

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 11: MASTER SUMMARY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Wigner's theorem — easy direction, aggregated.**

    For every dimension `n`:

    (1) Every unitary  U  induces a Wigner symmetry of the ray space
        via  ψ ↦ U *ᵥ ψ.

    (2) Every antiunitary (= unitary composed with coordinatewise
        complex conjugation)  V  also induces one via
        ψ ↦ V *ᵥ ψ̄.

    The CONVERSE — that every Wigner symmetry is of this form — is
    `WignerHardDirection n`, out of scope here. -/
theorem wigner_easy_direction_master (n : ℕ) :
    (∀ (U : Matrix (Fin n) (Fin n) ℂ),
        U ∈ Matrix.unitaryGroup (Fin n) ℂ →
        ∃ T : Ray n → Ray n, IsWignerSymmetry T ∧
          ∀ ψ : Ray n, (T ψ).val = U *ᵥ ψ.val)
    ∧ (∀ (V : Matrix (Fin n) (Fin n) ℂ),
        V ∈ Matrix.unitaryGroup (Fin n) ℂ →
        ∃ T : Ray n → Ray n, IsWignerSymmetry T ∧
          ∀ ψ : Ray n, (T ψ).val = V *ᵥ (conjVec ψ.val)) :=
  ⟨unitary_induces_wigner, antiunitary_induces_wigner⟩

end UnifiedTheory.LayerB.WignerTheorem
