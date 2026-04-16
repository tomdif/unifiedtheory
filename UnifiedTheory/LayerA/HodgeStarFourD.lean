/-
  LayerA/HodgeStarFourD.lean — Hodge star on 2-forms in 4D: involutivity and
  self-dual / anti-self-dual decomposition.

  THE MATHEMATICS:

  In d = 4 (Euclidean signature), the Hodge star on 2-forms satisfies
  star^2 = id. This is the p = 2, n = 4 case of the general formula
  star^2 = (-1)^{p(n-p)} on p-forms in n dimensions.

  Since star^2 = id, the space of 2-forms decomposes into eigenspaces:
    Lambda^2_+ = { w | star w = +w }  (self-dual 2-forms),     dim = 3
    Lambda^2_- = { w | star w = -w }  (anti-self-dual 2-forms), dim = 3

  Every 2-form decomposes as w = w+ + w- where w± = (w ± star w)/2.

  REPRESENTATION:

  We represent 2-forms concretely as elements of Fin 6 -> R, where the
  six basis 2-forms are indexed as:
    0 <-> e01,  1 <-> e02,  2 <-> e03,  3 <-> e12,  4 <-> e13,  5 <-> e23

  The Hodge star in Euclidean 4D signature acts as:
    e01 -> e23,   e23 -> e01    (indices 0 <-> 5)
    e02 -> -e13,  e13 -> -e02   (indices 1 <-> 4, with sign flip)
    e03 -> e12,   e12 -> e03    (indices 2 <-> 3)

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.LayerA.KPDecomposition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Fin.VecNotation

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.HodgeStarFourD

/-! ### Section 1: The space of 2-forms -/

/-- The space of 2-forms in 4D, represented as Fin 6 -> R.
    The six components correspond to the basis 2-forms:
      0 <-> e01, 1 <-> e02, 2 <-> e03, 3 <-> e12, 4 <-> e13, 5 <-> e23 -/
abbrev TwoForm := Fin 6 → ℝ

/-! ### Section 2: The Hodge star operator -/

/-- The Hodge star operator on 2-forms in Euclidean 4D, defined
    component-wise on the standard basis:
      star(e01) = e23,   star(e23) = e01
      star(e02) = -e13,  star(e13) = -e02
      star(e03) = e12,   star(e12) = e03
    Extended linearly to all 2-forms. -/
noncomputable def hodgeStar : TwoForm →ₗ[ℝ] TwoForm where
  toFun ω i :=
    match i with
    | 0 => ω 5       -- star(e01) component comes from e23
    | 1 => -(ω 4)    -- star(e02) component comes from -e13
    | 2 => ω 3       -- star(e03) component comes from e12
    | 3 => ω 2       -- star(e12) component comes from e03
    | 4 => -(ω 1)    -- star(e13) component comes from -e02
    | 5 => ω 0       -- star(e23) component comes from e01
  map_add' x y := by
    ext i; fin_cases i <;> simp [Pi.add_apply] <;> ring
  map_smul' r x := by
    ext i; fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, mul_neg]

/-! ### Section 3: star squared = id (the key theorem) -/

/-- **The Hodge star is an involution on 2-forms in 4D.**
    star . star = id, i.e., applying the Hodge star twice gives back the
    original 2-form. This is the p = 2, n = 4 case of the general
    formula star^2 = (-1)^{p(n-p)} = (-1)^4 = +1 on p-forms. -/
theorem hodge_star_sq_eq_id :
    hodgeStar.comp hodgeStar = LinearMap.id := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hodgeStar, LinearMap.comp_apply]

/-- Point-wise version: star(star w) = w for every 2-form w. -/
theorem hodge_star_sq (ω : TwoForm) : hodgeStar (hodgeStar ω) = ω := by
  have h := hodge_star_sq_eq_id
  exact LinearMap.ext_iff.mp h ω

/-! ### Section 4: Self-dual and anti-self-dual 2-forms -/

/-- A 2-form is **self-dual** if star w = +w. -/
def IsSelfDual (ω : TwoForm) : Prop := hodgeStar ω = ω

/-- A 2-form is **anti-self-dual** if star w = -w. -/
def IsAntiSelfDual (ω : TwoForm) : Prop := hodgeStar ω = -ω

/-- The self-dual subspace as a submodule (kernel of star - id). -/
noncomputable def selfDual : Submodule ℝ TwoForm :=
  LinearMap.ker (hodgeStar - LinearMap.id)

/-- The anti-self-dual subspace as a submodule (kernel of star + id). -/
noncomputable def antiSelfDual : Submodule ℝ TwoForm :=
  LinearMap.ker (hodgeStar + LinearMap.id)

/-- Membership in the self-dual subspace is equivalent to star w = w. -/
theorem mem_selfDual_iff (ω : TwoForm) :
    ω ∈ selfDual ↔ hodgeStar ω = ω := by
  constructor
  · intro h
    rw [selfDual, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    exact h
  · intro h
    rw [selfDual, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact h

/-- Membership in the anti-self-dual subspace is equivalent to star w = -w. -/
theorem mem_antiSelfDual_iff (ω : TwoForm) :
    ω ∈ antiSelfDual ↔ hodgeStar ω = -ω := by
  constructor
  · intro h
    rw [antiSelfDual, LinearMap.mem_ker, LinearMap.add_apply, add_eq_zero_iff_eq_neg] at h
    exact h
  · intro h
    rw [antiSelfDual, LinearMap.mem_ker, LinearMap.add_apply, add_eq_zero_iff_eq_neg]
    exact h

/-! ### Section 5: Decomposition w = w_plus + w_minus -/

/-- The self-dual projection: w_plus = (w + star w) / 2. -/
noncomputable def sdProj (ω : TwoForm) : TwoForm :=
  (1/2 : ℝ) • (ω + hodgeStar ω)

/-- The anti-self-dual projection: w_minus = (w - star w) / 2. -/
noncomputable def asdProj (ω : TwoForm) : TwoForm :=
  (1/2 : ℝ) • (ω - hodgeStar ω)

/-- The self-dual projection is self-dual: star(w_plus) = w_plus. -/
theorem sdProj_is_selfDual (ω : TwoForm) : hodgeStar (sdProj ω) = sdProj ω := by
  simp only [sdProj]
  ext i
  fin_cases i <;> simp [hodgeStar, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The anti-self-dual projection is anti-self-dual: star(w_minus) = -w_minus. -/
theorem asdProj_is_antiSelfDual (ω : TwoForm) :
    hodgeStar (asdProj ω) = -asdProj ω := by
  simp only [asdProj]
  ext i
  fin_cases i <;>
    simp [hodgeStar, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> ring

/-- **Every 2-form decomposes as w = w_plus + w_minus.**
    This is the eigenspace decomposition for the involution star. -/
theorem two_forms_eq_sd_plus_asd (ω : TwoForm) :
    ω = sdProj ω + asdProj ω := by
  ext i
  simp [sdProj, asdProj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The self-dual projection lands in the self-dual subspace. -/
theorem sdProj_mem_selfDual (ω : TwoForm) : sdProj ω ∈ selfDual := by
  rw [mem_selfDual_iff]
  exact sdProj_is_selfDual ω

/-- The anti-self-dual projection lands in the anti-self-dual subspace. -/
theorem asdProj_mem_antiSelfDual (ω : TwoForm) : asdProj ω ∈ antiSelfDual := by
  rw [mem_antiSelfDual_iff]
  exact asdProj_is_antiSelfDual ω

/-! ### Section 6: The projections are idempotent -/

/-- The self-dual projection is idempotent. -/
theorem sdProj_idempotent (ω : TwoForm) : sdProj (sdProj ω) = sdProj ω := by
  ext i
  simp only [sdProj, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hodgeStar]
  fin_cases i <;> simp <;> ring

/-- The anti-self-dual projection is idempotent. -/
theorem asdProj_idempotent (ω : TwoForm) : asdProj (asdProj ω) = asdProj ω := by
  ext i
  simp only [asdProj, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hodgeStar]
  fin_cases i <;> simp <;> ring

/-! ### Section 7: Dimensions of the eigenspaces -/

/-- For any 2-form w in the self-dual subspace, its 6 components satisfy
    w(0) = w(5), w(1) = -w(4), w(2) = w(3). So it is determined by
    3 free parameters: w(0), w(1), w(2). -/
theorem selfDual_determined_by_three (ω : TwoForm) (hω : ω ∈ selfDual) :
    ω 0 = ω 5 ∧ ω 1 = -(ω 4) ∧ ω 2 = ω 3 := by
  rw [mem_selfDual_iff] at hω
  constructor
  · have h := congr_fun hω 5
    simp [hodgeStar] at h
    linarith
  constructor
  · have h := congr_fun hω 4
    simp [hodgeStar] at h
    linarith
  · have h := congr_fun hω 3
    simp [hodgeStar] at h
    linarith

/-- For any 2-form w in the anti-self-dual subspace, its 6 components satisfy
    w(0) = -w(5), w(1) = w(4), w(2) = -w(3). So it is determined by
    3 free parameters: w(0), w(1), w(2). -/
theorem antiSelfDual_determined_by_three (ω : TwoForm) (hω : ω ∈ antiSelfDual) :
    ω 0 = -(ω 5) ∧ ω 1 = ω 4 ∧ ω 2 = -(ω 3) := by
  rw [mem_antiSelfDual_iff] at hω
  constructor
  · have h := congr_fun hω 5
    simp [hodgeStar, Pi.neg_apply] at h
    linarith
  constructor
  · have h := congr_fun hω 4
    simp [hodgeStar, Pi.neg_apply] at h
    linarith
  · have h := congr_fun hω 3
    simp [hodgeStar, Pi.neg_apply] at h
    linarith

/-- Construct a self-dual 2-form from 3 parameters. -/
noncomputable def mkSelfDual (a b c : ℝ) : TwoForm :=
  fun i => match i with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => c
  | 4 => -b
  | 5 => a

/-- The constructed self-dual form is indeed self-dual. -/
theorem mkSelfDual_mem (a b c : ℝ) : mkSelfDual a b c ∈ selfDual := by
  rw [mem_selfDual_iff]
  ext i; fin_cases i <;> simp [hodgeStar, mkSelfDual]

/-- Every self-dual form equals mkSelfDual applied to its first 3 components. -/
theorem selfDual_eq_mk (ω : TwoForm) (hω : ω ∈ selfDual) :
    ω = mkSelfDual (ω 0) (ω 1) (ω 2) := by
  obtain ⟨h05, h14, h23⟩ := selfDual_determined_by_three ω hω
  ext i; fin_cases i <;> simp [mkSelfDual, h05, h14, h23]

/-- Construct an anti-self-dual 2-form from 3 parameters. -/
noncomputable def mkAntiSelfDual (a b c : ℝ) : TwoForm :=
  fun i => match i with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => -c
  | 4 => b
  | 5 => -a

/-- The constructed anti-self-dual form is indeed anti-self-dual. -/
theorem mkAntiSelfDual_mem (a b c : ℝ) : mkAntiSelfDual a b c ∈ antiSelfDual := by
  rw [mem_antiSelfDual_iff]
  ext i; fin_cases i <;> simp [hodgeStar, mkAntiSelfDual]

/-- Every anti-self-dual form equals mkAntiSelfDual applied to its first 3 components. -/
theorem antiSelfDual_eq_mk (ω : TwoForm) (hω : ω ∈ antiSelfDual) :
    ω = mkAntiSelfDual (ω 0) (ω 1) (ω 2) := by
  obtain ⟨h05, h14, h23⟩ := antiSelfDual_determined_by_three ω hω
  ext i; fin_cases i <;> simp [mkAntiSelfDual, h05, h14, h23]

/-- **The self-dual subspace has dimension 3.**

    Proof: We exhibit a linear equivalence between R^3 and the self-dual
    subspace via mkSelfDual (which is a bijection by selfDual_eq_mk). -/
theorem dim_self_dual_eq_three :
    Module.finrank ℝ selfDual = 3 := by
  -- Build a linear map from R^3 to selfDual
  let toSD : (Fin 3 → ℝ) →ₗ[ℝ] selfDual := {
    toFun := fun v => ⟨mkSelfDual (v 0) (v 1) (v 2), mkSelfDual_mem _ _ _⟩
    map_add' := by
      intro x y
      ext i; fin_cases i <;> simp [mkSelfDual, Pi.add_apply] <;> ring
    map_smul' := by
      intro r x
      ext i; fin_cases i <;> simp [mkSelfDual, Pi.smul_apply, smul_eq_mul, mul_neg]
  }
  -- Show it's injective
  have hinj : Function.Injective toSD := by
    intro x y hxy
    have hxy' := congr_arg Subtype.val hxy
    ext i; fin_cases i
    · exact congr_fun hxy' 0
    · exact congr_fun hxy' 1
    · exact congr_fun hxy' 2
  -- Show it's surjective
  have hsurj : Function.Surjective toSD := by
    intro ⟨w, hw⟩
    have heq := selfDual_eq_mk w hw
    refine ⟨fun i => match i with | 0 => w 0 | 1 => w 1 | 2 => w 2, ?_⟩
    apply Subtype.ext
    show mkSelfDual (w 0) (w 1) (w 2) = w
    exact heq.symm
  -- A linear bijection preserves dimension
  have hbij : Function.Bijective toSD := ⟨hinj, hsurj⟩
  have equiv := LinearEquiv.ofBijective toSD hbij
  rw [← LinearEquiv.finrank_eq equiv]
  simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]

/-- **The anti-self-dual subspace has dimension 3.** -/
theorem dim_anti_self_dual_eq_three :
    Module.finrank ℝ antiSelfDual = 3 := by
  let toASD : (Fin 3 → ℝ) →ₗ[ℝ] antiSelfDual := {
    toFun := fun v =>
      ⟨mkAntiSelfDual (v 0) (v 1) (v 2), mkAntiSelfDual_mem _ _ _⟩
    map_add' := by
      intro x y
      ext i; fin_cases i <;> simp [mkAntiSelfDual, Pi.add_apply] <;> ring
    map_smul' := by
      intro r x
      ext i; fin_cases i <;> simp [mkAntiSelfDual, Pi.smul_apply, smul_eq_mul, mul_neg]
  }
  have hinj : Function.Injective toASD := by
    intro x y hxy
    have hxy' := congr_arg Subtype.val hxy
    ext i; fin_cases i
    · exact congr_fun hxy' 0
    · exact congr_fun hxy' 1
    · exact congr_fun hxy' 2
  have hsurj : Function.Surjective toASD := by
    intro ⟨w, hw⟩
    have heq := antiSelfDual_eq_mk w hw
    refine ⟨fun i => match i with | 0 => w 0 | 1 => w 1 | 2 => w 2, ?_⟩
    apply Subtype.ext
    show mkAntiSelfDual (w 0) (w 1) (w 2) = w
    exact heq.symm
  have hbij : Function.Bijective toASD := ⟨hinj, hsurj⟩
  have equiv := LinearEquiv.ofBijective toASD hbij
  rw [← LinearEquiv.finrank_eq equiv]
  simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]

/-! ### Section 8: The general involutivity formula -/

/-- **The general formula: (-1)^{p(n-p)} for p=2, n=4 gives +1.**
    This is a simple arithmetic verification that grounds the algebraic
    computation above in the general theory. -/
theorem hodge_sq_sign_formula : (-1 : ℤ) ^ (2 * (4 - 2)) = 1 := by norm_num

/-! ### Section 9: Summary

  The complete Hodge star story in 4D:

  1. star^2 = id on 2-forms (hodge_star_sq_eq_id)
  2. Every w = w+ + w- where w± = (w ± star w)/2 (two_forms_eq_sd_plus_asd)
  3. w+ is self-dual, w- is anti-self-dual (sdProj_is_selfDual, asdProj_is_antiSelfDual)
  4. dim(Lambda^2_+) = dim(Lambda^2_-) = 3 (dim_self_dual_eq_three, dim_anti_self_dual_eq_three)

  The self-dual / anti-self-dual decomposition is fundamental to:
  - Instantons (self-dual Yang-Mills connections, F = star F)
  - The chirality of the gravitational field in 4D
  - The topological classification of 4-manifolds (b2+, b2-)
  - The structure of the Weyl curvature tensor (W+, W-) -/

end UnifiedTheory.LayerA.HodgeStarFourD
