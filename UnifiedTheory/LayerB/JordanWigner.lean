import Mathlib

/-!
# The Jordan–Wigner transformation: core algebra

This module formalises, **unconditionally** (by explicit `2×2` and `4×4`
matrix computation), the algebraic heart of the Jordan–Wigner (JW)
transformation, which maps a spin-`1/2` chain to a chain of spinless
fermions.

## The single-site ladder operators

On a single site we use the `2×2` Pauli ladder operators
```
  σ⁺ = |0⟩⟨1| = !![0,1; 0,0],     σ⁻ = |1⟩⟨0| = !![0,0; 1,0],
```
which are `σ⁺ = (X + iY)/2`, `σ⁻ = (X − iY)/2`.  These satisfy the
**on-site fermionic relations**:

* `σ⁺ σ⁺ = 0`, `σ⁻ σ⁻ = 0`  (Pauli exclusion — you cannot create or
  destroy an excitation twice on the same site);
* `{σ⁺, σ⁻} = σ⁺σ⁻ + σ⁻σ⁺ = I`  (the anticommutator equals the
  identity);
* `σ⁺σ⁻ = |0⟩⟨0| = (I + Z)/2`  (the *hole* projector) and
  `σ⁻σ⁺ = |1⟩⟨1| = (I − Z)/2`  (the *number* operator `n`), with
  `σ⁺σ⁻ + σ⁻σ⁺ = I` and `σ⁺σ⁻ − σ⁻σ⁺ = Z`;
* the number operator `n = σ⁻σ⁺` is idempotent, `n² = n`, with
  eigenvalues `0, 1`.

## The Jordan–Wigner string

The on-site relations are *bosonic between different sites*: distinct
single-site ladder operators **commute**, whereas genuine fermions must
**anticommute**.  The JW transformation fixes this by attaching to each
site a *string* of `Z` operators on all sites to its left:
```
  cⱼ = (∏_{l < j} (−Zₗ)) · σ⁻ⱼ .
```
The mechanism rests on the elementary fact that on a single site `Z`
**anticommutes** with `σ±`:
```
  Z σ⁺ = −σ⁺ Z,     Z σ⁻ = −σ⁻ Z.
```
Threaded through the tensor product, this converts on-site
(anti)commutation into the full fermionic canonical anticommutation
relations (CAR).  We exhibit the simplest non-trivial instance
explicitly: on two sites the operators `Z ⊗ σ⁻` and `σ⁻ ⊗ I`
**anticommute** (a `4×4` computation),
```
  (Z ⊗ σ⁻)(σ⁻ ⊗ I) = −(σ⁻ ⊗ I)(Z ⊗ σ⁻),
```
which is precisely the JW string producing fermionic statistics between
different sites.

## What is proved here

Everything in this file is an *unconditional* explicit matrix identity
(no `sorry`, no custom `axiom`).  The full `n`-site CAR algebra is stated
as the named target `JordanWigner_CAR_Target`, and the master theorem
`jordan_wigner_master` collects the on-site relations, the `Z`-string
anticommutation, and the two-site fermionic anticommutation that drive
it.
-/

namespace UnifiedTheory.LayerB.JordanWigner

open Matrix

/-! ## Single-site operators -/

/-- The raising ladder operator `σ⁺ = |0⟩⟨1| = !![0,1; 0,0]`. -/
noncomputable def sigmaPlus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The lowering ladder operator `σ⁻ = |1⟩⟨0| = !![0,0; 1,0]`. -/
noncomputable def sigmaMinus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- The Pauli `Z` matrix `!![1,0; 0,-1]` (the JW-string building block).

Identical to `pauliZ` defined in `UniversalGates` / `GottesmanKnill`; we
re-state it locally so this module is self-contained. -/
noncomputable def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The single-site number operator `n = σ⁻σ⁺ = |1⟩⟨1| = (I − Z)/2`. -/
noncomputable def numberOp : Matrix (Fin 2) (Fin 2) ℂ := sigmaMinus * sigmaPlus

/-- A uniform tactic for proving `2×2` complex-matrix identities by
expanding the matrix product on each of the four entries. -/
macro "matrix2" : tactic =>
  `(tactic|
    (ext i j
     fin_cases i <;> fin_cases j <;>
       simp [sigmaPlus, sigmaMinus, pauliZ, numberOp, Matrix.mul_apply,
         Fin.sum_univ_two, Matrix.one_apply, Matrix.add_apply,
         Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply] <;>
       norm_num))

/-! ## On-site fermionic relations -/

/-- Pauli exclusion (raising): `σ⁺ σ⁺ = 0`. -/
theorem sigmaPlus_sq : sigmaPlus * sigmaPlus = 0 := by matrix2

/-- Pauli exclusion (lowering): `σ⁻ σ⁻ = 0`. -/
theorem sigmaMinus_sq : sigmaMinus * sigmaMinus = 0 := by matrix2

/-- The on-site canonical anticommutation relation
`{σ⁺, σ⁻} = σ⁺σ⁻ + σ⁻σ⁺ = I`. -/
theorem anticomm_plus_minus :
    sigmaPlus * sigmaMinus + sigmaMinus * sigmaPlus = 1 := by matrix2

/-- The hole projector `σ⁺σ⁻ = |0⟩⟨0| = !![1,0; 0,0]`. -/
theorem sigmaPlus_mul_sigmaMinus :
    sigmaPlus * sigmaMinus = !![1, 0; 0, 0] := by matrix2

/-- The number operator `σ⁻σ⁺ = |1⟩⟨1| = !![0,0; 0,1]`. -/
theorem sigmaMinus_mul_sigmaPlus :
    sigmaMinus * sigmaPlus = !![0, 0; 0, 1] := by matrix2

/-- The hole projector equals `(I + Z)/2`. -/
theorem sigmaPlus_mul_sigmaMinus_eq :
    sigmaPlus * sigmaMinus = (2 : ℂ)⁻¹ • (1 + pauliZ) := by matrix2

/-- The number operator equals `(I − Z)/2`. -/
theorem sigmaMinus_mul_sigmaPlus_eq :
    sigmaMinus * sigmaPlus = (2 : ℂ)⁻¹ • (1 - pauliZ) := by matrix2

/-- Sum of the two projectors is the identity: `σ⁺σ⁻ + σ⁻σ⁺ = I`.
(Equivalent to `anticomm_plus_minus`, recorded for symmetry with the
difference relation below.) -/
theorem projectors_sum :
    sigmaPlus * sigmaMinus + sigmaMinus * sigmaPlus = 1 := by matrix2

/-- Difference of the two projectors is `Z`: `σ⁺σ⁻ − σ⁻σ⁺ = Z`. -/
theorem projectors_diff :
    sigmaPlus * sigmaMinus - sigmaMinus * sigmaPlus = pauliZ := by matrix2

/-- The number operator is idempotent: `n² = n` (eigenvalues `0, 1`). -/
theorem numberOp_idempotent :
    (sigmaMinus * sigmaPlus) * (sigmaMinus * sigmaPlus)
      = sigmaMinus * sigmaPlus := by matrix2

/-! ## The `Z`-string mechanism: `Z` anticommutes with `σ±` -/

/-- The string building block anticommutes with the raising operator:
`Z σ⁺ = −σ⁺ Z`. -/
theorem Z_anticomm_sigmaPlus : pauliZ * sigmaPlus = -(sigmaPlus * pauliZ) := by
  matrix2

/-- The string building block anticommutes with the lowering operator:
`Z σ⁻ = −σ⁻ Z`. -/
theorem Z_anticomm_sigmaMinus :
    pauliZ * sigmaMinus = -(sigmaMinus * pauliZ) := by matrix2

/-! ## Two-site fermionic anticommutation (the JW string)

We give the two relevant `4×4` operators explicitly, with the
convention `Fin 4 ∋ 2·i + j` for the tensor factor `(i, j)`, i.e. the
block decomposition
```
  A ⊗ B = !![ A₀₀·B , A₀₁·B ; A₁₀·B , A₁₁·B ].
```
With `Z = diag(1, −1)`, `σ⁻ = !![0,0; 1,0]` and `I₂`, this gives the two
matrices below. -/

/-- `Z ⊗ σ⁻` as an explicit `4×4` matrix. -/
noncomputable def Z_tensor_sigmaMinus : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, -1, 0]

/-- `σ⁻ ⊗ I` as an explicit `4×4` matrix. -/
noncomputable def sigmaMinus_tensor_I : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- A uniform tactic for `4×4` complex-matrix identities. -/
macro "matrix4" : tactic =>
  `(tactic|
    (ext i j
     fin_cases i <;> fin_cases j <;>
       simp [Z_tensor_sigmaMinus, sigmaMinus_tensor_I, Matrix.mul_apply,
         Fin.sum_univ_four, Matrix.neg_apply] <;>
       norm_num))

/-- **Two-site Jordan–Wigner anticommutation.**  The `Z`-string makes
operators on different sites anticommute:
```
  (Z ⊗ σ⁻)(σ⁻ ⊗ I) = −(σ⁻ ⊗ I)(Z ⊗ σ⁻).
```
This is the elementary instance of fermionic statistics produced by the
JW transformation. -/
theorem twoSite_anticomm :
    Z_tensor_sigmaMinus * sigmaMinus_tensor_I
      = -(sigmaMinus_tensor_I * Z_tensor_sigmaMinus) := by matrix4

/-- Equivalent anticommutator form: `{Z ⊗ σ⁻, σ⁻ ⊗ I} = 0`. -/
theorem twoSite_anticomm' :
    Z_tensor_sigmaMinus * sigmaMinus_tensor_I
      + sigmaMinus_tensor_I * Z_tensor_sigmaMinus = 0 := by matrix4

/-! ## The named `n`-site CAR target

The two-site computation above is the seed of the full fermionic algebra
obtained by JW.  We state the `n`-site target abstractly.  Given local
ladder operators `σ⁻ⱼ` on a chain of `n` sites and the JW string, the
fermionic operators
```
  cⱼ := (∏_{l < j} (−Zₗ)) · σ⁻ⱼ
```
satisfy the canonical anticommutation relations (CAR):
```
  {cᵢ, cⱼ}   = 0,        {cᵢ, cⱼ†}  = δᵢⱼ · I.
```
`JordanWigner_CAR_Target n` packages exactly this statement for a family
`c : Fin n → M` of operators valued in a (non-commutative) ring `M`,
where `dagger` is the involution playing the role of Hermitian
conjugation.  The two-site theorem `twoSite_anticomm` is the witnessing
instance of the off-diagonal `{cᵢ, cⱼ} = 0` part. -/
def JordanWigner_CAR_Target
    {M : Type*} [Ring M] (n : ℕ) (c : Fin n → M) (dagger : M → M) : Prop :=
  (∀ i j : Fin n, c i * c j + c j * c i = 0) ∧
  (∀ i j : Fin n,
    c i * dagger (c j) + dagger (c j) * c i = if i = j then 1 else 0)

/-! ## Master theorem -/

/-- **Jordan–Wigner master theorem.**  All of the unconditional algebraic
facts driving the JW transformation, collected in one statement:

1. on-site Pauli exclusion `σ⁺σ⁺ = 0`, `σ⁻σ⁻ = 0`;
2. the on-site CAR `{σ⁺, σ⁻} = I`;
3. the projector identities `σ⁺σ⁻ + σ⁻σ⁺ = I` and `σ⁺σ⁻ − σ⁻σ⁺ = Z`;
4. idempotence of the number operator `n² = n`;
5. the `Z`-string anticommutations `Zσ± = −σ±Z`;
6. the two-site fermionic anticommutation `(Z⊗σ⁻)(σ⁻⊗I) =
   −(σ⁻⊗I)(Z⊗σ⁻)`. -/
theorem jordan_wigner_master :
    sigmaPlus * sigmaPlus = 0 ∧
    sigmaMinus * sigmaMinus = 0 ∧
    sigmaPlus * sigmaMinus + sigmaMinus * sigmaPlus = 1 ∧
    sigmaPlus * sigmaMinus - sigmaMinus * sigmaPlus = pauliZ ∧
    (sigmaMinus * sigmaPlus) * (sigmaMinus * sigmaPlus) = sigmaMinus * sigmaPlus ∧
    pauliZ * sigmaPlus = -(sigmaPlus * pauliZ) ∧
    pauliZ * sigmaMinus = -(sigmaMinus * pauliZ) ∧
    Z_tensor_sigmaMinus * sigmaMinus_tensor_I
      = -(sigmaMinus_tensor_I * Z_tensor_sigmaMinus) :=
  ⟨sigmaPlus_sq, sigmaMinus_sq, anticomm_plus_minus, projectors_diff,
    numberOp_idempotent, Z_anticomm_sigmaPlus, Z_anticomm_sigmaMinus,
    twoSite_anticomm⟩

-- Axiom audit: `jordan_wigner_master` depends only on the standard
-- Lean/Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`).  No
-- `sorry`, no custom `axiom`.
#print axioms jordan_wigner_master

end UnifiedTheory.LayerB.JordanWigner
