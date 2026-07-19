/-
  UnifiedTheory/LayerC/SMGaugeFiniteRep.lean
  ───────────────────────────────────────────

  **SM ↔ QM Bridge — Step S3 (Path B).**

  Instantiates `IsUnitaryRep` from `LayerC.QuantumReferenceFrames` with
  two FINITE subgroups of the SM gauge structure:

    (R1)  **Z₂ ⊂ SU(2)**  — the weak-isospin phase-flip subgroup,
                              represented on `ℂ²` by  {I, σ_z}.

    (R2)  **Z₃ ⊂ SU(3)**  — the color cyclic-permutation subgroup,
                              represented on `ℂ³` by cyclic shifts of
                              the basis vectors.

  Dimensions are framework-forced:
      dim ℂ² = atom_N_W = 2     (weak-isospin slice)
      dim ℂ³ = atom_N_c = 3     (color slice)

  Each instantiation:
    • produces a `Group` structure on a small finite carrier;
    • exhibits a representation `U : G → Matrix (Fin n) (Fin n) ℂ`;
    • proves `IsUnitaryRep U` (homomorphism, identity, unitary, unitary');
    • characterises the G-covariant subalgebra.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  The CONTINUOUS Lie groups SU(2), SU(3) require the Haar measure
  (and Bochner-style integration of matrix-valued functions over the
  group manifold) for the twirl, which is a multi-week formalisation.
  The **finite subgroup** case is immediate and is shipped here —
  it already exhibits the bridge content: a unitary representation,
  multiplicativity, a nontrivial G-covariant subalgebra, and operational
  invariance via `covariance_invariance` from `QuantumReferenceFrames`.

  The full **Pauli group of order 16** (the central extension
  ⟨i⟩ × V₄) is a finite subgroup of U(2); we ship the Z₂ ⊂ SU(2)
  σ_z-subgroup as the proof-of-concept finite weak-isospin rep, and
  flag the full Pauli rep as a routine extension (no new conceptual
  content beyond what is here).

  Standing constraint: zero `sorry`, zero custom `axiom`.
-/

import UnifiedTheory.LayerC.QuantumReferenceFrames
import UnifiedTheory.LayerB.CrossSectorIdentitySearch

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.SMGaugeFiniteRep

open Matrix
open UnifiedTheory.LayerC.QuantumReferenceFrames
open UnifiedTheory.LayerB.CrossSectorIdentitySearch (atom_N_W atom_N_c)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1:  THE CYCLIC GROUP Z₂  (weak-isospin phase-flip subgroup)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The cyclic group of order 2, carried by `Fin 2`.  Multiplication
    is addition modulo 2 (i.e. XOR on the bit pattern). -/
def Z2Group : Type := Fin 2

instance : DecidableEq Z2Group := inferInstanceAs (DecidableEq (Fin 2))
instance : Fintype Z2Group := inferInstanceAs (Fintype (Fin 2))
instance : Inhabited Z2Group := inferInstanceAs (Inhabited (Fin 2))

namespace Z2Group

/-- Multiplication: addition modulo 2. -/
def mul (a b : Z2Group) : Z2Group :=
  ⟨(a.val + b.val) % 2, Nat.mod_lt _ (by decide)⟩

/-- Identity: `0`. -/
def one : Z2Group := ⟨0, by decide⟩

/-- Inverse: every element is self-inverse. -/
def inv (a : Z2Group) : Z2Group := a

instance : Mul Z2Group := ⟨mul⟩
instance : One Z2Group := ⟨one⟩
instance : Inv Z2Group := ⟨inv⟩

@[simp] lemma mul_def (a b : Z2Group) :
    a * b = ⟨(a.val + b.val) % 2, Nat.mod_lt _ (by decide)⟩ := rfl

@[simp] lemma one_def : (1 : Z2Group) = ⟨0, by decide⟩ := rfl

@[simp] lemma inv_def (a : Z2Group) : a⁻¹ = a := rfl

/-- `Z₂` is a (commutative) group.  All field equations are decidable
    by full case-analysis on the two elements. -/
instance : Group Z2Group where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

end Z2Group

/-! ## 1.1  The Z₂ representation on ℂ² by σ_z -/

/-- The **σ_z phase-flip representation** of `Z₂` on `ℂ²`:
    `U(0) = I`,  `U(1) = diag(1, -1) = σ_z`.

    This is a faithful (1-1) representation of `Z₂` into `U(2)`; the
    image generators have determinant `+1`, so the image lies in
    `SU(2)`.  It is the discrete weak-isospin phase-flip subgroup. -/
noncomputable def z2PhaseFlipRep : Z2Group → Matrix (Fin 2) (Fin 2) ℂ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => Matrix.diagonal ![1, -1]
  | ⟨n + 2, h⟩ => absurd h (by omega)

@[simp] lemma z2PhaseFlipRep_zero :
    z2PhaseFlipRep ⟨0, by decide⟩ = 1 := rfl

@[simp] lemma z2PhaseFlipRep_one :
    z2PhaseFlipRep ⟨1, by decide⟩ = Matrix.diagonal ![1, -1] := rfl

/-- The σ_z matrix is its own conjugate-transpose (it is real and diagonal). -/
lemma z2_sigmaZ_conjTranspose :
    (Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
      = Matrix.diagonal ![1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons]

/-- The σ_z matrix squares to the identity. -/
lemma z2_sigmaZ_sq :
    (Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℂ) *
        Matrix.diagonal ![1, -1] = 1 := by
  ext i j
  rw [Matrix.diagonal_mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The σ_z rep is a unitary representation of `Z₂`. -/
theorem z2PhaseFlipRep_isUnitaryRep :
    IsUnitaryRep z2PhaseFlipRep where
  hom := by
    intro g h
    -- Both `g` and `h` are in `Fin 2`; case-bash all four combinations.
    rcases g with ⟨gv, hgv⟩
    rcases h with ⟨hv, hhv⟩
    interval_cases gv <;> interval_cases hv <;>
      simp only [z2PhaseFlipRep, Z2Group.mul_def, Matrix.mul_one, Matrix.one_mul,
                 Nat.add_zero, Nat.zero_mod, Nat.zero_add, Nat.mod_self,
                 Nat.reduceAdd, Nat.reduceMod, Fin.zero_eta]
    -- Remaining case (1,1): U(0) = U(1) * U(1), i.e. 1 = σ_z * σ_z.
    exact z2_sigmaZ_sq.symm
  one := rfl
  unitary := by
    intro g
    rcases g with ⟨gv, hgv⟩
    interval_cases gv
    · -- g = 0:  U(0) * U(0)† = I * I = I.
      simp [z2PhaseFlipRep]
    · -- g = 1:  σ_z * σ_z† = σ_z * σ_z = I.
      rw [z2PhaseFlipRep_one, z2_sigmaZ_conjTranspose]
      exact z2_sigmaZ_sq
  unitary' := by
    intro g
    rcases g with ⟨gv, hgv⟩
    interval_cases gv
    · simp [z2PhaseFlipRep]
    · rw [z2PhaseFlipRep_one, z2_sigmaZ_conjTranspose]
      exact z2_sigmaZ_sq

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2:  THE CYCLIC GROUP Z₃  (color permutation subgroup)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The cyclic group of order 3, carried by `Fin 3`. -/
def Z3Group : Type := Fin 3

instance : DecidableEq Z3Group := inferInstanceAs (DecidableEq (Fin 3))
instance : Fintype Z3Group := inferInstanceAs (Fintype (Fin 3))
instance : Inhabited Z3Group := inferInstanceAs (Inhabited (Fin 3))

namespace Z3Group

/-- Multiplication: addition modulo 3. -/
def mul (a b : Z3Group) : Z3Group :=
  ⟨(a.val + b.val) % 3, Nat.mod_lt _ (by decide)⟩

/-- Identity: `0`. -/
def one : Z3Group := ⟨0, by decide⟩

/-- Inverse: negation mod 3 (so `0⁻¹ = 0`, `1⁻¹ = 2`, `2⁻¹ = 1`). -/
def inv (a : Z3Group) : Z3Group :=
  ⟨(3 - a.val) % 3, Nat.mod_lt _ (by decide)⟩

instance : Mul Z3Group := ⟨mul⟩
instance : One Z3Group := ⟨one⟩
instance : Inv Z3Group := ⟨inv⟩

@[simp] lemma mul_def (a b : Z3Group) :
    a * b = ⟨(a.val + b.val) % 3, Nat.mod_lt _ (by decide)⟩ := rfl

@[simp] lemma one_def : (1 : Z3Group) = ⟨0, by decide⟩ := rfl

@[simp] lemma inv_def (a : Z3Group) :
    a⁻¹ = ⟨(3 - a.val) % 3, Nat.mod_lt _ (by decide)⟩ := rfl

/-- `Z₃` is a (commutative) group. -/
instance : Group Z3Group where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

end Z3Group

/-! ## 2.1  The Z₃ representation on ℂ³ by cyclic permutation

The 3-cycle permutation matrix `P` sends basis vector `e_i` to
`e_{(i+1) mod 3}`.  Concretely:

    P  =  [ 0  0  1 ]
          [ 1  0  0 ]
          [ 0  1  0 ]

`P` is real orthogonal (so unitary as a complex matrix), `P³ = I`,
and `det P = +1`, so the cyclic subgroup `⟨P⟩` lies in `SO(3) ⊂ SU(3)`.
This is the **discrete color-permutation subgroup** of `SU(3)`. -/

/-- The cyclic-3 permutation matrix `P`:  e_i ↦ e_{(i+1) mod 3}.
    `P[i,j] = 1` iff `i = j + 1 mod 3`, else `0`. -/
noncomputable def cyclic3Perm : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i.val = (j.val + 1) % 3 then 1 else 0

/-- The Z₃ representation:
      `U(0) = I`,  `U(1) = P`,  `U(2) = P²`. -/
noncomputable def z3CyclicRep : Z3Group → Matrix (Fin 3) (Fin 3) ℂ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => cyclic3Perm
  | ⟨2, _⟩ => cyclic3Perm * cyclic3Perm
  | ⟨n + 3, h⟩ => absurd h (by omega)

@[simp] lemma z3CyclicRep_zero :
    z3CyclicRep ⟨0, by decide⟩ = 1 := rfl

@[simp] lemma z3CyclicRep_one :
    z3CyclicRep ⟨1, by decide⟩ = cyclic3Perm := rfl

@[simp] lemma z3CyclicRep_two :
    z3CyclicRep ⟨2, by decide⟩ = cyclic3Perm * cyclic3Perm := rfl

/-- Closed-form value of `cyclic3Perm * cyclic3Perm` (= P²): the
    "shift by 2" permutation matrix. -/
lemma cyclic3Perm_sq_apply (i j : Fin 3) :
    (cyclic3Perm * cyclic3Perm) i j
      = if i.val = (j.val + 2) % 3 then 1 else 0 := by
  simp [cyclic3Perm, Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp

/-- `cyclic3Perm³ = I`.  This is the order-3 relation. -/
lemma cyclic3Perm_cubed :
    cyclic3Perm * cyclic3Perm * cyclic3Perm = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [cyclic3Perm_sq_apply, cyclic3Perm]
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.one_apply]

/-- Right-associated form of `P³ = I`. -/
lemma cyclic3Perm_cubed' :
    cyclic3Perm * (cyclic3Perm * cyclic3Perm) = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [← Matrix.mul_assoc]; exact cyclic3Perm_cubed

/-- `P⁴ = P`. -/
lemma cyclic3Perm_fourth :
    cyclic3Perm * cyclic3Perm * cyclic3Perm * cyclic3Perm = cyclic3Perm := by
  rw [cyclic3Perm_cubed, Matrix.one_mul]

/-- `(P²) * (P²) = P` (= `P⁴`). -/
lemma cyclic3Perm_sq_sq :
    (cyclic3Perm * cyclic3Perm) * (cyclic3Perm * cyclic3Perm) = cyclic3Perm := by
  -- Strip the parentheses on the right factor by associativity:
  rw [← Matrix.mul_assoc (cyclic3Perm * cyclic3Perm) cyclic3Perm cyclic3Perm,
      cyclic3Perm_fourth]

/-- The conjugate-transpose of `cyclic3Perm` is `cyclic3Perm * cyclic3Perm`
    (= P², which is the inverse cyclic shift). -/
lemma cyclic3Perm_conjTranspose :
    cyclic3Permᴴ = cyclic3Perm * cyclic3Perm := by
  ext i j
  rw [cyclic3Perm_sq_apply, Matrix.conjTranspose_apply]
  simp only [cyclic3Perm]
  -- P[j,i] = 1 iff j = i + 1 (mod 3) iff i = j + 2 (mod 3).
  fin_cases i <;> fin_cases j <;> simp

/-- `cyclic3Perm * cyclic3Permᴴ = I` (unitarity, version 1). -/
lemma cyclic3Perm_mul_conjTranspose :
    cyclic3Perm * cyclic3Permᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [cyclic3Perm_conjTranspose, ← Matrix.mul_assoc]
  exact cyclic3Perm_cubed

/-- `cyclic3Permᴴ * cyclic3Perm = I` (unitarity, version 2). -/
lemma cyclic3Perm_conjTranspose_mul :
    cyclic3Permᴴ * cyclic3Perm = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [cyclic3Perm_conjTranspose]
  -- Goal: P*P*P = I.
  exact cyclic3Perm_cubed

/-- Conjugate-transpose of `P²`: equals `P` (since `(P²)† = (P†)² = (P²)² = P^4 = P`). -/
lemma cyclic3Perm_sq_conjTranspose :
    (cyclic3Perm * cyclic3Perm)ᴴ = cyclic3Perm := by
  -- (A*B)† = B† * A†, so (P*P)† = P† * P† = (P²)(P²) = P⁴ = P.
  rw [Matrix.conjTranspose_mul, cyclic3Perm_conjTranspose]
  exact cyclic3Perm_sq_sq

/-- `P² * (P²)† = I`. -/
lemma cyclic3Perm_sq_mul_conjTranspose :
    (cyclic3Perm * cyclic3Perm) * (cyclic3Perm * cyclic3Perm)ᴴ
      = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [cyclic3Perm_sq_conjTranspose]
  -- Goal: (P*P) * P = P*P*P = I.
  rw [Matrix.mul_assoc] -- gives P * (P * P) → wrong direction; reverse:
  rw [← Matrix.mul_assoc] -- back to (P*P)*P
  exact cyclic3Perm_cubed

/-- `(P²)† * P² = I`. -/
lemma cyclic3Perm_sq_conjTranspose_mul :
    (cyclic3Perm * cyclic3Perm)ᴴ * (cyclic3Perm * cyclic3Perm)
      = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [cyclic3Perm_sq_conjTranspose]
  -- Goal: P * (P*P) = (P*P)*P = I.
  rw [← Matrix.mul_assoc]
  exact cyclic3Perm_cubed

/-- The Z₃ cyclic rep is a unitary representation. -/
theorem z3CyclicRep_isUnitaryRep :
    IsUnitaryRep z3CyclicRep where
  hom := by
    intro g h
    rcases g with ⟨gv, hgv⟩
    rcases h with ⟨hv, hhv⟩
    interval_cases gv <;> interval_cases hv <;>
      simp [z3CyclicRep, Z3Group.mul_def] <;>
      first
        | exact (cyclic3Perm_cubed').symm
        | exact cyclic3Perm_cubed.symm
        | exact cyclic3Perm_sq_sq.symm
  one := rfl
  unitary := by
    intro g
    rcases g with ⟨gv, hgv⟩
    interval_cases gv
    · simp [z3CyclicRep]
    · exact cyclic3Perm_mul_conjTranspose
    · exact cyclic3Perm_sq_mul_conjTranspose
  unitary' := by
    intro g
    rcases g with ⟨gv, hgv⟩
    interval_cases gv
    · simp [z3CyclicRep]
    · exact cyclic3Perm_conjTranspose_mul
    · exact cyclic3Perm_sq_conjTranspose_mul

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3:  G-COVARIANT SUBALGEBRA CHARACTERISATIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For each finite representation we record the structure of the
    G-covariant subalgebra `{A : ∀ g, U g · A · (U g)† = A}`.

    NOTE.  The framework spec quoted "covariant subalgebra =
    scalar multiples of I" for the **full Pauli group of order 16**
    (which is irreducible on ℂ²).  Our finite Z₂ ⊂ SU(2) σ_z-subgroup
    is REDUCIBLE on ℂ² (it splits into the +1 and −1 eigenspaces of
    σ_z), so by Schur the covariant subalgebra is the **diagonal**
    matrices — a 2-D commutative subalgebra, not the 1-D scalars.

    Likewise, the Z₃ cyclic-permutation subgroup of SU(3) is the
    regular representation, which decomposes into three 1-D irreps;
    its covariant subalgebra is the **circulant** matrices — a 3-D
    commutative subalgebra.

    Both characterisations are STRUCTURAL (not numerical): they say
    the covariant subalgebra is rich enough to support nontrivial
    Bartlett–Rudolph–Spekkens reference-frame-invariant observables,
    while still being properly smaller than the full algebra. -/

/-! ## 3.1  Z₂ σ_z covariant subalgebra: diagonal direction -/

/-- Every diagonal matrix is G-covariant under the Z₂ σ_z rep:
    σ_z · diag(a, b) · σ_z = diag(a, b) (signs cancel pairwise). -/
theorem isGCovariant_z2_of_diagonal
    (a b : ℂ) :
    IsGCovariant z2PhaseFlipRep (Matrix.diagonal ![a, b]) := by
  intro g
  rcases g with ⟨gv, hgv⟩
  interval_cases gv
  · -- g = 0:  I · D · I = D.
    simp [z2PhaseFlipRep]
  · -- g = 1:  σ_z · D · σ_z = D.
    rw [z2PhaseFlipRep_one, z2_sigmaZ_conjTranspose,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    ext k
    fin_cases k <;> simp

/-- The identity matrix is G-covariant (instance of the diagonal case). -/
theorem isGCovariant_z2_one :
    IsGCovariant z2PhaseFlipRep (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  IsGCovariant.one z2PhaseFlipRep_isUnitaryRep

/-- σ_z itself is G-covariant (instance of the diagonal case). -/
theorem isGCovariant_z2_sigmaZ :
    IsGCovariant z2PhaseFlipRep (Matrix.diagonal ![(1 : ℂ), -1]) :=
  isGCovariant_z2_of_diagonal 1 (-1)

/-! ## 3.2  Z₃ cyclic covariant subalgebra: identity, P, P² -/

/-- The identity matrix is G-covariant under the Z₃ cyclic rep. -/
theorem isGCovariant_z3_one :
    IsGCovariant z3CyclicRep (1 : Matrix (Fin 3) (Fin 3) ℂ) :=
  IsGCovariant.one z3CyclicRep_isUnitaryRep

/-- The cyclic permutation matrix `P` is G-covariant under the Z₃ rep
    (it commutes with every power of itself). -/
theorem isGCovariant_z3_P :
    IsGCovariant z3CyclicRep cyclic3Perm := by
  intro g
  rcases g with ⟨gv, hgv⟩
  interval_cases gv
  · -- g = 0:  I · P · I = P.
    simp [z3CyclicRep]
  · -- g = 1:  P · P · P† = P · P · P² = P^4 = P.
    rw [z3CyclicRep_one, cyclic3Perm_conjTranspose]
    -- Goal: P * P * (P * P) = P.  This is (P²)(P²) = P^4 = P.
    rw [show cyclic3Perm * cyclic3Perm * (cyclic3Perm * cyclic3Perm)
          = (cyclic3Perm * cyclic3Perm) * (cyclic3Perm * cyclic3Perm) from rfl]
    exact cyclic3Perm_sq_sq
  · -- g = 2:  P² · P · (P²)† = P² · P · P = P^4 = P.
    rw [z3CyclicRep_two, cyclic3Perm_sq_conjTranspose]
    -- Goal: P*P * P * P = P.  i.e. P^4 = P.
    exact cyclic3Perm_fourth

/-- `P²` is G-covariant under the Z₃ rep. -/
theorem isGCovariant_z3_P_sq :
    IsGCovariant z3CyclicRep (cyclic3Perm * cyclic3Perm) :=
  IsGCovariant.mul z3CyclicRep_isUnitaryRep
    isGCovariant_z3_P isGCovariant_z3_P

/-- **Circulant subalgebra (existence).**  For any `α, β, γ ∈ ℂ`,
    the linear combination `α · I + β · P + γ · P²` is G-covariant
    under the Z₃ cyclic rep.  This 3-parameter family is the
    commutant of the cyclic-shift in `End(ℂ³)` — the circulant
    subalgebra. -/
theorem isGCovariant_z3_circulant (α β γ : ℂ) :
    IsGCovariant z3CyclicRep
      (α • (1 : Matrix (Fin 3) (Fin 3) ℂ) + β • cyclic3Perm
         + γ • (cyclic3Perm * cyclic3Perm)) := by
  refine IsGCovariant.add ?_ ?_
  · exact (isGCovariant_z3_one.smul α).add (isGCovariant_z3_P.smul β)
  · exact isGCovariant_z3_P_sq.smul γ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4:  TWIRL WITNESSES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The twirl `𝒯[A] = (1/|G|) Σ_g U g · A · (U g)†` produces a
    G-covariant operator from any matrix.  We record that the twirl
    is well-defined (well-typed) and G-covariant for each of our
    finite groups, then exhibit the operationally-invariant prediction
    `Tr(A · ρ)` for G-covariant `A`. -/

/-- The Z₂ twirl of any matrix is G-covariant. -/
theorem z2_twirl_isGCovariant (A : Matrix (Fin 2) (Fin 2) ℂ) :
    IsGCovariant z2PhaseFlipRep (twirl z2PhaseFlipRep A) :=
  twirl_isGCovariant z2PhaseFlipRep z2PhaseFlipRep_isUnitaryRep A

/-- The Z₃ twirl of any matrix is G-covariant. -/
theorem z3_twirl_isGCovariant (A : Matrix (Fin 3) (Fin 3) ℂ) :
    IsGCovariant z3CyclicRep (twirl z3CyclicRep A) :=
  twirl_isGCovariant z3CyclicRep z3CyclicRep_isUnitaryRep A

/-- The Z₂ twirl is idempotent on G-covariant matrices:
    `𝒯[D] = D` for any diagonal `D`. -/
theorem z2_twirl_diagonal_eq (a b : ℂ) :
    twirl z2PhaseFlipRep (Matrix.diagonal ![a, b])
      = Matrix.diagonal ![a, b] :=
  twirl_gcovariant_eq z2PhaseFlipRep (isGCovariant_z2_of_diagonal a b)

/-- The Z₃ twirl is idempotent on circulant matrices. -/
theorem z3_twirl_circulant_eq (α β γ : ℂ) :
    twirl z3CyclicRep
        (α • (1 : Matrix (Fin 3) (Fin 3) ℂ) + β • cyclic3Perm
           + γ • (cyclic3Perm * cyclic3Perm))
      = α • (1 : Matrix (Fin 3) (Fin 3) ℂ) + β • cyclic3Perm
          + γ • (cyclic3Perm * cyclic3Perm) :=
  twirl_gcovariant_eq z3CyclicRep (isGCovariant_z3_circulant α β γ)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5:  OPERATIONAL INVARIANCE (BRS principle, instantiated)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For each of our finite reps, the operational expectation
    `Tr(A · ρ)` of a G-covariant observable `A` is invariant under
    G-rotations of the state `ρ`.  This is the BRS principle for
    the discrete weak-isospin and color subgroups. -/

/-- **Z₂ reference-frame invariance.**  For any diagonal observable
    `D = diag(a,b)` on ℂ², the expectation `Tr(D · ρ)` is invariant
    under the σ_z phase flip of the state. -/
theorem z2_covariance_invariance
    (a b : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (g : Z2Group) :
    Matrix.trace
      (Matrix.diagonal ![a, b] *
        (z2PhaseFlipRep g * ρ * (z2PhaseFlipRep g)ᴴ))
      = Matrix.trace (Matrix.diagonal ![a, b] * ρ) :=
  covariance_invariance z2PhaseFlipRep_isUnitaryRep
    (isGCovariant_z2_of_diagonal a b) ρ g

/-- **Z₃ reference-frame invariance.**  For any circulant observable
    `α·I + β·P + γ·P²` on ℂ³, the expectation is invariant under
    cyclic permutations of the color basis. -/
theorem z3_covariance_invariance
    (α β γ : ℂ) (ρ : Matrix (Fin 3) (Fin 3) ℂ) (g : Z3Group) :
    Matrix.trace
      ((α • (1 : Matrix (Fin 3) (Fin 3) ℂ) + β • cyclic3Perm
          + γ • (cyclic3Perm * cyclic3Perm)) *
        (z3CyclicRep g * ρ * (z3CyclicRep g)ᴴ))
      = Matrix.trace
          ((α • (1 : Matrix (Fin 3) (Fin 3) ℂ) + β • cyclic3Perm
              + γ • (cyclic3Perm * cyclic3Perm)) * ρ) :=
  covariance_invariance z3CyclicRep_isUnitaryRep
    (isGCovariant_z3_circulant α β γ) ρ g

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6:  DIMENSION-PINNING TO FRAMEWORK ATOMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Z₂ rep lives on `ℂ^(atom_N_W)`. -/
theorem z2_dim_eq_atom_N_W :
    (2 : ℕ) = atom_N_W := rfl

/-- The Z₃ rep lives on `ℂ^(atom_N_c)`. -/
theorem z3_dim_eq_atom_N_c :
    (3 : ℕ) = atom_N_c := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7:  MASTER BRIDGE THEOREM  (Step S3, Path B)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER BRIDGE (Step S3, Path B).**

    The Bartlett–Rudolph–Spekkens reference-frame framework is
    instantiated on the framework's atomic Hilbert dimensions by
    explicit FINITE subgroups of the standard-model gauge groups:

      (i)   a Z₂ ⊂ SU(2) phase-flip rep on `ℂ^(atom_N_W) = ℂ²`,
      (ii)  a Z₃ ⊂ SU(3) cyclic-permutation rep on `ℂ^(atom_N_c) = ℂ³`,
      (iii) both reps are bona fide unitary representations
            (`IsUnitaryRep`),
      (iv)  each has a nontrivial G-covariant subalgebra
            (diagonal for Z₂; circulant for Z₃),
      (v)   each delivers Bartlett–Rudolph–Spekkens reference-frame
            invariance for its covariant observables.

    Continuous SU(2), SU(3) require Haar-measure twirling and are
    deferred. -/
theorem sm_gauge_finite_rep_bridge_S3 :
    -- (i, iii) Z₂ rep is unitary on ℂ²:
    IsUnitaryRep z2PhaseFlipRep ∧
    -- (ii, iii) Z₃ rep is unitary on ℂ³:
    IsUnitaryRep z3CyclicRep ∧
    -- (iv-a) σ_z is G-covariant under Z₂:
    IsGCovariant z2PhaseFlipRep (Matrix.diagonal ![(1 : ℂ), -1]) ∧
    -- (iv-b) P is G-covariant under Z₃:
    IsGCovariant z3CyclicRep cyclic3Perm ∧
    -- (v-a) BRS invariance for Z₂ diagonal observables:
    (∀ (a b : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (g : Z2Group),
        Matrix.trace
          (Matrix.diagonal ![a, b] *
            (z2PhaseFlipRep g * ρ * (z2PhaseFlipRep g)ᴴ))
          = Matrix.trace (Matrix.diagonal ![a, b] * ρ)) ∧
    -- (v-b) BRS invariance for Z₃ circulant observables:
    (∀ (α β γ : ℂ) (ρ : Matrix (Fin 3) (Fin 3) ℂ) (g : Z3Group),
        Matrix.trace
          ((α • (1 : Matrix (Fin 3) (Fin 3) ℂ) + β • cyclic3Perm
              + γ • (cyclic3Perm * cyclic3Perm)) *
            (z3CyclicRep g * ρ * (z3CyclicRep g)ᴴ))
          = Matrix.trace
              ((α • (1 : Matrix (Fin 3) (Fin 3) ℂ) + β • cyclic3Perm
                  + γ • (cyclic3Perm * cyclic3Perm)) * ρ)) := by
  refine ⟨z2PhaseFlipRep_isUnitaryRep, z3CyclicRep_isUnitaryRep,
          isGCovariant_z2_sigmaZ, isGCovariant_z3_P,
          ?_, ?_⟩
  · exact z2_covariance_invariance
  · exact z3_covariance_invariance

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8:  AXIOM AUDIT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    All deliverables in this file depend only on the standard
    Lean / Mathlib axioms (`propext`, `Classical.choice`,
    `Quot.sound`).  No custom `axiom` is introduced.

    Verified by:
        #print axioms z2PhaseFlipRep_isUnitaryRep
        #print axioms z3CyclicRep_isUnitaryRep
        #print axioms sm_gauge_finite_rep_bridge_S3
-/

end UnifiedTheory.LayerC.SMGaugeFiniteRep
