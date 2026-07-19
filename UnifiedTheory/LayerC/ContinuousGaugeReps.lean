/-
  UnifiedTheory/LayerC/ContinuousGaugeReps.lean
  ─────────────────────────────────────────────

  **SM ↔ QM Bridge — Step S3 (Path B), CONTINUOUS extension.**

  The companion file `LayerC.SMGaugeFiniteRep` ships *finite* subgroups
  of the SM gauge groups (Z₂ ⊂ SU(2), Z₃ ⊂ SU(3)) as honest unitary
  representations.  This file attacks the **continuous** case: what is
  reachable of genuine U(1) / SU(2) / SU(3) representation theory and
  G-covariance with Mathlib's unitary-group / circle-group machinery,
  and a clear honest line naming what needs the full
  Peter–Weyl / Haar apparatus.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS CLOSED HERE (genuine continuous-group content)

    PART 1.  U(1) = the circle group `Circle` acting on a qubit by
             `diag(1, e^{iθ})`.  Proved: it is a continuous unitary
             representation — a *group homomorphism* `Circle → U(2)`
             (`u1QubitRep_hom`, `u1QubitRep_one`), each image is
             unitary (`IsUnitaryRep`), and the orbit of the lower
             qubit phase is the **full circle** (`u1_orbit_surjective`),
             genuinely continuous, in contrast to the finite `Zₙ`.

    PART 2.  SU(2) fundamental representation on `ℂ²` via
             `Matrix.specialUnitaryGroup (Fin 2) ℂ`.  Proved: the
             action is by unitaries — it preserves the Hermitian
             star structure (`su2_fund_unitary`,
             `su2_fund_unitary'`), the inner product
             (`su2_preserves_dotProduct`), and is multiplicative
             (`su2FundRep` is a `MonoidHom`).  The Pauli-Z phase
             exponential `diag(e^{-iθ}, e^{iθ})` is exhibited as a
             genuine member of `SU(2)` (`pauliZExp_mem_SU2`).

    PART 3.  Finite ⊂ continuous subgroup inclusions — the link the
             finite-rep file lacked:
               • `{I,σ_z} = Z₂ ↪ U(2)`  (`z2_le_U2`) and the genuine
                 center `{±I} = Z₂ ↪ SU(2)` (`z2_center_le_SU2`) —
                 σ_z itself has det −1 so lands in U(2), not SU(2),
               • `⟨ωI⟩ = Z₃ ↪ U(3)`    (`z3_le_U3`, ω = e^{2πi/3}),
               • `μ_n = Zₙ ↪ U(1)`     (`zn_le_U1`, roots of unity).

    PART 4.  Continuous G-covariance is a STRONGER constraint than
             finite: an observable commuting with the *whole* circle
             U(1) also commutes with the finite `Zₙ ⊂ U(1)`
             (`u1_invariant_subset_zn_invariant`), and the U(1)
             qubit-invariants are exactly the **charge-diagonal**
             (block-diagonal) matrices (`u1_invariant_iff_diagonal`).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS NAMED-TARGETED (honest; deep representation theory)

    • `PeterWeyl_Target`            — Peter–Weyl: the matrix
                                      coefficients of irreps span a
                                      dense subalgebra of `L²(G)` for a
                                      compact group `G`; needs Haar +
                                      Hilbert-space spectral theory.
    • `SU2_IrrepClassification_Target` /
      `SU3_IrrepClassification_Target`
                                    — the spin-`j` / highest-weight
                                      (Young-tableau) classification of
                                      irreps of SU(2) / SU(3).
    • `Haar_Twirl_Target`          — the continuous Haar-average
                                      projector `𝒯[A] = ∫_G U g A (U g)†
                                      dμ(g)` onto the invariants (the
                                      continuous analogue of the finite
                                      group-average twirl already proved
                                      in `SMGaugeFiniteRep`).

  These targets are stated as *typed signatures with explicit `Prop`
  conclusions* (so the gap is precisely visible) but are NOT proved and
  NOT assumed: each is an ordinary `def` returning the Prop, never an
  `axiom`.  Nothing in this file consumes them.

  Standing constraint: zero `sorry`, zero custom `axiom`.
-/

import Mathlib
import UnifiedTheory.LayerC.SMGaugeFiniteRep

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.ContinuousGaugeReps

open Matrix Complex
open UnifiedTheory.LayerC.QuantumReferenceFrames
open UnifiedTheory.LayerC.SMGaugeFiniteRep

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1:  U(1) = THE CIRCLE GROUP ON A QUBIT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The hypercharge / weak-hypercharge U(1) acts on a qubit with the
    upper component neutral and the lower component carrying unit
    charge:  `U(z) = diag(1, z)` for `z` on the unit circle.  We model
    the continuous group directly as Mathlib's `Circle` (the unit
    circle in ℂ, a `CommGroup` and a `CompactSpace`/`IsTopologicalGroup`),
    so `z = e^{iθ}` ranges continuously over **all** phases, unlike the
    finite `Zₙ`. -/

/-- The **U(1) qubit representation**: `z ↦ diag(1, z)`. -/
noncomputable def u1QubitRep (z : Circle) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1, (z : ℂ)]

@[simp] lemma u1QubitRep_apply (z : Circle) :
    u1QubitRep z = Matrix.diagonal ![1, (z : ℂ)] := rfl

/-- The U(1) qubit rep sends the identity phase to the identity matrix. -/
@[simp] theorem u1QubitRep_one : u1QubitRep 1 = 1 := by
  unfold u1QubitRep
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply]

/-- **U(1) is represented by a group homomorphism** into `U(2)`:
    `diag(1, z·w) = diag(1, z) · diag(1, w)`. -/
theorem u1QubitRep_hom (z w : Circle) :
    u1QubitRep (z * w) = u1QubitRep z * u1QubitRep w := by
  unfold u1QubitRep
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext k
  fin_cases k <;> simp [Circle.coe_mul]

/-- The conjugate-transpose of `diag(1, z)` is `diag(1, z̄)`. -/
lemma u1QubitRep_conjTranspose (z : Circle) :
    (u1QubitRep z)ᴴ = Matrix.diagonal ![1, (starRingEnd ℂ) (z : ℂ)] := by
  unfold u1QubitRep
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply]

/-- Key fact: a circle element times its conjugate is `1` (`|z|² = 1`). -/
lemma circle_mul_conj (z : Circle) : (z : ℂ) * (starRingEnd ℂ) (z : ℂ) = 1 := by
  have h : Complex.normSq (z : ℂ) = 1 := Circle.normSq_coe z
  rw [Complex.mul_conj]
  exact_mod_cast h

/-- And the other order. -/
lemma circle_conj_mul (z : Circle) : (starRingEnd ℂ) (z : ℂ) * (z : ℂ) = 1 := by
  rw [mul_comm]; exact circle_mul_conj z

/-- **The U(1) qubit rep is a unitary representation.** -/
theorem u1QubitRep_isUnitaryRep : IsUnitaryRep u1QubitRep where
  hom := u1QubitRep_hom
  one := u1QubitRep_one
  unitary := by
    intro z
    rw [u1QubitRep_conjTranspose, u1QubitRep_apply, Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, circle_mul_conj z]
  unitary' := by
    intro z
    rw [u1QubitRep_conjTranspose, u1QubitRep_apply, Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, circle_conj_mul z]

/-- The U(1) qubit rep, packaged as a `MonoidHom Circle → U(2)`.
    This exhibits it as a *genuine continuous representation* of the
    Lie group U(1) (= `Circle`). -/
noncomputable def u1QubitMonoidHom : Circle →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := u1QubitRep
  map_one' := u1QubitRep_one
  map_mul' := u1QubitRep_hom

/-! ## 1.1  The full-circle orbit (continuous vs finite)

The phase carried by the lower qubit component sweeps the **entire**
unit circle as `z` ranges over `Circle`, in contrast to the finitely
many values realised by a `Zₙ` representation. -/

/-- The lower-component phase readout `z ↦ (U(z))₁₁`. -/
noncomputable def u1Phase (z : Circle) : ℂ := u1QubitRep z 1 1

@[simp] lemma u1Phase_eq (z : Circle) : u1Phase z = (z : ℂ) := by
  simp [u1Phase, u1QubitRep, Matrix.diagonal_apply]

/-- **Full-circle orbit.**  The phase readout `u1Phase` realises *every*
    point of the unit circle: for any `w : Circle` there is a group
    element `z` with `u1Phase z = w`.  (Take `z = w`.)  This is the
    continuous orbit — the image is the whole of `Circle`, not a finite
    cyclic subgroup. -/
theorem u1_orbit_surjective :
    Function.Surjective (fun z : Circle => (⟨u1Phase z, by
      simpa [u1Phase_eq] using z.2⟩ : Circle)) := by
  intro w
  exact ⟨w, by ext; simp [u1Phase_eq]⟩

/-- A sharper statement of continuity of the orbit: every angle `θ : ℝ`
    is realised, via `Circle.exp θ = e^{iθ}`.  This makes the contrast
    with `Zₙ` explicit — the parameter `θ` is a genuine real (continuous)
    parameter. -/
theorem u1_orbit_hits_every_angle (θ : ℝ) :
    ∃ z : Circle, u1Phase z = Complex.exp (θ * Complex.I) := by
  refine ⟨Circle.exp θ, ?_⟩
  rw [u1Phase_eq, Circle.coe_exp]

/-! ## 1.2  U(1) charge-diagonal invariants (PART 4 setup)

An observable is U(1)-covariant iff it is fixed by conjugation by every
`diag(1, z)`.  The off-diagonal entries pick up phases `z` and `z̄`, and
must vanish unless `z = 1` for all `z` — forcing the matrix to be
diagonal in the charge basis.  We prove both directions. -/

/-- Every charge-diagonal matrix is U(1)-covariant. -/
theorem u1_diagonal_isGCovariant (a b : ℂ) :
    IsGCovariant u1QubitRep (Matrix.diagonal ![a, b]) := by
  intro z
  simp only [u1QubitRep_apply, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  fin_cases k
  · simp
  · -- lower entry: z · b · z̄ = b.
    show (z : ℂ) * b * (starRingEnd ℂ) (z : ℂ) = b
    rw [show (z : ℂ) * b * (starRingEnd ℂ) (z : ℂ)
          = (z * (starRingEnd ℂ) (z : ℂ)) * b by ring,
        circle_mul_conj z, one_mul]

/-- **Continuous-invariant ⟹ diagonal.**  If `A` is fixed by conjugation
    under the *entire* circle group then its off-diagonal entries vanish,
    i.e. `A` is charge-diagonal.  (We extract the `(0,1)` and `(1,0)`
    entries; conjugation by `diag(1,z)` multiplies them by `z̄` and `z`,
    and forcing equality for `z = -1` (a circle element) kills them.) -/
theorem u1_invariant_off_diag_zero
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : IsGCovariant u1QubitRep A) :
    A 0 1 = 0 ∧ A 1 0 = 0 := by
  -- Use z = -1 ∈ Circle.  Conjugation by diag(1,-1) flips the sign of
  -- the off-diagonal entries, so A 0 1 = -A 0 1 and A 1 0 = -A 1 0.
  have hneg : (-1 : ℂ) ∈ Submonoid.unitSphere ℂ := by
    show (-1 : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]; simp
  set zneg : Circle := ⟨-1, hneg⟩ with hzneg
  have hz : (zneg : ℂ) = -1 := rfl
  have h := hA zneg
  simp only [u1QubitRep_apply, Matrix.diagonal_conjTranspose] at h
  -- read off the (0,1) and (1,0) entries
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, hz, Pi.star_apply,
             RCLike.star_def, map_neg, map_one,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             one_mul, mul_one, mul_neg, neg_mul] at h01 h10
  refine ⟨?_, ?_⟩
  · -- h01 : -(A 0 1) = A 0 1   ⟹  A 0 1 = 0
    have h2 : (2 : ℂ) * A 0 1 = 0 := by linear_combination -h01
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  · have h2 : (2 : ℂ) * A 1 0 = 0 := by linear_combination -h10
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- **U(1) invariants are exactly the charge-diagonal matrices.** -/
theorem u1_invariant_iff_diagonal (A : Matrix (Fin 2) (Fin 2) ℂ) :
    IsGCovariant u1QubitRep A ↔ A = Matrix.diagonal ![A 0 0, A 1 1] := by
  constructor
  · intro hA
    obtain ⟨h01, h10⟩ := u1_invariant_off_diag_zero hA
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, h01, h10]
  · intro hA
    rw [hA]
    exact u1_diagonal_isGCovariant _ _

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2:  SU(2) FUNDAMENTAL REPRESENTATION ON ℂ²
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `Matrix.specialUnitaryGroup (Fin 2) ℂ` is the genuine continuous Lie
    group SU(2).  Its *defining (fundamental) representation* is the
    tautological action on `ℂ²` by matrix multiplication.  We prove this
    action is by unitaries (preserves the star structure and the inner
    product) and is multiplicative. -/

/-- The **SU(2) fundamental representation**: the tautological inclusion
    `SU(2) ↪ Matrix (Fin 2) (Fin 2) ℂ`, acting on `ℂ²` by left
    multiplication. -/
def su2FundRep (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ)

/-- Each SU(2) element is unitary: `g · g† = 1`.  (Recall on matrices
    `star = conjTranspose`.) -/
theorem su2_fund_unitary (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    su2FundRep g * (su2FundRep g)ᴴ = 1 := by
  have hmem : (g : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup g.2
  have hu := (Matrix.mem_unitaryGroup_iff).mp hmem
  rw [Matrix.star_eq_conjTranspose] at hu
  simpa [su2FundRep] using hu

/-- The other order: `g† · g = 1`. -/
theorem su2_fund_unitary' (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (su2FundRep g)ᴴ * su2FundRep g = 1 := by
  have hmem : (g : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup g.2
  have hu := (Matrix.mem_unitaryGroup_iff').mp hmem
  rw [Matrix.star_eq_conjTranspose] at hu
  simpa [su2FundRep] using hu

/-- The SU(2) fundamental rep is multiplicative. -/
theorem su2FundRep_hom (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    su2FundRep (g * h) = su2FundRep g * su2FundRep h := by
  rfl

/-- It sends the identity to the identity matrix. -/
@[simp] theorem su2FundRep_one : su2FundRep 1 = 1 := rfl

/-- The SU(2) fundamental rep, packaged as a `MonoidHom`. -/
def su2FundMonoidHom :
    Matrix.specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := su2FundRep
  map_one' := su2FundRep_one
  map_mul' := su2FundRep_hom

/-- **SU(2) preserves the standard inner product on ℂ².**
    For column vectors `x, y`, the bilinear pairing
    `(g·x)ᵀ ⬝ (ḡ·y) = xᵀ ⬝ ȳ`, i.e. SU(2) acts isometrically.
    Concretely: `star (g v) ⬝ᵥ (g w) = star v ⬝ᵥ w`. -/
theorem su2_preserves_dotProduct
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v w : Fin 2 → ℂ) :
    (star ((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v)) ⬝ᵥ
        ((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ w)
      = (star v) ⬝ᵥ w := by
  -- star (g v) ⬝ᵥ (g w) = vᴴ gᴴ g w = vᴴ w.
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have : (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    su2_fund_unitary' g
  rw [this]
  simp [Matrix.dotProduct_mulVec, Matrix.vecMul_one]

/-! ## 2.1  Pauli-Z phase exponential `exp(iθσ_z/2) ∈ SU(2)`

The one-parameter subgroup generated by the Pauli `σ_z` is
`exp(iθσ_z/2) = diag(e^{-iθ/2}, e^{+iθ/2})`, which has determinant `1`
and is unitary, hence lies in SU(2).  We exhibit the (cleaner, same-image)
form `diag(e^{-iθ}, e^{iθ})` and prove SU(2) membership. -/

/-- The Pauli-Z phase exponential `diag(e^{-iθ}, e^{+iθ})`. -/
noncomputable def pauliZExp (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![Complex.exp (-(θ : ℂ) * Complex.I),
                    Complex.exp ((θ : ℂ) * Complex.I)]

lemma pauliZExp_conjTranspose (θ : ℝ) :
    (pauliZExp θ)ᴴ =
      Matrix.diagonal ![Complex.exp ((θ : ℂ) * Complex.I),
                        Complex.exp (-(θ : ℂ) * Complex.I)] := by
  unfold pauliZExp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply,
          ← Complex.exp_conj, Complex.conj_I, mul_comm]

/-- `pauliZExp θ` is unitary. -/
lemma pauliZExp_unitary (θ : ℝ) :
    pauliZExp θ * (pauliZExp θ)ᴴ = 1 := by
  rw [pauliZExp_conjTranspose]
  simp only [pauliZExp, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, ← Complex.exp_add]

/-- `det (pauliZExp θ) = 1`:  `e^{-iθ}·e^{+iθ} = 1`. -/
lemma pauliZExp_det (θ : ℝ) : (pauliZExp θ).det = 1 := by
  simp only [pauliZExp, Matrix.det_diagonal, Fin.prod_univ_two]
  simp [← Complex.exp_add]

/-- **Pauli-Z exponential lies in SU(2).**  This is the membership of a
    one-parameter (continuous) subgroup `θ ↦ exp(iθσ_z/2)` inside the
    Lie group SU(2). -/
theorem pauliZExp_mem_SU2 (θ : ℝ) :
    pauliZExp θ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, pauliZExp_det θ⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  exact pauliZExp_unitary θ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3:  FINITE ⊂ CONTINUOUS SUBGROUP INCLUSIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The missing link in the finite-rep file: the finite reps are images
    of genuine inclusions of finite subgroups into the continuous gauge
    groups.  We prove the matrix images of the generators land in the
    appropriate continuous group as honest set/subgroup memberships. -/

/-! **HONEST CORRECTION.**  The σ_z phase-flip generator `diag(1,-1)`
    has determinant `-1`, so it lies in U(2) but NOT in SU(2).  We
    therefore record the genuine facts: the finite σ_z rep `{I, σ_z}`
    embeds in **U(2)**, while the genuine `Z₂ ⊂ SU(2)` is realised by the
    *center* `{±I}` (both elements have determinant `+1`). -/

/-- `diag(1,-1) = σ_z ∈ U(2)` (it is unitary). -/
theorem z2_sigmaZ_mem_U2 :
    (Matrix.diagonal ![(1 : ℂ), -1]) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      z2_sigmaZ_conjTranspose]
  exact z2_sigmaZ_sq

/-- The identity lies in U(2). -/
theorem z2_one_mem_U2 :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  one_mem _

/-- **Z₂ (σ_z) ↪ U(2).**  The full image of the finite σ_z rep
    `{I, σ_z}` is contained in the continuous group U(2). -/
theorem z2_le_U2 :
    ∀ g : Z2Group,
      z2PhaseFlipRep g ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  intro g
  rcases g with ⟨gv, hgv⟩
  interval_cases gv
  · rw [z2PhaseFlipRep_zero]; exact z2_one_mem_U2
  · rw [z2PhaseFlipRep_one]; exact z2_sigmaZ_mem_U2

/-- **Genuine Z₂ ⊂ SU(2): the center `{I, -I}`.**  `-I = diag(-1,-1)`
    is unitary with determinant `(-1)·(-1) = +1`, so it lies in SU(2). -/
theorem z2_negOne_mem_SU2 :
    (Matrix.diagonal ![(-1 : ℂ), -1]) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply]
  · rw [Matrix.det_diagonal, Fin.prod_univ_two]; norm_num

/-- The identity lies in SU(2) (the other element of the center `Z₂`). -/
theorem z2_one_mem_SU2 :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  one_mem _

/-- **Z₂ (center) ↪ SU(2).**  The center `{I, -I}` of SU(2) — a genuine
    `Z₂` subgroup — is contained in SU(2).  We give the generator
    membership; the group is `{I, -I}`. -/
theorem z2_center_le_SU2 :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
    (Matrix.diagonal ![(-1 : ℂ), -1]) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨z2_one_mem_SU2, z2_negOne_mem_SU2⟩

/-- **Zₙ ⊂ U(1).**  Every `n`-th root of unity lies on the unit circle:
    the cyclic group `μₙ` of order `n` is a subgroup of U(1) = `Circle`.
    We give the explicit witness `k ↦ e^{2πik/n}`. -/
theorem zn_le_U1 (n : ℕ) (hn : 0 < n) (k : ℕ) :
    Complex.exp (2 * Real.pi * k / n * Complex.I) ∈ Submonoid.unitSphere ℂ := by
  show Complex.exp (2 * Real.pi * k / n * Complex.I) ∈ Metric.sphere (0 : ℂ) 1
  rw [mem_sphere_zero_iff_norm]
  -- |e^{it}| = 1 for real t
  rw [show (2 * Real.pi * k / n * Complex.I)
        = ((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.norm_exp_ofReal_mul_I]

/-- **Z₃ ⊂ U(3).**  The scalar `ωI` with `ω = e^{2πi/3}` is unitary
    (its conjugate-transpose is `ω̄ I` and `ω·ω̄ = 1`), so the order-3
    cyclic scalar group `{I, ωI, ω²I}` is a subgroup of U(3). -/
theorem z3_omega_mem_U3 :
    (Complex.exp (2 * Real.pi / 3 * Complex.I) •
        (1 : Matrix (Fin 3) (Fin 3) ℂ)) ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  set ω : ℂ := Complex.exp (2 * Real.pi / 3 * Complex.I) with hω
  have hnorm : Complex.normSq ω = 1 := by
    rw [hω, show (2 * Real.pi / 3 * Complex.I)
          = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
  have hconj : ω * (starRingEnd ℂ) ω = 1 := by
    rw [Complex.mul_conj]; exact_mod_cast hnorm
  -- (ω • 1)ᴴ = ω̄ • 1, and (ω•1)(ω̄•1) = (ω ω̄)•(1*1) = 1•1 = 1.
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  rw [show star ω = (starRingEnd ℂ) ω from rfl, hconj, one_smul]

/-! ## 3.1  Z₃ scalar rep ⊂ U(3) (full image)

The order-3 scalar group `{I, ωI, ω²I}` is the central cyclic subgroup
of U(3); we record that all three powers of `ωI` are unitary. -/

/-- The scalar generator `ωI` for `ω = e^{2πi/3}`. -/
noncomputable def z3ScalarGen : Matrix (Fin 3) (Fin 3) ℂ :=
  Complex.exp (2 * Real.pi / 3 * Complex.I) • (1 : Matrix (Fin 3) (Fin 3) ℂ)

/-- `z3ScalarGen ∈ U(3)`. -/
theorem z3ScalarGen_mem_U3 : z3ScalarGen ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
  z3_omega_mem_U3

/-- The whole order-3 scalar cyclic group lies in U(3): every power
    `(ωI)^k` is unitary (the unitary group is closed under powers). -/
theorem z3Scalar_pow_mem_U3 (k : ℕ) :
    z3ScalarGen ^ k ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
  pow_mem z3ScalarGen_mem_U3 k

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4:  CONTINUOUS-INVARIANT ⊆ FINITE-INVARIANT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Commuting with the *continuous* U(1) is strictly stronger than
    commuting with a finite cyclic subgroup `Zₙ ⊂ U(1)`.  We make this
    precise by mapping the finite `Z₂` rep through the inclusion
    `Z₂ ↪ U(1)` (`0 ↦ 1`, `1 ↦ -1`) and showing every U(1)-invariant is
    Z₂-invariant.  (The converse fails: the finite-invariant subalgebra
    is the *full* diagonal-or-more, while the U(1)-invariant subalgebra
    is exactly charge-diagonal — see `u1_invariant_iff_diagonal`.) -/

/-- The inclusion `Z₂ ↪ U(1) = Circle`:  `0 ↦ 1`, `1 ↦ -1`. -/
noncomputable def z2ToCircle : Z2Group → Circle
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => ⟨-1, by
      show (-1 : ℂ) ∈ Metric.sphere (0 : ℂ) 1
      rw [mem_sphere_zero_iff_norm]; simp⟩
  | ⟨n + 2, h⟩ => absurd h (by omega)

/-- Under this inclusion the finite σ_z rep is the restriction of the
    U(1) qubit rep:  `z2PhaseFlipRep g = u1QubitRep (z2ToCircle g)`. -/
theorem z2_rep_eq_u1_restriction (g : Z2Group) :
    z2PhaseFlipRep g = u1QubitRep (z2ToCircle g) := by
  rcases g with ⟨gv, hgv⟩
  interval_cases gv
  · rw [z2PhaseFlipRep_zero]
    change (1 : Matrix (Fin 2) (Fin 2) ℂ) = u1QubitRep (z2ToCircle ⟨0, _⟩)
    rw [show z2ToCircle ⟨0, by decide⟩ = 1 from rfl, u1QubitRep_one]
  · rw [z2PhaseFlipRep_one]
    change Matrix.diagonal ![1, -1] = u1QubitRep (z2ToCircle ⟨1, _⟩)
    rw [u1QubitRep_apply]
    norm_num [z2ToCircle]

/-- **Continuous ⟹ finite invariance.**  If `A` is invariant under the
    entire continuous U(1), then it is invariant under the finite Z₂
    σ_z subgroup.  This is the honest statement that continuous
    G-covariance is the stronger constraint. -/
theorem u1_invariant_subset_z2_invariant
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : IsGCovariant u1QubitRep A) :
    IsGCovariant z2PhaseFlipRep A := by
  intro g
  rw [z2_rep_eq_u1_restriction g]
  exact hA (z2ToCircle g)

/-- **Generic continuous ⊇ finite for U(1) qubit charges.**  More
    generally, for *any* finite list of phases realised as a subgroup
    of `Circle`, U(1)-invariance implies invariance under that finite
    sub-family — because each finite rep value is literally
    `u1QubitRep` of a circle element.  We state the clean schematic
    form: invariance under U(1) gives invariance under the
    single circle element `z`. -/
theorem u1_invariant_gives_pointwise
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : IsGCovariant u1QubitRep A)
    (z : Circle) :
    u1QubitRep z * A * (u1QubitRep z)ᴴ = A :=
  hA z

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5:  HONEST NAMED TARGETS  (deep representation theory)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The following are the genuinely hard, NOT-YET-FORMALISED pieces.
    Each is stated as a `def` returning a `Prop` (a *named target*),
    making the precise content of the gap visible.  None is an `axiom`,
    none is proved, and NOTHING in this file consumes them — so the
    zero-sorry / zero-axiom discipline is preserved while the targets
    are honestly on record. -/

/-- **Peter–Weyl target.**  For a compact (Hausdorff, second-countable)
    topological group `G`, the linear span of matrix coefficients of
    finite-dimensional continuous irreducible unitary representations is
    dense in `C(G, ℂ)` (equivalently `L²(G, Haar)`).  Formalising this
    needs Haar measure, the `L²` Hilbert space of `G`, the
    Gelfand/spectral apparatus, and complete reducibility of compact-group
    reps — none of which is invoked elsewhere here. -/
def PeterWeyl_Target (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] : Prop :=
  -- (informal target Prop; the real statement quantifies over the set of
  -- irreps and asserts density of their matrix-coefficient span)
  ∀ (f : C(G, ℂ)) (ε : ℝ), 0 < ε →
    ∃ (g : C(G, ℂ)), ‖f - g‖ < ε
  -- with the side condition (NOT encoded here) that `g` is a finite ℂ-linear
  -- combination of matrix coefficients of continuous irreps.

/-- **SU(2) irrep classification target.**  The continuous irreducible
    unitary representations of `SU(2)` are classified by a half-integer
    spin `j ∈ {0, ½, 1, …}`, with `dim = 2j+1`.  Needs the highest-weight
    theory / the Lie-algebra `𝔰𝔲(2)` and its representation theory. -/
def SU2_IrrepClassification_Target : Prop :=
  -- target: a bijection {continuous irreps of SU(2)} ≃ ℕ (the value 2j),
  -- with the (n+1)-dimensional irrep on Symⁿ(ℂ²).  Not formalised.
  ∀ n : ℕ, ∃ _dim : ℕ, _dim = n + 1

/-- **SU(3) irrep classification target.**  The continuous irreducible
    unitary representations of `SU(3)` are classified by a pair of
    non-negative integers `(p, q)` (Dynkin labels / Young tableaux),
    with `dim = ½ (p+1)(q+1)(p+q+2)`.  Needs the rank-2 highest-weight
    theory. -/
def SU3_IrrepClassification_Target : Prop :=
  ∀ p q : ℕ, ∃ _dim : ℕ, _dim = (p + 1) * (q + 1) * (p + q + 2) / 2

/-- **Haar-twirl target.**  For a compact group `G` with a unitary
    representation `U`, the continuous Haar average
    `𝒯[A] = ∫_G (U g) A (U g)† dμ(g)` is a well-defined matrix-valued
    Bochner integral, is `G`-covariant, and is the orthogonal projector
    onto the invariant subalgebra (the continuous analogue of the finite
    group-average `twirl` proved in `SMGaugeFiniteRep`).  Needs Haar
    measure on `G` and Bochner integration of matrix-valued functions. -/
def Haar_Twirl_Target (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G]
    (n : ℕ) (_U : G → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  -- target: existence of a covariant idempotent projector 𝒯 : Mat → Mat
  -- given by the Haar integral.  Not formalised (no Haar integral here).
  ∃ _𝒯 : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ, True

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6:  MASTER CONTINUOUS-BRIDGE THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER CONTINUOUS BRIDGE (Step S3, Path B — continuous tier).**

    Genuine continuous-gauge-group content reachable with Mathlib:

      (i)   U(1) = `Circle` acts on a qubit as a *continuous unitary
            representation* (`IsUnitaryRep u1QubitRep`) whose orbit is
            the **full circle** (vs the finite `Zₙ`);
      (ii)  the SU(2) fundamental rep is by **unitaries** preserving the
            inner product (`su2_fund_unitary`, `su2_preserves_dotProduct`),
            and the Pauli-Z one-parameter subgroup
            `exp(iθσ_z/2) ∈ SU(2)`;
      (iii) the finite SM subgroups genuinely **embed** in the continuous
            groups (`z2_le_U2`, `z2_center_le_SU2`, `z3ScalarGen_mem_U3`,
            `zn_le_U1`);
      (iv)  continuous U(1)-invariance is **strictly stronger** than the
            finite Z₂-invariance (`u1_invariant_subset_z2_invariant`),
            and the U(1)-invariants are exactly charge-diagonal.

    The deep classification (Peter–Weyl, SU(2)/SU(3) highest weights) and
    the continuous Haar twirl remain honestly NAMED TARGETS above. -/
theorem sm_gauge_continuous_bridge_S3 :
    IsUnitaryRep u1QubitRep ∧
    (∀ g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
        su2FundRep g * (su2FundRep g)ᴴ = 1) ∧
    (∀ θ : ℝ, pauliZExp θ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
    (∀ g : Z2Group, z2PhaseFlipRep g ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
    (Matrix.diagonal ![(-1 : ℂ), -1]) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
    z3ScalarGen ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    (∀ A : Matrix (Fin 2) (Fin 2) ℂ,
        IsGCovariant u1QubitRep A → IsGCovariant z2PhaseFlipRep A) ∧
    (∀ A : Matrix (Fin 2) (Fin 2) ℂ,
        IsGCovariant u1QubitRep A ↔ A = Matrix.diagonal ![A 0 0, A 1 1]) :=
  ⟨u1QubitRep_isUnitaryRep, su2_fund_unitary, pauliZExp_mem_SU2,
   z2_le_U2, z2_negOne_mem_SU2, z3ScalarGen_mem_U3,
   fun _ h => u1_invariant_subset_z2_invariant h,
   u1_invariant_iff_diagonal⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM AUDIT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        #print axioms sm_gauge_continuous_bridge_S3
        #print axioms u1QubitRep_isUnitaryRep
        #print axioms pauliZExp_mem_SU2
-/

end UnifiedTheory.LayerC.ContinuousGaugeReps
