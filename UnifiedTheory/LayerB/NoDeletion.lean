/-
  LayerB/NoDeletion.lean — The quantum no-deletion theorem
  (Pati–Braunstein 2000).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  The standard quantum no-deletion theorem (Pati–Braunstein,
  Nature 404, 164 (2000)) — the dual of no-cloning — instantiated
  in the framework's amplitude vocabulary:

      There is no ℝ-linear map
          T : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ
      such that
          T (vecMulVec v v) = vecMulVec v e₀
      for every single-particle state v : Fin n → ℝ, whenever n ≥ 2.

  In words: there is no linear deletion map that, fed two copies of
  an arbitrary unknown amplitude `v`, returns one copy of `v` plus a
  fixed "blank" (ancilla) state `|0⟩`.  This is the dual statement
  to no-cloning: cloning forbids `|ψ⟩|0⟩ → |ψ⟩|ψ⟩` linearly,
  deletion forbids `|ψ⟩|ψ⟩ → |ψ⟩|0⟩` linearly.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE PATI–BRAUNSTEIN ARGUMENT (real-amplitude form)

  Set
      a := T (vecMulVec e₀ e₁),     b := T (vecMulVec e₁ e₀).
  Both are matrices.  Apply the deletion equation at v = e₀, e₁,
  e₀ + e₁, and e₀ + 2·e₁.

  At v = e₀:                T(e₀ ⊗ e₀) = e₀ ⊗ e₀.
  At v = e₁:                T(e₁ ⊗ e₁) = e₁ ⊗ e₀.
  At v = e₀ + e₁:           T(input₁) = (e₀ + e₁) ⊗ e₀ = e₀⊗e₀ + e₁⊗e₀,
      input₁ = e₀⊗e₀ + e₀⊗e₁ + e₁⊗e₀ + e₁⊗e₁,
      LHS = e₀⊗e₀ + a + b + e₁⊗e₀  (linearity + diagonal evals),
      ⟹  a + b = 0.                                        … (I)
  At v = e₀ + 2·e₁:          T(input₂) = (e₀ + 2e₁) ⊗ e₀
                                       = e₀⊗e₀ + 2·(e₁⊗e₀),
      input₂ = e₀⊗e₀ + 2·(e₀⊗e₁) + 2·(e₁⊗e₀) + 4·(e₁⊗e₁),
      LHS = e₀⊗e₀ + 2a + 2b + 4·(e₁⊗e₀),
      ⟹  2(a+b) + 4·(e₁⊗e₀) = 2·(e₁⊗e₀).
  Using (I):  4·(e₁⊗e₀) = 2·(e₁⊗e₀)  ⟹  2·(e₁⊗e₀) = 0.
  At entry (1, 0):  2·1·1 = 0,  contradiction.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS FRAMEWORK-DERIVED VS STANDARD QM

  • Linearity of the two-particle amplitude space
    `Matrix (Fin n) (Fin n) ℝ` is part of the framework
    (`MetricDefects.Perturbation`, `K_proj`, `P_proj`, and the
    same linearity already used by `NoCloning.lean`).
  • The tensor-product map `vecMulVec` is the same one used by
    `Entanglement.lean`, `QuantumEntanglement.lean`, and
    `NoCloning.lean`.
  • Once we agree to take the deletion map T as a *linear* map of
    these spaces, the proof is the standard QM argument — a
    corollary of linearity.

  HONEST SCOPE.  Real-amplitude version.  Full QM no-deletion
  uses unitary operations on the joint system + ancilla; here only
  linearity is used.  The framework supplies the linear structure
  (the same linearity that gives the K/P projections in
  `MetricDefects.lean`); given that linearity, no-deletion follows
  by the textbook Pati–Braunstein 2000 argument.

  Connection to no-cloning:  no-cloning and no-deletion are
  *dual* under input/output swap.  Cloning fails because the
  output `v ⊗ v` is *quadratic* in `v` while T must be linear;
  deletion fails because the input `v ⊗ v` is quadratic in `v`
  while T's image must respect linear superposition.  Both
  obstructions reduce to "you cannot linearize a quadratic"; here
  we expose the duality by sharing the basis-vector and
  tensor-evaluation infrastructure of `NoCloning.lean`.

  Zero `sorry`. Zero custom axioms.
-/
import UnifiedTheory.LayerB.NoCloning
import Mathlib.Algebra.Module.LinearMap.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.NoDeletion

open UnifiedTheory.LayerB.QuantumEntanglement
open UnifiedTheory.LayerB.Entanglement
open UnifiedTheory.LayerB.NoCloning
open Matrix

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE DELETION PREDICATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A *deletion map* on the two-particle amplitude space sends
    every diagonal state `v ⊗ v` to `v ⊗ |0⟩`, where `|0⟩` is the
    standard "blank ancilla" basis vector e₀.  The Pati–Braunstein
    no-deletion theorem says no such *linear* map exists for n ≥ 2.

    NB: T is a linear map on the FULL two-particle space; the
    deletion equation only constrains it on the diagonal subset
    `{ v ⊗ v : v }`.  The contradiction will come from evaluating
    that constraint at carefully chosen superpositions.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A function `T : TwoParticleState n → TwoParticleState n` is a
    **deletion map** iff it sends every diagonal two-particle state
    `v ⊗ v` (= `vecMulVec v v`) to `v ⊗ |0⟩` (= `vecMulVec v e₀`),
    where `|0⟩ = e₀` is the standard ancilla basis state. -/
def IsDeletionMap {m : ℕ} (T : TwoParticleState (m + 2) → TwoParticleState (m + 2)) :
    Prop :=
  ∀ v : Fin (m + 2) → ℝ, T (Matrix.vecMulVec v v) = Matrix.vecMulVec v (basisE0 m)

/-- A `LinearMap` is a **linear deletion map** iff its underlying
    function is a deletion map. -/
def IsLinearDeletionMap {m : ℕ}
    (T : TwoParticleState (m + 2) →ₗ[ℝ] TwoParticleState (m + 2)) : Prop :=
  IsDeletionMap (T : TwoParticleState (m + 2) → TwoParticleState (m + 2))

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: TENSOR-PRODUCT EXPANSIONS OF THE TEST INPUTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Pati–Braunstein argument needs algebraic expansions of
    `vecMulVec (e₀ + k·e₁) (e₀ + k·e₁)` for k = 1, 2, broken into
    the four basis tensors.  We prove these as direct matrix
    identities; once these are in place, the no-deletion proof is
    purely linear-algebraic.

    Notation throughout (with v_k := e₀ + k·e₁):
        v_k ⊗ v_k = e₀⊗e₀ + k·(e₀⊗e₁) + k·(e₁⊗e₀) + k²·(e₁⊗e₁).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The bilinearity expansion of `vecMulVec (e₀ + e₁) (e₀ + e₁)`. -/
theorem vecMulVec_e0_plus_e1_self (m : ℕ) :
    Matrix.vecMulVec (basisE0 m + basisE1 m) (basisE0 m + basisE1 m)
      = Matrix.vecMulVec (basisE0 m) (basisE0 m)
        + Matrix.vecMulVec (basisE0 m) (basisE1 m)
        + Matrix.vecMulVec (basisE1 m) (basisE0 m)
        + Matrix.vecMulVec (basisE1 m) (basisE1 m) := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.add_apply, Matrix.add_apply]
  ring

/-- The bilinearity expansion of `vecMulVec (e₀ + 2·e₁) (e₀ + 2·e₁)`. -/
theorem vecMulVec_e0_plus_2e1_self (m : ℕ) :
    Matrix.vecMulVec (basisE0 m + (2 : ℝ) • basisE1 m)
                     (basisE0 m + (2 : ℝ) • basisE1 m)
      = Matrix.vecMulVec (basisE0 m) (basisE0 m)
        + (2 : ℝ) • Matrix.vecMulVec (basisE0 m) (basisE1 m)
        + (2 : ℝ) • Matrix.vecMulVec (basisE1 m) (basisE0 m)
        + (4 : ℝ) • Matrix.vecMulVec (basisE1 m) (basisE1 m) := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.add_apply, Pi.smul_apply,
             Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The right-hand-side expansion: `vecMulVec (e₀ + e₁) e₀ = e₀⊗e₀ + e₁⊗e₀`. -/
theorem vecMulVec_e0_plus_e1_e0 (m : ℕ) :
    Matrix.vecMulVec (basisE0 m + basisE1 m) (basisE0 m)
      = Matrix.vecMulVec (basisE0 m) (basisE0 m)
        + Matrix.vecMulVec (basisE1 m) (basisE0 m) := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.add_apply, Matrix.add_apply]
  ring

/-- The right-hand-side expansion: `vecMulVec (e₀ + 2·e₁) e₀
        = e₀⊗e₀ + 2·(e₁⊗e₀)`. -/
theorem vecMulVec_e0_plus_2e1_e0 (m : ℕ) :
    Matrix.vecMulVec (basisE0 m + (2 : ℝ) • basisE1 m) (basisE0 m)
      = Matrix.vecMulVec (basisE0 m) (basisE0 m)
        + (2 : ℝ) • Matrix.vecMulVec (basisE1 m) (basisE0 m) := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.add_apply, Pi.smul_apply,
             Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: BASIS TENSOR EVALUATIONS AT (1, 0)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We will read the contradiction off entry (1, 0).  We need the
    five entry evaluations:
        (e₀⊗e₀)(1,0) = 0     (e₀⊗e₁)(1,0) = 0     (e₁⊗e₀)(1,0) = 1
        (e₁⊗e₁)(1,0) = 0
    These let us turn the matrix equation `4·(e₁⊗e₀) = 2·(e₁⊗e₀)`
    into the scalar equation `4 = 2`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `(e₀ ⊗ e₀)(1, 0) = 0`. -/
theorem vecMulVec_e0_e0_at_10 (m : ℕ) :
    (Matrix.vecMulVec (basisE0 m) (basisE0 m))
        (1 : Fin (m + 2)) (0 : Fin (m + 2)) = 0 := by
  rw [Matrix.vecMulVec_apply, basisE0_one, basisE0_zero]; ring

/-- `(e₀ ⊗ e₁)(1, 0) = 0`. -/
theorem vecMulVec_e0_e1_at_10 (m : ℕ) :
    (Matrix.vecMulVec (basisE0 m) (basisE1 m))
        (1 : Fin (m + 2)) (0 : Fin (m + 2)) = 0 := by
  rw [Matrix.vecMulVec_apply, basisE0_one, basisE1_zero]; ring

/-- `(e₁ ⊗ e₀)(1, 0) = 1`. -/
theorem vecMulVec_e1_e0_at_10 (m : ℕ) :
    (Matrix.vecMulVec (basisE1 m) (basisE0 m))
        (1 : Fin (m + 2)) (0 : Fin (m + 2)) = 1 := by
  rw [Matrix.vecMulVec_apply, basisE1_one, basisE0_zero]; ring

/-- `(e₁ ⊗ e₁)(1, 0) = 0`. -/
theorem vecMulVec_e1_e1_at_10 (m : ℕ) :
    (Matrix.vecMulVec (basisE1 m) (basisE1 m))
        (1 : Fin (m + 2)) (0 : Fin (m + 2)) = 0 := by
  rw [Matrix.vecMulVec_apply, basisE1_one, basisE1_zero]; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE NO-DELETION THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Combine the four deletion evaluations (at e₀, e₁, e₀+e₁,
    e₀+2·e₁) with linearity of T to derive
        2·(e₁ ⊗ e₀) = 0 (as a matrix equation),
    then read off entry (1, 0) for the scalar contradiction
    `2 = 0`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE QUANTUM NO-DELETION THEOREM (real-amplitude form).**
    Pati–Braunstein 2000.

    There is no ℝ-linear map
        T : TwoParticleState (m+2) →ₗ[ℝ] TwoParticleState (m+2)
    such that  T (vecMulVec v v) = vecMulVec v e₀  for every
    single-particle state `v : Fin (m+2) → ℝ`, in any dimension
    `n = m + 2 ≥ 2`. -/
theorem no_deletion (m : ℕ)
    (T : TwoParticleState (m + 2) →ₗ[ℝ] TwoParticleState (m + 2))
    (hDel : IsLinearDeletionMap T) : False := by
  -- Diagonal deletion values
  have hT_e0 :
      T (Matrix.vecMulVec (basisE0 m) (basisE0 m))
        = Matrix.vecMulVec (basisE0 m) (basisE0 m) := hDel (basisE0 m)
  have hT_e1 :
      T (Matrix.vecMulVec (basisE1 m) (basisE1 m))
        = Matrix.vecMulVec (basisE1 m) (basisE0 m) := hDel (basisE1 m)
  -- Deletion at v = e₀ + e₁
  have hT_v1 :
      T (Matrix.vecMulVec (basisE0 m + basisE1 m) (basisE0 m + basisE1 m))
        = Matrix.vecMulVec (basisE0 m + basisE1 m) (basisE0 m) :=
    hDel (basisE0 m + basisE1 m)
  -- Deletion at v = e₀ + 2·e₁
  have hT_v2 :
      T (Matrix.vecMulVec (basisE0 m + (2 : ℝ) • basisE1 m)
                          (basisE0 m + (2 : ℝ) • basisE1 m))
        = Matrix.vecMulVec (basisE0 m + (2 : ℝ) • basisE1 m) (basisE0 m) :=
    hDel (basisE0 m + (2 : ℝ) • basisE1 m)
  -- Apply T's linearity to expand T (sum) into a sum of T's
  have hT_v1_lin :
      T (Matrix.vecMulVec (basisE0 m) (basisE0 m))
        + T (Matrix.vecMulVec (basisE0 m) (basisE1 m))
        + T (Matrix.vecMulVec (basisE1 m) (basisE0 m))
        + T (Matrix.vecMulVec (basisE1 m) (basisE1 m))
        = Matrix.vecMulVec (basisE0 m) (basisE0 m)
          + Matrix.vecMulVec (basisE1 m) (basisE0 m) := by
    -- LHS = T (sum of four) by linearity
    have hLHS :
        T (Matrix.vecMulVec (basisE0 m) (basisE0 m))
          + T (Matrix.vecMulVec (basisE0 m) (basisE1 m))
          + T (Matrix.vecMulVec (basisE1 m) (basisE0 m))
          + T (Matrix.vecMulVec (basisE1 m) (basisE1 m))
        = T (Matrix.vecMulVec (basisE0 m) (basisE0 m)
              + Matrix.vecMulVec (basisE0 m) (basisE1 m)
              + Matrix.vecMulVec (basisE1 m) (basisE0 m)
              + Matrix.vecMulVec (basisE1 m) (basisE1 m)) := by
      simp [LinearMap.map_add]
    rw [hLHS, ← vecMulVec_e0_plus_e1_self, hT_v1, vecMulVec_e0_plus_e1_e0]
  have hT_v2_lin :
      T (Matrix.vecMulVec (basisE0 m) (basisE0 m))
        + (2 : ℝ) • T (Matrix.vecMulVec (basisE0 m) (basisE1 m))
        + (2 : ℝ) • T (Matrix.vecMulVec (basisE1 m) (basisE0 m))
        + (4 : ℝ) • T (Matrix.vecMulVec (basisE1 m) (basisE1 m))
        = Matrix.vecMulVec (basisE0 m) (basisE0 m)
          + (2 : ℝ) • Matrix.vecMulVec (basisE1 m) (basisE0 m) := by
    have hLHS :
        T (Matrix.vecMulVec (basisE0 m) (basisE0 m))
          + (2 : ℝ) • T (Matrix.vecMulVec (basisE0 m) (basisE1 m))
          + (2 : ℝ) • T (Matrix.vecMulVec (basisE1 m) (basisE0 m))
          + (4 : ℝ) • T (Matrix.vecMulVec (basisE1 m) (basisE1 m))
        = T (Matrix.vecMulVec (basisE0 m) (basisE0 m)
              + (2 : ℝ) • Matrix.vecMulVec (basisE0 m) (basisE1 m)
              + (2 : ℝ) • Matrix.vecMulVec (basisE1 m) (basisE0 m)
              + (4 : ℝ) • Matrix.vecMulVec (basisE1 m) (basisE1 m)) := by
      simp [LinearMap.map_add]
    rw [hLHS, ← vecMulVec_e0_plus_2e1_self, hT_v2, vecMulVec_e0_plus_2e1_e0]
  -- Substitute the diagonal deletion values into both equations
  rw [hT_e0, hT_e1] at hT_v1_lin hT_v2_lin
  -- Read off entry (1, 0) of both equations to obtain the scalar relations
  have hE1 := congr_fun (congr_fun hT_v1_lin 1) 0
  have hE2 := congr_fun (congr_fun hT_v2_lin 1) 0
  -- Abbreviate the "T(off-diagonal)" entries at (1, 0)
  set α : ℝ := (T (Matrix.vecMulVec (basisE0 m) (basisE1 m))) 1 0
    with hα_def
  set β : ℝ := (T (Matrix.vecMulVec (basisE1 m) (basisE0 m))) 1 0
    with hβ_def
  -- Simplify hE1 to:  α + β = 0
  have hE1' : α + β = 0 := by
    have := hE1
    -- LHS: (e₀⊗e₀)(1,0) + α + β + (e₁⊗e₀)(1,0) = (e₀⊗e₀)(1,0) + (e₁⊗e₀)(1,0)
    simp only [Matrix.add_apply, vecMulVec_e0_e0_at_10, vecMulVec_e1_e0_at_10,
               ← hα_def, ← hβ_def] at this
    linarith
  -- Simplify hE2 to:  2α + 2β + 4·(e₁⊗e₀)(1,0) = 2·(e₁⊗e₀)(1,0)
  -- i.e.  2α + 2β + 4 = 2.
  have hE2' : (2 : ℝ) * α + (2 : ℝ) * β + 4 = 2 := by
    have := hE2
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
               vecMulVec_e0_e0_at_10, vecMulVec_e1_e0_at_10,
               ← hα_def, ← hβ_def] at this
    linarith
  -- Contradiction: from hE1' (α + β = 0) and hE2' we get 4 = 2.
  have : (4 : ℝ) = 2 := by linarith
  norm_num at this

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: NO LINEAR DELETER EXISTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Restated existentially:  no linear deleter exists, in any
    dimension `n = m + 2 ≥ 2`. -/
theorem no_linear_deleter_exists (m : ℕ) :
    ¬ ∃ T : TwoParticleState (m + 2) →ₗ[ℝ] TwoParticleState (m + 2),
        IsLinearDeletionMap T := by
  intro ⟨T, hT⟩
  exact no_deletion m T hT

/-- **Corollary: no linear amplitude-space map can implement deletion.**

    Re-statement of `no_deletion` emphasizing that the obstruction
    is purely about *linearity*, the same algebraic property that
    gives `K_proj`, `P_proj`, and the rest of the framework's
    amplitude machinery.  Given the framework's linear amplitude
    structure, no deletion map can be built. -/
theorem no_deletion_from_linearity (m : ℕ)
    (T : TwoParticleState (m + 2) →ₗ[ℝ] TwoParticleState (m + 2)) :
    ¬ (∀ v : Fin (m + 2) → ℝ,
        T (Matrix.vecMulVec v v) = Matrix.vecMulVec v (basisE0 m)) := by
  intro h
  exact no_deletion m T h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: CLONING / DELETION DUALITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    No-cloning forbids a linear `(Fin n → ℝ) →ₗ[ℝ] H ⊗ H` sending
    v ↦ v ⊗ v.  No-deletion forbids a linear `H ⊗ H →ₗ[ℝ] H ⊗ H`
    sending v ⊗ v ↦ v ⊗ |0⟩.  The two are dual under the swap of
    domain and codomain on the diagonal `{ v ⊗ v }`.  Both follow
    from the same algebraic fact:  the map  `v ↦ v ⊗ v`  is
    *quadratic* in v and cannot be matched by a linear map on
    either side.

    The bridge below records that BOTH no-go theorems hold in the
    framework's amplitude vocabulary, with a shared dimension
    parameter `m : ℕ` (so `n = m + 2 ≥ 2`).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Cloning–deletion duality bundle.**  In any dimension
    `n = m + 2 ≥ 2`:

    (1) No linear cloning map exists   (`no_linear_cloner_exists`).
    (2) No linear deletion map exists  (`no_linear_deleter_exists`).
    (3) Both follow from the same linearity-vs-quadratic-tensor
        obstruction. -/
theorem cloning_deletion_duality (m : ℕ) :
    (¬ ∃ T : (Fin (m + 2) → ℝ) →ₗ[ℝ] TwoParticleState (m + 2),
        IsLinearCloningMap T)
    ∧ (¬ ∃ T : TwoParticleState (m + 2) →ₗ[ℝ] TwoParticleState (m + 2),
        IsLinearDeletionMap T) :=
  ⟨no_linear_cloner_exists m, no_linear_deleter_exists m⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE QUANTUM NO-DELETION BUNDLE.**

    A self-contained statement of the no-deletion theorem in the
    framework's amplitude vocabulary, together with the contradiction
    pieces and the cloning-duality bridge.  Concretely:

    (1) No linear deletion map exists in any dimension `n = m+2 ≥ 2`.

    (2) Equivalently, no linear `T` satisfies
        `T (vecMulVec v v) = vecMulVec v e₀` for every `v`.

    (3) The four basis evaluations witnessing the obstruction at
        entry (1, 0):
            (e₀⊗e₀)(1,0) = 0,  (e₀⊗e₁)(1,0) = 0,
            (e₁⊗e₀)(1,0) = 1,  (e₁⊗e₁)(1,0) = 0.

    (4) Cloning–deletion duality:  BOTH no-cloning AND no-deletion
        hold, each as a corollary of linearity of the amplitude
        space.

    Honest scope:  this is the textbook Pati–Braunstein 2000
    no-deletion theorem over the framework's real-amplitude space.
    The framework supplies the *linearity* of the amplitude space
    (the same linearity used by `K_proj`/`P_proj` in
    `MetricDefects.lean`); the impossibility result follows by
    the standard argument.  Full QM no-deletion uses unitary
    operations on the joint system + ancilla; here only linearity
    is used. -/
theorem no_deletion_master :
    -- (1) No linear deleter exists in every dimension n ≥ 2.
    (∀ m : ℕ, ¬ ∃ T : TwoParticleState (m + 2) →ₗ[ℝ] TwoParticleState (m + 2),
        IsLinearDeletionMap T)
    -- (2) Equivalent direct statement.
    ∧ (∀ (m : ℕ)
          (T : TwoParticleState (m + 2) →ₗ[ℝ] TwoParticleState (m + 2)),
          ¬ (∀ v : Fin (m + 2) → ℝ,
              T (Matrix.vecMulVec v v) = Matrix.vecMulVec v (basisE0 m)))
    -- (3) Witness entries forcing the contradiction at (1, 0).
    ∧ (∀ m : ℕ,
          (Matrix.vecMulVec (basisE0 m) (basisE0 m))
              (1 : Fin (m + 2)) (0 : Fin (m + 2)) = 0
          ∧ (Matrix.vecMulVec (basisE0 m) (basisE1 m))
              (1 : Fin (m + 2)) (0 : Fin (m + 2)) = 0
          ∧ (Matrix.vecMulVec (basisE1 m) (basisE0 m))
              (1 : Fin (m + 2)) (0 : Fin (m + 2)) = 1
          ∧ (Matrix.vecMulVec (basisE1 m) (basisE1 m))
              (1 : Fin (m + 2)) (0 : Fin (m + 2)) = 0)
    -- (4) Cloning–deletion duality:  both no-go theorems hold.
    ∧ (∀ m : ℕ,
          (¬ ∃ T : (Fin (m + 2) → ℝ) →ₗ[ℝ] TwoParticleState (m + 2),
              IsLinearCloningMap T)
          ∧ (¬ ∃ T : TwoParticleState (m + 2) →ₗ[ℝ] TwoParticleState (m + 2),
              IsLinearDeletionMap T)) :=
  ⟨no_linear_deleter_exists,
   no_deletion_from_linearity,
   fun m => ⟨vecMulVec_e0_e0_at_10 m, vecMulVec_e0_e1_at_10 m,
             vecMulVec_e1_e0_at_10 m, vecMulVec_e1_e1_at_10 m⟩,
   cloning_deletion_duality⟩

end UnifiedTheory.LayerB.NoDeletion
