/-
  LayerB/NoCloning.lean — The quantum no-cloning theorem

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  The standard quantum no-cloning theorem (Wootters–Zurek 1982,
  Dieks 1982), instantiated in the framework's amplitude vocabulary:

      There is no ℝ-linear map  T : (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ
      such that  T v = vecMulVec v v  for every single-particle state
      v : Fin n → ℝ,  whenever n ≥ 2.

  The standard QM proof:

    Take v = e₀ + e₁  (basis vectors in Fin n with n ≥ 2).
    By linearity of T:
        T (e₀ + e₁) = T e₀ + T e₁ = (e₀ ⊗ e₀) + (e₁ ⊗ e₁).
    By cloning at v:
        T (e₀ + e₁) = (e₀ + e₁) ⊗ (e₀ + e₁)
                    = (e₀ ⊗ e₀) + (e₀ ⊗ e₁) + (e₁ ⊗ e₀) + (e₁ ⊗ e₁).
    Equating component (0, 1):
        LHS = e₀ 0 · e₀ 1 + e₁ 0 · e₁ 1 = 1·0 + 0·1 = 0.
        RHS = (e₀+e₁) 0 · (e₀+e₁) 1 = 1·1 = 1.
    Hence 0 = 1.  Contradiction.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS FRAMEWORK-DERIVED VS STANDARD QM

  • Linearity of the amplitude space `Fin n → ℝ` and of the two-particle
    space `Matrix (Fin n) (Fin n) ℝ` is part of the framework
    (`MetricDefects.Perturbation`, `K_proj`, `P_proj` are linear maps
    in this same space).
  • The tensor-product map `vecMulVec` is the same one already used by
    `Entanglement.lean` and `QuantumEntanglement.lean` for separability.
  • Once we agree to take the cloner T as a *linear* map of these spaces,
    the proof is the standard QM argument — a corollary of linearity.

  The framework supplies the linear structure on amplitudes (this is the
  same linearity that gives the K/P projections in `MetricDefects.lean`);
  no-cloning is the standard textbook QM consequence.

  HONEST SCOPE.  This is *not* a "framework prediction" in the sense of
  novel content beyond standard QM.  It is the textbook no-cloning theorem
  expressed in the framework's amplitude vocabulary.  What the framework
  contributes is the *linearity* of the amplitude space (which is itself
  derived elsewhere in LayerA/LayerB); given that linearity, no-cloning
  follows in ~150 lines.

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.QuantumEntanglement
import Mathlib.Algebra.Module.LinearMap.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.NoCloning

open UnifiedTheory.LayerB.QuantumEntanglement
open UnifiedTheory.LayerB.Entanglement
open Matrix

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE CLONING PREDICATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A *cloning map* on the single-particle amplitude space `Fin n → ℝ`
    is a function `T` to the two-particle space such that, for every
    state `v`, the output equals the tensor product `v ⊗ v`.  The QM
    no-cloning theorem says no such *linear* T exists for n ≥ 2.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A function `T : (Fin n → ℝ) → TwoParticleState n` is a **cloning map**
    iff it sends every single-particle state `v` to the tensor product
    `v ⊗ v` (i.e., `vecMulVec v v`). -/
def IsCloningMap {n : ℕ} (T : (Fin n → ℝ) → TwoParticleState n) : Prop :=
  ∀ v : Fin n → ℝ, T v = Matrix.vecMulVec v v

/-- A `LinearMap` is a **linear cloning map** iff its underlying function
    is a cloning map. -/
def IsLinearCloningMap {n : ℕ}
    (T : (Fin n → ℝ) →ₗ[ℝ] TwoParticleState n) : Prop :=
  IsCloningMap (T : (Fin n → ℝ) → TwoParticleState n)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE TWO COMPUTATIONAL BASIS VECTORS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For n = m + 2 we have the two distinct indices 0 and 1.  We take
    the obvious basis-vector states
        e₀ = (1, 0, …, 0),     e₁ = (0, 1, 0, …, 0)
    and evaluate the cloning identity at v = e₀ + e₁.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The first computational basis state, `e₀ : Fin (m+2) → ℝ`, with
    `e₀ 0 = 1` and `e₀ i = 0` for `i ≠ 0`. -/
def basisE0 (m : ℕ) : Fin (m + 2) → ℝ := fun i => if i = 0 then 1 else 0

/-- The second computational basis state, `e₁ : Fin (m+2) → ℝ`, with
    `e₁ 1 = 1` and `e₁ i = 0` for `i ≠ 1`. -/
def basisE1 (m : ℕ) : Fin (m + 2) → ℝ := fun i => if i = 1 then 1 else 0

@[simp] theorem basisE0_zero (m : ℕ) : basisE0 m (0 : Fin (m + 2)) = 1 := by
  unfold basisE0; simp

@[simp] theorem basisE0_one (m : ℕ) : basisE0 m (1 : Fin (m + 2)) = 0 := by
  unfold basisE0
  have h : (1 : Fin (m + 2)) ≠ 0 := by
    intro h
    have : (1 : Fin (m + 2)).val = (0 : Fin (m + 2)).val := by rw [h]
    simp at this
  simp [h]

@[simp] theorem basisE1_zero (m : ℕ) : basisE1 m (0 : Fin (m + 2)) = 0 := by
  unfold basisE1
  have h : (0 : Fin (m + 2)) ≠ 1 := by
    intro h
    have : (0 : Fin (m + 2)).val = (1 : Fin (m + 2)).val := by rw [h]
    simp at this
  simp [h]

@[simp] theorem basisE1_one (m : ℕ) : basisE1 m (1 : Fin (m + 2)) = 1 := by
  unfold basisE1; simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: TWO TENSOR-PRODUCT EVALUATIONS AT (0, 1)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    These are the two halves of the contradiction:
      (3a) (e₀ ⊗ e₀)(0,1) + (e₁ ⊗ e₁)(0,1) = 0          (linearity side)
      (3b) ((e₀+e₁) ⊗ (e₀+e₁))(0,1)        = 1          (cloning side)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `(e₀ ⊗ e₀)(0, 1) = 0`. -/
theorem vecMulVec_e0_e0_at_01 (m : ℕ) :
    (Matrix.vecMulVec (basisE0 m) (basisE0 m))
        (0 : Fin (m + 2)) (1 : Fin (m + 2)) = 0 := by
  rw [Matrix.vecMulVec_apply, basisE0_zero, basisE0_one]
  ring

/-- `(e₁ ⊗ e₁)(0, 1) = 0`. -/
theorem vecMulVec_e1_e1_at_01 (m : ℕ) :
    (Matrix.vecMulVec (basisE1 m) (basisE1 m))
        (0 : Fin (m + 2)) (1 : Fin (m + 2)) = 0 := by
  rw [Matrix.vecMulVec_apply, basisE1_zero, basisE1_one]
  ring

/-- `((e₀ + e₁) ⊗ (e₀ + e₁))(0, 1) = 1`. -/
theorem vecMulVec_sum_at_01 (m : ℕ) :
    (Matrix.vecMulVec (basisE0 m + basisE1 m) (basisE0 m + basisE1 m))
        (0 : Fin (m + 2)) (1 : Fin (m + 2)) = 1 := by
  rw [Matrix.vecMulVec_apply]
  simp [Pi.add_apply]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE NO-CLONING THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Assume `T` is a *linear* map satisfying the cloning identity for
    every input.  Apply it to `e₀`, `e₁`, and `e₀ + e₁`.  Linearity
    forces `T (e₀ + e₁) = T e₀ + T e₁`; cloning forces it to equal
    `(e₀ + e₁) ⊗ (e₀ + e₁)`.  Reading off entry (0, 1) gives `0 = 1`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE QUANTUM NO-CLONING THEOREM (real-amplitude form).**

    There is no ℝ-linear map `T : (Fin (m+2) → ℝ) →ₗ[ℝ] Matrix (Fin (m+2)) (Fin (m+2)) ℝ`
    such that `T v = vecMulVec v v` for every `v`.  In framework
    vocabulary:  no linear cloner exists on the single-particle
    amplitude space, in any dimension `n = m + 2 ≥ 2`. -/
theorem no_cloning (m : ℕ)
    (T : (Fin (m + 2) → ℝ) →ₗ[ℝ] TwoParticleState (m + 2))
    (hClone : IsLinearCloningMap T) : False := by
  -- Cloning at the three states e₀, e₁, e₀ + e₁
  have hT_e0  : T (basisE0 m) = Matrix.vecMulVec (basisE0 m) (basisE0 m) :=
    hClone (basisE0 m)
  have hT_e1  : T (basisE1 m) = Matrix.vecMulVec (basisE1 m) (basisE1 m) :=
    hClone (basisE1 m)
  have hT_sum : T (basisE0 m + basisE1 m)
              = Matrix.vecMulVec (basisE0 m + basisE1 m) (basisE0 m + basisE1 m) :=
    hClone (basisE0 m + basisE1 m)
  -- Linearity: T (e₀ + e₁) = T e₀ + T e₁
  have hT_add : T (basisE0 m + basisE1 m) = T (basisE0 m) + T (basisE1 m) :=
    map_add T _ _
  -- Combine: (e₀+e₁)⊗(e₀+e₁) = e₀⊗e₀ + e₁⊗e₁ as matrices
  have hMat : Matrix.vecMulVec (basisE0 m + basisE1 m) (basisE0 m + basisE1 m)
            = Matrix.vecMulVec (basisE0 m) (basisE0 m)
              + Matrix.vecMulVec (basisE1 m) (basisE1 m) := by
    rw [← hT_sum, hT_add, hT_e0, hT_e1]
  -- Read off entry (0, 1)
  have hEntry := congr_fun (congr_fun hMat 0) 1
  -- LHS = 1 by `vecMulVec_sum_at_01`
  rw [vecMulVec_sum_at_01] at hEntry
  -- RHS = 0 + 0 = 0 by the two basis evaluations
  have hRHS :
      (Matrix.vecMulVec (basisE0 m) (basisE0 m)
        + Matrix.vecMulVec (basisE1 m) (basisE1 m))
        (0 : Fin (m + 2)) (1 : Fin (m + 2)) = 0 := by
    change (Matrix.vecMulVec (basisE0 m) (basisE0 m)) 0 1
         + (Matrix.vecMulVec (basisE1 m) (basisE1 m)) 0 1 = 0
    rw [vecMulVec_e0_e0_at_01, vecMulVec_e1_e1_at_01]
    ring
  rw [hRHS] at hEntry
  -- hEntry : (1 : ℝ) = 0
  exact one_ne_zero hEntry

/-- Restated existentially:  no linear cloner exists. -/
theorem no_linear_cloner_exists (m : ℕ) :
    ¬ ∃ T : (Fin (m + 2) → ℝ) →ₗ[ℝ] TwoParticleState (m + 2),
        IsLinearCloningMap T := by
  intro ⟨T, hT⟩
  exact no_cloning m T hT

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: CONNECTION TO THE FRAMEWORK'S K/P LINEARITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `MetricDefects.K_proj` and `P_proj` are linear maps on the same
    matrix amplitude space used here for two-particle states.  The
    no-cloning result depends only on linearity of `T`; that is the
    *same* algebraic structure (ℝ-linearity of amplitude maps) that
    underlies the K/P decomposition.  The corollary below states the
    no-cloning theorem as an obstruction in this same linear category:
    no linear K/P-style projection from one amplitude space to the
    two-particle amplitude space can clone.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Corollary: no linear amplitude-space map can implement cloning.**

    Re-statement of `no_cloning` emphasizing that the obstruction is
    purely about *linearity*, the same algebraic property that gives
    `K_proj`, `P_proj`, and the rest of the framework's amplitude
    machinery.  Given the framework's linear amplitude structure, the
    cloning map cannot be built. -/
theorem no_cloning_from_linearity (m : ℕ)
    (T : (Fin (m + 2) → ℝ) →ₗ[ℝ] TwoParticleState (m + 2)) :
    ¬ (∀ v : Fin (m + 2) → ℝ, T v = Matrix.vecMulVec v v) := by
  intro h
  exact no_cloning m T h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE QUANTUM NO-CLONING BUNDLE.**

    A self-contained statement of the no-cloning theorem in the
    framework's amplitude vocabulary, together with the contradiction
    pieces.  Concretely:

    (1) No linear cloner exists in any dimension `n = m + 2 ≥ 2`.

    (2) Equivalently, no linear `T` satisfies `T v = vecMulVec v v`
        for every `v`.

    (3) The two basis evaluations witnessing the obstruction:
        `(e₀ ⊗ e₀)(0,1) = 0`,  `(e₁ ⊗ e₁)(0,1) = 0`,
        but `((e₀+e₁) ⊗ (e₀+e₁))(0,1) = 1`.

    Honest scope: this is the textbook no-cloning theorem (Wootters–Zurek
    1982, Dieks 1982) over the framework's real-amplitude space.  The
    framework supplies the *linearity* of the amplitude space (the same
    linearity used by `K_proj`/`P_proj` in `MetricDefects.lean`); the
    impossibility result follows by the standard argument.  This is not
    a framework-specific prediction beyond standard QM. -/
theorem no_cloning_master :
    -- (1) No linear cloner exists.
    (∀ m : ℕ, ¬ ∃ T : (Fin (m + 2) → ℝ) →ₗ[ℝ] TwoParticleState (m + 2),
        IsLinearCloningMap T)
    -- (2) Equivalent direct statement.
    ∧ (∀ (m : ℕ)
          (T : (Fin (m + 2) → ℝ) →ₗ[ℝ] TwoParticleState (m + 2)),
          ¬ (∀ v : Fin (m + 2) → ℝ, T v = Matrix.vecMulVec v v))
    -- (3) Witness entries forcing the contradiction.
    ∧ (∀ m : ℕ,
          (Matrix.vecMulVec (basisE0 m) (basisE0 m))
              (0 : Fin (m + 2)) (1 : Fin (m + 2)) = 0
          ∧ (Matrix.vecMulVec (basisE1 m) (basisE1 m))
              (0 : Fin (m + 2)) (1 : Fin (m + 2)) = 0
          ∧ (Matrix.vecMulVec (basisE0 m + basisE1 m) (basisE0 m + basisE1 m))
              (0 : Fin (m + 2)) (1 : Fin (m + 2)) = 1) :=
  ⟨no_linear_cloner_exists,
   no_cloning_from_linearity,
   fun m => ⟨vecMulVec_e0_e0_at_01 m, vecMulVec_e1_e1_at_01 m, vecMulVec_sum_at_01 m⟩⟩

end UnifiedTheory.LayerB.NoCloning
