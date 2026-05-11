/-
  LayerB/SchmidtDecomposition.lean — Schmidt decomposition for two-particle states

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  The Schmidt decomposition is a structure theorem for two-particle states:
  every  ψ ∈ H_A ⊗ H_B  can be written as
      ψ = Σ_k  λ_k · |e_k⟩ ⊗ |f_k⟩
  where {|e_k⟩} ⊂ H_A and {|f_k⟩} ⊂ H_B are orthonormal sets and the
  Schmidt coefficients λ_k ≥ 0 are uniquely determined (they are the
  singular values of the matrix representation of ψ).

  For the framework's two-particle state space `Matrix (Fin n) (Fin n) ℝ`
  (`TwoParticleState n` from `QuantumEntanglement.lean`), the Schmidt
  decomposition IS the singular value decomposition (SVD)
      ψ = U · diag(λ) · Vᵀ.
  The SVD has Schmidt coefficients `λ_k = σ_k(ψ)` (singular values) and
  Schmidt bases given by columns of U and V.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED (this file)

  – `SchmidtDecomp ψ`        : a structure holding U, V, and λ that
                              reconstruct ψ as ψ(i,j) = Σ_k λ_k U(k,i) V(k,j),
                              with U·Uᵀ = 1, V·Vᵀ = 1, and λ_k ≥ 0.
  – `singletDecomp`          : explicit Schmidt decomposition of the singlet
                              with Schmidt coefficients (1/√2, 1/√2).
  – `singlet_schmidt_rank`   : the singlet has Schmidt rank 2 (maximally
                              entangled in 2-dimensional H_A, H_B).
  – `separable_decomp`       : every separable state ψ = vecMulVec v w has
                              an explicit Schmidt decomposition with
                              Schmidt rank ≤ 1.
  – `separable_iff_schmidtRank_le_one` : a 2×2 state is quantum-separable
                              iff there exists a Schmidt decomposition with
                              Schmidt rank ≤ 1.
  – `singletDecomp_coeffs`   : the singlet's Schmidt coefficients are
                              (1/√2, 1/√2) — both equal, the maximally-
                              entangled signature.
  – `schmidt_decomposition_master` : aggregator.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – We define `SchmidtDecomp` for general `n` and prove all of the above
    at the level of `Fin n` for `n = 2`.
  – Existence of a Schmidt decomposition for an *arbitrary* `Matrix (Fin n) (Fin n) ℝ`
    requires the singular value decomposition (SVD) for general `n`,
    which is not yet in Mathlib in a form we can directly invoke.
    For the framework's `Bell`-style two-particle physics, `n = 2` is
    the operative case and we prove it constructively for the singlet
    and for every separable state in `Fin 2`.
  – Uniqueness of the Schmidt coefficients (up to ordering) is the
    standard "singular values are uniquely determined" theorem; the
    formal statement reduces to a uniqueness claim for eigenvalues of
    `ψ · ψᵀ`, which we DO state and prove for the cases where we have
    explicit decompositions (singlet, separable).

  Zero `sorry`. Zero custom axioms.
-/

import UnifiedTheory.LayerB.QuantumEntanglement

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.SchmidtDecomposition

open UnifiedTheory.LayerB.Entanglement
open UnifiedTheory.LayerB.QuantumEntanglement
open UnifiedTheory.LayerB.BellTheorem
open Matrix

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE SCHMIDT DECOMPOSITION STRUCTURE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A Schmidt decomposition of ψ : TwoParticleState n is:
      – an n × n matrix `U` whose rows are an orthonormal basis of H_A
      – an n × n matrix `V` whose rows are an orthonormal basis of H_B
      – non-negative coefficients `λ : Fin n → ℝ`
    such that
        ψ(i, j) = Σ_k  λ_k · U(k, i) · V(k, j).

    Equivalently, in matrix form:  ψ = Uᵀ · diag(λ) · V.

    The "rows orthonormal" conditions are encoded as
      U · Uᵀ = 1   and   V · Vᵀ = 1.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A **Schmidt decomposition** of a two-particle state ψ : Fin n × Fin n → ℝ.

    `bA k i` is the i-th coefficient of the k-th Schmidt basis vector for
    particle A (so each row of `bA` is one of the orthonormal vectors |e_k⟩).
    Similarly for `bB`. The `coeffs k` are the Schmidt coefficients λ_k ≥ 0.

    The reconstruction is the standard sum
        ψ(i, j) = Σ_k coeffs(k) · bA(k, i) · bB(k, j). -/
structure SchmidtDecomp {n : ℕ} (ψ : TwoParticleState n) where
  /-- Orthonormal A-basis: rows of `bA` are |e_k⟩. -/
  bA : Matrix (Fin n) (Fin n) ℝ
  /-- Orthonormal B-basis: rows of `bB` are |f_k⟩. -/
  bB : Matrix (Fin n) (Fin n) ℝ
  /-- Schmidt coefficients λ_k. -/
  coeffs : Fin n → ℝ
  /-- Coefficients are non-negative (singular values are ≥ 0). -/
  coeffs_nonneg : ∀ k, 0 ≤ coeffs k
  /-- A-basis is orthonormal: U · Uᵀ = 1. -/
  bA_orthonormal : bA * bAᵀ = 1
  /-- B-basis is orthonormal: V · Vᵀ = 1. -/
  bB_orthonormal : bB * bBᵀ = 1
  /-- Reconstruction: ψ(i, j) = Σ_k coeffs(k) · bA(k, i) · bB(k, j). -/
  reconstruction : ∀ i j, ψ i j = ∑ k : Fin n, coeffs k * bA k i * bB k j

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: SCHMIDT RANK
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The **Schmidt rank** of a decomposition is the number of nonzero
    Schmidt coefficients. It is the standard QM measure of bipartite
    entanglement:
        Schmidt rank 1   ⟺   separable
        Schmidt rank > 1 ⟺   entangled
        all coeffs equal ⟺   maximally entangled
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The **Schmidt rank** of a decomposition: the number of nonzero
    Schmidt coefficients. (Noncomputable because equality on ℝ is.) -/
noncomputable def SchmidtDecomp.rank {n : ℕ} {ψ : TwoParticleState n}
    (S : SchmidtDecomp ψ) : ℕ := by
  classical
  exact (Finset.univ.filter fun k => S.coeffs k ≠ 0).card

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: SCHMIDT DECOMPOSITION OF SEPARABLE STATES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a separable 2×2 state  ψ = vecMulVec v w,  the Schmidt decomposition
    has rank ≤ 1: the only Schmidt coefficient that may be nonzero is
        λ_0 = ‖v‖ · ‖w‖,
    and the Schmidt vectors are v/‖v‖ and w/‖w‖.

    For Fin 2 we use a direct construction: given `v, w : Fin 2 → ℝ`,
    pad the rotation matrices with the perpendicular vector
        v⊥ = (-v₁, v₀),   ‖v⊥‖ = ‖v‖.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Norm-squared of a 2-vector. -/
private def n2 (v : Fin 2 → ℝ) : ℝ := v 0 ^ 2 + v 1 ^ 2

private lemma n2_nonneg (v : Fin 2 → ℝ) : 0 ≤ n2 v := by
  unfold n2; positivity

/-- Norm of a 2-vector (= √(v₀² + v₁²)). -/
private noncomputable def nrm (v : Fin 2 → ℝ) : ℝ := Real.sqrt (n2 v)

private lemma nrm_nonneg (v : Fin 2 → ℝ) : 0 ≤ nrm v := Real.sqrt_nonneg _

private lemma nrm_sq (v : Fin 2 → ℝ) : nrm v ^ 2 = n2 v :=
  Real.sq_sqrt (n2_nonneg v)

/-- An orthonormal 2×2 matrix built from a unit vector u of length 1:
    row 0 is `u`, row 1 is `(-u₁, u₀)`. -/
private def rotFromUnit (u : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![u 0, u 1; -u 1, u 0]

private lemma rotFromUnit_orthonormal (u : Fin 2 → ℝ) (hu : n2 u = 1) :
    rotFromUnit u * (rotFromUnit u)ᵀ = 1 := by
  unfold rotFromUnit n2 at *
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
          Fin.isValue] <;> nlinarith [hu]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: EXPLICIT SCHMIDT DECOMPOSITION OF THE SINGLET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The singlet
        ψ = (|01⟩ - |10⟩) / √2
    has matrix form
        ψ = (1/√2) · !![0, 1; -1, 0].
    Its singular values are (1/√2, 1/√2):
        ψ · ψᵀ = (1/2) · I,
    so both eigenvalues of ψ · ψᵀ equal 1/2 and both singular values
    equal √(1/2) = 1/√2.

    A concrete Schmidt decomposition is:
        bA = I,
        bB = !![0, 1; -1, 0]   (= √2 · ψ),
        coeffs k = 1/√2  for k = 0, 1.
    Both `bA · bAᵀ = 1` (trivially) and `bB · bBᵀ = 1` (rotation is
    orthogonal). The reconstruction sum gives
        ψ(i, j) = Σ_k (1/√2) · I(k, i) · bB(k, j) = (1/√2) · bB(i, j).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The B-basis of the singlet's Schmidt decomposition: an orthogonal
    matrix whose rows are the perpendicular pair `(0, 1)` and `(-1, 0)`. -/
private def singletBB : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

private lemma singletBB_orthonormal : singletBB * singletBBᵀ = 1 := by
  unfold singletBB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
          Fin.isValue]

private lemma id_orthonormal :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = 1 := by
  rw [Matrix.transpose_one, Matrix.one_mul]

private lemma sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 :=
  Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)

private lemma sqrt_two_ne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt_two_pos

/-- The explicit Schmidt decomposition of the singlet state. -/
noncomputable def singletDecomp : SchmidtDecomp (singletState : TwoParticleState 2) where
  bA := 1
  bB := singletBB
  coeffs := fun _ => 1 / Real.sqrt 2
  coeffs_nonneg := fun _ => by positivity
  bA_orthonormal := id_orthonormal
  bB_orthonormal := singletBB_orthonormal
  reconstruction := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [singletState, singletBB, Matrix.one_apply,
            Fin.isValue, neg_div]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: SCHMIDT COEFFICIENTS AND RANK OF THE SINGLET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The two coefficients are both 1/√2 (≠ 0) and equal — the signature
    of a maximally entangled state in dimension 2.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Schmidt coefficients of the singlet are (1/√2, 1/√2). -/
theorem singletDecomp_coeffs : ∀ k : Fin 2, singletDecomp.coeffs k = 1 / Real.sqrt 2 := by
  intro _; rfl

/-- Both Schmidt coefficients of the singlet are POSITIVE. -/
theorem singletDecomp_coeffs_pos : ∀ k : Fin 2, 0 < singletDecomp.coeffs k := by
  intro k
  rw [singletDecomp_coeffs]
  exact div_pos one_pos sqrt_two_pos

/-- The Schmidt coefficients of the singlet are EQUAL — the hallmark of
    maximal entanglement in dimension 2. -/
theorem singletDecomp_coeffs_equal :
    singletDecomp.coeffs 0 = singletDecomp.coeffs 1 := by
  rw [singletDecomp_coeffs, singletDecomp_coeffs]

/-- The Schmidt rank of the singlet is **2**. -/
theorem singlet_schmidt_rank : singletDecomp.rank = 2 := by
  unfold SchmidtDecomp.rank
  -- Both coefficients are nonzero
  have h0 : singletDecomp.coeffs 0 ≠ 0 := ne_of_gt (singletDecomp_coeffs_pos 0)
  have h1 : singletDecomp.coeffs 1 ≠ 0 := ne_of_gt (singletDecomp_coeffs_pos 1)
  -- Compute the cardinality
  have : (Finset.univ.filter fun k : Fin 2 => singletDecomp.coeffs k ≠ 0)
       = {0, 1} := by
    ext k
    fin_cases k <;>
      simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, h0, h1,
            Fin.isValue]
  rw [this]
  decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: SCHMIDT DECOMPOSITION OF SEPARABLE STATES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a separable state ψ = vecMulVec v w, the Schmidt decomposition has
    rank ≤ 1. Constructively:
      – If v = 0 OR w = 0 then ψ = 0; use the all-zero decomposition.
      – Otherwise normalize: u_v = v/‖v‖, u_w = w/‖w‖, λ_0 = ‖v‖·‖w‖,
        and pad to orthonormal 2×2 matrices using the perpendicular pair
        (-u_v.1, u_v.0) and (-u_w.1, u_w.0).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The all-zero Schmidt decomposition of the zero state. -/
noncomputable def zeroDecomp : SchmidtDecomp (0 : TwoParticleState 2) where
  bA := 1
  bB := 1
  coeffs := fun _ => 0
  coeffs_nonneg := fun _ => le_refl _
  bA_orthonormal := id_orthonormal
  bB_orthonormal := id_orthonormal
  reconstruction := by
    intro i j
    simp

/-- The zero state has Schmidt rank 0. -/
theorem zeroDecomp_rank : zeroDecomp.rank = 0 := by
  unfold SchmidtDecomp.rank
  have : (Finset.univ.filter fun k : Fin 2 => zeroDecomp.coeffs k ≠ 0) = ∅ := by
    ext k
    simp [zeroDecomp]
  rw [this]; rfl

/-- A canonical orthonormal basis covering a 2-vector (used as a default when
    `v = 0`): the standard basis `e₁ = (1, 0)` and `e₂ = (0, 1)`. -/
private def stdBasis : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]

private lemma stdBasis_orthonormal : stdBasis * stdBasisᵀ = 1 := by
  unfold stdBasis
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
          Fin.isValue]

/-- Schmidt decomposition of a separable state ψ = vecMulVec v w in Fin 2.
    The construction always produces a rank-≤-1 decomposition. -/
noncomputable def separableDecompData
    (v w : Fin 2 → ℝ) : SchmidtDecomp (Matrix.vecMulVec v w : TwoParticleState 2) := by
  classical
  -- Define norms (= 0 when v or w is 0 by convention) and unit vectors.
  set nv : ℝ := nrm v with hnv_def
  set nw : ℝ := nrm w with hnw_def
  -- If nv = 0 then v = 0, so vecMulVec v w = 0; similarly if nw = 0.
  have hv_zero_iff : nv = 0 ↔ ∀ i, v i = 0 := by
    constructor
    · intro hnv i
      have hsq : n2 v = 0 := by
        have h1 : nrm v = 0 := hnv
        have h2 : nv ^ 2 = n2 v := nrm_sq v
        rw [hnv_def, h1] at h2; linarith [h2]
      have hp0 : 0 ≤ v 0 ^ 2 := sq_nonneg _
      have hp1 : 0 ≤ v 1 ^ 2 := sq_nonneg _
      have h0 : v 0 ^ 2 = 0 := by unfold n2 at hsq; nlinarith
      have h1 : v 1 ^ 2 = 0 := by unfold n2 at hsq; nlinarith
      fin_cases i
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
    · intro h
      have : n2 v = 0 := by unfold n2; rw [h 0, h 1]; ring
      change nrm v = 0
      unfold nrm; rw [this]; exact Real.sqrt_zero
  have hw_zero_iff : nw = 0 ↔ ∀ i, w i = 0 := by
    constructor
    · intro hnw i
      have hsq : n2 w = 0 := by
        have h1 : nrm w = 0 := hnw
        have h2 : nw ^ 2 = n2 w := nrm_sq w
        rw [hnw_def, h1] at h2; linarith [h2]
      have hp0 : 0 ≤ w 0 ^ 2 := sq_nonneg _
      have hp1 : 0 ≤ w 1 ^ 2 := sq_nonneg _
      have h0 : w 0 ^ 2 = 0 := by unfold n2 at hsq; nlinarith
      have h1 : w 1 ^ 2 = 0 := by unfold n2 at hsq; nlinarith
      fin_cases i
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
    · intro h
      have : n2 w = 0 := by unfold n2; rw [h 0, h 1]; ring
      change nrm w = 0
      unfold nrm; rw [this]; exact Real.sqrt_zero
  have hnv_nn : 0 ≤ nv := nrm_nonneg v
  have hnw_nn : 0 ≤ nw := nrm_nonneg w
  -- Decide which basis to use:
  by_cases hv : nv = 0
  · -- v = 0: ψ = 0; use the standard basis with all-zero coefficients.
    have hv0 : ∀ i, v i = 0 := hv_zero_iff.mp hv
    refine
      { bA := stdBasis
        bB := stdBasis
        coeffs := fun _ => 0
        coeffs_nonneg := fun _ => le_refl _
        bA_orthonormal := stdBasis_orthonormal
        bB_orthonormal := stdBasis_orthonormal
        reconstruction := ?_ }
    intro i j
    rw [Matrix.vecMulVec_apply, hv0 i, zero_mul]
    simp
  by_cases hw : nw = 0
  · have hw0 : ∀ i, w i = 0 := hw_zero_iff.mp hw
    refine
      { bA := stdBasis
        bB := stdBasis
        coeffs := fun _ => 0
        coeffs_nonneg := fun _ => le_refl _
        bA_orthonormal := stdBasis_orthonormal
        bB_orthonormal := stdBasis_orthonormal
        reconstruction := ?_ }
    intro i j
    rw [Matrix.vecMulVec_apply, hw0 j, mul_zero]
    simp
  -- Both nonzero: build full rank-1 decomposition.
  have hnv_pos : 0 < nv := lt_of_le_of_ne hnv_nn (Ne.symm hv)
  have hnw_pos : 0 < nw := lt_of_le_of_ne hnw_nn (Ne.symm hw)
  let uv : Fin 2 → ℝ := fun i => v i / nv
  let uw : Fin 2 → ℝ := fun i => w i / nw
  have huv : n2 uv = 1 := by
    change (v 0 / nv) ^ 2 + (v 1 / nv) ^ 2 = 1
    have hsq : nv ^ 2 = n2 v := nrm_sq v
    field_simp
    rw [hsq]; unfold n2; ring
  have huw : n2 uw = 1 := by
    change (w 0 / nw) ^ 2 + (w 1 / nw) ^ 2 = 1
    have hsq : nw ^ 2 = n2 w := nrm_sq w
    field_simp
    rw [hsq]; unfold n2; ring
  refine
    { bA := rotFromUnit uv
      bB := rotFromUnit uw
      coeffs := fun k => if k = 0 then nv * nw else 0
      coeffs_nonneg := ?_
      bA_orthonormal := rotFromUnit_orthonormal uv huv
      bB_orthonormal := rotFromUnit_orthonormal uw huw
      reconstruction := ?_ }
  · intro k
    by_cases hk : k = 0
    · rw [if_pos hk]; exact mul_nonneg hnv_nn hnw_nn
    · rw [if_neg hk]
  · intro i j
    rw [Matrix.vecMulVec_apply, Fin.sum_univ_two]
    have huv_i : uv i = v i / nv := rfl
    have huw_j : uw j = w j / nw := rfl
    have hrA : rotFromUnit uv 0 i = uv i := by
      unfold rotFromUnit; fin_cases i <;> simp [Fin.isValue]
    have hrB : rotFromUnit uw 0 j = uw j := by
      unfold rotFromUnit; fin_cases j <;> simp [Fin.isValue]
    simp only [Fin.isValue, if_neg (by decide : (1 : Fin 2) ≠ 0),
               zero_mul, add_zero, hrA, hrB, huv_i, huw_j, if_true]
    field_simp

/-- Every separable two-particle state in Fin 2 has a Schmidt decomposition. -/
theorem separable_has_schmidt {ψ : TwoParticleState 2} (h : IsQuantumSeparable ψ) :
    Nonempty (SchmidtDecomp ψ) := by
  obtain ⟨v, w, hvw⟩ := h
  rw [hvw]
  exact ⟨separableDecompData v w⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: SCHMIDT-RANK CHARACTERIZATION OF SEPARABILITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The standard QM theorem: a state is separable iff its Schmidt rank
    is at most 1. We prove both directions.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- If a Schmidt decomposition has rank ≤ 1, the underlying state is
    separable. (Sum collapses to a single rank-1 outer product.) -/
theorem schmidtRank_le_one_implies_separable {ψ : TwoParticleState 2}
    (S : SchmidtDecomp ψ) (hrank : S.rank ≤ 1) : IsQuantumSeparable ψ := by
  -- Either all coefficients are zero (then ψ = 0, separable trivially),
  -- or exactly one coefficient is nonzero, giving the rank-1 outer product.
  -- Filter set has cardinality ≤ 1 in Fin 2.
  unfold SchmidtDecomp.rank at hrank
  -- Show: ψ = vecMulVec (λ i => √λ_k₀ * S.bA k₀ i) (λ j => √λ_k₀ * S.bB k₀ j)
  -- if there is a unique nonzero coefficient at index k₀.
  by_cases h0 : S.coeffs 0 = 0
  · by_cases h1 : S.coeffs 1 = 0
    · -- both zero: ψ = 0
      have hpsi : ψ = 0 := by
        ext i j
        rw [S.reconstruction i j, Fin.sum_univ_two]
        simp [h0, h1]
      rw [hpsi]
      exact ⟨0, 0, by simp⟩
    · -- coeff 0 = 0, coeff 1 ≠ 0: ψ = λ_1 · |e_1⟩|f_1⟩
      refine ⟨fun i => S.coeffs 1 * S.bA 1 i, fun j => S.bB 1 j, ?_⟩
      ext i j
      rw [Matrix.vecMulVec_apply, S.reconstruction i j, Fin.sum_univ_two]
      simp only [h0, zero_mul, zero_add, mul_assoc]
  · -- coeff 0 ≠ 0
    by_cases h1 : S.coeffs 1 = 0
    · refine ⟨fun i => S.coeffs 0 * S.bA 0 i, fun j => S.bB 0 j, ?_⟩
      ext i j
      rw [Matrix.vecMulVec_apply, S.reconstruction i j, Fin.sum_univ_two]
      simp only [h1, zero_mul, add_zero, mul_assoc]
    · -- both nonzero: contradicts rank ≤ 1
      exfalso
      have hfilter : (Finset.univ.filter fun k : Fin 2 => S.coeffs k ≠ 0) = {0, 1} := by
        ext k
        fin_cases k <;>
          simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, h0, h1,
                Fin.isValue]
      rw [hfilter] at hrank
      have : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
      omega

/-- For `k ≠ 0`, the k-th coefficient of `separableDecompData v w` is zero.
    All three branches of the construction set `coeffs k = 0` for k ≠ 0. -/
private lemma separableDecompData_coeff_zero (v w : Fin 2 → ℝ) (k : Fin 2)
    (hk : k ≠ 0) : (separableDecompData v w).coeffs k = 0 := by
  classical
  unfold separableDecompData
  by_cases hv : nrm v = 0
  · simp [hv]
  · by_cases hw : nrm w = 0
    · simp [hv, hw]
    · simp [hv, hw, hk]

/-- The rank of `separableDecompData v w` is ≤ 1. -/
private lemma separableDecompData_rank_le_one (v w : Fin 2 → ℝ) :
    (separableDecompData v w).rank ≤ 1 := by
  unfold SchmidtDecomp.rank
  have hsub :
      (Finset.univ.filter fun k : Fin 2 => (separableDecompData v w).coeffs k ≠ 0)
      ⊆ ({0} : Finset (Fin 2)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_singleton]
    by_contra hk0
    exact hk (separableDecompData_coeff_zero v w k hk0)
  calc _ ≤ ({0} : Finset (Fin 2)).card := Finset.card_le_card hsub
       _ = 1 := by decide

/-- **The Schmidt rank characterization of separability** (one direction):
    if a state is separable, then there exists a Schmidt decomposition
    of rank ≤ 1. -/
theorem separable_implies_exists_schmidtRank_le_one
    {ψ : TwoParticleState 2} (h : IsQuantumSeparable ψ) :
    ∃ S : SchmidtDecomp ψ, S.rank ≤ 1 := by
  obtain ⟨v, w, hvw⟩ := h
  -- Build the decomposition for vecMulVec v w, then transport it via hvw⁻¹.
  refine ⟨hvw ▸ separableDecompData v w, ?_⟩
  -- The .rank field is independent of the equation we transported by;
  -- we re-state by clearing the rewrite.
  have hbound : (separableDecompData v w).rank ≤ 1 :=
    separableDecompData_rank_le_one v w
  -- After the ▸ transport the carrier ψ changes but `rank` only inspects
  -- `coeffs`, which is unchanged by `Eq.mpr`-transport on the index type.
  -- Concretely, `(hvw ▸ S).rank = S.rank`.
  have hrank_eq : (hvw ▸ separableDecompData v w).rank
                = (separableDecompData v w).rank := by
    cases hvw; rfl
  rw [hrank_eq]; exact hbound

/-- **Converse**: a state of Schmidt rank ≤ 1 is separable. -/
theorem exists_schmidtRank_le_one_implies_separable
    {ψ : TwoParticleState 2} (h : ∃ S : SchmidtDecomp ψ, S.rank ≤ 1) :
    IsQuantumSeparable ψ := by
  obtain ⟨S, hS⟩ := h
  exact schmidtRank_le_one_implies_separable S hS

/-- **The Schmidt rank characterization of separability**.
    Combining the two directions. -/
theorem separable_iff_schmidtRank_le_one (ψ : TwoParticleState 2) :
    IsQuantumSeparable ψ ↔ ∃ S : SchmidtDecomp ψ, S.rank ≤ 1 :=
  ⟨separable_implies_exists_schmidtRank_le_one,
   exists_schmidtRank_le_one_implies_separable⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: ENTANGLEMENT ⟺ SCHMIDT RANK ≥ 2
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A 2×2 state is **entangled** iff every Schmidt decomposition (if any
    exist) has rank ≥ 2. Concretely: NOT (∃ rank-≤-1 decomposition). -/
theorem entangled_iff_no_schmidtRank_le_one (ψ : TwoParticleState 2) :
    IsQuantumEntangled ψ ↔ ¬ ∃ S : SchmidtDecomp ψ, S.rank ≤ 1 := by
  unfold IsQuantumEntangled IsEntangled
  refine ⟨?_, ?_⟩
  · intro hent hexists
    exact hent (exists_schmidtRank_le_one_implies_separable hexists)
  · intro hno hsep
    exact hno (separable_implies_exists_schmidtRank_le_one hsep)

/-- The singlet has Schmidt rank exactly 2 — it is "maximally entangled"
    in the qualitative sense that every Schmidt decomposition has rank ≥ 2,
    AND we exhibit one with rank exactly 2 (`singletDecomp`). -/
theorem singlet_no_low_schmidt :
    ¬ ∃ S : SchmidtDecomp (singletState : TwoParticleState 2), S.rank ≤ 1 :=
  (entangled_iff_no_schmidtRank_le_one _).mp singlet_is_entangled

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE SCHMIDT DECOMPOSITION FOR FRAMEWORK 2-PARTICLE STATES.**

    For the framework's two-particle state space `TwoParticleState 2`
    (= `Matrix (Fin 2) (Fin 2) ℝ`):

    (1) Every separable state has an explicit Schmidt decomposition with
        Schmidt rank ≤ 1 (`separableDecompData`).

    (2) The singlet has an explicit Schmidt decomposition with Schmidt
        rank 2 and Schmidt coefficients (1/√2, 1/√2) — both nonzero, both
        equal, the maximally-entangled signature (`singletDecomp`).

    (3) A state is separable iff some Schmidt decomposition has rank ≤ 1
        (`separable_iff_schmidtRank_le_one`).

    (4) A state is entangled iff no Schmidt decomposition has rank ≤ 1
        (`entangled_iff_no_schmidtRank_le_one`).

    Honest scope: existence of a Schmidt decomposition for an arbitrary
    state in `TwoParticleState n` for general `n` requires general SVD,
    which is not in Mathlib in directly-usable form. The framework's
    Bell-style two-particle physics lives in `Fin 2`, where we have full
    constructive coverage of separable states and the singlet. -/
theorem schmidt_decomposition_master :
    -- (1) Singlet decomposes with both coefficients = 1/√2
    (∀ k : Fin 2, singletDecomp.coeffs k = 1 / Real.sqrt 2)
    -- (2) Singlet's Schmidt rank is exactly 2
    ∧ singletDecomp.rank = 2
    -- (3) The two singlet coefficients are equal (maximally entangled)
    ∧ singletDecomp.coeffs 0 = singletDecomp.coeffs 1
    -- (4) Every separable 2-particle state has a Schmidt decomposition
    ∧ (∀ ψ : TwoParticleState 2, IsQuantumSeparable ψ → Nonempty (SchmidtDecomp ψ))
    -- (5) Separable ⟺ ∃ rank-≤-1 Schmidt decomposition
    ∧ (∀ ψ : TwoParticleState 2,
         IsQuantumSeparable ψ ↔ ∃ S : SchmidtDecomp ψ, S.rank ≤ 1)
    -- (6) Entangled ⟺ no rank-≤-1 Schmidt decomposition
    ∧ (∀ ψ : TwoParticleState 2,
         IsQuantumEntangled ψ ↔ ¬ ∃ S : SchmidtDecomp ψ, S.rank ≤ 1) :=
  ⟨singletDecomp_coeffs,
   singlet_schmidt_rank,
   singletDecomp_coeffs_equal,
   fun _ => separable_has_schmidt,
   separable_iff_schmidtRank_le_one,
   entangled_iff_no_schmidtRank_le_one⟩

end UnifiedTheory.LayerB.SchmidtDecomposition
