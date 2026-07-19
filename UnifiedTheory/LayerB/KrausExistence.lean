/-
  LayerB/KrausExistence.lean
  ──────────────────────────

  Phase 2.3 (partial) of the Kraus existence theorem.

  Defines the CP / CPTP predicates via the Choi matrix and proves the
  EASY direction:  every Kraus representation produces a CP map (and a
  CPTP map when the completeness relation holds, which it does by the
  `KrausRepresentation` structure).

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `IsCP L`   :=  `(choi L).PosSemidef`         (definition).
    2. `IsCPTP L` :=  `IsCP L ∧ ∀ ρ, (L ρ).trace = ρ.trace`.
    3. `KrausRepresentation.toLinearMap`  : every Kraus rep induces
       a linear map between matrix algebras.
    4. `choi_kraus_apply` : element-wise formula for the Choi matrix
       of a Kraus-induced map.
    5. `choi_kraus_isHermitian` : the Choi matrix of a Kraus-induced
       map is Hermitian.
    6. `choi_kraus_eq_stacked_mul_conjTranspose` : structural identity
       `choi(K.toLinearMap) = B · B†` where B is the stacked Kraus
       matrix.  This makes the PSD conclusion manifest.
    7. `kraus_isTP` : every Kraus-induced map is trace-preserving.

  WHAT IS DEFERRED to a future file (Phase 2.4):
    – `kraus_isCP` (the easy direction): the PSD conclusion follows
      from `choi_kraus_eq_stacked_mul_conjTranspose` but Mathlib's
      `Matrix.posSemidef_self_mul_conjTranspose` requires a
      `StarOrderedRing ℂ` instance whose resolution under
      `open scoped ComplexOrder` clashes with the `Complex.partialOrder`
      vs `RCLike.toPartialOrder` distinction.  A direct dot-product
      PSD proof can be written but is left for a follow-up.
    – `kraus_isCPTP` (combines `kraus_isCP` and `kraus_isTP`).
    – The HARD direction: given CPTP L, exhibit a Kraus representation
      K such that L = K.toLinearMap.  Requires spectral decomposition
      of the Choi matrix + the vec/unvec inverse (already scaffolded
      in `VecUnvec.lean`) + element-wise reconstruction.
-/

import UnifiedTheory.LayerB.ChoiMatrix
import UnifiedTheory.LayerB.VecUnvec
import Mathlib.Analysis.Matrix.Order

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Kraus

open Matrix Complex
open scoped ComplexOrder

/-- Local `AddLeftMono ℂ` — needed for Mathlib's PSD sum lemmas
    on complex matrices.  See `KrausRepresentation.lean` for context. -/
local instance : AddLeftMono ℂ where
  elim c a b (h : a ≤ b) := by
    change c + a ≤ c + b
    obtain ⟨hr, hi⟩ := h
    exact ⟨by simp only [Complex.add_re]; linarith,
           by simp only [Complex.add_im]; linarith⟩

/-! ## Custom PSD helpers for ℂ (bypassing StarOrderedRing typeclass) -/

/-- Sum of non-negatives in ℂ is non-negative, proved manually to
    avoid the OrderedAddCommMonoid ℂ typeclass-resolution issue. -/
private theorem complex_sum_nonneg
    {α : Type*} [DecidableEq α] {s : Finset α} (f : α → ℂ)
    (h : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∑ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ h_notin ih =>
    rw [Finset.sum_insert h_notin]
    have h1 := h _ (Finset.mem_insert_self _ _)
    have ih' := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [Complex.nonneg_iff] at h1 ih' ⊢
    refine ⟨?_, ?_⟩
    · rw [Complex.add_re]; linarith [h1.1, ih'.1]
    · rw [Complex.add_im]; linarith [h1.2, ih'.2]

/-- For ℂ:  `0 ≤ star z * z`.  Manual proof via `Complex.mul_conj`. -/
private theorem complex_star_mul_self_nonneg (z : ℂ) : 0 ≤ star z * z := by
  have h_eq : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [mul_comm]
    exact Complex.mul_conj z
  rw [h_eq, Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · simp only [Complex.ofReal_re]; exact Complex.normSq_nonneg z
  · simp only [Complex.ofReal_im]

/-- **`B · B†` is PSD for any complex rectangular matrix B.**

    This is the ℂ-specialized version of `Matrix.posSemidef_self_mul_conjTranspose`,
    proved without invoking the disputed `StarOrderedRing ℂ` instance.
    Generic over index types so it works on `Fin m × Fin n` as well as `Fin k`. -/
theorem complex_posSemidef_self_mul_conjTranspose {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (B : Matrix p q ℂ) : (B * B.conjTranspose).PosSemidef := by
  suffices h : ((B.conjTranspose).conjTranspose * B.conjTranspose).PosSemidef by
    rwa [Matrix.conjTranspose_conjTranspose] at h
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact Matrix.isHermitian_conjTranspose_mul_self _
  · intro x
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_conjTranspose, star_star]
    change 0 ≤ ∑ i, star ((B.conjTranspose *ᵥ x) i) * (B.conjTranspose *ᵥ x) i
    apply complex_sum_nonneg
    intro i _
    exact complex_star_mul_self_nonneg _

/-! ## 1. CP and CPTP predicates -/

/-- A linear map `L : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ` is completely
    positive iff its Choi matrix is positive semidefinite.  This is the
    Choi-Jamiolkowski characterization of CP, taken as our definition. -/
def IsCP {m n : ℕ}
    (L : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (choi L).PosSemidef

/-- `L` is completely positive AND trace-preserving (CPTP). -/
def IsCPTP {m n : ℕ}
    (L : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsCP L ∧ ∀ ρ : Matrix (Fin m) (Fin m) ℂ, (L ρ).trace = ρ.trace

/-! ## 2. KrausRepresentation → LinearMap -/

/-- The linear map induced by a Kraus representation. -/
noncomputable def KrausRepresentation.toLinearMap
    {m n k : ℕ} (K : KrausRepresentation m n k) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun ρ := K.apply ρ
  map_add' ρ σ := K.apply_add ρ σ
  map_smul' c ρ := K.apply_smul c ρ

@[simp]
theorem KrausRepresentation.toLinearMap_apply
    {m n k : ℕ} (K : KrausRepresentation m n k)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    K.toLinearMap ρ = K.apply ρ := rfl

/-! ## 3. The Choi matrix of a Kraus-induced map: rank-1 sum form -/

/-- For a Kraus representation `K`, the Choi matrix of the induced
    linear map evaluates element-wise as:

        choi(K.toLinearMap)⟨a,c⟩⟨b,d⟩  =  Σᵢ Kᵢ[c, a] · conj(Kᵢ[d, b]) .

    This is the "rank-1 sum" form that makes PSD manifest. -/
theorem choi_kraus_apply
    {m n k : ℕ} (K : KrausRepresentation m n k)
    (a b : Fin m) (c d : Fin n) :
    choi K.toLinearMap ⟨a, c⟩ ⟨b, d⟩
      = ∑ i, K.K i c a * star (K.K i d b) := by
  -- choi L ⟨a,c⟩ ⟨b,d⟩ = L(single a b 1) c d = K.apply (single a b 1) c d
  -- = (Σ_i K_i · single a b 1 · K_i†) c d
  -- = Σ_i (K_i · single a b 1 · K_i†) c d
  -- = Σ_i (K_i)[c, a] · conj((K_i)[d, b])    (by computing the product)
  simp only [choi_apply, KrausRepresentation.toLinearMap_apply,
             KrausRepresentation.apply]
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  -- (K_i · single a b 1 · K_i†) c d = K_i[c, a] · conj(K_i[d, b])
  -- Step 1: (K_i · single a b 1)[c, j] = K_i[c, a] · δ_{j,b}
  -- Step 2: Σ_j K_i[c, a] · δ_{j,b} · K_i†[j, d] = K_i[c, a] · K_i†[b, d]
  -- Step 3: K_i†[b, d] = conj(K_i[d, b])
  rw [Matrix.mul_apply]
  -- Σ_j (K_i · single a b 1)[c, j] * (K_i)†[j, d]
  have h_inner : ∀ j,
      (K.K i * Matrix.single a b (1 : ℂ)) c j
        = if j = b then K.K i c a else 0 := by
    intro j
    by_cases hj : j = b
    · -- Main case: j = b
      subst hj
      simp [Matrix.mul_single_apply_same]
    · -- Off-diagonal: j ≠ b
      have h_zero : (K.K i * Matrix.single a b (1 : ℂ)) c j = 0 := by
        rw [Matrix.mul_single_apply_of_ne (hbj := hj)]
      rw [h_zero]
      simp [hj]
  simp_rw [h_inner]
  -- Σ_j (if j = b then K_i[c, a] else 0) * (K_i†)[j, d]
  rw [Finset.sum_eq_single b]
  · -- main: K_i[c, a] * (K_i†)[b, d] = K_i[c, a] * conj(K_i[d, b])
    simp [Matrix.conjTranspose_apply]
  · -- non-main: 0 * _ = 0
    intro j _ hj
    simp [hj]
  · intro h; exfalso; exact h (Finset.mem_univ _)

/-! ## 4. KrausRepresentation induces a CP map (easy direction) -/

/-- The Choi matrix of a Kraus-induced map is Hermitian. -/
theorem choi_kraus_isHermitian
    {m n k : ℕ} (K : KrausRepresentation m n k) :
    (choi K.toLinearMap).IsHermitian := by
  -- (choi L)⟨a,c⟩⟨b,d⟩ = Σᵢ Kᵢ[c,a] · conj(Kᵢ[d,b])
  -- conjTranspose: (choi L)†⟨a,c⟩⟨b,d⟩ = conj((choi L)⟨b,d⟩⟨a,c⟩)
  --              = conj(Σᵢ Kᵢ[d,b] · conj(Kᵢ[c,a]))
  --              = Σᵢ conj(Kᵢ[d,b]) · Kᵢ[c,a]
  --              = (choi L)⟨a,c⟩⟨b,d⟩
  unfold Matrix.IsHermitian
  ext ⟨a, c⟩ ⟨b, d⟩
  rw [Matrix.conjTranspose_apply]
  rw [choi_kraus_apply, choi_kraus_apply]
  -- star(Σᵢ Kᵢ[d,b] · conj(Kᵢ[c,a])) = Σᵢ Kᵢ[c,a] · conj(Kᵢ[d,b])
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- star (K_i d b * star (K_i c a)) = K_i c a * star (K_i d b)
  rw [StarMul.star_mul, star_star, mul_comm]

/-- The "stacked Kraus" matrix:  `B[(a,c), i] := K_i[c, a]`. -/
def stackedKraus {m n k : ℕ} (K : KrausRepresentation m n k) :
    Matrix (Fin m × Fin n) (Fin k) ℂ :=
  fun ⟨a, c⟩ i => K.K i c a

/-- The Choi matrix of a Kraus-induced map equals `B · B†` where B is
    the stacked-Kraus matrix.  This is the structural identity that
    makes PSD manifest (since `B · B†` is always PSD).  The PSD
    conclusion itself (`IsCP K.toLinearMap`) is deferred to Phase 2.4
    because Mathlib's `posSemidef_self_mul_conjTranspose` over ℂ
    requires a `StarOrderedRing ℂ` instance whose resolution is
    subtle under `open scoped ComplexOrder`. -/
theorem choi_kraus_eq_stacked_mul_conjTranspose
    {m n k : ℕ} (K : KrausRepresentation m n k) :
    choi K.toLinearMap = (stackedKraus K) * (stackedKraus K).conjTranspose := by
  ext ⟨a, c⟩ ⟨b, d⟩
  rw [choi_kraus_apply]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [stackedKraus, Matrix.conjTranspose_apply]

/-- **Kraus-induced maps are CP.** -/
theorem kraus_isCP {m n k : ℕ} (K : KrausRepresentation m n k) :
    IsCP K.toLinearMap := by
  unfold IsCP
  rw [choi_kraus_eq_stacked_mul_conjTranspose]
  exact complex_posSemidef_self_mul_conjTranspose (stackedKraus K)

/-- **Kraus representations are trace-preserving.**
    For any matrix ρ, Tr(K.apply ρ) = Tr(ρ). -/
theorem kraus_isTP {m n k : ℕ} (K : KrausRepresentation m n k)
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    (K.toLinearMap ρ).trace = ρ.trace := by
  rw [KrausRepresentation.toLinearMap_apply]
  exact K.trace_apply ρ

/-- **Kraus-induced maps are CPTP.** -/
theorem kraus_isCPTP {m n k : ℕ} (K : KrausRepresentation m n k) :
    IsCPTP K.toLinearMap := ⟨kraus_isCP K, kraus_isTP K⟩

end UnifiedTheory.LayerB.Kraus
