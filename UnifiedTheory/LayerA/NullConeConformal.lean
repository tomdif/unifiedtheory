/-
  LayerA/NullConeConformal.lean -- Null cone determines conformal class

  Proves the algebraic core of Malament's theorem in both 2D and general n+1
  dimensions: if two symmetric bilinear forms have the same null cone as the
  Minkowski metric, they are conformally equivalent: g2 = lambda * g1.

  The 2D case is proved by direct evaluation at two null test vectors.
  The general n+1 case uses NullConeGeneral.null_cone_general: both forms
  must have the Minkowski diagonal structure, so they differ by a scalar.
-/
import UnifiedTheory.LayerA.NullConeGeneral
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.NullConeConformal

open Finset

/-! ### 2D Minkowski null cone -/

/-- The 2D Minkowski quadratic form: Q(v) = -(v 0)^2 + (v 1)^2. -/
def etaQuad (v : Fin 2 -> ℝ) : ℝ :=
  -(v 0) ^ 2 + (v 1) ^ 2

/-- A general symmetric quadratic form on R^2. -/
def symQuad (g00 g01 g11 : ℝ) (v : Fin 2 -> ℝ) : ℝ :=
  g00 * (v 0) ^ 2 + 2 * g01 * (v 0) * (v 1) + g11 * (v 1) ^ 2

/-- A vector is null for the Minkowski form. -/
def isNullEta (v : Fin 2 -> ℝ) : Prop :=
  etaQuad v = 0

private def ePlus : Fin 2 -> ℝ := fun _ => 1

private def eMinus : Fin 2 -> ℝ := fun i => if i = 0 then 1 else -1

private lemma ePlus_0 : ePlus (0 : Fin 2) = 1 := rfl
private lemma ePlus_1 : ePlus (1 : Fin 2) = 1 := rfl
private lemma eMinus_0 : eMinus (0 : Fin 2) = 1 := rfl
private lemma eMinus_1 : eMinus (1 : Fin 2) = -1 := by
  simp [eMinus]

private lemma ePlus_null : isNullEta ePlus := by
  simp [isNullEta, etaQuad, ePlus_0, ePlus_1]

private lemma eMinus_null : isNullEta eMinus := by
  simp [isNullEta, etaQuad, eMinus_0, eMinus_1]

/-- Coefficient extraction: null-vanishing forces g01 = 0 and g11 = -g00. -/
theorem null_same_coeffs (g00 g01 g11 : ℝ)
    (hnull : ∀ v : Fin 2 -> ℝ, isNullEta v -> symQuad g00 g01 g11 v = 0) :
    g01 = 0 ∧ g11 = -g00 := by
  have h1 := hnull ePlus ePlus_null
  have h2 := hnull eMinus eMinus_null
  simp only [symQuad, ePlus_0, ePlus_1, eMinus_0, eMinus_1] at h1 h2
  constructor <;> nlinarith

/-- **Algebraic Malament theorem (2D).**
    Null-vanishing symmetric form equals (-g00) * eta. -/
theorem null_cone_conformal_2d (g00 g01 g11 : ℝ)
    (hnull : ∀ v : Fin 2 -> ℝ, isNullEta v -> symQuad g00 g01 g11 v = 0) :
    ∀ v : Fin 2 -> ℝ, symQuad g00 g01 g11 v = (-g00) * etaQuad v := by
  obtain ⟨hb, hc⟩ := null_same_coeffs g00 g01 g11 hnull
  intro v; simp only [symQuad, etaQuad, hb, hc]; ring

/-- Existential form: any null-vanishing form is conformal to eta. -/
theorem null_cone_conformal_exists_2d (g00 g01 g11 : ℝ)
    (hnull : ∀ v : Fin 2 -> ℝ, isNullEta v -> symQuad g00 g01 g11 v = 0) :
    ∃ c : ℝ, ∀ v : Fin 2 -> ℝ, symQuad g00 g01 g11 v = c * etaQuad v :=
  ⟨-g00, null_cone_conformal_2d g00 g01 g11 hnull⟩

/-- **Two metrics with the same null cone are conformally equivalent (2D).** -/
theorem conformal_from_same_null_cone_2d
    (a1 b1 c1 a2 b2 c2 : ℝ)
    (h1 : ∀ v : Fin 2 -> ℝ, isNullEta v -> symQuad a1 b1 c1 v = 0)
    (h2 : ∀ v : Fin 2 -> ℝ, isNullEta v -> symQuad a2 b2 c2 v = 0)
    (ha1 : a1 ≠ 0) :
    ∃ mu : ℝ, ∀ v : Fin 2 -> ℝ,
      symQuad a2 b2 c2 v = mu * symQuad a1 b1 c1 v := by
  obtain ⟨hb1, hc1⟩ := null_same_coeffs a1 b1 c1 h1
  obtain ⟨hb2, hc2⟩ := null_same_coeffs a2 b2 c2 h2
  exact ⟨a2 / a1, fun v => by
    simp only [symQuad, hb1, hc1, hb2, hc2]; field_simp; ring⟩

/-! ### General n+1 dimensions (n >= 2) -/

section General

open NullConeGeneral

/-- The Minkowski quadratic form on R^{n+1}. -/
def minkQuadGen {n : ℕ} (v : Fin (n + 1) -> ℝ) : ℝ :=
  -(v 0) ^ 2 + ∑ i : Fin n, (v (Fin.succ i)) ^ 2

/-- **Null cone determines entries (general n+1).**

    If a symmetric form M vanishes on the Minkowski null cone,
    then all off-diagonal entries vanish and all spatial diagonal
    entries equal -M(0,0).

    This is a direct repackaging of null_cone_general. -/
theorem null_determines_entries {n : ℕ} (hn : 1 < n)
    (M : Fin (n + 1) -> Fin (n + 1) -> ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (h_null : ∀ v : Fin (n + 1) -> ℝ,
      minkQuadGen v = 0 ->
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * v i * v j = 0)) :
    -- Cross terms vanish
    (∀ k : Fin n, M 0 (Fin.succ k) = 0) ∧
    -- Off-diagonal spatial entries vanish
    (∀ k l : Fin n, k ≠ l -> M (Fin.succ k) (Fin.succ l) = 0) ∧
    -- All spatial diagonal entries are equal
    (∀ k l : Fin n,
      M (Fin.succ k) (Fin.succ k) = M (Fin.succ l) (Fin.succ l)) ∧
    -- Spatial diagonal = -M(0,0)
    (∀ k : Fin n, M (Fin.succ k) (Fin.succ k) = -(M 0 0)) :=
  null_cone_general hn M hSym h_null

/-- **Conformal equivalence from null cone (general n+1, entry-wise).**

    If two symmetric forms M1 and M2 both vanish on the Minkowski null
    cone, and M1(0,0) != 0, then M2 = (M2(0,0)/M1(0,0)) * M1 as
    matrices (entry-wise equality).

    This is the general algebraic Malament theorem. -/
theorem conformal_from_same_null_cone_general {n : ℕ} (hn : 1 < n)
    (M1 M2 : Fin (n + 1) -> Fin (n + 1) -> ℝ)
    (hSym1 : ∀ i j, M1 i j = M1 j i)
    (hSym2 : ∀ i j, M2 i j = M2 j i)
    (h_null1 : ∀ v : Fin (n + 1) -> ℝ,
      minkQuadGen v = 0 ->
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M1 i j * v i * v j = 0))
    (h_null2 : ∀ v : Fin (n + 1) -> ℝ,
      minkQuadGen v = 0 ->
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M2 i j * v i * v j = 0))
    (hM1 : M1 0 0 ≠ 0) :
    -- There exists mu such that M2 = mu * M1 entry-wise
    ∃ mu : ℝ, ∀ i j : Fin (n + 1), M2 i j = mu * M1 i j := by
  obtain ⟨h1_cross, h1_offdiag, _, h1_diag⟩ :=
    null_determines_entries hn M1 hSym1 h_null1
  obtain ⟨h2_cross, h2_offdiag, _, h2_diag⟩ :=
    null_determines_entries hn M2 hSym2 h_null2
  refine ⟨M2 0 0 / M1 0 0, fun i j => ?_⟩
  -- Case split on whether i and j are 0 or Fin.succ k
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · -- i = 0
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · -- i = 0, j = 0: M2 0 0 = (M2 0 0 / M1 0 0) * M1 0 0
      field_simp
    · -- i = 0, j = succ j': both are 0
      rw [h2_cross j', h1_cross j', mul_zero]
  · -- i = succ i'
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · -- i = succ i', j = 0: both are 0 (by symmetry)
      have : M2 i'.succ 0 = 0 := by rw [hSym2]; exact h2_cross i'
      have : M1 i'.succ 0 = 0 := by rw [hSym1]; exact h1_cross i'
      simp [*]
    · -- i = succ i', j = succ j'
      by_cases hij : i' = j'
      · -- diagonal: M2(i'+1, i'+1) = -(M2 0 0), M1 same
        subst hij
        rw [h2_diag i', h1_diag i']
        field_simp
      · -- off-diagonal: both are 0
        rw [h2_offdiag i' j' hij, h1_offdiag i' j' hij, mul_zero]

/-- **Conformal class uniqueness (general n+1).**

    If two symmetric forms vanish on the Minkowski null cone, their ratio
    is a single real number. This is the content of Malament's theorem:
    the null cone (equivalently, the causal structure) determines the
    metric up to a conformal factor. -/
theorem conformal_class_uniqueness {n : ℕ} (hn : 1 < n)
    (M1 M2 : Fin (n + 1) -> Fin (n + 1) -> ℝ)
    (hSym1 : ∀ i j, M1 i j = M1 j i)
    (hSym2 : ∀ i j, M2 i j = M2 j i)
    (h_null1 : ∀ v : Fin (n + 1) -> ℝ,
      minkQuadGen v = 0 ->
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M1 i j * v i * v j = 0))
    (h_null2 : ∀ v : Fin (n + 1) -> ℝ,
      minkQuadGen v = 0 ->
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M2 i j * v i * v j = 0))
    (hM1 : M1 0 0 ≠ 0) :
    ∃ mu : ℝ, ∀ i j : Fin (n + 1), M2 i j = mu * M1 i j :=
  conformal_from_same_null_cone_general hn M1 M2 hSym1 hSym2
    h_null1 h_null2 hM1

/-! ### Physical interpretation: n = 3 (3+1 spacetime) -/

/-- **Malament's theorem for 3+1 spacetime.**

    In 3+1 dimensions (n = 3, so n+1 = 4), if two Lorentzian metrics
    have the same null cone as the Minkowski metric, they are conformally
    equivalent. This is the physically relevant case.

    The proof is an instance of the general theorem with n = 3 > 1. -/
theorem malament_3plus1
    (g1 g2 : Fin 4 -> Fin 4 -> ℝ)
    (hSym1 : ∀ i j, g1 i j = g1 j i)
    (hSym2 : ∀ i j, g2 i j = g2 j i)
    (h_null1 : ∀ v : Fin 4 -> ℝ,
      minkQuadGen v = 0 ->
      (∑ i : Fin 4, ∑ j : Fin 4, g1 i j * v i * v j = 0))
    (h_null2 : ∀ v : Fin 4 -> ℝ,
      minkQuadGen v = 0 ->
      (∑ i : Fin 4, ∑ j : Fin 4, g2 i j * v i * v j = 0))
    (hg1 : g1 0 0 ≠ 0) :
    ∃ mu : ℝ, ∀ i j : Fin 4, g2 i j = mu * g1 i j :=
  conformal_from_same_null_cone_general (by norm_num : 1 < 3) g1 g2
    hSym1 hSym2 h_null1 h_null2 hg1

end General

end UnifiedTheory.LayerA.NullConeConformal
