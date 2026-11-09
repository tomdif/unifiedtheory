/- Actual link-plane reflection on the periodic spatial slice. Every
coarse link is split into two endpoint half-edges. The plane fixes no
coarse vertex, so the half-edges split into two genuinely disjoint copies,
including both periodic seams. No reflection positivity is assumed. -/
import UnifiedTheory.Clay.YangMills.WilsonTimeSlab
import UnifiedTheory.Clay.YangMills.PeriodicHalfGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SpatialHalfEdgeGeometry
noncomputable section
open WilsonTimeSlab

abbrev Link (N : ℕ) := SpatialVertex N × Fin 3
abbrev HalfEdge (N : ℕ) := Link N ⊕ Link N

def reflectVertex (N : ℕ) (x : SpatialVertex N) : SpatialVertex N :=
  fun j => if j = 0 then -(x j + 1) else x j

theorem reflectVertex_involutive (N : ℕ) : Function.Involutive (reflectVertex N) := by
  intro x
  funext j
  by_cases hj : j = 0 <;> simp [reflectVertex, hj]

theorem reflectVertex_step_tangent (N : ℕ) (x : SpatialVertex N)
    (j : Fin 3) (hj : j ≠ 0) :
    reflectVertex N (spatialStep N x j) = spatialStep N (reflectVertex N x) j := by
  funext k
  by_cases hk : k = 0
  · subst k
    simp [reflectVertex, spatialStep, hj]
  · simp [reflectVertex, spatialStep, hk]

theorem reflectVertex_step_normal (N : ℕ) (x : SpatialVertex N) :
    spatialStep N (reflectVertex N (spatialStep N x 0)) 0 = reflectVertex N x := by
  funext j
  by_cases hj : j = 0
  · subst j
    simp [reflectVertex, spatialStep]
  · simp [reflectVertex, spatialStep, hj]

def reflectLink (N : ℕ) (e : Link N) : Link N :=
  (if e.2 = 0 then reflectVertex N (spatialStep N e.1 0) else reflectVertex N e.1, e.2)

theorem reflectLink_direction (N : ℕ) (e : Link N) : (reflectLink N e).2 = e.2 := rfl

theorem reflectLink_involutive (N : ℕ) : Function.Involutive (reflectLink N) := by
  rintro ⟨x,j⟩
  by_cases hj : j = 0
  · subst j
    simpa only [reflectLink, ↓reduceIte, reflectVertex_step_normal, Prod.mk.injEq,
      and_true] using reflectVertex_involutive N x
  · simpa only [reflectLink, if_neg hj, Prod.mk.injEq, and_true]
      using reflectVertex_involutive N x

def endpoint (N : ℕ) : HalfEdge N → SpatialVertex N
  | Sum.inl e => e.1
  | Sum.inr e => spatialStep N e.1 e.2

def reflectHalf (N : ℕ) : HalfEdge N → HalfEdge N
  | Sum.inl e => if e.2 = 0 then Sum.inr (reflectLink N e) else Sum.inl (reflectLink N e)
  | Sum.inr e => if e.2 = 0 then Sum.inl (reflectLink N e) else Sum.inr (reflectLink N e)

theorem reflectHalf_involutive (N : ℕ) : Function.Involutive (reflectHalf N) := by
  intro e
  cases e with
  | inl e =>
    by_cases he : e.2 = 0 <;>
      simp [reflectHalf, he, reflectLink_direction, reflectLink_involutive N e]
  | inr e =>
    by_cases he : e.2 = 0 <;>
      simp [reflectHalf, he, reflectLink_direction, reflectLink_involutive N e]

theorem reflectHalf_endpoint (N : ℕ) (e : HalfEdge N) :
    endpoint N (reflectHalf N e) = reflectVertex N (endpoint N e) := by
  cases e with
  | inl e =>
    rcases e with ⟨x,j⟩
    by_cases hj : j = 0
    · subst j
      simp [reflectHalf, reflectLink, endpoint, reflectVertex_step_normal]
    · simp [reflectHalf, reflectLink, endpoint, hj]
  | inr e =>
    rcases e with ⟨x,j⟩
    by_cases hj : j = 0
    · subst j
      simp [reflectHalf, reflectLink, endpoint]
    · simp [reflectHalf, reflectLink, endpoint, hj,
        reflectVertex_step_tangent N x j hj]

variable (n : ℕ) [NeZero n]

def Positive (e : HalfEdge (2 * n)) : Prop := (endpoint (2 * n) e 0).val < n

theorem positive_reflected_iff (e : HalfEdge (2 * n)) :
    Positive n (reflectHalf (2 * n) e) ↔ ¬ Positive n e := by
  unfold Positive
  rw [reflectHalf_endpoint]
  simp only [reflectVertex, ↓reduceIte]
  rw [PeriodicHalfGeometry.val_neg_add_one]
  have ht := (endpoint (2 * n) e 0).val_lt
  have hn := NeZero.pos n
  omega

theorem reflectHalf_ne (e : HalfEdge (2 * n)) : reflectHalf (2 * n) e ≠ e := by
  intro he
  have h := positive_reflected_iff n e
  rw [he] at h
  exact iff_not_self h

abbrev PositiveHalf := {e : HalfEdge (2 * n) // Positive n e}
instance positiveHalfFintype : Fintype (PositiveHalf n) := Fintype.ofFinite _

def glue : PositiveHalf n ⊕ PositiveHalf n → HalfEdge (2 * n)
  | Sum.inl p => p.val
  | Sum.inr p => reflectHalf (2 * n) p.val

def split (e : HalfEdge (2 * n)) : PositiveHalf n ⊕ PositiveHalf n := by
  classical
  exact if he : Positive n e then Sum.inl ⟨e,he⟩ else
    Sum.inr ⟨reflectHalf (2 * n) e, (positive_reflected_iff n e).mpr he⟩

theorem split_glue (p : PositiveHalf n ⊕ PositiveHalf n) : split n (glue n p) = p := by
  classical
  cases p with
  | inl p => simp [split, glue, p.property]
  | inr p =>
    have hn : ¬ Positive n (reflectHalf (2 * n) p.val) := by
      rw [positive_reflected_iff]
      exact not_not.mpr p.property
    simp only [glue, split, dif_neg hn]
    apply congrArg Sum.inr
    exact Subtype.ext (reflectHalf_involutive (2 * n) p.val)

theorem glue_split (e : HalfEdge (2 * n)) : glue n (split n e) = e := by
  classical
  by_cases he : Positive n e
  · simp [split, he, glue]
  · simp [split, he, glue, reflectHalf_involutive (2 * n) e]

def piecesEquiv : PositiveHalf n ⊕ PositiveHalf n ≃ HalfEdge (2 * n) where
  toFun := glue n
  invFun := split n
  left_inv := split_glue n
  right_inv := glue_split n

end
end UnifiedTheory.Clay.YangMills.SpatialHalfEdgeGeometry
