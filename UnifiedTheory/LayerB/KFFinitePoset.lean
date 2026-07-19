/-
  LayerB/KFFinitePoset.lean

  GENERIC K_F ON A FINITE POSET

  The existing `LayerA/KFComputable.lean` verifies hand-written matrices
  for deterministic product orders, while the T11 sprinkling file stores
  numerical experiment summaries.  This file supplies the missing API:
  an evaluable K_F operator for an arbitrary `NoBackgroundSpace.FinPoset`.

  For rank r, a chamber is a canonically oriented strictly increasing
  r-tuple of events.  For chambers A and B,

      K_F(A,B) = det(zeta[A,B]) + det(zeta[B,A]) - delta(A,B),

  exactly matching the formula used by the existing K_F research branch.
  Rank one is exposed separately as a matrix on the event carrier itself.

  At every rank, the normalized trace-square moment divides Tr(K_F^2) by
  the square of the nonzero chamber-carrier size (using one when the rank
  has no chambers).  For a real symmetric matrix this is the normalized
  second power sum of its eigenvalues.  We use the trace formula directly,
  so benchmark evaluation stays exact over the rationals.
-/

import UnifiedTheory.LayerB.NoBackgroundSpace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.KFFinitePoset

open Matrix
open UnifiedTheory.LayerB.NoBackgroundSpace

/-! ## 1. Generic chamber-rank operator -/

/-- A canonically oriented rank-`r` chamber: a strictly increasing tuple
of events.  Strict increase removes the arbitrary orientation choice that
would arise from representing a chamber by an unordered finite set. -/
abbrev Chamber (P : FinPoset) (r : ℕ) :=
  { point : Fin r → Fin P.n // StrictMono point }

/-- The chamber carrier is finite and can therefore be enumerated for
exact finite-matrix evaluation. -/
def chamberCount (P : FinPoset) (r : ℕ) : ℕ :=
  Fintype.card (Chamber P r)

/-- The rational order kernel `zeta(i,j) = 1` exactly when `i ≼ j`. -/
def orderKernel (P : FinPoset) (i j : Fin P.n) : ℚ :=
  if P.rel i j = true then 1 else 0

@[simp]
theorem orderKernel_eq_one_iff (P : FinPoset) (i j : Fin P.n) :
    orderKernel P i j = 1 ↔ P.rel i j = true := by
  by_cases h : P.rel i j = true <;> simp [orderKernel, h]

@[simp]
theorem orderKernel_self (P : FinPoset) (i : Fin P.n) :
    orderKernel P i i = 1 := by
  simp [orderKernel, P.refl]

/-- The zeta block between two oriented chambers. -/
def zetaBlock (P : FinPoset) {r : ℕ} (A B : Chamber P r) :
    Matrix (Fin r) (Fin r) ℚ :=
  fun a b => orderKernel P (A.1 a) (B.1 b)

/-- The full determinant-defined K_F operator at chamber rank `r`. -/
def kFAtRank (P : FinPoset) (r : ℕ) :
    Matrix (Chamber P r) (Chamber P r) ℚ :=
  fun A B =>
    (zetaBlock P A B).det + (zetaBlock P B A).det -
      if A = B then 1 else 0

/-- The complementary oriented determinant channel.  Unlike `kFAtRank`, it
retains the forward-minus-backward information discarded by symmetrization. -/
def kFOrientationAtRank (P : FinPoset) (r : ℕ) :
    Matrix (Chamber P r) (Chamber P r) ℚ :=
  fun A B => (zetaBlock P A B).det - (zetaBlock P B A).det

/-- K_F is symmetric by construction. -/
theorem kFAtRank_symmetric (P : FinPoset) (r : ℕ) :
    (kFAtRank P r).transpose = kFAtRank P r := by
  ext A B
  change kFAtRank P r B A = kFAtRank P r A B
  unfold kFAtRank
  by_cases h : A = B
  · subst B
    rfl
  · have h' : B ≠ A := Ne.symm h
    simp [h, h', add_comm]

/-- The retained orientation channel is skew-symmetric. -/
theorem kFOrientationAtRank_skew (P : FinPoset) (r : ℕ) :
    (kFOrientationAtRank P r).transpose = -kFOrientationAtRank P r := by
  ext A B
  simp [kFOrientationAtRank]

/-- Expanded two-chamber formula.  Keeping this lemma separate makes exact
rank-two evaluation avoid repeatedly normalizing small determinants. -/
theorem kFOrientationAtRank_two_apply (P : FinPoset)
    (A B : Chamber P 2) :
    kFOrientationAtRank P 2 A B =
      (orderKernel P (A.1 0) (B.1 0) * orderKernel P (A.1 1) (B.1 1) -
        orderKernel P (A.1 0) (B.1 1) * orderKernel P (A.1 1) (B.1 0)) -
      (orderKernel P (B.1 0) (A.1 0) * orderKernel P (B.1 1) (A.1 1) -
        orderKernel P (B.1 0) (A.1 1) * orderKernel P (B.1 1) (A.1 0)) := by
  simp [kFOrientationAtRank, zetaBlock, Matrix.det_fin_two]

/-- Symmetric and oriented channels together reconstruct the directed forward
zeta determinant exactly.  Thus the information loss is localized precisely
to omission of `kFOrientationAtRank`. -/
theorem forwardDet_from_symmetric_and_orientation (P : FinPoset) (r : ℕ)
    (A B : Chamber P r) :
    (zetaBlock P A B).det =
      (kFAtRank P r A B + (if A = B then 1 else 0) +
        kFOrientationAtRank P r A B) / 2 := by
  unfold kFAtRank kFOrientationAtRank
  ring

/-- The backward directed determinant is reconstructed by subtracting the
orientation channel instead. -/
theorem backwardDet_from_symmetric_and_orientation (P : FinPoset) (r : ℕ)
    (A B : Chamber P r) :
    (zetaBlock P B A).det =
      (kFAtRank P r A B + (if A = B then 1 else 0) -
        kFOrientationAtRank P r A B) / 2 := by
  unfold kFAtRank kFOrientationAtRank
  ring

/-! ## 2. Rank-one event-carrier API -/

/-- The unique rank-one chamber supported on an event. -/
def singletonChamber (P : FinPoset) (i : Fin P.n) : Chamber P 1 :=
  ⟨fun _ => i, by
    intro a b hab
    fin_cases a
    fin_cases b
    simp at hab⟩

/-- K_F at chamber rank one, canonically indexed by the events themselves.
This is the operator used by the existing size-one finite computations. -/
def kFSizeOne (P : FinPoset) : Matrix (Fin P.n) (Fin P.n) ℚ :=
  fun i j => orderKernel P i j + orderKernel P j i -
    if i = j then 1 else 0

/-- The event-carrier formula is literally the rank-one specialization of
the generic determinant operator, not an independently chosen surrogate. -/
theorem kFAtRank_one_apply (P : FinPoset) (i j : Fin P.n) :
    kFAtRank P 1 (singletonChamber P i) (singletonChamber P j) =
      kFSizeOne P i j := by
  by_cases h : i = j
  · subst j
    simp [kFAtRank, zetaBlock, singletonChamber, kFSizeOne]
  · have hfun : (fun _ : Fin 1 => i) ≠ (fun _ : Fin 1 => j) := by
      intro hf
      exact h (congrFun hf 0)
    simp [kFAtRank, zetaBlock, singletonChamber, kFSizeOne, h, hfun]

@[simp]
theorem kFSizeOne_self (P : FinPoset) (i : Fin P.n) :
    kFSizeOne P i i = 1 := by
  simp [kFSizeOne]

theorem kFSizeOne_symmetric (P : FinPoset) :
    (kFSizeOne P).transpose = kFSizeOne P := by
  ext i j
  change kFSizeOne P j i = kFSizeOne P i j
  unfold kFSizeOne
  by_cases h : i = j
  · subst j
    rfl
  · have h' : j ≠ i := Ne.symm h
    simp [h, h', add_comm]

/-- Distinct comparable events give matrix entry one. -/
theorem kFSizeOne_eq_one_of_strict (P : FinPoset) (i j : Fin P.n)
    (hne : i ≠ j) (hij : P.rel i j = true) :
    kFSizeOne P i j = 1 := by
  have hji : P.rel j i ≠ true := by
    intro h
    exact hne (P.antisymm i j hij h)
  simp [kFSizeOne, orderKernel, hij, hji, hne]

/-- Distinct incomparable events give matrix entry zero. -/
theorem kFSizeOne_eq_zero_of_incomparable (P : FinPoset) (i j : Fin P.n)
    (hne : i ≠ j) (hij : P.rel i j = false) (hji : P.rel j i = false) :
    kFSizeOne P i j = 0 := by
  simp [kFSizeOne, orderKernel, hij, hji, hne]

/-! ## 3. Exact normalized spectral coordinate -/

/-- The second trace moment of the determinant operator at arbitrary
chamber rank. -/
def kFSecondMomentAtRank (P : FinPoset) (r : ℕ) : ℚ :=
  Matrix.trace (kFAtRank P r * kFAtRank P r)

/-- Reindexing the finite chamber carrier does not change the second moment.
This form reduces exact benchmark evaluation to an explicit finite matrix. -/
theorem kFSecondMomentAtRank_reindex (P : FinPoset) (r : ℕ)
    {m : Type*} [Fintype m] (e : m ≃ Chamber P r) :
    kFSecondMomentAtRank P r =
      ∑ i : m, ∑ j : m,
        kFAtRank P r (e i) (e j) * kFAtRank P r (e j) (e i) := by
  simp only [kFSecondMomentAtRank, Matrix.trace]
  calc
    (∑ A : Chamber P r, ∑ B : Chamber P r,
        kFAtRank P r A B * kFAtRank P r B A) =
        ∑ i : m, ∑ B : Chamber P r,
          kFAtRank P r (e i) B * kFAtRank P r B (e i) :=
      (Equiv.sum_comp e (fun A => ∑ B : Chamber P r,
        kFAtRank P r A B * kFAtRank P r B A)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Equiv.sum_comp e (fun B =>
        kFAtRank P r (e i) B * kFAtRank P r B (e i))).symm

/-- A nonzero normalization carrier.  It is the actual chamber count when
chambers exist and one for an empty chamber carrier. -/
def chamberNormalization (P : FinPoset) (r : ℕ) : ℕ :=
  max 1 (chamberCount P r)

theorem chamberNormalization_pos (P : FinPoset) (r : ℕ) :
    0 < chamberNormalization P r := by
  simp [chamberNormalization]

/-- Carrier-normalized second spectral moment at arbitrary chamber rank. -/
def normalizedKFSecondMomentAtRank (P : FinPoset) (r : ℕ) : ℚ :=
  kFSecondMomentAtRank P r / (chamberNormalization P r : ℚ) ^ 2

theorem normalizedKFSecondMomentAtRank_denominator_ne_zero
    (P : FinPoset) (r : ℕ) :
    (chamberNormalization P r : ℚ) ^ 2 ≠ 0 := by
  norm_num [Nat.ne_of_gt (chamberNormalization_pos P r)]

/-- The second trace moment `Tr(K_F^2)`. -/
def kFSecondMoment (P : FinPoset) : ℚ :=
  Matrix.trace (kFSizeOne P * kFSizeOne P)

/-- Carrier-normalized second spectral moment.  Positivity of `P.n`
ensures the denominator is nonzero. -/
def normalizedKFSecondMoment (P : FinPoset) : ℚ :=
  kFSecondMoment P / (P.n : ℚ) ^ 2

/-- The normalization denominator is nonzero for every `FinPoset`. -/
theorem normalizedKFSecondMoment_denominator_ne_zero (P : FinPoset) :
    (P.n : ℚ) ^ 2 ≠ 0 := by
  norm_num [Nat.ne_of_gt P.hn]

/-! ## Trust regression output -/

#print axioms kFAtRank_symmetric
#print axioms kFOrientationAtRank_skew
#print axioms kFOrientationAtRank_two_apply
#print axioms forwardDet_from_symmetric_and_orientation
#print axioms kFAtRank_one_apply
#print axioms kFSizeOne_symmetric
#print axioms kFSizeOne_eq_one_of_strict
#print axioms kFSecondMomentAtRank_reindex
#print axioms normalizedKFSecondMomentAtRank_denominator_ne_zero
#print axioms normalizedKFSecondMoment_denominator_ne_zero

end UnifiedTheory.LayerB.KFFinitePoset
