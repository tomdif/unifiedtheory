/-
  Audit/KFCausalCSpecTrilateration.lean   (Volume sector — Step 4, Lorentzian trilateration)

  Step 4 of the Hauptvermutung ladder: recover a point's local coordinates from its
  proper-time / squared-interval relations to `d+1` timelike-related anchors.

  The key structural fact is that the LorentzIAN squared interval is quadratic, but its
  DIFFERENCES between anchors are affine-LINEAR in the point:

      σ²(p, a_i) - σ²(p, a_o) = -2 B(p, a_i - a_o) + (B(a_i,a_i) - B(a_o,a_o)),

  where `σ²(x,y) = B(x-y, x-y)` and `B` is the (symmetric, nondegenerate) metric form.
  Hence the interval measurements determine `B(p, a_i - a_o)` for each anchor, and if the
  anchor differences `a_i - a_o` are in general position (they B-determine a vector:
  `B w (a_i - a_o) = 0 ∀i ⟹ w = 0`, i.e. they span under the nondegenerate `B`), the
  point is pinned uniquely.

  `lorentzian_trilateration` proves exactly this: two points with identical squared
  intervals to every anchor coincide.  Stated over an abstract nondegenerate symmetric
  bilinear form, so the Minkowski `η = diag(-1,1,…,1)` is the intended instance and the
  Euclidean case is covered too.  Timelike proper times `τ_i = √(-σ²_i)` determine the
  `σ²_i`, so proper-time data is exactly the input this consumes -- with NO longest chains
  and NO ambient coordinates, only intrinsic interval relations.

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecTrilateration

/-- **Lorentzian trilateration (Step 4).**  Let `B` be a symmetric bilinear metric form
and `a : ι → V` anchors whose differences from a reference `o` are in general position
(`hdet`: `B w (a i - a o) = 0 ∀ i ⟹ w = 0`).  Then the squared intervals
`σ²(·, a i) = B (· - a i) (· - a i)` to all anchors determine the point: any two points
with the same interval data coincide.  For the Minkowski form this is recovery of a
local coordinate from `d+1` timelike-anchor proper times, replacing longest chains. -/
theorem lorentzian_trilateration
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    {ι : Type*} (a : ι → V) (o : ι)
    (hdet : ∀ w : V, (∀ i, B w (a i - a o) = 0) → w = 0)
    (p q : V)
    (hmeas : ∀ i, B (p - a i) (p - a i) = B (q - a i) (q - a i)) :
    p = q := by
  rw [← sub_eq_zero]
  apply hdet
  intro i
  have expand : ∀ x y : V, B (x - y) (x - y) = B x x - B x y - B y x + B y y := by
    intro x y
    simp only [map_sub, LinearMap.sub_apply]
    ring
  have hi := hmeas i
  have ho := hmeas o
  rw [expand p (a i), expand q (a i)] at hi
  rw [expand p (a o), expand q (a o)] at ho
  simp only [map_sub, LinearMap.sub_apply]
  have s1 := hsymm (a i) p
  have s2 := hsymm (a i) q
  have s3 := hsymm (a o) p
  have s4 := hsymm (a o) q
  linarith [hi, ho, s1, s2, s3, s4]

/-- **Recovered inner products.**  Under the same hypotheses, the interval data fixes the
metric inner products `B(p, a i - a o)` themselves (the affine-linear observables), not
just the point: equal interval measurements give equal inner products against every
anchor difference.  This is the linear system trilateration actually solves. -/
theorem trilateration_innerProduct_determined
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    {ι : Type*} (a : ι → V) (o : ι) (p q : V)
    (hmeas : ∀ i, B (p - a i) (p - a i) = B (q - a i) (q - a i)) (i : ι) :
    B p (a i - a o) = B q (a i - a o) := by
  have expand : ∀ x y : V, B (x - y) (x - y) = B x x - B x y - B y x + B y y := by
    intro x y
    simp only [map_sub, LinearMap.sub_apply]
    ring
  have hi := hmeas i
  have ho := hmeas o
  rw [expand p (a i), expand q (a i)] at hi
  rw [expand p (a o), expand q (a o)] at ho
  simp only [map_sub]
  have s1 := hsymm (a i) p
  have s2 := hsymm (a i) q
  have s3 := hsymm (a o) p
  have s4 := hsymm (a o) q
  linarith [hi, ho, s1, s2, s3, s4]

#print axioms lorentzian_trilateration
#print axioms trilateration_innerProduct_determined

end UnifiedTheory.Audit.KFCausalCSpecTrilateration
