/- Simultaneous deletion of a finite family of spatial plaquettes fixed by
one reflection plane. The omitted background retains the required symmetry;
no estimate is iterated through an arbitrary nonsymmetric action. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights
noncomputable section
open WilsonTimeSlab SpatialPlaquetteCutGeometry SpatialWilsonPlaquetteKernels
open SpatialWilsonReflectionKernel WilsonSingleLinkStaples

variable (n : ℕ) [NeZero n]

def Aligned (S : Finset (Plaquette n)) : Prop := ∀ p ∈ S, Crossing n p

def omitted (S : Finset (Plaquette n)) (s : ℝ) (p : Plaquette n) : ℝ := by
  classical
  exact if p ∈ S then 0 else s

def patchDefect (S : Finset (Plaquette n)) (u : SpatialLinks (2 * n) Q) : ℝ :=
  ∑ p ∈ S, defect n p u

omit [NeZero n] in
theorem patchDefect_nonneg (S : Finset (Plaquette n)) (u : SpatialLinks (2 * n) Q) :
    0 ≤ patchDefect n S u :=
  Finset.sum_nonneg (fun p _ => (WilsonSlabBounds.characterDefect_bounds
    (spatialHolonomy u p.1 p.2.val.1 p.2.val.2)).1)

omit [NeZero n] in
theorem patchDefect_continuous (S : Finset (Plaquette n)) : Continuous (patchDefect n S) :=
  continuous_finset_sum S (fun p _ => defect_continuous n p)

omit [NeZero n] in
theorem omitted_nonneg (S : Finset (Plaquette n)) (s : ℝ) (hs : 0 ≤ s) (p : Plaquette n) :
    0 ≤ omitted n S s p := by
  classical
  unfold omitted
  split_ifs <;> linarith

omit [NeZero n] in
theorem reflection_mem (S : Finset (Plaquette n)) (hS : Aligned n S) (p : Plaquette n) :
    reflectPlaquette n p ∈ S ↔ p ∈ S := by
  constructor
  · intro hp
    have he : p = reflectPlaquette n p :=
      (reflectPlaquette_involutive n p).symm.trans
        (SpatialWilsonInsertion.crossing_fixed n _ (hS _ hp))
    rwa [← he] at hp
  · intro hp
    rw [SpatialWilsonInsertion.crossing_fixed n p (hS p hp)]
    exact hp

omit [NeZero n] in
theorem omitted_reflection (S : Finset (Plaquette n)) (hS : Aligned n S)
    (s : ℝ) (p : Plaquette n) : omitted n S s (reflectPlaquette n p) = omitted n S s p := by
  classical
  simp only [omitted, reflection_mem n S hS p]

omit [NeZero n] in
theorem omitted_half (S : Finset (Plaquette n)) (s : ℝ) :
    (fun p => omitted n S s p / 2) = omitted n S (s / 2) := by
  classical
  funext p
  by_cases hp : p ∈ S <;> simp [omitted, hp]

theorem action_restore (S : Finset (Plaquette n)) (s : ℝ) (u : SpatialLinks (2 * n) Q) :
    action n (fun _ => s) u = action n (omitted n S s) u + s * patchDefect n S u := by
  classical
  have he (p : Plaquette n) : s * defect n p u = omitted n S s p * defect n p u +
      if p ∈ S then s * defect n p u else 0 := by
    by_cases hp : p ∈ S <;> simp [omitted, hp]
  unfold action patchDefect
  calc
    _ = ∑ p, (omitted n S s p * defect n p u +
        if p ∈ S then s * defect n p u else 0) := Finset.sum_congr rfl (fun p _ => he p)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]; simp

theorem weight_restore (S : Finset (Plaquette n)) (s : ℝ) (u : SpatialLinks (2 * n) Q) :
    weight n (fun _ => s) u = weight n (omitted n S s) u *
      Real.exp (-s * patchDefect n S u) := by
  unfold weight
  rw [action_restore, neg_add, Real.exp_add]
  congr 2
  ring

theorem weight_restore_product (S : Finset (Plaquette n)) (s : ℝ)
    (u : SpatialLinks (2 * n) Q) :
    weight n (fun _ => s) u = weight n (omitted n S s) u *
      ∏ p : S, Real.exp (-s * defect n p.val u) := by
  rw [weight_restore]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  simp only [patchDefect, Finset.mul_sum]
  exact (Finset.sum_coe_sort S (fun p => -s * defect n p u)).symm

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights
