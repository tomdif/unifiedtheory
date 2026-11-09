/- Exact oriented Minkowski double-cone transport. The retarded boost has
negative time coefficient and swaps the tips. No curved causal relation is
identified by definition. -/
import UnifiedTheory.Audit.KFCausalConformal4DBoostedMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DDiamondAffine
noncomputable section
open Real Set
open KFCausalConformal4DDiamondBenchmark (Point)
open KFCausalConformal4DBoostedMoments

def future (v : Point) : Prop := 0<v 0 ∧ lorentzSquare v<0
def diamond (p q : Point) : Set Point := {x | future (x-p) ∧ future (q-x)}
def tip (T : ℝ) : Point := ![T,0,0,0]
def restDiamond (T : ℝ) : Set Point := diamond (-tip T) (tip T)
def endpoint (t r : ℝ) : Point := ![t,r,0,0]
def center (t r : ℝ) : Point := ![t/2,r/2,0,0]
def affine (o : Point) (A B : ℝ) (z : Point) : Point := o+boost A B z

theorem boost_inverse (A B : ℝ) (h : A^2-B^2=1) (v : Point) :
    boost A (-B) (boost A B v)=v := by
  ext i
  fin_cases i <;> simp [boost]
  · nlinarith [congrArg (fun x : ℝ => x*v 0) h]
  · nlinarith [congrArg (fun x : ℝ => x*v 1) h]

private theorem boost_neg (A B : ℝ) (v : Point) : boost A B (-v) = -boost A B v := by
  ext i
  fin_cases i <;> simp [boost] <;> ring

private theorem square_neg (v : Point) : lorentzSquare (-v)=lorentzSquare v := by
  simp [lorentzSquare]

theorem future_reverse_boost (A B : ℝ) (h : A^2-B^2=1) (hA : A<0)
    (v : Point) (hv : future v) : future (-boost A B v) := by
  have hv0 := hv.1
  have hvq := hv.2
  have hB : |B| < -A := by nlinarith [sq_abs B,abs_nonneg B]
  have hv1 : |v 1| < v 0 := by
    dsimp [lorentzSquare] at hvq
    nlinarith [sq_abs (v 1),sq_nonneg (v 2),sq_nonneg (v 3),abs_nonneg (v 1)]
  have hm : B*v 1 < (-A)*v 0 := by
    calc B*v 1 ≤ |B*v 1| := le_abs_self _
         _ = |B| * |v 1| := abs_mul _ _
         _ ≤ |B| * v 0 := mul_le_mul_of_nonneg_left hv1.le (abs_nonneg B)
         _ < (-A)*v 0 := mul_lt_mul_of_pos_right hB hv0
  refine ⟨?_,?_⟩
  · change 0 < -(A*v 0+B*v 1)
    linarith
  · rw [square_neg,boost_lorentz A B h]
    exact hvq

theorem future_boost_iff (A B : ℝ) (h : A^2-B^2=1) (hA : A<0) (v : Point) :
    future (boost A B v) ↔ future (-v) := by
  constructor
  · intro hv
    have hi := future_reverse_boost A (-B) (by nlinarith [h]) hA (boost A B v) hv
    rwa [boost_inverse A B h] at hi
  · intro hv
    have hi := future_reverse_boost A B h hA (-v) hv
    simpa only [boost_neg,neg_neg] using hi

private theorem affine_sub (o : Point) (A B : ℝ) (x y : Point) :
    affine o A B x-affine o A B y=boost A B (x-y) := by
  ext i
  fin_cases i <;> simp [affine,boost] <;> ring

theorem affine_diamond_iff (o : Point) (A B : ℝ) (h : A^2-B^2=1) (hA : A<0)
    (p q z : Point) :
    affine o A B z ∈ diamond (affine o A B q) (affine o A B p) ↔ z ∈ diamond p q := by
  change (future (affine o A B z-affine o A B q) ∧
    future (affine o A B p-affine o A B z)) ↔ (future (z-p) ∧ future (q-z))
  rw [affine_sub,affine_sub,future_boost_iff A B h hA,future_boost_iff A B h hA]
  simp only [neg_sub,and_comm]

def boostEquiv (A B : ℝ) (h : A^2-B^2=1) : Point ≃L[ℝ] Point :=
  (show Point ≃ₗ[ℝ] Point from
    { toFun := boost A B
      invFun := boost A (-B)
      left_inv := boost_inverse A B h
      right_inv := fun v => by simpa only [neg_neg] using boost_inverse A (-B) (by nlinarith [h]) v
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp [boost] <;> ring
      map_smul' := fun a x => by
        ext i
        fin_cases i <;> simp [boost] <;> ring }).toContinuousLinearEquiv

def affineEquiv (o : Point) (A B : ℝ) (h : A^2-B^2=1) : Point ≃ₜ Point :=
  (boostEquiv A B h).toHomeomorph.trans (Homeomorph.addLeft o)

theorem affineEquiv_apply (o : Point) (A B : ℝ) (h : A^2-B^2=1) (z : Point) :
    affineEquiv o A B h z=affine o A B z := rfl

theorem affine_diamond_image (o : Point) (A B : ℝ) (h : A^2-B^2=1) (hA : A<0)
    (p q : Point) : affine o A B '' diamond p q =
      diamond (affine o A B q) (affine o A B p) := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (affine_diamond_iff o A B h hA p q z).2 hz
  · intro hx
    obtain ⟨z,rfl⟩ := (affineEquiv o A B h).surjective x
    exact ⟨z,(affine_diamond_iff o A B h hA p q z).1 hx,rfl⟩

theorem retarded_parameters (t r : ℝ) (ht : t<0) (hq : 0<t^2-r^2) :
    (t/sqrt (t^2-r^2))^2-(r/sqrt (t^2-r^2))^2=1 ∧
    t/sqrt (t^2-r^2)<0 ∧ 0<sqrt (t^2-r^2)/2 := by
  have hs := sqrt_pos.mpr hq
  refine ⟨?_,div_neg_of_neg_of_pos ht hs,by positivity⟩
  rw [div_pow,div_pow,← sub_div,sq_sqrt hq.le,div_self (ne_of_gt hq)]

theorem retarded_tips (t r : ℝ) (hq : 0<t^2-r^2) :
    affine (center t r) (t/sqrt (t^2-r^2)) (r/sqrt (t^2-r^2))
      (tip (sqrt (t^2-r^2)/2))=endpoint t r ∧
    affine (center t r) (t/sqrt (t^2-r^2)) (r/sqrt (t^2-r^2))
      (-tip (sqrt (t^2-r^2)/2))=0 := by
  have hs : sqrt (t^2-r^2) ≠ 0 := ne_of_gt (sqrt_pos.mpr hq)
  constructor <;> ext i <;> fin_cases i <;>
    simp [affine,center,boost,tip,endpoint] <;> field_simp <;> ring

theorem retarded_diamond_image (t r : ℝ) (ht : t<0) (hq : 0<t^2-r^2) :
    affine (center t r) (t/sqrt (t^2-r^2)) (r/sqrt (t^2-r^2)) ''
      restDiamond (sqrt (t^2-r^2)/2)=diamond (endpoint t r) 0 := by
  obtain ⟨h,hA,_⟩ := retarded_parameters t r ht hq
  obtain ⟨hp,hm⟩ := retarded_tips t r hq
  rw [restDiamond,affine_diamond_image _ _ _ h hA,hp,hm]

#print axioms boost_inverse
#print axioms future_reverse_boost
#print axioms future_boost_iff
#print axioms affine_diamond_iff
#print axioms affineEquiv_apply
#print axioms affine_diamond_image
#print axioms retarded_parameters
#print axioms retarded_tips
#print axioms retarded_diamond_image
end
end UnifiedTheory.Audit.KFCausalConformal4DDiamondAffine
