/- Quadratic symmetric finite differences of unit-quaternion words.
Repeated occurrences are allowed; no nondegeneracy of the lattice is needed. -/
import UnifiedTheory.Clay.YangMills.WilsonRowGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.QuaternionSymmetricChange
noncomputable section
open WilsonSlabOperator
open scoped Quaternion RealInnerProductSpace

def Variation (a ap am : Q) (d k : ℝ) : Prop :=
  ‖(ap : ℍ) - (a : ℍ)‖ ≤ k*d ∧ ‖(am : ℍ) - (a : ℍ)‖ ≤ k*d ∧
    ‖(ap : ℍ) + (am : ℍ) - (a : ℍ) - (a : ℍ)‖ ≤ k^2*d^2

theorem unit_norm (a : Q) : ‖(a : ℍ)‖ = 1 := CStarRing.norm_of_mem_unitary a.property

theorem same (a : Q) (d : ℝ) : Variation a a a d 0 := by
  simp [Variation, sub_self]

theorem same_one (a : Q) (d : ℝ) (hd : 0 ≤ d) : Variation a a a d 1 := by
  simp only [Variation, sub_self, norm_zero, one_mul, one_pow]
  constructor
  · exact hd
  constructor
  · exact hd
  have he : (a : ℍ) + (a : ℍ) - (a : ℍ) - (a : ℍ) = 0 := by abel
  rw [he, norm_zero]
  positivity

theorem inverse (a ap am : Q) (d k : ℝ) (h : Variation a ap am d k) :
    Variation a⁻¹ ap⁻¹ am⁻¹ d k := by
  change ‖star (ap : ℍ) - star (a : ℍ)‖ ≤ k*d ∧
    ‖star (am : ℍ) - star (a : ℍ)‖ ≤ k*d ∧
    ‖star (ap : ℍ) + star (am : ℍ) - star (a : ℍ) - star (a : ℍ)‖ ≤ k^2*d^2
  simpa only [← star_sub, ← star_add, norm_star] using h

theorem product (a ap am b bp bm : Q) (d k l : ℝ)
    (hd : 0 ≤ d) (hk : 0 ≤ k) (_hl : 0 ≤ l)
    (ha : Variation a ap am d k) (hb : Variation b bp bm d l) :
    Variation (a*b) (ap*bp) (am*bm) d (k+l) := by
  have first (x xp y yp : Q) (hx : ‖(xp : ℍ)-(x : ℍ)‖ ≤ k*d)
      (hy : ‖(yp : ℍ)-(y : ℍ)‖ ≤ l*d) :
      ‖((xp*yp : Q) : ℍ)-((x*y : Q) : ℍ)‖ ≤ (k+l)*d := by
    change ‖(xp : ℍ)*(yp : ℍ)-(x : ℍ)*(y : ℍ)‖ ≤ _
    calc
      _ = ‖((xp : ℍ)-(x : ℍ))*(yp : ℍ)+(x : ℍ)*((yp : ℍ)-(y : ℍ))‖ := by
        congr 1
        noncomm_ring
      _ ≤ ‖((xp : ℍ)-(x : ℍ))*(yp : ℍ)‖ +
          ‖(x : ℍ)*((yp : ℍ)-(y : ℍ))‖ := norm_add_le _ _
      _ = ‖(xp : ℍ)-(x : ℍ)‖+‖(yp : ℍ)-(y : ℍ)‖ := by
        rw [norm_mul, norm_mul, unit_norm, unit_norm, mul_one, one_mul]
      _ ≤ _ := by nlinarith
  refine ⟨first a ap b bp ha.1 hb.1, first a am b bm ha.2.1 hb.2.1, ?_⟩
  change ‖(ap : ℍ)*(bp : ℍ)+(am : ℍ)*(bm : ℍ)-
    (a : ℍ)*(b : ℍ)-(a : ℍ)*(b : ℍ)‖ ≤ _
  have he : (ap : ℍ)*(bp : ℍ)+(am : ℍ)*(bm : ℍ)-
      (a : ℍ)*(b : ℍ)-(a : ℍ)*(b : ℍ) =
      ((ap : ℍ)+(am : ℍ)-(a : ℍ)-(a : ℍ))*(b : ℍ) +
      (a : ℍ)*((bp : ℍ)+(bm : ℍ)-(b : ℍ)-(b : ℍ)) +
      ((ap : ℍ)-(a : ℍ))*((bp : ℍ)-(b : ℍ)) +
      ((am : ℍ)-(a : ℍ))*((bm : ℍ)-(b : ℍ)) := by noncomm_ring
  rw [he]
  have hnorm (w x y z : ℍ) : ‖w+x+y+z‖ ≤ ‖w‖+‖x‖+‖y‖+‖z‖ := by
    linarith [norm_add_le (w+x+y) z, norm_add_le (w+x) y, norm_add_le w x]
  have hsum : ‖((ap : ℍ)+(am : ℍ)-(a : ℍ)-(a : ℍ))*(b : ℍ) +
      (a : ℍ)*((bp : ℍ)+(bm : ℍ)-(b : ℍ)-(b : ℍ)) +
      ((ap : ℍ)-(a : ℍ))*((bp : ℍ)-(b : ℍ)) +
      ((am : ℍ)-(a : ℍ))*((bm : ℍ)-(b : ℍ))‖ ≤
      ‖(ap : ℍ)+(am : ℍ)-(a : ℍ)-(a : ℍ)‖ +
      ‖(bp : ℍ)+(bm : ℍ)-(b : ℍ)-(b : ℍ)‖ +
      ‖(ap : ℍ)-(a : ℍ)‖*‖(bp : ℍ)-(b : ℍ)‖ +
      ‖(am : ℍ)-(a : ℍ)‖*‖(bm : ℍ)-(b : ℍ)‖ := by
    simpa only [norm_mul, unit_norm, mul_one, one_mul] using hnorm
      (((ap : ℍ)+(am : ℍ)-(a : ℍ)-(a : ℍ))*(b : ℍ))
      ((a : ℍ)*((bp : ℍ)+(bm : ℍ)-(b : ℍ)-(b : ℍ)))
      (((ap : ℍ)-(a : ℍ))*((bp : ℍ)-(b : ℍ)))
      (((am : ℍ)-(a : ℍ))*((bm : ℍ)-(b : ℍ)))
  apply hsum.trans
  have hp := mul_le_mul ha.1 hb.1 (norm_nonneg _) (mul_nonneg hk hd)
  have hm := mul_le_mul ha.2.1 hb.2.1 (norm_nonneg _) (mul_nonneg hk hd)
  nlinarith [ha.2.2, hb.2.2]

theorem rotation (q a : Q) :
    Variation a (q*a) (q⁻¹*a) ‖(q : ℍ)-1‖ 1 := by
  have hi : ‖((q⁻¹ : Q) : ℍ)-1‖ = ‖(q : ℍ)-1‖ := by
    change ‖star (q : ℍ)-(1 : ℍ)‖ = _
    simpa only [star_sub, star_one] using norm_star ((q : ℍ)-1)
  have hq : (q : ℍ)*((q⁻¹ : Q) : ℍ) = 1 := by
    change ((q*q⁻¹ : Q) : ℍ) = 1
    rw [mul_inv_cancel]
    rfl
  have he : (q : ℍ)+((q⁻¹ : Q) : ℍ)-1-1 =
      ((q : ℍ)-1)*(1-((q⁻¹ : Q) : ℍ)) := by
    calc
      _ = ((q : ℍ)-1)*(1-((q⁻¹ : Q) : ℍ)) +
          ((q : ℍ)*((q⁻¹ : Q) : ℍ)-1) := by noncomm_ring
      _ = _ := by rw [hq, sub_self, add_zero]
  have hbase : Variation 1 q q⁻¹ ‖(q : ℍ)-1‖ 1 := by
    refine ⟨by simp, by simpa only [OneMemClass.coe_one, one_mul] using hi.le, ?_⟩
    change ‖(q : ℍ)+((q⁻¹ : Q) : ℍ)-1-1‖ ≤ _
    rw [he, norm_mul, norm_sub_rev 1, hi]
    simp [pow_two]
  simpa only [one_mul, add_zero] using
    product 1 q q⁻¹ a a a ‖(q : ℍ)-1‖ 1 0 (norm_nonneg _) (by norm_num)
      (by norm_num) hbase (same a _)

theorem character_second (a ap am : Q) (d k : ℝ) (h : Variation a ap am d k) :
    |(WilsonSingleLinkStaples.character ap).re + (WilsonSingleLinkStaples.character am).re -
      (WilsonSingleLinkStaples.character a).re - (WilsonSingleLinkStaples.character a).re| ≤
      2*k^2*d^2 := by
  simp only [WilsonSingleLinkStaples.character_re]
  have he : 2*(ap : ℍ).re+2*(am : ℍ).re-2*(a : ℍ).re-2*(a : ℍ).re =
      2*((ap : ℍ)+(am : ℍ)-(a : ℍ)-(a : ℍ)).re := by simp; ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ)<2)]
  let z := (ap : ℍ)+(am : ℍ)-(a : ℍ)-(a : ℍ)
  have hr := abs_real_inner_le_norm (1 : ℍ) z
  have hz := SU2HaarTilt.rotated_real (1 : Q) z
  simp only [OneMemClass.coe_one, star_one, one_mul] at hz
  rw [← hz, norm_one, one_mul] at hr
  nlinarith [h.2.2]

end
end UnifiedTheory.Clay.YangMills.QuaternionSymmetricChange
