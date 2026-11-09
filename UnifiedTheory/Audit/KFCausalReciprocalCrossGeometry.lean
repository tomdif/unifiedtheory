/- A common real coordinate change diagonalizes the off-diagonal overlap
of two different reciprocal Gaussian widths. The resulting widths are
complex; their phases are retained. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianCoordinates
import UnifiedTheory.Audit.KFCausalComplexPotentialGaussian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalCrossGeometry
noncomputable section
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalGaussianCoordinates (exponent reconstruct area)
open KFCausalReciprocalGaussianStates (quadratic)
open scoped ComplexConjugate

def A (α w v : ℝ) (r : ℂ) : ℂ :=
  ((α/2:ℝ):ℂ)*(conj r^2*((1/w:ℝ):ℂ)+r^2*((1/v:ℝ):ℂ))
def B (α w v : ℝ) (r : ℂ) : ℂ := ((α/2:ℝ):ℂ)*(conj r^2*(w:ℂ)+r^2*(v:ℂ))
def C (α β w v : ℝ) (r : ℂ) : ℂ := B α w v r-((8*β*r.im^2:ℝ):ℂ)
def diagonal (a b c d : ℂ) (u : Transverse) : ℂ :=
  a*(u 0:ℂ)^2+b*(u 1:ℂ)^2+c*(u 2:ℂ)^2+a*(u 3:ℂ)^2+d*(u 4:ℂ)^2

theorem quadratic_reconstruct (w : ℝ) (hw : w ≠ 0) (r : ℂ) (u : Transverse) :
    quadratic w (reconstruct 1 r u) =
      ((u 0)^2+(u 3)^2)/(2*w)+(w/2)*((u 1)^2+(u 2)^2) := by
  dsimp [quadratic,KFCausalQuarticChargeProfiles.chargedRadius,
    KFCausalChargedPairCoordinates.pairPolynomial,reconstruct]
  field_simp
  ring

theorem exponent_reconstruct (α β w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (r : ℂ) (u : Transverse) :
    conj (exponent α β w r (reconstruct 1 r u))+exponent α β v r (reconstruct 1 r u) =
      -diagonal (A α w v r) (B α w v r) (C α β w v r) (2*(β:ℂ)) u := by
  unfold exponent
  rw [quadratic_reconstruct w hw,quadratic_reconstruct v hv]
  dsimp [reconstruct]
  unfold diagonal C A B
  apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.one_re,Complex.one_im,Complex.re_ofNat,Complex.im_ofNat,pow_two]
  all_goals field_simp; ring

theorem weight_exponential (a b c d : ℂ) (u : Transverse) :
    KFCausalComplexPotentialGaussian.weight a b c d u = Complex.exp (-diagonal a b c d u) := by
  simp only [KFCausalComplexPotentialGaussian.weight,KFCausalComplexPotentialGaussian.widths,
    Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one,
    ← Complex.exp_add]
  congr 1
  dsimp [diagonal]
  ring

theorem overlap_reconstruct (α β w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0) (r : ℂ) (u : Transverse) :
    conj (Complex.exp (exponent α β w r (reconstruct 1 r u)))*
      Complex.exp (exponent α β v r (reconstruct 1 r u)) =
        KFCausalComplexPotentialGaussian.weight (A α w v r) (B α w v r)
          (C α β w v r) (2*(β:ℂ)) u := by
  rw [← Complex.exp_conj,← Complex.exp_add,exponent_reconstruct α β w v hw hv,weight_exponential]

theorem A_re (α w v : ℝ) (r : ℂ) : (A α w v r).re = (α*area r/2)*(1/w+1/v) := by
  simp only [A,area,pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem B_re (α w v : ℝ) (r : ℂ) : (B α w v r).re = (α*area r/2)*(w+v) := by
  simp only [B,area,pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem widths_positive (α β w v : ℝ) (r : ℂ) (hw : 1 ≤ w) (hv : 1 ≤ v)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    0 < (A α w v r).re ∧ 0 < (B α w v r).re ∧
      0 < (C α β w v r).re ∧ 0 < (2*(β:ℂ)).re := by
  have hw' : 0 < w := by linarith
  have hv' : 0 < v := by linarith
  have hp : 0 < α*area r/2 := by positivity
  have hb : α*area r ≤ (α*area r/2)*(w+v) := by nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · rw [A_re]
    exact mul_pos hp (add_pos (one_div_pos.mpr hw') (one_div_pos.mpr hv'))
  · rw [B_re]
    exact mul_pos hp (add_pos hw' hv')
  · simp only [C,Complex.sub_re,Complex.ofReal_re,B_re]
    linarith
  · simpa using mul_pos (by norm_num : (0:ℝ)<2) hβ

#print axioms quadratic_reconstruct
#print axioms exponent_reconstruct
#print axioms weight_exponential
#print axioms overlap_reconstruct
#print axioms A_re
#print axioms B_re
#print axioms widths_positive
end
end UnifiedTheory.Audit.KFCausalReciprocalCrossGeometry
