/- The reciprocal overlap has a common Laplace coordinate. This algebra
retains the complex phase and identifies the positive-quadrant chart
needed for a wedge integral; it does not assert that integral formula. -/
import UnifiedTheory.Audit.KFCausalReciprocalCrossResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalWedgeGeometry
noncomputable section
open scoped ComplexConjugate
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalReciprocalCrossGeometry (A B)
open KFCausalComplexGaussianMoments (gaussianValue)

def gamma (α : ℝ) (r : ℂ) : ℂ := (α:ℂ)*r^2/2

def chart (α : ℝ) (r : ℂ) (x y : ℝ) : ℂ := gamma α r*(x:ℂ)+conj (gamma α r)*(y:ℂ)

def first (α : ℝ) (r z : ℂ) : ℝ := z.re/(α*area r)+z.im/(2*α*r.re*r.im)
def second (α : ℝ) (r z : ℂ) : ℝ := z.re/(α*area r)-z.im/(2*α*r.re*r.im)
def wedge (α : ℝ) (r : ℂ) : Set ℂ := {z | 0 ≤ first α r z ∧ 0 ≤ second α r z}

theorem B_laplace (α w v : ℝ) (r : ℂ) :
    B α w v r = conj (gamma α r)*(w:ℂ)+gamma α r*(v:ℂ) := by
  simp only [B,gamma,map_div₀,map_mul,map_pow,Complex.conj_ofReal,map_ofNat,Complex.ofReal_div,
    Complex.ofReal_ofNat]
  ring

theorem A_reciprocal (α w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0) (r : ℂ) :
    A α w v r*(w:ℂ)*(v:ℂ) = conj (B α w v r) := by
  have hwc : (w:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  have hvc : (v:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
  simp only [A,B,map_mul,map_add,map_pow,Complex.conj_ofReal,starRingEnd_self_apply]
  push_cast
  field_simp
  ring

theorem gaussianValue_square (b : ℂ) : gaussianValue b^2 = (Real.pi:ℂ)/b := by
  unfold gaussianValue
  rw [← Complex.cpow_nat_mul]
  norm_num

theorem broad_factor (α w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0) (r : ℂ) :
    gaussianValue (A α w v r)^2 = (Real.pi:ℂ)*(w:ℂ)*(v:ℂ)/conj (B α w v r) := by
  rw [gaussianValue_square,← A_reciprocal α w v hw hv]
  have hwc : (w:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  have hvc : (v:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
  by_cases ha : A α w v r = 0
  · simp [ha]
  · field_simp

theorem chart_re (α x y : ℝ) (r : ℂ) :
    (chart α r x y).re = (α*area r/2)*(x+y) := by
  simp only [chart,gamma,area,pow_two,Complex.add_re,Complex.mul_re,Complex.mul_im,
    Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem chart_im (α x y : ℝ) (r : ℂ) :
    (chart α r x y).im = α*r.re*r.im*(x-y) := by
  simp only [chart,gamma,pow_two,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem first_chart (α x y : ℝ) (r : ℂ) (hα : α ≠ 0) (hA : area r ≠ 0)
    (ha : r.re ≠ 0) (hb : r.im ≠ 0) : first α r (chart α r x y) = x := by
  rw [first,chart_re,chart_im]
  field_simp
  ring

theorem second_chart (α x y : ℝ) (r : ℂ) (hα : α ≠ 0) (hA : area r ≠ 0)
    (ha : r.re ≠ 0) (hb : r.im ≠ 0) : second α r (chart α r x y) = y := by
  rw [second,chart_re,chart_im]
  field_simp
  ring

theorem chart_coordinates (α : ℝ) (r z : ℂ) (hα : α ≠ 0) (hA : area r ≠ 0)
    (ha : r.re ≠ 0) (hb : r.im ≠ 0) : chart α r (first α r z) (second α r z) = z := by
  apply Complex.ext
  · rw [chart_re,first,second]
    field_simp
    ring
  · rw [chart_im,first,second]
    field_simp
    ring

theorem chart_mem_wedge (α x y : ℝ) (r : ℂ) (hα : α ≠ 0) (hA : area r ≠ 0)
    (ha : r.re ≠ 0) (hb : r.im ≠ 0) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    chart α r x y ∈ wedge α r := by
  exact ⟨by rwa [first_chart α x y r hα hA ha hb],by rwa [second_chart α x y r hα hA ha hb]⟩

theorem mode_product (α w v x y : ℝ) (r : ℂ) :
    conj (Complex.exp (-(w:ℂ)*chart α r x y))*Complex.exp (-(v:ℂ)*chart α r x y) =
      Complex.exp (-B α w v r*(x:ℂ)-conj (B α w v r)*(y:ℂ)) := by
  rw [← Complex.exp_conj,← Complex.exp_add]
  congr 1
  simp only [chart,B_laplace,map_neg,map_mul,map_add,Complex.conj_ofReal,starRingEnd_self_apply]
  ring

#print axioms B_laplace
#print axioms A_reciprocal
#print axioms gaussianValue_square
#print axioms broad_factor
#print axioms chart_re
#print axioms chart_im
#print axioms first_chart
#print axioms second_chart
#print axioms chart_coordinates
#print axioms chart_mem_wedge
#print axioms mode_product
end
end UnifiedTheory.Audit.KFCausalReciprocalWedgeGeometry
