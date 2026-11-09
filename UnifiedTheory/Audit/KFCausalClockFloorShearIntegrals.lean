/- Actual five-dimensional Gaussian estimates, including integration of
the real shear. The integrated majorant is independent of the shear size;
its remaining clock dependence is exp(-2 Re(s)). -/
import UnifiedTheory.Audit.KFCausalClockFloorShearBounds
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorShearIntegrals
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds

def chargedDensity (k : ℝ) (x : Charged) : ℝ := Real.exp (-k*squared x)

theorem chargedDensity_product (k : ℝ) (x : Charged) :
    chargedDensity k x = ∏ i, Real.exp (-k*(x i)^2) := by
  rw [← Real.exp_sum]
  simp only [chargedDensity,squared,Finset.mul_sum]

theorem chargedDensity_integrable (k : ℝ) (hk : 0 < k) : Integrable (chargedDensity k) := by
  have he : chargedDensity k = (fun x : Charged => ∏ i, Real.exp (-k*(x i)^2)) :=
    funext (chargedDensity_product k)
  rw [he]
  exact Integrable.fintype_prod (fun _ : Fin 4 => integrable_exp_neg_mul_sq hk)

theorem chargedDensity_integral (k : ℝ) (hk : 0 < k) :
    (∫ x : Charged, chargedDensity k x) = (Real.pi/k)^2 := by
  simp_rw [chargedDensity_product]
  rw [integral_fintype_prod_volume_eq_pow (ι := Fin 4) (fun r : ℝ => Real.exp (-k*r^2))]
  simp only [integral_gaussian,Fintype.card_fin]
  calc
    Real.sqrt (Real.pi/k)^4 = (Real.sqrt (Real.pi/k)^2)^2 := by ring
    _ = (Real.pi/k)^2 := by rw [Real.sq_sqrt (by positivity)]

theorem majorant_continuous (k b d : ℝ) : Continuous (majorant k b d) := by
  unfold majorant squared mix
  fun_prop

theorem majorant_nonnegative (k b d : ℝ) (x : Grouped) : 0 ≤ majorant k b d x := by
  unfold majorant
  positivity

theorem majorant_inner_integral (k b d : ℝ) (x : Charged) :
    (∫ r : ℝ, majorant k b d (x,r)) = chargedDensity k x * Real.sqrt (Real.pi/b) := by
  dsimp only [majorant,chargedDensity]
  rw [integral_const_mul,integral_add_right_eq_self (fun r : ℝ => Real.exp (-b*r^2)),
    integral_gaussian]

theorem majorant_integrable (k b d : ℝ) (hk : 0 < k) (hb : 0 < b) :
    Integrable (majorant k b d) := by
  rw [Measure.volume_eq_prod Charged ℝ]
  apply (integrable_prod_iff (majorant_continuous k b d).aestronglyMeasurable).mpr
  constructor
  · apply ae_of_all
    intro x
    exact ((measurePreserving_add_right (volume : Measure ℝ) (d*mix x)).integrable_comp_of_integrable
      (integrable_exp_neg_mul_sq hb)).const_mul (Real.exp (-k*squared x))
  · have he (x : Charged) : (∫ r : ℝ, ‖majorant k b d (x,r)‖) =
        chargedDensity k x * Real.sqrt (Real.pi/b) := by
      simp_rw [Real.norm_eq_abs,abs_of_nonneg (majorant_nonnegative k b d _)]
      exact majorant_inner_integral k b d x
    simp_rw [he]
    exact (chargedDensity_integrable k hk).mul_const _

theorem majorant_integral (k b d : ℝ) (hk : 0 < k) (hb : 0 < b) :
    (∫ x : Grouped, majorant k b d x) = (Real.pi/k)^2 * Real.sqrt (Real.pi/b) := by
  have hi := majorant_integrable k b d hk hb
  rw [Measure.volume_eq_prod Charged ℝ] at hi
  rw [Measure.volume_eq_prod Charged ℝ,integral_prod _ hi]
  simp_rw [majorant_inner_integral]
  rw [integral_mul_const,chargedDensity_integral k hk]

theorem packet_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (z : ℂ) (hz : |z.im| ≤ Real.pi/3) : MemLp (packet α β z) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (packet_continuous α β z).aestronglyMeasurable).mpr
  apply (majorant_integrable ((α/2)*Real.exp z.re) (2*β) (2*((complexScale z).re-1))
    (by positivity) (by positivity)).mono'
    ((packet_continuous α β z).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact packet_square_bound α β hα.le hβ.le hw z hz x

def transverseConstant (α β : ℝ) : ℝ := (2*Real.pi/α)^2*Real.sqrt (Real.pi/(2*β))

theorem transverseConstant_nonnegative (α β : ℝ) : 0 ≤ transverseConstant α β := by
  unfold transverseConstant
  positivity

theorem packet_square_integral_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (z : ℂ) (hz : |z.im| ≤ Real.pi/3) :
    (∫ x : Grouped, ‖packet α β z x‖^2) ≤ transverseConstant α β * Real.exp (-2*z.re) := by
  have hm := packet_memLp α β hα hβ hw z hz
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).mp hm
  have hb := integral_mono hi
    (majorant_integrable ((α/2)*Real.exp z.re) (2*β) (2*((complexScale z).re-1))
      (by positivity) (by positivity))
    (packet_square_bound α β hα.le hβ.le hw z hz)
  rw [majorant_integral _ _ _ (by positivity) (by positivity)] at hb
  have he : (Real.pi/((α/2)*Real.exp z.re))^2 =
      (2*Real.pi/α)^2*Real.exp (-2*z.re) := by
    rw [show -2*z.re = -(z.re+z.re) by ring,Real.exp_neg,Real.exp_add]
    field_simp
  rw [he] at hb
  simpa only [transverseConstant,mul_assoc,mul_comm,mul_left_comm] using hb

#print axioms chargedDensity_product
#print axioms chargedDensity_integrable
#print axioms chargedDensity_integral
#print axioms majorant_continuous
#print axioms majorant_nonnegative
#print axioms majorant_inner_integral
#print axioms majorant_integrable
#print axioms majorant_integral
#print axioms packet_memLp
#print axioms transverseConstant_nonnegative
#print axioms packet_square_integral_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorShearIntegrals
