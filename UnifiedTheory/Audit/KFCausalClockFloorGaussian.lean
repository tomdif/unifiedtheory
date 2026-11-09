/- The optional equal-mobility clock-floor flow removes the proved
negative-width obstruction for the gravity Gaussian: every transverse
slice stays L2 throughout the closed target strip. This is not a bound
on the joint clock integral, the sheared matter Gaussian, the energy
form domain, or the physical Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalClockFloorFlow
import UnifiedTheory.Audit.KFCausalGaussianSliceDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussian
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalClockFloorFlow
open UnifiedTheory.Audit.KFCausalGaussianSliceDomain

def coefficient (ε : ℝ) (q : ℂ) : ℂ := Complex.exp (complexInverse ε q)
def floorGaussian (ε α : ℝ) (q : ℂ) : ℝ → ℂ := gaussian ((α:ℂ)*coefficient ε q)

theorem coefficient_analytic (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    AnalyticAt ℂ (coefficient ε) q := (complexInverse_analytic ε hε q hq).cexp

theorem coefficient_re_positive (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    0 < (coefficient ε q).re := by
  rw [coefficient,Complex.exp_re]
  have hm : |(complexInverse ε q).im| < Real.pi/2 := complexInverse_mem ε hε q hq
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp hm))

theorem coefficient_real (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    coefficient ε (q:ℂ) = (Real.exp ((chartIso ε hε).symm q):ℂ) := by
  rw [coefficient,complexInverse_real ε hε,Complex.ofReal_exp]

theorem coefficient_real_scale (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    coefficient ε (q:ℂ) = ((scale ((chartIso ε hε).symm q))^2:ℝ) := by
  rw [coefficient_real ε hε]
  apply congrArg Complex.ofReal
  rw [scale, ← Real.exp_nat_mul]
  congr 1
  ring

theorem floorGaussian_real (ε α : ℝ) (hε : 0 < ε) (q x : ℝ) :
    floorGaussian ε α (q:ℂ) x = gaussian (α:ℂ) (scale ((chartIso ε hε).symm q)*x) := by
  rw [floorGaussian,coefficient_real_scale ε hε]
  unfold gaussian
  push_cast
  congr 1
  ring

theorem floorGaussian_inverse_coordinate (ε α : ℝ) (hε : 0 < ε) (q : ℝ) (x : Transverse) :
    floorGaussian ε α (q:ℂ) (x 0) =
      gaussian (α:ℂ) (((coordinateHomeomorph ε hε).symm (q,x)).2 0) := by
  rw [floorGaussian_real ε α hε,coordinateHomeomorph_symm_apply]
  rfl

theorem floorGaussian_memLp (ε α : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (q : ℂ) (hq : q ∈ targetStrip ε) : MemLp (floorGaussian ε α q) 2 volume := by
  apply (gaussian_memLp_iff _).mpr
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_pos hα (coefficient_re_positive ε hε q hq)

theorem scalar_floorGaussian_memLp (ε α : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (q : ℂ) (hq : q ∈ targetStrip ε) (c : ℂ) :
    MemLp (fun x : ℝ => c*floorGaussian ε α q x) 2 volume :=
  (floorGaussian_memLp ε α hε hα q hq).const_mul c

#print axioms coefficient_analytic
#print axioms coefficient_re_positive
#print axioms coefficient_real
#print axioms coefficient_real_scale
#print axioms floorGaussian_real
#print axioms floorGaussian_inverse_coordinate
#print axioms floorGaussian_memLp
#print axioms scalar_floorGaussian_memLp

end
end UnifiedTheory.Audit.KFCausalClockFloorGaussian
