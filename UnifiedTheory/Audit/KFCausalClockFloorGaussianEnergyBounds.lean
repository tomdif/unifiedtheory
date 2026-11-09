/- Uniform analytic-strip mass estimates relative to physical Gaussian mass.
The clock floor and clock profile remain fixed; the transverse widths may vary. -/
import UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
import UnifiedTheory.Audit.KFCausalClockFloorFieldMoments
import UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergyBounds
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped)
open UnifiedTheory.Audit.KFCausalClockFloorShearIntegrals
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalClockFloorFieldBounds
open UnifiedTheory.Audit.KFCausalClockFloorFieldMoments
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial

def stripMass (ε a : ℝ) : ℝ :=
  16*Real.exp (2*a*(Real.pi*ε/3)^2)*(∫ q : ℝ, clockEnvelope ε a q)

theorem stripMass_nonnegative (ε a : ℝ) : 0 ≤ stripMass ε a := by
  have hi : 0 ≤ ∫ q : ℝ, clockEnvelope ε a q :=
    integral_nonneg (fun q => by unfold clockEnvelope; positivity)
  unfold stripMass
  positivity

theorem line_mass_bound (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    (∫ z : ℝ × Grouped, ‖line ε a α β y z‖^2) ≤ stripMass ε a*gaussianMass α β := by
  have hm := line_memLp ε a α β y hε ha hα hβ hw hy
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).mp hm
  have he : Real.exp (2*a*y^2) ≤ Real.exp (2*a*(Real.pi*ε/3)^2) := by
    apply Real.exp_le_exp.mpr
    have hs : y^2 ≤ (Real.pi*ε/3)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) (by positivity)).mpr hy
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  have hc : 0 ≤ ∫ q : ℝ, clockEnvelope ε a q :=
    integral_nonneg (fun q => by unfold clockEnvelope; positivity)
  rw [Measure.volume_eq_prod ℝ Grouped] at hi ⊢
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ q : ℝ, (Real.exp (2*a*y^2)*transverseConstant α β)*clockEnvelope ε a q :=
      integral_mono hi.integral_prod_left (((clockEnvelope_integrable ε a ha).const_mul _))
        (line_inner_bound ε a α β y · hε hα hβ hw hy)
    _ = (Real.exp (2*a*y^2)*transverseConstant α β)*(∫ q : ℝ, clockEnvelope ε a q) :=
      integral_const_mul _ _
    _ ≤ (Real.exp (2*a*(Real.pi*ε/3)^2)*transverseConstant α β)*(∫ q : ℝ, clockEnvelope ε a q) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (transverseConstant_nonnegative α β)) hc
    _ = _ := by rw [transverseConstant_eq]; unfold stripMass; ring

theorem quadratic_mass_bound (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) :
    (∫ z : ℝ × Grouped, ‖(fieldLine ε hε l z:ℂ)^2*line ε a α β y z‖^2) ≤
      (8*(2*‖l‖^2*momentBound α β)^2*stripMass ε a)*gaussianMass α β := by
  have hq := quadratic_line_memLp ε a α β y hε ha hα hβ hw hy l
  have hh := line_memLp ε a (α/2) (β/2) y hε ha (by positivity) (by positivity) (by linarith) hy
  have hi (z : ℝ × Grouped) := pow_le_pow_left₀ (norm_nonneg _)
    (quadratic_line_bound ε a α β y hε hα hβ hw hy l z) 2
  calc
    _ ≤ ∫ z : ℝ × Grouped, (2*‖l‖^2*momentBound α β)^2*‖line ε a (α/2) (β/2) y z‖^2 :=
      integral_mono ((memLp_two_iff_integrable_sq_norm hq.1).mp hq)
        (((memLp_two_iff_integrable_sq_norm hh.1).mp hh).const_mul _)
        (fun z => by simpa only [mul_pow] using hi z)
    _ = (2*‖l‖^2*momentBound α β)^2*(∫ z : ℝ × Grouped, ‖line ε a (α/2) (β/2) y z‖^2) :=
      integral_const_mul _ _
    _ ≤ (2*‖l‖^2*momentBound α β)^2*(stripMass ε a*gaussianMass (α/2) (β/2)) :=
      mul_le_mul_of_nonneg_left (line_mass_bound ε a (α/2) (β/2) y hε ha
        (by positivity) (by positivity) (by linarith) hy) (sq_nonneg _)
    _ ≤ (2*‖l‖^2*momentBound α β)^2*(stripMass ε a*(8*gaussianMass α β)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (gaussianMass_half_bound α β hα hβ)
        (stripMass_nonnegative ε a)) (sq_nonneg _)
    _ = _ := by ring

def groundMoment : ℝ := 128+8*flowBound

theorem ground_moment (hbar : ℝ) (hh : hbar ≠ 0) :
    momentBound (groundWidth hbar) (neutralWidth hbar) = |hbar| *groundMoment := by
  unfold momentBound neutralWidth groundWidth groundMoment
  field_simp
  ring

def quadraticMass (ε a : ℝ) (l : Transverse →L[ℝ] ℝ) : ℝ :=
  8*(2*‖l‖^2*groundMoment)^2*stripMass ε a

theorem quadraticMass_nonnegative (ε a : ℝ) (l : Transverse →L[ℝ] ℝ) :
    0 ≤ quadraticMass ε a l :=
  mul_nonneg (by positivity) (stripMass_nonnegative ε a)

theorem ground_quadratic_mass_bound (ε a hbar y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hh1 : |hbar| ≤ 1) (hy : |y| ≤ Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) :
    (∫ z : ℝ × Grouped, ‖(fieldLine ε hε l z:ℂ)^2*
      line ε a (groundWidth hbar) (neutralWidth hbar) y z‖^2) ≤
      quadraticMass ε a l*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  have hg : 0 ≤ groundMoment := by unfold groundMoment; positivity [flowBound_positive]
  have hm : momentBound (groundWidth hbar) (neutralWidth hbar) ≤ groundMoment := by
    rw [ground_moment hbar hh]
    exact mul_le_of_le_one_left hg hh1
  have hs := pow_le_pow_left₀
    (show 0 ≤ 2*‖l‖^2*momentBound (groundWidth hbar) (neutralWidth hbar) from
      mul_nonneg (by positivity) (momentBound_positive _ _ (groundWidth_positive hbar hh)
        (neutralWidth_positive hbar hh)).le)
    (mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2*‖l‖^2)) 2
  exact (quadratic_mass_bound ε a _ _ y hε ha (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) hy l).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num))
        (stripMass_nonnegative ε a)) (gaussianMass_positive _ _
          (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)).le)

#print axioms stripMass_nonnegative
#print axioms line_mass_bound
#print axioms quadratic_mass_bound
#print axioms ground_moment
#print axioms quadraticMass_nonnegative
#print axioms ground_quadratic_mass_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergyBounds
