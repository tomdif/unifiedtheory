/- Exact physical Gaussian normalization and a width-halving estimate.
These control ratios of trial-state energies as the Planck parameter varies. -/
import UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative
import UnifiedTheory.Audit.KFCausalClockFloorShearIntegrals
import UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities (configurationProfile)
open UnifiedTheory.Audit.KFCausalGaussianSliceDomain (gaussian_norm_square)

def gaussianMass (α β : ℝ) : ℝ := (Real.pi/(2*α))^2*Real.sqrt (Real.pi/(2*β))

theorem gaussianMass_positive (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    0 < gaussianMass α β := by unfold gaussianMass; positivity

theorem physicalGaussian_square (α β : ℝ) (x : Transverse) :
    ‖physicalGaussian α β x‖^2 = ∏ i : Fin 5, Real.exp (-(2*widths α β i)*(x i)^2) := by
  rw [physicalGaussian_product,norm_prod,← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Complex.ofReal_re] using gaussian_norm_square (widths α β i:ℂ) (x i)

theorem physicalGaussian_mass (α β : ℝ) (hα : 0 < α) :
    (∫ x : Transverse, ‖physicalGaussian α β x‖^2) = gaussianMass α β := by
  simp_rw [physicalGaussian_square]
  rw [integral_fintype_prod_volume_eq_prod (fun (i : Fin 5) (r : ℝ) => Real.exp (-(2*widths α β i)*r^2))]
  simp only [integral_gaussian,widths,Fin.prod_univ_succ,Fin.prod_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,mul_one]
  have hsq : Real.sqrt (Real.pi/(2*α))^2 = Real.pi/(2*α) := Real.sq_sqrt (by positivity)
  unfold gaussianMass
  calc
    _ = (Real.sqrt (Real.pi/(2*α))^2)^2*Real.sqrt (Real.pi/(2*β)) := by ring
    _ = _ := by rw [hsq]

theorem gaussianMass_half_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    gaussianMass (α/2) (β/2) ≤ 8*gaussianMass α β := by
  have hs : Real.sqrt (Real.pi/β) ≤ 2*Real.sqrt (Real.pi/(2*β)) := by
    have h1 := Real.sq_sqrt (show 0 ≤ Real.pi/β by positivity)
    have h2 := Real.sq_sqrt (show 0 ≤ Real.pi/(2*β) by positivity)
    have he : Real.pi/β = 2*(Real.pi/(2*β)) := by field_simp
    nlinarith only [h1,h2,he,Real.sqrt_nonneg (Real.pi/β),Real.sqrt_nonneg (Real.pi/(2*β))]
  have he : (Real.pi/α)^2 = 4*(Real.pi/(2*α))^2 := by field_simp; ring
  unfold gaussianMass
  simp only [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
  change (Real.pi/α)^2*Real.sqrt (Real.pi/β) ≤ _
  calc
    _ ≤ (Real.pi/α)^2*(2*Real.sqrt (Real.pi/(2*β))) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by rw [he]; ring

theorem transverseConstant_eq (α β : ℝ) :
    KFCausalClockFloorShearIntegrals.transverseConstant α β = 16*gaussianMass α β := by
  unfold KFCausalClockFloorShearIntegrals.transverseConstant gaussianMass
  ring

theorem product_square_integral (g : ℝ → ℂ) (p : Transverse → ℂ)
    (hg : MemLp g 2 volume) (hp : MemLp p 2 volume) :
    (∫ z : Configuration, ‖g z.1*p z.2‖^2) =
      (∫ s : ℝ, ‖g s‖^2)*(∫ x : Transverse, ‖p x‖^2) := by
  have h1 := (memLp_two_iff_integrable_sq_norm hg.1).mp hg
  have h2 := (memLp_two_iff_integrable_sq_norm hp.1).mp hp
  have hi := h1.mul_prod h2
  simp only [norm_mul,mul_pow]
  rw [Measure.volume_eq_prod ℝ Transverse,integral_prod _ hi]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]

theorem profile_square_integral (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    (∫ z : Configuration, ‖configurationProfile α β g z‖^2) =
      (∫ s : ℝ, ‖g s‖^2)*gaussianMass α β := by
  exact (product_square_integral g _ hg (physicalGaussian_memLp α β hα hβ)).trans
    (congrArg (fun m : ℝ => (∫ s : ℝ, ‖g s‖^2)*m) (physicalGaussian_mass α β hα))

#print axioms gaussianMass_positive
#print axioms physicalGaussian_square
#print axioms physicalGaussian_mass
#print axioms gaussianMass_half_bound
#print axioms transverseConstant_eq
#print axioms product_square_integral
#print axioms profile_square_integral

end
end UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
