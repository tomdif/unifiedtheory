/- Uniform finite-clock growth for every fixed neutral profile whose
actual transverse energy is integrable at the compared clock positions.
This includes interference inside the profile and imposes no degree cutoff. -/
import UnifiedTheory.Audit.KFCausalNeutralProfileMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralProfileGrowth
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale)
open UnifiedTheory.Audit.KFCausalNeutralPlaneCoordinates
open UnifiedTheory.Audit.KFCausalNeutralPlaneMeasure
open UnifiedTheory.Audit.KFCausalNeutralPlaneMarginal
open UnifiedTheory.Audit.KFCausalNeutralPlaneClockGeometry
open UnifiedTheory.Audit.KFCausalNeutralPlaneActualBound
open UnifiedTheory.Audit.KFCausalNeutralPlaneIntegrability
open UnifiedTheory.Audit.KFCausalNeutralPlaneUniformGrowth
open UnifiedTheory.Audit.KFCausalNeutralProfileMarginal

def actualProfileDensity (α β ε y s : ℝ) (F : ℂ → ℂ) (x z : ℝ) : ℝ :=
  profileDensity (prefactor α (scale ε y s)) β (planeWidth α β (scale ε y s))
    (fieldSlope (scale ε y s)) F x z

theorem actualProfileDensity_factorization (α β ε y s : ℝ) (F : ℂ → ℂ) (x z : ℝ) :
    actualProfileDensity α β ε y s F x z =
      actualDensity α β ε y s 1 x z * ‖F ((x:ℂ)+(z:ℂ)*Complex.I)‖^2 := by
  simp [actualProfileDensity,profileDensity,actualDensity,KFCausalQuarticPlaneDomination.density]

theorem actualProfileDensity_integrable (α β ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0)
    (F : ℂ → ℂ)
    (hF : Integrable (profileEnergyDensity α β (scale ε y s) F) volume) :
    Integrable (fun v : Fin 2 → ℝ => actualProfileDensity α β ε y s F (v 0) (v 1)) volume := by
  let r := scale ε y s
  have hb : r.im ≠ 0 := scale_im_ne_zero ε y s hε hy hy0
  have hA : 0 < r.re^2-r.im^2 := scale_square_re_positive ε y s hε hy
  let f2 := fun x : ℝ => Real.exp (-(2*α*(r.re^2-r.im^2))*x^2)
  let f1 := fun x : ℝ => Real.exp (-(α*(r.re^2-r.im^2))*x^2)
  let g2 := fun v : Fin 2 → ℝ => profileDensity 1 β (planeWidth α β r) (fieldSlope r) F (v 0) (v 1)
  let g3 := fun u : Fin 3 → ℝ => f1 (u 0)*g2 (fun i => u i.succ)
  let g4 := fun u : Fin 4 → ℝ => f2 (u 0)*g3 (fun i => u i.succ)
  have h5 : Integrable (fun u : Transverse => f2 (u 0)*g4 (fun i => u i.succ)) volume := by
    have hi := reconstruct_integrable r hb (profileEnergyDensity α β r F) hF
    convert hi using 1
    funext u
    simp only [profileEnergyDensity,gaussian_norm_reconstruct α β r hb,
      field_reconstruct r hb,neutral_position r hb,profile_factorization]
    rfl
  have hf1 : (∫ x, f1 x) ≠ 0 := by
    dsimp [f1]
    rw [integral_gaussian]
    positivity
  have hf2 : (∫ x, f2 x) ≠ 0 := by
    dsimp [f2]
    rw [integral_gaussian]
    positivity
  have h2 := integrable_tail_product 2 f1 g2
    (integrable_tail_product 3 f2 g3 (integrable_tail_product 4 f2 g4 h5 hf2) hf2) hf1
  convert h2.const_mul (prefactor α r) using 1
  funext v
  unfold actualProfileDensity g2 profileDensity
  dsimp [r]
  ring

theorem exists_uniform_profileDensity_growth (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ε y : ℝ, 0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 →
      ∀ (F : ℂ → ℂ) (s t x z : ℝ), s ≤ t →
        actualProfileDensity α β ε y t F x z ≤
          Real.exp (C*(t-s))*actualProfileDensity α β ε y s F x z := by
  obtain ⟨C,hC,hg⟩ := exists_uniform_density_growth α hα
  refine ⟨C,hC,?_⟩
  intro β ε y hε hy hy0 F s t x z hst
  rw [actualProfileDensity_factorization,actualProfileDensity_factorization]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (hg β ε y hε hy hy0 1 s t x z hst) (sq_nonneg ‖F ((x:ℂ)+(z:ℂ)*Complex.I)‖)

theorem exists_uniform_profileEnergy_growth (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ε y : ℝ, 0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 →
      ∀ (F : ℂ → ℂ) (s t : ℝ), s ≤ t →
        Integrable (profileEnergyDensity α β (scale ε y s) F) volume →
        Integrable (profileEnergyDensity α β (scale ε y t) F) volume →
        (∫ q, profileEnergyDensity α β (scale ε y t) F q) ≤
          Real.exp (C*(t-s))*(∫ q, profileEnergyDensity α β (scale ε y s) F q) := by
  obtain ⟨C,hC,hg⟩ := exists_uniform_profileDensity_growth α hα
  refine ⟨C,hC,?_⟩
  intro β ε y hε hy hy0 F s t hst hs ht
  rw [profileEnergy_plane_integral α β _ (scale_im_ne_zero ε y t hε hy hy0),
    profileEnergy_plane_integral α β _ (scale_im_ne_zero ε y s hε hy hy0)]
  change (∫ v : Fin 2 → ℝ, actualProfileDensity α β ε y t F (v 0) (v 1)) ≤
    Real.exp (C*(t-s))*(∫ v : Fin 2 → ℝ, actualProfileDensity α β ε y s F (v 0) (v 1))
  rw [← integral_const_mul]
  apply integral_mono (actualProfileDensity_integrable α β ε y t hα hε hy hy0 F ht)
    ((actualProfileDensity_integrable α β ε y s hα hε hy hy0 F hs).const_mul _)
  intro v
  exact hg β ε y hε hy hy0 F s t (v 0) (v 1) hst

#print axioms actualProfileDensity_factorization
#print axioms actualProfileDensity_integrable
#print axioms exists_uniform_profileDensity_growth
#print axioms exists_uniform_profileEnergy_growth
end
end UnifiedTheory.Audit.KFCausalNeutralProfileGrowth
