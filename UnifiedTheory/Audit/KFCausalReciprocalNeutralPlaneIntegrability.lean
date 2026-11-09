/- Absolute integrability survives removal of the three nonzero Gaussian
spectators. Actual neutral exponential-polynomial pairs are integrable
in the reduced plane at every clock value, rather than only almost every. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralSliceIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralPlaneIntegrability
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalGaussianCoordinates (reconstruct)
open KFCausalReciprocalNeutralKernel (density planeDensity swap)
open KFCausalReciprocalCrossGeometry (A B C)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalClockFloorRelativeShift (scale)

theorem tail_integrable (n : ℕ) (f : ℝ → ℂ) (g : (Fin n → ℝ) → ℂ)
    (hf : (∫ x, f x) ≠ 0)
    (h : Integrable (fun u : Fin (n+1) → ℝ => f (u 0)*g (fun i => u i.succ))) :
    Integrable g := by
  have hp : Integrable (fun p : ℝ × (Fin n → ℝ) => f p.1*g p.2) := by
    have hi := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm.integrable_comp_of_integrable h
    simpa only [Function.comp_def,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
      Fin.insertNth_zero,Equiv.coe_fn_mk,Fin.cons_succ,Fin.zero_succAbove,
      cast_eq,Fin.cons_zero] using hi
  have hg : Integrable (fun u => (∫ x, f x)*g u) := by
    simpa only [integral_mul_const] using hp.integral_prod_right
  exact (integrable_const_mul_iff (IsUnit.mk0 _ hf) g).mp hg

theorem integrable_swap (f : Transverse → ℂ) (hf : Integrable f) :
    Integrable (fun u => f (swap u)) := by
  have hm := (volume_measurePreserving_piCongrLeft (fun _ : Fin 5 => ℝ)
    (Equiv.swap (2:Fin 5) 3)).integrable_comp_of_integrable hf
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin 5 => ℝ) (Equiv.swap (2:Fin 5) 3) :
      Transverse → Transverse) = swap := by
    funext u i
    fin_cases i <;> norm_num [swap,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft,
      Equiv.swap_apply_def,Fin.ext_iff]
    rfl
  rwa [he] at hm

theorem gaussian_integral_ne_zero (a : ℂ) (ha : 0 < a.re) :
    (∫ x : ℝ, Complex.exp (-a*(x:ℂ)^2)) ≠ 0 := by
  have he := KFCausalComplexGaussianMoments.value_zero a ha
  simp only [KFCausalComplexGaussianMoments.value,KFCausalComplexGaussianMoments.moment,
    pow_zero,one_mul] at he
  rw [he,KFCausalComplexGaussianMoments.gaussianValue]
  apply Complex.cpow_ne_zero_iff.mpr
  left
  exact div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by intro h; simp [h] at ha)

theorem plane_integrable (α β w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (r : ℂ) (F G : ℂ → ℂ) (hA : 0 < (A α w v r).re) (hB : 0 < (B α w v r).re)
    (hi : Integrable (density α β w v r F G)) :
    Integrable (planeDensity β (C α β w v r) r F G) := by
  have hc := (KFCausalReciprocalCrossKernel.integrable_coordinates r _).mp hi
  have hs := integrable_swap _ hc
  change Integrable (fun u => density α β w v r F G (reconstruct 1 r (swap u))) at hs
  simp_rw [KFCausalReciprocalNeutralKernel.density_factorization α β w v hw hv] at hs
  let fa : ℝ → ℂ := fun x => Complex.exp (-A α w v r*(x:ℂ)^2)
  let fb : ℝ → ℂ := fun x => Complex.exp (-B α w v r*(x:ℂ)^2)
  let g := planeDensity β (C α β w v r) r F G
  have hfa : (∫ x, fa x) ≠ 0 := gaussian_integral_ne_zero _ hA
  have hfb : (∫ x, fb x) ≠ 0 := gaussian_integral_ne_zero _ hB
  have h4 := tail_integrable 4 fa
    (fun u => fb (u 0)*(fa (u 1)*g ![u 2,u 3])) hfa hs
  have h3 := tail_integrable 3 fb
    (fun u => fa (u 0)*g ![u 1,u 2]) hfb h4
  have h2 := tail_integrable 2 fa (fun u => g ![u 0,u 1]) hfa h3
  have he : (fun u : Fin 2 → ℝ => g ![u 0,u 1]) = g := by
    funext u
    rw [show ![u 0,u 1] = u from by ext i; fin_cases i <;> rfl]
  rwa [he] at h2

theorem actual_plane_integrable (α β ε y s w v : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hw : 1 ≤ w) (hv : 1 ≤ v) (b d : ℂ) (P Q : Polynomial ℂ) :
    Integrable (planeDensity β (C α β w v (scale ε y s)) (scale ε y s)
      (exponentialProfile b 1 P) (exponentialProfile d 1 Q)) := by
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  obtain ⟨hA,hB,_,_⟩ := KFCausalReciprocalCrossGeometry.widths_positive α β w v _ hw hv ha hc hβ
  exact plane_integrable α β w v (by linarith) (by linarith) _ _ _ hA hB
    (KFCausalReciprocalNeutralSliceIntegrability.density_integrable α β ε y s w v
      hα hβ hwidth hε hy hw hv b d P Q)

#print axioms tail_integrable
#print axioms integrable_swap
#print axioms gaussian_integral_ne_zero
#print axioms plane_integrable
#print axioms actual_plane_integrable
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralPlaneIntegrability
