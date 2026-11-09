/- Identify the common-real-source quartic energy with the original
finite-family positive joint density. All source amplitudes, charged
width cross terms, and the original product measure are retained. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianEnergy
import UnifiedTheory.Audit.KFCausalGaussianSourceJointKernel
import UnifiedTheory.Audit.KFCausalChargedProductFubini

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalOriginalCommonRealGaussianEnergy
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalNeutralPositiveForm (profileSum positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalChargedEvenMomentFamily (packet)
open KFCausalChargedEvenMomentImaginaryBound (gamma)
open KFCausalCommonRealGaussianEnergy (neutralWeight neutralLine density energy)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalQuarticPlaneDomination (potential)

theorem profile_factor (n : ℕ) (α B : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (u v x Y : ℝ) :
    profileSum n w c (fun _ => exponentialProfile (B:ℂ) 1 1)
      (KFCausalReciprocalWedgeGeometry.chart α r (u^2+v^2) Y)
      (KFCausalReciprocalNeutralKernel.neutral r v x) =
      Complex.exp ((B:ℂ)*KFCausalReciprocalNeutralKernel.neutral r v x)*
        packet 0 (gamma α r) w (fun i => c i*(w i:ℂ)) ((u,v),Y) := by
  rw [KFCausalChargedEvenMomentFamily.packet_expansion]
  simp only [profileSum,KFCausalReciprocalWedgeLaplace.laplaceSum,exponentialProfile,
    Polynomial.eval_one,pow_zero,one_mul,mul_one,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : KFCausalReciprocalWedgeGeometry.chart α r (u^2+v^2) Y =
      gamma α r*((u:ℂ)^2+(v:ℂ)^2)+conj (gamma α r)*(Y:ℂ) := by
    simp [KFCausalReciprocalWedgeGeometry.chart,KFCausalReciprocalWedgeGeometry.gamma,gamma]
  rw [he]
  ring

theorem original_density (n : ℕ) (α β B : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (u v x Y : ℝ) :
    positiveDensity n α β w r c (fun _ => exponentialProfile (B:ℂ) 1 1) ((u,![v,x]),Y) =
      potential (x+fieldSlope r*v)*neutralWeight β B x*Real.exp ((8*β*r.im^2)*v^2)*
        ‖packet 0 (gamma α r) w (fun i => c i*(w i:ℂ)) ((u,v),Y)‖^2 := by
  unfold positiveDensity
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [profile_factor,norm_mul,mul_pow,Complex.norm_exp,← Real.exp_nat_mul]
  have he : 2*((B:ℂ)*KFCausalReciprocalNeutralKernel.neutral r v x).re=2*B*x := by
    simp [KFCausalReciprocalNeutralKernel.neutral,Complex.mul_re]
    ring
  norm_num only [Nat.cast_ofNat] at *
  rw [he]
  unfold KFCausalReciprocalNeutralLaplace.weight neutralWeight
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [show -2*β*x^2+8*β*r.im^2*v^2 = (-2*β*x^2)+((8*β*r.im^2)*v^2) by ring,
    Real.exp_add,Real.exp_add]
  ring

theorem original_energy (n : ℕ) (α β B : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (hβ : 0 < β) (hp : 0 < (gamma α r).re) (hw : ∀ i, 0 < w i)
    (hd : ∀ i, 8*β*r.im^2 < 2*(gamma α r).re*w i) :
    (∫ z, positiveDensity n α β w r c (fun _ => exponentialProfile (B:ℂ) 1 1) z ∂jointMeasure) =
      energy β B (fieldSlope r) (gamma α r) (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) := by
  have hre : 2*(gamma α r).re=α*KFCausalReciprocalGaussianCoordinates.area r := by
    simp [gamma,KFCausalReciprocalGaussianCoordinates.area,pow_two,Complex.mul_re,Complex.mul_im]
    ring
  have hf := KFCausalGaussianSourceJointKernel.family_integrable n α β w r
    (fun _ => (B:ℂ)) c hβ (fun i => by have hdi := hd i; rw [hre] at hdi; nlinarith)
  rw [KFCausalJointNeutralFourierIntegral.joint_integral_iterated _ hf]
  rw [show energy β B (fieldSlope r) (gamma α r) (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) =
      ∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ,
        density β B (fieldSlope r) (gamma α r) (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) ((u,v),Y) from
    KFCausalChargedProductFubini.integral_order _
      (KFCausalCommonRealGaussianEnergy.density_integrable β B (fieldSlope r) (gamma α r)
        (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) hβ hp hw hd)]
  simp only [original_density,integral_mul_const,density,neutralLine]

#print axioms profile_factor
#print axioms original_density
#print axioms original_energy
end
end UnifiedTheory.Audit.KFCausalOriginalCommonRealGaussianEnergy
