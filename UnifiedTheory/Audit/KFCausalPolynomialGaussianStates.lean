/- Physical coordinate powers times a sourced Gaussian are exactly
normalized source-circle coefficients in L2, at every natural degree.
These are physical coordinates, before the ordered complex clock shift. -/
import UnifiedTheory.Audit.KFCausalSourceCircleCoefficients
import UnifiedTheory.Audit.KFCausalL2IntegralRepresentative
import UnifiedTheory.Audit.KFCausalGaussianAllRadiusMoments
import UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalPolynomialGaussianStates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalSourceCircleCoefficients
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceSize sourceConstant)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (linearSource)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (physicalProfile_curve_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum (profileState profileState_coe)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative (configuration_product_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalGaussianAllRadiusMoments (gaussian_power_memLp)

def circleSource (b : Fin 5 → ℂ) (i : Fin 5) (θ : ℝ) : Fin 5 → ℂ :=
  fun j => b j+if j=i then circle θ else 0

def sourceBound (b : Fin 5 → ℂ) : ℝ := ∑ j, (‖b j‖+1)^2

theorem circleSource_continuous (b : Fin 5 → ℂ) (i : Fin 5) :
    Continuous (circleSource b i) := by
  apply continuous_pi
  intro j
  by_cases hj : j=i
  · simpa only [circleSource,if_pos hj] using continuous_const.add circle_continuous
  · simp only [circleSource,if_neg hj,add_zero]
    exact continuous_const

theorem circleSource_bound (b : Fin 5 → ℂ) (i : Fin 5) (θ : ℝ) :
    sourceSize (circleSource b i θ) ≤ sourceBound b := by
  apply Finset.sum_le_sum
  intro j _
  have hn : ‖circleSource b i θ j‖ ≤ ‖b j‖+1 := by
    unfold circleSource
    by_cases hj : j=i
    · simpa only [if_pos hj,circle_norm] using norm_add_le (b j) (circle θ)
    · simp only [if_neg hj,add_zero]
      linarith
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem linearSource_circle (b : Fin 5 → ℂ) (i : Fin 5) (θ : ℝ) (x : Transverse) :
    linearSource (circleSource b i θ) x = linearSource b x+circle θ*(x i:ℂ) := by
  simp only [linearSource,circleSource,add_mul,Finset.sum_add_distrib,ite_mul,zero_mul]
  simp

theorem circleProfile (p α β : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ) (i : Fin 5)
    (n : ℕ) (θ : ℝ) (x : Configuration) :
    physicalProfile (weight n θ) p α β (circleSource b i θ) g x =
      (weight n θ*Complex.exp ((x.2 i:ℂ)*circle θ))*physicalProfile 1 p α β b g x := by
  simp only [physicalProfile,clockMultiplier,sourcedPacket,linearSource_circle,Complex.exp_add,one_mul]
  rw [mul_comm (circle θ) (x.2 i:ℂ)]
  ring

theorem packet_power_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (i : Fin 5) (n : ℕ) :
    MemLp (fun x : Transverse => (x i:ℂ)^n*sourcedPacket α β b x) 2 volume := by
  have hc : Continuous (fun x : Transverse => (x i:ℂ)^n*sourcedPacket α β b x) :=
    ((Complex.continuous_ofReal.comp (continuous_apply i)).pow n).mul (sourcedPacket_continuous α β b)
  apply ((gaussian_power_memLp (α/2) (β/2) (by positivity) (by positivity) i n).const_mul
    (Real.exp (sourceConstant α β b/2):ℂ)).of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  have hm := mul_le_mul_of_nonneg_left (sourcedPacket_bound α β hα hβ hw b x)
    (norm_nonneg ((x i:ℂ)^n))
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_left_comm] using hm

def polynomialProfile (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ)
    (i : Fin 5) (n : ℕ) (x : Configuration) : ℂ :=
  (x.2 i:ℂ)^n*physicalProfile C p α β b g x

theorem polynomialProfile_memLp (C : ℂ) (p α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume) (i : Fin 5) (n : ℕ) :
    MemLp (polynomialProfile C p α β b g i n) 2 volume := by
  convert configuration_product_memLp _ _ (clockMultiplier_memLp C p g hg)
    (packet_power_memLp α β hα hβ hw b i n) using 1
  funext x
  unfold polynomialProfile physicalProfile
  ring

def polynomialState (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (i : Fin 5) (n : ℕ) : Hilbert :=
  (polynomialProfile_memLp C p α β hα hβ hw b g hg i n).toLp
    (polynomialProfile C p α β b g i n)

theorem polynomialState_coe (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (i : Fin 5) (n : ℕ) :
    polynomialState α β hα hβ hw C p b g hg i n =ᵐ[volume] polynomialProfile C p α β b g i n :=
  (polynomialProfile_memLp C p α β hα hβ hw b g hg i n).coeFn_toLp

theorem coefficient_eq (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (hgc : Continuous g) (i : Fin 5) (n : ℕ) :
    (C*normalization n) •
      (∫ θ, profileState α β hα hβ hw (weight n θ) p (circleSource b i θ) g hg ∂angleMeasure) =
      polynomialState α β hα hβ hw C p b g hg i n := by
  let U : ℝ → Hilbert := fun θ =>
    (C*normalization n) • profileState α β hα hβ hw (weight n θ) p (circleSource b i θ) g hg
  let F : ℝ → Configuration → ℂ := fun θ x =>
    (C*normalization n)*(weight n θ*Complex.exp ((x.2 i:ℂ)*circle θ))*
      physicalProfile 1 p α β b g x
  have hu : Continuous U := continuous_const.smul
    (physicalProfile_curve_continuous α β (sourceBound b) hα hβ hw
      (weight n) (fun _ => p) (circleSource b i) g hg
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (circleSource_bound b i))
  have hf : Continuous (fun z : ℝ × Configuration => F z.1 z.2) := by
    have hc := circle_continuous
    have hn := weight_continuous n
    unfold F physicalProfile clockMultiplier sourcedPacket linearSource
      KFCausalClockFloorCoherentStrip.clockPhase physicalGaussian
    fun_prop
  have hr (θ : ℝ) : U θ =ᵐ[volume] F θ := by
    filter_upwards [Lp.coeFn_smul (C*normalization n)
      (profileState α β hα hβ hw (weight n θ) p (circleSource b i θ) g hg),
      profileState_coe α β hα hβ hw (weight n θ) p (circleSource b i θ) g hg] with x hx hy
    change ((C*normalization n) • profileState α β hα hβ hw (weight n θ) p (circleSource b i θ) g hg) x = _ 
    rw [hx,Pi.smul_apply,hy,smul_eq_mul,circleProfile]
    exact (mul_assoc _ _ _).symm
  have hm (x : Configuration) : (∫ θ, F θ x ∂angleMeasure) = polynomialProfile C p α β b g i n x := by
    dsimp only [F]
    rw [integral_mul_const,integral_const_mul]
    have he := exponential_coefficient n (x.2 i:ℂ)
    calc
      _ = C*(normalization n*(∫ θ, weight n θ*Complex.exp ((x.2 i:ℂ)*circle θ) ∂angleMeasure))*
          physicalProfile 1 p α β b g x := by ring
      _ = _ := by
        rw [he]
        unfold polynomialProfile physicalProfile clockMultiplier
        ring
  have he := KFCausalL2IntegralRepresentative.integral_coe U F
    (polynomialProfile C p α β b g i n) hu hf hr
    (polynomialProfile_memLp C p α β hα hβ hw b g hg i n) hm
  have hi : (∫ θ, U θ ∂angleMeasure) =
      (C*normalization n) • (∫ θ, profileState α β hα hβ hw (weight n θ) p
        (circleSource b i θ) g hg ∂angleMeasure) := integral_smul _ _
  apply Lp.ext
  exact (hi ▸ he).trans (polynomialState_coe α β hα hβ hw C p b g hg i n).symm

#print axioms circleSource_continuous
#print axioms circleSource_bound
#print axioms linearSource_circle
#print axioms circleProfile
#print axioms packet_power_memLp
#print axioms polynomialProfile_memLp
#print axioms polynomialState_coe
#print axioms coefficient_eq
end
end UnifiedTheory.Audit.KFCausalPolynomialGaussianStates
