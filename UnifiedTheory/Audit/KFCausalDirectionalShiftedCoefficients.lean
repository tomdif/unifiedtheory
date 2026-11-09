/- Exact source coefficients of the actual ordered potential factors.
Their L2 representatives are derived from the continuous graph-valued
source family, including field powers zero, one and two. -/
import UnifiedTheory.Audit.KFCausalDirectionalGaussianDomain
import UnifiedTheory.Audit.KFCausalL2ContinuousMean
import UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalDirectionalShiftedCoefficients
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalSourceCircleCoefficients
open KFCausalDirectionalGaussianCoefficients
open KFCausalRelativeGaussianDifferential (position exponent)
open KFCausalClockFloorRelativeShift (scale scale_smooth)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open KFCausalGaussianResponseDensities (amplitude)
open KFCausalSourcedResponseFactorBridge (index input_factor_density)
open KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorShiftedOutput (shift_bound)

def shiftedLinear (d : Transverse) (r : ℂ) (q : Transverse) : ℂ :=
  ∑ i, (d i:ℂ)*position r q i

theorem exponent_curve (α β : ℝ) (d : Transverse) (θ : ℝ) (r : ℂ) (q : Transverse) :
    exponent α β (sourceCurve d θ) r q =
      shiftedLinear d r q*circle θ+exponent α β 0 r q := by
  simp only [exponent,sourceCurve,shiftedLinear,Pi.zero_apply,zero_mul,
    Finset.sum_const_zero,zero_sub,Finset.sum_mul]
  have he : (∑ i : Fin 5, circle θ*(d i:ℂ)*position r q i) =
      ∑ i : Fin 5, (d i:ℂ)*position r q i*circle θ := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

theorem amplitude_curve (ε a α β p y : ℝ) (d : Transverse) (k : ℕ) (θ : ℝ)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (x : Configuration) :
    amplitude ε a α β p y (sourceCurve d θ) (weight k θ) l n x =
      (weight k θ*Complex.exp (shiftedLinear d (scale ε y x.1) x.2*circle θ))*
        amplitude ε a α β p y 0 1 l n x := by
  simp only [amplitude,KFCausalRelativeGaussianDifferential.profile,
    exponent_curve,Complex.exp_add,one_mul]
  ring

theorem shiftedLinear_continuous (ε y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (d : Transverse) :
    Continuous (fun x : Configuration => shiftedLinear d (scale ε y x.1) x.2) := by
  have hr := (scale_smooth ε y hε hy).continuous.comp
    (continuous_fst : Continuous (fun x : Configuration => x.1))
  have hp (i : Fin 5) : Continuous (fun x : Configuration => position (scale ε y x.1) x.2 i) := by
    unfold position
    split_ifs <;> fun_prop
  exact continuous_finset_sum _ (fun i _ => continuous_const.mul (hp i))

theorem amplitude_continuous (ε a α β p y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (C : ℂ) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    Continuous (amplitude ε a α β p y 0 C l n) := by
  have hr := (scale_smooth ε y hε hy).continuous.comp
    (continuous_fst : Continuous (fun x : Configuration => x.1))
  have hA := (clockAmplitude_smooth ε a p y hε hy).continuous.comp
    (continuous_fst : Continuous (fun x : Configuration => x.1))
  have hp (i : Fin 5) : Continuous (fun x : Configuration => position (scale ε y x.1) x.2 i) := by
    unfold position
    split_ifs <;> fun_prop
  have he : Continuous (fun x : Configuration => exponent α β 0 (scale ε y x.1) x.2) := by
    unfold exponent
    fun_prop
  exact ((Complex.continuous_ofReal.comp (l.continuous.comp continuous_snd)).pow n.val).mul
    (continuous_const.mul (hA.mul he.cexp))

def shiftedProfile (ε a α β p y : ℝ) (C : ℂ) (d : Transverse) (k : ℕ)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (x : Configuration) : ℂ :=
  (shiftedLinear d (scale ε y x.1) x.2)^k*amplitude ε a α β p y 0 C l n x

theorem shiftedProfile_continuous (ε a α β p y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (C : ℂ) (d : Transverse) (k : ℕ)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    Continuous (shiftedProfile ε a α β p y C d k l n) :=
  ((shiftedLinear_continuous ε y hε hy d).pow k).mul
    (amplitude_continuous ε a α β p y hε hy C l n)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h

theorem output_coe (C : ℂ) (p : ℝ) (d : Transverse) (k : ℕ) (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    KFCausalDirectionalGaussianDomain.output ε a h hε ha hh C p d k hb v l (index n) =ᵐ[volume]
      shiftedProfile ε a α β p (-h/2) C d k l n := by
  let U : ℝ → Hilbert := fun θ => (C*normalization k) •
    KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw
      (weight k θ) p (sourceCurve d θ) h hb v l (index n)
  let F : ℝ → Configuration → ℂ := fun θ x =>
    (C*normalization k)*(weight k θ*
      Complex.exp (shiftedLinear d (scale ε (-h/2) x.1) x.2*circle θ))*
      amplitude ε a α β p (-h/2) 0 1 l n x
  have hu : Continuous U := continuous_const.smul
    (KFCausalSourcedCurveDomain.factor_continuous ε a h hε ha hh hb |p| (sourceBound d)
      (weight k) (fun _ => p) (sourceCurve d) (weight_continuous k)
      continuous_const (sourceCurve_continuous d) (fun θ => (weight_norm k θ).le)
      (fun _ => le_rfl) (sourceCurve_bound d) v l (index n))
  have hf : Continuous (fun z : ℝ × Configuration => F z.1 z.2) := by
    have hd := (shiftedLinear_continuous ε (-h/2) hε (shift_bound ε h hb) d).comp
      (continuous_snd : Continuous (fun z : ℝ × Configuration => z.2))
    have hc := circle_continuous.comp (continuous_fst : Continuous (fun z : ℝ × Configuration => z.1))
    have hwc := (weight_continuous k).comp (continuous_fst : Continuous (fun z : ℝ × Configuration => z.1))
    have hAc := (amplitude_continuous ε a α β p (-h/2) hε (shift_bound ε h hb) 1 l n).comp
      (continuous_snd : Continuous (fun z : ℝ × Configuration => z.2))
    exact (continuous_const.mul (hwc.mul (hd.mul hc).cexp)).mul hAc
  have hr (θ : ℝ) : U θ =ᵐ[volume] F θ := by
    filter_upwards [Lp.coeFn_smul (C*normalization k)
      (KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw
        (weight k θ) p (sourceCurve d θ) h hb v l (index n)),
      input_factor_density ε a α β hε ha hα hβ hw (weight k θ) p
        (sourceCurve d θ) h hb v l n] with x hx hy
    change ((C*normalization k) •
      (KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw
        (weight k θ) p (sourceCurve d θ) h hb v l (index n))) x = _
    rw [hx,Pi.smul_apply,smul_eq_mul,hy,amplitude_curve]
    exact (mul_assoc _ _ _).symm
  have hm (x : Configuration) : (∫ θ, F θ x ∂angleMeasure) =
      shiftedProfile ε a α β p (-h/2) C d k l n x := by
    dsimp only [F]
    rw [integral_mul_const,integral_const_mul]
    have he := exponential_coefficient k (shiftedLinear d (scale ε (-h/2) x.1) x.2)
    calc
      _ = C*(normalization k*(∫ θ, weight k θ*
          Complex.exp (shiftedLinear d (scale ε (-h/2) x.1) x.2*circle θ) ∂angleMeasure))*
          amplitude ε a α β p (-h/2) 0 1 l n x := by ring
      _ = _ := by
        rw [he]
        unfold shiftedProfile amplitude
        ring
  have he := KFCausalL2ContinuousMean.integral_coe U F
    (shiftedProfile ε a α β p (-h/2) C d k l n) hu hf hr
    (shiftedProfile_continuous ε a α β p (-h/2) hε (shift_bound ε h hb) C d k l n) hm
  have hi : (∫ θ, U θ ∂angleMeasure) =
      KFCausalDirectionalGaussianDomain.output ε a h hε ha hh C p d k hb v l (index n) :=
    integral_smul _ _
  exact hi ▸ he

#print axioms exponent_curve
#print axioms amplitude_curve
#print axioms shiftedLinear_continuous
#print axioms amplitude_continuous
#print axioms shiftedProfile_continuous
#print axioms output_coe
end
end UnifiedTheory.Audit.KFCausalDirectionalShiftedCoefficients
