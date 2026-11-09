/- A quantitative lower bound for the charge-averaged exponential tilt
of the actual second harmonic. This is a classical scalar estimate. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClassicalShearTiltGrowth
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)

def profile (θ : ℝ) : ℝ := (Real.cos θ^2-Real.sin θ^2)/2
def mass (a : ℝ) : ℝ := mean (fun θ => Real.exp (a*profile θ))
def moment (a : ℝ) : ℝ := mean (fun θ => profile θ*Real.exp (a*profile θ))

theorem profile_continuous : Continuous profile := by unfold profile; fun_prop

theorem profile_lower (θ : ℝ) : -(1/2:ℝ) ≤ profile θ := by
  have hs := Real.sin_sq_add_cos_sq θ
  unfold profile
  nlinarith [sq_nonneg (Real.cos θ)]

theorem profile_on_arc (θ : ℝ) (hθ : θ ∈ Icc 0 (Real.pi/6)) : (1/4:ℝ) ≤ profile θ := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ 2*θ by linarith [hθ.1])
    (show Real.pi/3 ≤ Real.pi by linarith [Real.pi_pos])
    (show 2*θ ≤ Real.pi/3 by linarith [hθ.2])
  rw [Real.cos_pi_div_three,Real.cos_two_mul] at hc
  have hs := Real.sin_sq_add_cos_sq θ
  unfold profile
  nlinarith

theorem centered_lower (a x : ℝ) (ha : 0 ≤ a) (hx : -(1/2:ℝ) ≤ x) :
    -(5/8:ℝ)*Real.exp (a/8) ≤ (x-1/8)*Real.exp (a*x) := by
  by_cases hc : (1/8:ℝ) ≤ x
  · exact le_trans (show -(5/8:ℝ)*Real.exp (a/8) ≤ 0 by nlinarith [Real.exp_pos (a/8)])
      (mul_nonneg (by linarith) (Real.exp_pos _).le)
  · have he : Real.exp (a*x) ≤ Real.exp (a/8) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc
      -(5/8:ℝ)*Real.exp (a/8) ≤ -(5/8:ℝ)*Real.exp (a*x) :=
        mul_le_mul_of_nonpos_left he (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem arc_mass : angleMeasure.real (Ioc 0 (1/12:ℝ)) = 1/12 := by
  have hs : Ioc (0:ℝ) (1/12) ∩ Ioc 0 1 = Ioc 0 (1/12) :=
    inter_eq_left.mpr (by intro x hx; exact ⟨hx.1,by linarith [hx.2]⟩)
  unfold Measure.real angleMeasure
  rw [Measure.restrict_apply measurableSet_Ioc,hs]
  norm_num

theorem centered_integral_lower (a : ℝ) (ha : 0 ≤ a) :
    (1/96:ℝ)*Real.exp (a/4)-(5/8:ℝ)*Real.exp (a/8) ≤ moment a-(1/8:ℝ)*mass a := by
  let v : ℝ → ℝ := fun θ => profile (2*Real.pi*θ)
  let H : ℝ → ℝ := fun θ => (v θ-1/8)*Real.exp (a*v θ)+(5/8:ℝ)*Real.exp (a/8)
  have hv : Continuous v := profile_continuous.comp (continuous_const.mul continuous_id)
  have hH : Continuous H := by dsimp [H]; fun_prop
  have hi : Integrable H angleMeasure := (continuous_angle_memLp H hH).integrable (by norm_num)
  have hn : 0 ≤ᵐ[angleMeasure] H := Filter.Eventually.of_forall fun θ => by
    have hl := centered_lower a (v θ) ha (profile_lower _)
    dsimp [H]
    linarith
  have hlocal : ∀ θ ∈ Ioc (0:ℝ) (1/12), (1/8:ℝ)*Real.exp (a/4) ≤ H θ := by
    intro θ hθ
    have hp : (1/4:ℝ) ≤ v θ := profile_on_arc _ ⟨by have ht := hθ.1.le; positivity,
      by nlinarith [hθ.2,Real.pi_pos]⟩
    have he : Real.exp (a/4) ≤ Real.exp (a*v θ) := Real.exp_le_exp.mpr (by nlinarith)
    have hm := mul_le_mul (show (1/8:ℝ) ≤ v θ-1/8 by linarith) he
      (Real.exp_pos _).le (by linarith : 0 ≤ v θ-1/8)
    dsimp [H]
    linarith [Real.exp_pos (a/8)]
  have hb : angleMeasure.real (Ioc 0 (1/12:ℝ))*((1/8:ℝ)*Real.exp (a/4)) ≤ ∫ θ, H θ ∂angleMeasure := by
    calc
      _ = ∫ θ in Ioc (0:ℝ) (1/12), (1/8:ℝ)*Real.exp (a/4) ∂angleMeasure := by
        rw [setIntegral_const,smul_eq_mul]
      _ ≤ ∫ θ in Ioc (0:ℝ) (1/12), H θ ∂angleMeasure :=
        integral_mono_ae (integrable_const _) hi.integrableOn
          ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hlocal))
      _ ≤ _ := setIntegral_le_integral hi hn
  rw [arc_mass] at hb
  have he : (∫ θ, H θ ∂angleMeasure) = moment a-(1/8:ℝ)*mass a+(5/8:ℝ)*Real.exp (a/8) := by
    have heI : Integrable (fun θ => Real.exp (a*v θ)) angleMeasure :=
      (continuous_angle_memLp _ (by fun_prop)).integrable (by norm_num)
    have hxI : Integrable (fun θ => v θ*Real.exp (a*v θ)) angleMeasure :=
      (continuous_angle_memLp _ (by fun_prop)).integrable (by norm_num)
    have hid : H = fun θ => v θ*Real.exp (a*v θ)-(1/8:ℝ)*Real.exp (a*v θ)+(5/8:ℝ)*Real.exp (a/8) := by
      funext θ; dsimp [H]; ring
    rw [hid]
    dsimp only
    have hadd := integral_add (hxI.sub (heI.const_mul (1/8:ℝ)))
      (integrable_const ((5/8:ℝ)*Real.exp (a/8)))
    have hsub := integral_sub hxI (heI.const_mul (1/8:ℝ))
    simp only [Pi.sub_apply] at hadd hsub
    rw [hadd,hsub,integral_const_mul,integral_const]
    simp only [probReal_univ,one_smul]
    rw [moment,mass,mean_eq_angle,mean_eq_angle]
  rw [he] at hb
  linarith

theorem moment_lower (a : ℝ) (ha : 480 ≤ a) : (1/8:ℝ)*mass a ≤ moment a := by
  have hc := centered_integral_lower a (by linarith)
  have he : 60 ≤ Real.exp (a/8) := by linarith [Real.add_one_le_exp (a/8)]
  have hsq : Real.exp (a/4) = Real.exp (a/8)*Real.exp (a/8) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsq] at hc
  have hp := mul_le_mul_of_nonneg_right he (Real.exp_pos (a/8)).le
  nlinarith

#print axioms profile_continuous
#print axioms profile_lower
#print axioms profile_on_arc
#print axioms centered_lower
#print axioms arc_mass
#print axioms centered_integral_lower
#print axioms moment_lower
end
end UnifiedTheory.Audit.KFCausalClassicalShearTiltGrowth
