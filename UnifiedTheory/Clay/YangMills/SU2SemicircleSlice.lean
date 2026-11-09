/- Actual semicircle density of the quaternion Haar real coordinate.
The planar change of variables, its support, radial factor, angular cosine
substitution, and Fubini integrability are proved from concrete integrals.
The final first-coordinate formula has no density premise. It closes that
geometric input to the finite-cutoff source approximation, without asserting
an interacting continuum limit or a physical coupling trajectory. -/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import UnifiedTheory.Clay.YangMills.SU2HaarSlice
import UnifiedTheory.Clay.YangMills.SU2HaarScalarBridge
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2SemicircleSlice
noncomputable section
open MeasureTheory Set Real

/-- The angular sine-square weight becomes the semicircle density under
`u=cos θ`, including both endpoints through the interval integral theorem. -/
theorem angular_cosine (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ^2 * F (Real.cos θ)) =
      ∫ u in (-1 : ℝ)..1, Real.sqrt (1-u^2) * F u := by
  have hc : Continuous (fun u : ℝ => Real.sqrt (1-u^2) * F u) := by fun_prop
  have h := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := Real.pi) (f := Real.cos) (f' := fun θ => -Real.sin θ)
    (g := fun u : ℝ => Real.sqrt (1-u^2) * F u)
    (fun θ _ => Real.hasDerivAt_cos θ) Real.continuous_sin.neg.continuousOn hc
  have he : (∫ θ in (0 : ℝ)..Real.pi,
      ((fun u : ℝ => Real.sqrt (1-u^2) * F u) ∘ Real.cos) θ * (-Real.sin θ)) =
      -(∫ θ in (0 : ℝ)..Real.pi, Real.sin θ^2 * F (Real.cos θ)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθ' : θ ∈ Icc 0 Real.pi := by
      simpa only [uIcc_of_le Real.pi_pos.le] using hθ
    dsimp only [Function.comp_apply]
    rw [← Real.sin_eq_sqrt_one_sub_cos_sq hθ'.1 hθ'.2]
    ring
  rw [he, Real.cos_zero, Real.cos_pi,
    intervalIntegral.integral_symm (a := (-1 : ℝ)) (b := (1 : ℝ))] at h
  linarith

/-- The actual upper-half unit-disk integrand, extended by zero. -/
def planeIntegrand (F : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 < p.2 then p.2^2 * (if Real.sqrt (p.1^2 + p.2^2)<1 then
    F (p.1 / Real.sqrt (p.1^2 + p.2^2)) else 0) else 0

def polarIntegrand (F : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1^3 * Real.sin p.2^2 * F (Real.cos p.2)

def polarDomain : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) Real.pi

theorem polar_radius (ρ θ : ℝ) (hρ : 0 ≤ ρ) :
    Real.sqrt ((ρ * Real.cos θ)^2 + (ρ * Real.sin θ)^2) = ρ := by
  have he : (ρ * Real.cos θ)^2 + (ρ * Real.sin θ)^2 = ρ^2 := by
    nlinarith [Real.cos_sq_add_sin_sq θ]
  rw [he, Real.sqrt_sq hρ]

theorem polarDomain_subset : polarDomain ⊆ polarCoord.target := by
  intro p hp
  exact ⟨hp.1.1, lt_trans (neg_neg_of_pos Real.pi_pos) hp.2.1, hp.2.2⟩

theorem transformed_inside (F : ℝ → ℝ) (p : ℝ × ℝ) (hp : p ∈ polarDomain) :
    p.1 * planeIntegrand F (polarCoord.symm p) = polarIntegrand F p := by
  have hs : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2
  simp only [planeIntegrand, polarCoord_symm_apply, if_pos (mul_pos hp.1.1 hs),
    polar_radius _ _ hp.1.1.le, if_pos hp.1.2]
  have hc : p.1 * Real.cos p.2 / p.1 = Real.cos p.2 := by field_simp [hp.1.1.ne']
  rw [hc]
  unfold polarIntegrand
  ring

/-- Polar points outside the positive-angle unit-radius rectangle contribute zero. -/
theorem transformed_outside (F : ℝ → ℝ) (p : ℝ × ℝ)
    (hp : p ∈ polarCoord.target \ polarDomain) :
    p.1 * planeIntegrand F (polarCoord.symm p) = 0 := by
  have hρ : 0 < p.1 := hp.1.1
  have hθ : p.2 ∈ Ioo (-Real.pi) Real.pi := hp.1.2
  by_cases hr : p.1 < 1
  · have hθ0 : p.2 ≤ 0 := by
      by_contra hn
      exact hp.2 ⟨⟨hρ,hr⟩, ⟨lt_of_not_ge hn,hθ.2⟩⟩
    have hs : Real.sin p.2 ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le hθ0 hθ.1.le
    have hy : ¬0 < p.1 * Real.sin p.2 := not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hρ.le hs)
    simp only [planeIntegrand, polarCoord_symm_apply, if_neg hy, mul_zero]
  · simp only [planeIntegrand, polarCoord_symm_apply, polar_radius _ _ hρ.le, if_neg hr,
      mul_zero, ite_self]

theorem radial_integral : (∫ ρ in Ioo (0 : ℝ) 1, ρ^3) = 1 / 4 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num [integral_pow]

theorem angular_set_integral (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ θ in Ioo (0 : ℝ) Real.pi, Real.sin θ^2 * F (Real.cos θ)) =
      ∫ u in (-1 : ℝ)..1, Real.sqrt (1-u^2) * F u := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le Real.pi_pos.le]
  exact angular_cosine F hF

/-- Exact planar polar integration with its radial Jacobian and factor `1/4`. -/
theorem plane_integral (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ p : ℝ × ℝ, planeIntegrand F p) =
      (1 / 4) * (∫ u in (-1 : ℝ)..1, Real.sqrt (1-u^2) * F u) := by
  calc
    _ = ∫ p in polarCoord.target, p.1 * planeIntegrand F (polarCoord.symm p) := by
      simpa only [smul_eq_mul] using (integral_comp_polarCoord_symm (planeIntegrand F)).symm
    _ = ∫ p in polarDomain, p.1 * planeIntegrand F (polarCoord.symm p) :=
      setIntegral_eq_of_subset_of_forall_diff_eq_zero polarCoord.open_target.measurableSet
        polarDomain_subset (transformed_outside F)
    _ = ∫ p in polarDomain, polarIntegrand F p := by
      apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      exact transformed_inside F
    _ = (∫ ρ in Ioo (0 : ℝ) 1, ρ^3) *
        (∫ θ in Ioo (0 : ℝ) Real.pi, Real.sin θ^2 * F (Real.cos θ)) := by
      simpa only [polarDomain, polarIntegrand, mul_assoc] using
        (setIntegral_prod_mul (fun ρ : ℝ => ρ^3)
          (fun θ : ℝ => Real.sin θ^2 * F (Real.cos θ)) (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) Real.pi))
    _ = _ := by rw [radial_integral, angular_set_integral F hF]

theorem halfplane_integral (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ p : ℝ × ℝ in univ ×ˢ Ioi (0 : ℝ),
      p.2^2 * (if Real.sqrt (p.1^2 + p.2^2)<1 then
        F (p.1 / Real.sqrt (p.1^2 + p.2^2)) else 0)) =
      (1 / 4) * (∫ u in (-1 : ℝ)..1, Real.sqrt (1-u^2) * F u) := by
  rw [← integral_indicator (MeasurableSet.univ.prod measurableSet_Ioi)]
  convert plane_integral F hF using 1
  apply integral_congr_ae
  filter_upwards with p
  simp [planeIntegrand, Set.indicator]

/-- The actual bounded-support integrability theorem justifies Fubini. -/
theorem iterated_integral (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ t : ℝ, ∫ r in Ioi (0 : ℝ), r^2 * SU2HaarSlice.radialBallTest F t r) =
      (1 / 4) * (∫ u in (-1 : ℝ)..1, Real.sqrt (1-u^2) * F u) := by
  have h := halfplane_integral F hF
  change (∫ p : ℝ × ℝ in univ ×ˢ Ioi (0 : ℝ),
    p.2^2 * SU2HaarSlice.radialBallTest F p.1 p.2) = _ at h
  rw [Measure.volume_eq_prod ℝ ℝ,
    setIntegral_prod _ (SU2HaarSlice.integrableOn_planarBallTest F hF),
    Measure.restrict_univ] at h
  exact h

/-- Actual normalized quaternion Haar integration has the semicircle density. -/
theorem haar_semicircle (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ q : SU2QuaternionEquivalence.UnitQuaternion,
        F (q : Quaternion ℝ).re ∂SU2HaarTilt.haar) =
      (2 / Real.pi) * SU2ScalarTilt.semicircleIntegral 0 F := by
  rw [SU2HaarSlice.compactHaar_integral_radial F hF,
    integral_const_mul, iterated_integral F hF]
  have he : (∫ u in (-1 : ℝ)..1, Real.sqrt (1-u^2) * F u) =
      SU2ScalarTilt.semicircleIntegral 0 F := by
    simp [SU2ScalarTilt.semicircleIntegral, SU2ScalarTilt.weight]
  rw [he]
  field_simp [Real.pi_ne_zero]

/-- The previously explicit geometric obligation is discharged, using
normalization at the constant test rather than an assumed density formula. -/
theorem firstCoordinateFormula : SU2HaarScalarBridge.FirstCoordinateFormula := by
  intro F hF
  have hone := haar_semicircle (fun _ => 1) continuous_const
  have hone' : 1 = (2 / Real.pi) * SU2ScalarTilt.partition 0 := by
    simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
      smul_eq_mul, one_mul, SU2ScalarTilt.partition] using hone
  have hc : 2 / Real.pi = 1 / SU2ScalarTilt.partition 0 :=
    (eq_div_iff (SU2ScalarTilt.partition_pos 0).ne').2 hone'.symm
  rw [haar_semicircle F hF, hc]
  ring

end
end UnifiedTheory.Clay.YangMills.SU2SemicircleSlice
