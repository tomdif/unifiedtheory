/- Scalar bounds for weighted charge averages. They retain both signs of the
matter tilt and control neutral velocity without cyclic-position invariance. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterNeutralShift
import UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterOrbitBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterNeutralShift
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p q_apply p_apply)
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergy (staticKinetic growingKinetic)
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds (phaseSize)
open UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds (phaseSize_nonnegative phaseSize_rotate shear_abs_bound)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)

theorem mean_mul_abs_bound (w f : ℝ → ℝ) (L : ℝ) (hw : Continuous w) (hf : Continuous f)
    (hw0 : ∀ θ, 0 ≤ w θ) (hb : ∀ θ, |f θ| ≤ L) :
    |mean (fun θ => w θ*f θ)| ≤ mean w*L := by
  have hlo := mean_mono (fun θ => w θ*(-L)) (fun θ => w θ*f θ)
    (hw.mul continuous_const) (hw.mul hf)
    (fun θ => mul_le_mul_of_nonneg_left (abs_le.mp (hb θ)).1 (hw0 θ))
  have hhi := mean_mono (fun θ => w θ*f θ) (fun θ => w θ*L)
    (hw.mul hf) (hw.mul continuous_const)
    (fun θ => mul_le_mul_of_nonneg_left (abs_le.mp (hb θ)).2 (hw0 θ))
  rw [mean_mul_const] at hlo hhi
  rw [mul_neg] at hlo
  exact abs_le.mpr ⟨hlo,hhi⟩

theorem distinguished_squares_bound (z : Phase) :
    (p (.inl 1) z)^2+(q (.inr 2) z)^2+(p (.inr 3) z)^2 ≤ phaseSize z := by
  unfold phaseSize staticKinetic growingKinetic
  nlinarith [sq_nonneg (p (.inr 1) z),sq_nonneg (q (.inl 0) z),
    sq_nonneg (p (.inr 2) z),sq_nonneg (q (.inl 1) z),
    sq_nonneg (p (.inl 0) z),sq_nonneg (q (.inr 1) z)]

theorem distinguished_abs_bounds (z : Phase) :
    |p (.inl 1) z| ≤ phaseSize z+1 ∧ |q (.inr 2) z| ≤ phaseSize z+1 ∧
      |p (.inr 3) z| ≤ phaseSize z+1 := by
  have h := distinguished_squares_bound z
  have hP := phaseSize_nonnegative z
  constructor
  · nlinarith [sq_abs (p (.inl 1) z),sq_nonneg (|p (.inl 1) z|-1),sq_nonneg (q (.inr 2) z),sq_nonneg (p (.inr 3) z)]
  constructor
  · nlinarith [sq_abs (q (.inr 2) z),sq_nonneg (|q (.inr 2) z|-1),sq_nonneg (p (.inl 1) z),sq_nonneg (p (.inr 3) z)]
  · nlinarith [sq_abs (p (.inr 3) z),sq_nonneg (|p (.inr 3) z|-1),sq_nonneg (p (.inl 1) z),sq_nonneg (q (.inr 2) z)]

theorem slope_abs_bound (θ : ℝ) (z : Phase) : |KFCausalClassicalMatterNeutralShift.slope θ z| ≤ 4*(phaseSize z+1) := by
  have hs : |scale| ≤ 1 := by nlinarith [scale_square,sq_abs scale,abs_nonneg scale]
  have hp := (distinguished_abs_bounds z).1
  have hq := (distinguished_abs_bounds z).2.1
  have hsin : |Real.sin θ*p (.inl 1) z| ≤ |p (.inl 1) z| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one θ)
  have hcos : |Real.cos θ*q (.inr 2) z| ≤ |q (.inr 2) z| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one θ)
  have ha := abs_add_le (Real.sin θ*p (.inl 1) z) (Real.cos θ*q (.inr 2) z)
  unfold KFCausalClassicalMatterNeutralShift.slope
  rw [abs_mul,abs_mul]
  norm_num only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith [abs_nonneg (Real.sin θ*p (.inl 1) z+Real.cos θ*q (.inr 2) z)]

theorem fieldValue_orbit_bound (θ : ℝ) (z : Phase) :
    |fieldValue (rotate θ z)| ≤ 4*(phaseSize z+1)+|q (.inr 3) z| := by
  have he : fieldValue (rotate θ z) = KFCausalClassicalMatterNeutralShift.slope θ z+q (.inr 3) z := by
    rw [fieldValue_rotate]
    simp only [KFCausalClassicalMatterNeutralShift.slope,q_apply,p_apply]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (slope_abs_bound θ z) le_rfl)

theorem neutralMean_abs_bound (m g κ C : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) (z : Phase) :
    |neutralMean m g κ C z| ≤ weightedMean m g κ C z*(4*(phaseSize z+1)) := by
  exact mean_mul_abs_bound _ _ _
    (by have hp := potential_continuous m g κ z; have hs := shear_continuous z; fun_prop)
    (slope_continuous z)
    (fun θ => mul_nonneg (hκ.trans (potential_ge_vacuum m g κ hm hg _)) (Real.exp_pos _).le)
    (fun θ => slope_abs_bound θ z)

theorem weightedTilt_abs_bound (m g κ C : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (hC : 0 < C) (z : Phase) :
    |weightedTilt m g κ C z| ≤ weightedMean m g κ C z*(2*phaseSize z/C) := by
  have h := mean_mul_abs_bound
    (fun θ => potential m g κ (rotate θ z)*Real.exp (shear (rotate θ z)/C))
    (fun θ => shear (rotate θ z)/C) (2*phaseSize z/C)
    (by have hp := potential_continuous m g κ z; have hs := shear_continuous z; fun_prop)
    ((shear_continuous z).div_const C)
    (fun θ => mul_nonneg (hκ.trans (potential_ge_vacuum m g κ hm hg _)) (Real.exp_pos _).le)
    (fun θ => by
      rw [abs_div,abs_of_pos hC]
      apply div_le_div_of_nonneg_right _ hC.le
      simpa only [phaseSize_rotate] using shear_abs_bound (rotate θ z))
  simpa only [weightedTilt,weightedMean,mul_assoc,mul_comm,mul_left_comm] using h

def potentialEnvelope (m g κ P N : ℝ) : ℝ :=
  κ+(m/2)*(4*(P+1)+N)^2+(g/4)*(4*(P+1)+N)^4

theorem potential_orbit_upper (m g κ : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (θ : ℝ) (z : Phase) :
    potential m g κ (rotate θ z) ≤ potentialEnvelope m g κ (phaseSize z) |q (.inr 3) z| := by
  have h := fieldValue_orbit_bound θ z
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have h4 := pow_le_pow_left₀ (abs_nonneg _) h 4
  rw [sq_abs] at h2
  have hp4 : (fieldValue (rotate θ z))^4 = ((fieldValue (rotate θ z))^2)^2 := by ring
  rw [pow_abs,hp4,abs_of_nonneg (sq_nonneg _)] at h4
  unfold potential potentialEnvelope
  nlinarith [mul_le_mul_of_nonneg_left h2 (div_nonneg hm (by norm_num : (0:ℝ) ≤ 2)),
    mul_le_mul_of_nonneg_left h4 (div_nonneg hg (by norm_num : (0:ℝ) ≤ 4))]

theorem weightedMean_upper (m g κ C : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (hC : 0 < C) (z : Phase) :
    weightedMean m g κ C z ≤ potentialEnvelope m g κ (phaseSize z) |q (.inr 3) z| *
      Real.exp (2*phaseSize z/C) := by
  have hV : 0 ≤ potentialEnvelope m g κ (phaseSize z) |q (.inr 3) z| := by
    unfold potentialEnvelope
    positivity
  have h := mean_mono (fun θ => potential m g κ (rotate θ z)*Real.exp (shear (rotate θ z)/C))
    (fun _ => potentialEnvelope m g κ (phaseSize z) |q (.inr 3) z| *Real.exp (2*phaseSize z/C))
    (by have hp := potential_continuous m g κ z; have hs := shear_continuous z; fun_prop) continuous_const
    (fun θ => mul_le_mul (potential_orbit_upper m g κ hm hg θ z)
      (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
        (by simpa only [phaseSize_rotate] using (le_abs_self (shear (rotate θ z))).trans (shear_abs_bound (rotate θ z))) hC.le))
      (Real.exp_pos _).le hV)
  simpa only [mean_const] using h

#print axioms mean_mul_abs_bound
#print axioms distinguished_squares_bound
#print axioms distinguished_abs_bounds
#print axioms slope_abs_bound
#print axioms fieldValue_orbit_bound
#print axioms neutralMean_abs_bound
#print axioms weightedTilt_abs_bound
#print axioms potential_orbit_upper
#print axioms weightedMean_upper

end
end UnifiedTheory.Audit.KFCausalClassicalMatterOrbitBounds
