/- The reference Gaussian on active interior links has its exact Haar
partition and a polynomial inverse bound. The interacting law is not factored. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchLocalEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchGaussianPartition
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonPatchConditioning
open WilsonPatchNeighborhood WilsonPatchLocalEnergy
open scoped Quaternion

local instance haar_right : QuaternionHaarDoubling.haar.IsMulRightInvariant := by
  exact RegulatedGauge.compactHaar_right Q

theorem centered_gaussian (s : ℝ) (b : Q) :
    (∫ q, Real.exp (-s * ‖(q : ℍ) - (b : ℍ)‖ ^ 2) ∂QuaternionHaarDoubling.haar) =
      SU2GaussianMass.mass s := by
  have hh := integral_mul_right_eq_self (μ := QuaternionHaarDoubling.haar)
    (SU2GaussianMass.weight s) b⁻¹
  simpa only [SU2GaussianMass.weight, QuaternionChordMidpoint.rotation_chord] using hh

def gaussianCap (β : ℝ) : ℝ := SU2GaussianMass.cap (36 * (β + 1))

theorem gaussianCap_positive (β : ℝ) (hβ : 0 ≤ β) : 0 < gaussianCap β := by
  have hh := SU2GaussianMass.mass_cap_lower (36 * (β + 1)) (by linarith)
  have hm := SU2GaussianMass.mass_pos (36 * (β + 1))
  change 0 < SU2GaussianMass.cap (36 * (β + 1))
  nlinarith

theorem gaussianCap_formula (β : ℝ) :
    gaussianCap β = (864 * SU2ScalarTilt.partition 0 / Real.Gamma (3 / 2)) *
      (β + 1) * Real.sqrt (β + 1) := by
  unfold gaussianCap SU2GaussianMass.cap
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 36)]
  norm_num
  ring

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

theorem distance_inside (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (x : Inside n S) : distanceSq n v₀ (insert n S v₀ x) =
      ∑ e : {e : SpatialVertex n × Fin 3 // e ∈ S}, ‖(x e : ℍ) - (v₀ e.1 : ℍ)‖ ^ 2 := by
  calc
    _ = ∑ e ∈ S, ‖(v₀ e : ℍ) - (insert n S v₀ x e : ℍ)‖ ^ 2 :=
      distance_supported n S v₀ _ (insert_outside n S v₀ x)
    _ = ∑ e : {e : SpatialVertex n × Fin 3 // e ∈ S},
        ‖(v₀ e.1 : ℍ) - (insert n S v₀ x e.1 : ℍ)‖ ^ 2 :=
      Finset.sum_subtype (p := fun e : SpatialVertex n × Fin 3 => e ∈ S)
        S (fun _ => Iff.rfl) (fun e => ‖(v₀ e : ℍ) - (insert n S v₀ x e : ℍ)‖ ^ 2)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      have he : insert n S v₀ x e.1 = x e := WilsonBlockMarginal.assemble_inside S _ e.1 e.2
      rw [he, norm_sub_rev]

/-- Only this reference Gaussian factors; the Wilson action retains all
incident plaquettes and every crossing interaction. -/
theorem gaussian_integral (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (s : ℝ) :
    (∫ x, Real.exp (-s * distanceSq n v₀ (insert n S v₀ x)) ∂haar n S) =
      (SU2GaussianMass.mass s) ^ S.card := by
  simp_rw [distance_inside, Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod
    (μ := fun _ : {e : SpatialVertex n × Fin 3 // e ∈ S} => QuaternionHaarDoubling.haar)
    (fun e (q : Q) => Real.exp (-s * ‖(q : ℍ) - (v₀ e.1 : ℍ)‖ ^ 2))]
  simp only [centered_gaussian, Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- The entropy cost is per active link, with no exterior-volume term. -/
theorem gaussian_lower (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (β : ℝ) (hβ : 0 ≤ β) :
    Real.exp (-((S.card : ℝ) * Real.log (gaussianCap β))) ≤
      ∫ x, Real.exp (-(36 * β) * distanceSq n v₀ (insert n S v₀ x)) ∂haar n S := by
  rw [gaussian_integral, Real.exp_neg, Real.exp_nat_mul,
    Real.exp_log (gaussianCap_positive β hβ)]
  have hm := SU2GaussianMass.mass_antitone (show 36 * β ≤ 36 * (β + 1) by linarith)
  have hc := SU2GaussianMass.mass_cap_lower (36 * (β + 1)) (by linarith)
  have hp := gaussianCap_positive β hβ
  have hh : 1 ≤ SU2GaussianMass.mass (36 * β) * gaussianCap β := by
    have hmul := mul_le_mul_of_nonneg_right hm hp.le
    change _ * gaussianCap β ≤ _ * gaussianCap β at hmul
    exact hc.trans hmul
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hh S.card
  rw [one_pow, mul_pow] at hpow
  rw [← one_div]
  exact (div_le_iff₀ (pow_pos hp _)).mpr hpow

end
end UnifiedTheory.Clay.YangMills.WilsonPatchGaussianPartition
