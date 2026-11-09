/- A uniform positive overlap on normalized finite-dimensional charge
profiles. The constant is obtained from compactness, not supplied as a premise. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterHarmonics
import UnifiedTheory.Audit.KFCausalBoundedAngleExponential
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterOverlap
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClassicalMatterHarmonics
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalBoundedAngleExponential (Profiles meanL meanL_apply sinAngle cosAngle harmonics)
open scoped BoundedContinuousFunction

def firstProfile (a : Fin 3 → ℝ) : Profiles :=
  a 0 • (1:Profiles)+a 1 • cosAngle+a 2 • sinAngle

def secondProfile (b : Fin 4 → ℝ) : Profiles :=
  harmonics (b 0) (b 1) (b 2) (b 3)

theorem firstProfile_apply (a : Fin 3 → ℝ) (θ : ℝ) :
    firstProfile a θ = first a (2*Real.pi*θ) := by
  change a 0*1+a 1*Real.cos (2*Real.pi*θ)+a 2*Real.sin (2*Real.pi*θ) = _
  simp only [first,mul_one]

theorem secondProfile_apply (b : Fin 4 → ℝ) (θ : ℝ) :
    secondProfile b θ = second b (2*Real.pi*θ) := rfl

def overlap (k : ℕ) (x : (Fin 3 → ℝ) × (Fin 4 → ℝ)) : ℝ :=
  meanL (firstProfile x.1^(2*k)*(secondProfile x.2 ⊔ 0))

theorem overlap_continuous (k : ℕ) : Continuous (overlap k) := by
  unfold overlap
  apply meanL.continuous.comp
  unfold firstProfile secondProfile harmonics
  fun_prop

theorem overlap_eq_mean (k : ℕ) (a : Fin 3 → ℝ) (b : Fin 4 → ℝ) :
    overlap k (a,b) = mean (fun θ => first a θ^(2*k)*max (second b θ) 0) := by
  rw [mean_eq_angle,overlap,meanL_apply]
  congr 1
  funext θ
  change (firstProfile a θ)^(2*k)*max (secondProfile b θ) 0 = _
  rw [firstProfile_apply,secondProfile_apply]

theorem exists_uniform_overlap (k : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : Fin 3 → ℝ) (b : Fin 4 → ℝ),
      ‖a‖ = 1 → ‖b‖ = 1 → c ≤ overlap k (a,b) := by
  let K := Metric.sphere (0 : Fin 3 → ℝ) 1 ×ˢ Metric.sphere (0 : Fin 4 → ℝ) 1
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  obtain ⟨c,hc,hbound⟩ := hK.exists_forall_le' (overlap_continuous k).continuousOn (a := (0:ℝ)) (by
    intro x hx
    rw [overlap_eq_mean]
    apply overlap_positive
    · intro he
      have ha : ‖x.1‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx.1
      simp only [he,norm_zero] at ha
      norm_num at ha
    · intro he
      have hb : ‖x.2‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx.2
      simp only [he,norm_zero] at hb
      norm_num at hb)
  refine ⟨c,hc,?_⟩
  intro a b ha hb
  exact hbound (a,b) ⟨by simpa only [Metric.mem_sphere,dist_zero_right] using ha,
    by simpa only [Metric.mem_sphere,dist_zero_right] using hb⟩

theorem first_smul (r : ℝ) (a : Fin 3 → ℝ) (θ : ℝ) :
    first (r • a) θ = r*first a θ := by
  simp only [first,Pi.smul_apply,smul_eq_mul]
  ring

theorem second_smul (r : ℝ) (b : Fin 4 → ℝ) (θ : ℝ) :
    second (r • b) θ = r*second b θ := by
  simp only [second,Pi.smul_apply,smul_eq_mul]
  ring

theorem first_abs_bound (a : Fin 3 → ℝ) (θ : ℝ) :
    |first a θ| ≤ 3*‖a‖ := by
  have h (i : Fin 3) : |a i| ≤ ‖a‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm a i
  have hc : |a 1*Real.cos θ| ≤ ‖a‖ :=
    (by rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one θ)).trans (h 1))
  have hs : |a 2*Real.sin θ| ≤ ‖a‖ :=
    (by rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one θ)).trans (h 2))
  unfold first
  exact (abs_add_le _ _).trans (by linarith [abs_add_le (a 0) (a 1*Real.cos θ),h 0])

theorem second_abs_bound (b : Fin 4 → ℝ) (θ : ℝ) :
    |second b θ| ≤ 5*‖b‖ := by
  have h (i : Fin 4) : |b i| ≤ ‖b‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm b i
  have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hcc : |Real.cos θ^2| ≤ 1 := by rw [abs_pow]; nlinarith [abs_nonneg (Real.cos θ)]
  have hss : |Real.sin θ^2| ≤ 1 := by rw [abs_pow]; nlinarith [abs_nonneg (Real.sin θ)]
  have hdiff : |Real.cos θ^2-Real.sin θ^2| ≤ 2 := by
    have hh := abs_add_le (Real.cos θ^2) (-Real.sin θ^2)
    rw [abs_neg,← sub_eq_add_neg] at hh
    linarith
  have hprod : |Real.sin θ*Real.cos θ| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hc).trans hs
  have h0 : |b 0*(Real.cos θ^2-Real.sin θ^2)| ≤ 2*‖b‖ := by
    rw [abs_mul]
    nlinarith [mul_le_mul (h 0) hdiff (abs_nonneg _) (norm_nonneg b)]
  have h1 : |b 1*(Real.sin θ*Real.cos θ)| ≤ ‖b‖ := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hprod).trans (h 1)
  have h2 : |b 2*Real.sin θ| ≤ ‖b‖ := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hs).trans (h 2)
  have h3 : |b 3*Real.cos θ| ≤ ‖b‖ := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hc).trans (h 3)
  unfold second
  exact (abs_add_le _ _).trans (by
    linarith [abs_add_le (b 0*(Real.cos θ^2-Real.sin θ^2)+b 1*(Real.sin θ*Real.cos θ)) (b 2*Real.sin θ),
      abs_add_le (b 0*(Real.cos θ^2-Real.sin θ^2)) (b 1*(Real.sin θ*Real.cos θ))])

#print axioms firstProfile_apply
#print axioms secondProfile_apply
#print axioms overlap_continuous
#print axioms overlap_eq_mean
#print axioms exists_uniform_overlap
#print axioms first_smul
#print axioms second_smul
#print axioms first_abs_bound
#print axioms second_abs_bound

end
end UnifiedTheory.Audit.KFCausalClassicalMatterOverlap

