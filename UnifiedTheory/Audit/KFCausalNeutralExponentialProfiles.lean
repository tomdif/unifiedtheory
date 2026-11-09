/- Integrable neutral exponential-polynomial profiles and their finite
superpositions. The uniform growth constant does not depend on sources,
coefficients, polynomial degrees or the number of summands. -/
import UnifiedTheory.Audit.KFCausalNeutralProfileGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position exponent)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPolynomialOrbitEnvelope
open UnifiedTheory.Audit.KFCausalNeutralProfileMarginal
open UnifiedTheory.Audit.KFCausalNeutralProfileGrowth
open UnifiedTheory.Audit.KFCausalQuarticPlaneDomination (potential)

def neutralSource (b : ℂ) : Fin 5 → ℂ := ![0,0,0,0,b]
def exponentialProfile (b C : ℂ) (P : Polynomial ℂ) (z : ℂ) : ℂ :=
  C*Complex.exp (b*z)*P.eval z
def profileFactor (α β : ℝ) (r : ℂ) (F : ℂ → ℂ) (n : ℕ) (q : Transverse) : ℂ :=
  (pointField q:ℂ)^n*Complex.exp (exponent α β 0 r q)*F (position r q 4)

theorem neutralSource_exponent (α β : ℝ) (b r : ℂ) (q : Transverse) :
    exponent α β (neutralSource b) r q = exponent α β 0 r q+b*position r q 4 := by
  simp [exponent,neutralSource,Fin.sum_univ_succ]
  ring

theorem exponentialProfile_factor (α β ε y s : ℝ) (b C : ℂ)
    (P : Polynomial ℂ) (n : ℕ) (q : Transverse) :
    profileFactor α β (scale ε y s) (exponentialProfile b C P) n q =
      factor ε y α β (neutralSource b) C P pointField n q s := by
  simp only [profileFactor,exponentialProfile,factor,KFCausalPolynomialKernelResponse.transverse,
    KFCausalPolynomialKernelResponse.weight,KFCausalGaussianKernelResponse.transverse,
    KFCausalRelativeGaussianDifferential.profile,one_mul,neutralSource_exponent,Complex.exp_add]
  ring

theorem source_factor_memLp (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (b : Fin 5 → ℂ) (C : ℂ) (P : Polynomial ℂ) (n : ℕ) :
    MemLp (fun q : Transverse => factor ε y α β b C P pointField n q s) 2 volume := by
  have hc := KFCausalPolynomialKernelJointContinuity.factor_continuous ε y α β hε hy
    (fun _ : Transverse => s) (fun q => q) (fun _ => b) (fun _ => (1:ℂ))
    continuous_const continuous_id continuous_const continuous_const P pointField n
  have hm : MemLp (fun q : Transverse => factor ε y α β b 1 P pointField n q s) 2 volume := by
    apply (amplitudeEnvelope_memLp ε y α β hα hβ b P pointField n).of_le hc.aestronglyMeasurable
    filter_upwards [] with q
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (amplitudeEnvelope_nonnegative ε y α β b P pointField n q)] using
      factor_bound ε y α β hε hy hα hβ hw b b le_rfl 1 (by simp) P pointField n q s
  convert hm.const_mul C using 1
  funext q
  simp only [factor,KFCausalPolynomialKernelResponse.transverse,
    KFCausalGaussianKernelResponse.transverse,one_mul]
  ring

theorem profileEnergy_sum (α β : ℝ) (r : ℂ) (F : ℂ → ℂ) (q : Transverse) :
    profileEnergyDensity α β r F q =
      ‖profileFactor α β r F 0 q‖^2+
        (1/2:ℝ)*‖profileFactor α β r F 1 q‖^2+
        (1/4:ℝ)*‖profileFactor α β r F 2 q‖^2 := by
  simp only [profileEnergyDensity,potential,profileFactor,pow_zero,pow_one,
    norm_mul,norm_pow,norm_one,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem profileEnergy_integrable_of_factors (α β : ℝ) (r : ℂ) (F : ℂ → ℂ)
    (hF : ∀ n : ℕ, MemLp (profileFactor α β r F n) 2 volume) :
    Integrable (profileEnergyDensity α β r F) volume := by
  have hi (n : ℕ) : Integrable (fun q => ‖profileFactor α β r F n q‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (hF n).aestronglyMeasurable).mp (hF n)
  have he := funext (profileEnergy_sum α β r F)
  rw [he]
  exact ((hi 0).add ((hi 1).const_mul _)).add ((hi 2).const_mul _)

theorem exponentialProfile_factor_memLp (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (b C : ℂ) (P : Polynomial ℂ) (n : ℕ) :
    MemLp (profileFactor α β (scale ε y s) (exponentialProfile b C P) n) 2 volume := by
  change MemLp (fun q => profileFactor α β (scale ε y s) (exponentialProfile b C P) n q) 2 volume
  simp_rw [exponentialProfile_factor]
  exact source_factor_memLp α β ε y s hα hβ hw hε hy (neutralSource b) C P n

theorem exponentialProfile_integrable (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (b C : ℂ) (P : Polynomial ℂ) :
    Integrable (profileEnergyDensity α β (scale ε y s) (exponentialProfile b C P)) volume :=
  profileEnergy_integrable_of_factors α β _ _ fun n =>
    exponentialProfile_factor_memLp α β ε y s hα hβ hw hε hy b C P n

def finiteProfile {ι : Type*} (I : Finset ι) (b C : ι → ℂ) (P : ι → Polynomial ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ I, exponentialProfile (b i) (C i) (P i) z

theorem finiteProfile_factor {ι : Type*} (I : Finset ι) (b C : ι → ℂ)
    (P : ι → Polynomial ℂ) (α β : ℝ) (r : ℂ) (n : ℕ) (q : Transverse) :
    profileFactor α β r (finiteProfile I b C P) n q =
      ∑ i ∈ I, profileFactor α β r (exponentialProfile (b i) (C i) (P i)) n q := by
  simp only [profileFactor,finiteProfile,Finset.mul_sum]

theorem finiteProfile_integrable {ι : Type*} (I : Finset ι) (b C : ι → ℂ)
    (P : ι → Polynomial ℂ) (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Integrable (profileEnergyDensity α β (scale ε y s) (finiteProfile I b C P)) volume := by
  apply profileEnergy_integrable_of_factors
  intro n
  have hm := memLp_finset_sum I (fun i _ =>
    exponentialProfile_factor_memLp α β ε y s hα hβ hw hε hy (b i) (C i) (P i) n)
  change MemLp (fun q => profileFactor α β (scale ε y s) (finiteProfile I b C P) n q) 2 volume
  simp_rw [finiteProfile_factor]
  exact hm

theorem exists_uniform_finiteProfile_growth (α : ℝ) (hα : 0 < α) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ β ε y : ℝ, 0 < β → 32*β ≤ α →
      0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 →
      ∀ (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (s t : ℝ), s ≤ t →
        (∫ q, profileEnergyDensity α β (scale ε y t) (finiteProfile Finset.univ b C P) q) ≤
          Real.exp (K*(t-s))*
            (∫ q, profileEnergyDensity α β (scale ε y s) (finiteProfile Finset.univ b C P) q) := by
  obtain ⟨K,hK,hg⟩ := exists_uniform_profileEnergy_growth α hα
  refine ⟨K,hK,?_⟩
  intro β ε y hβ hw hε hy hy0 N b C P s t hst
  exact hg β ε y hε hy hy0 _ s t hst
    (finiteProfile_integrable Finset.univ b C P α β ε y s hα hβ hw hε hy)
    (finiteProfile_integrable Finset.univ b C P α β ε y t hα hβ hw hε hy)

#print axioms neutralSource_exponent
#print axioms exponentialProfile_factor
#print axioms source_factor_memLp
#print axioms profileEnergy_sum
#print axioms profileEnergy_integrable_of_factors
#print axioms exponentialProfile_factor_memLp
#print axioms exponentialProfile_integrable
#print axioms finiteProfile_factor
#print axioms finiteProfile_integrable
#print axioms exists_uniform_finiteProfile_growth
end
end UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles
