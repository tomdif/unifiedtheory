/- Finite neutral superpositions have the exact differentiated Gram
kernel of their full squared norm, with every off-diagonal source term. -/
import UnifiedTheory.Audit.KFCausalNeutralCrossKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalNeutralFiniteGram
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale)
open UnifiedTheory.Audit.KFCausalNeutralProfileMarginal
open UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles
open UnifiedTheory.Audit.KFCausalNeutralCrossKernel

def finiteKernel (ε y α β : ℝ) (N : ℕ) (b C : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  ∑ i, ∑ j, crossKernel ε y α β (b i) (b j) (C i) (C j) (P i) (P j) n s
def finiteDerivative (ε y α β : ℝ) (N : ℕ) (b C : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  ∑ i, ∑ j, crossDerivative ε y α β (b i) (b j) (C i) (C j) (P i) (P j) n s

theorem finiteFactor_memLp (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (n : ℕ) :
    MemLp (profileFactor α β (scale ε y s) (finiteProfile Finset.univ b C P) n) 2 volume := by
  change MemLp (fun q =>
    profileFactor α β (scale ε y s) (finiteProfile Finset.univ b C P) n q) 2 volume
  simp_rw [finiteProfile_factor]
  exact memLp_finset_sum Finset.univ fun i _ =>
    exponentialProfile_factor_memLp α β ε y s hα hβ hw hε hy (b i) (C i) (P i) n

theorem finiteKernel_gram (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (n : ℕ) :
    finiteKernel ε y α β N b C P n s =
      ∫ q : Transverse,
        star (profileFactor α β (scale ε y s) (finiteProfile Finset.univ b C P) n q)*
          profileFactor α β (scale ε y s) (finiteProfile Finset.univ b C P) n q := by
  let f := fun i : Fin N => profileFactor α β (scale ε y s) (exponentialProfile (b i) (C i) (P i)) n
  have hi (i j : Fin N) : Integrable (fun q => star (f i q)*f j q) volume :=
    cross_integrable α β ε y s hα hβ hw hε hy (b i) (b j) (C i) (C j) (P i) (P j) n
  have he (q : Transverse) :
      star (profileFactor α β (scale ε y s) (finiteProfile Finset.univ b C P) n q)*
        profileFactor α β (scale ε y s) (finiteProfile Finset.univ b C P) n q =
      ∑ i, ∑ j, star (f i q)*f j q := by
    simp [finiteProfile_factor,Finset.sum_mul,Finset.mul_sum,f]
    rw [Finset.sum_comm]
  simp_rw [he]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hi i j))]
  unfold finiteKernel
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum Finset.univ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact crossKernel_gram α β ε y s hα hβ hw hε hy _ _ _ _ _ _ n

theorem finiteKernel_re (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (n : ℕ) :
    (finiteKernel ε y α β N b C P n s).re =
      ∫ q : Transverse,
        ‖profileFactor α β (scale ε y s) (finiteProfile Finset.univ b C P) n q‖^2 := by
  let f := profileFactor α β (scale ε y s) (finiteProfile Finset.univ b C P) n
  have hm := finiteFactor_memLp α β ε y s hα hβ hw hε hy N b C P n
  have he : (∫ q : Transverse, (star (f q)*f q).re) =
      (∫ q : Transverse, star (f q)*f q).re :=
    integral_re (hm.star.integrable_mul hm)
  rw [finiteKernel_gram α β ε y s hα hβ hw hε hy]
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with q
  simp only [Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    Complex.sq_norm,Complex.normSq_apply,f]
  ring

theorem finiteKernel_derivative (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (n : ℕ) :
    HasDerivAt (finiteKernel ε y α β N b C P n)
      (finiteDerivative ε y α β N b C P n s) s :=
  HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
    crossKernel_derivative α β ε y s hα hβ hw hε hy
      (b i) (b j) (C i) (C j) (P i) (P j) n

def energyKernel (ε y α β : ℝ) (N : ℕ) (b C : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (s : ℝ) : ℂ :=
  finiteKernel ε y α β N b C P 0 s+
    (1/2:ℂ)*finiteKernel ε y α β N b C P 1 s+
    (1/4:ℂ)*finiteKernel ε y α β N b C P 2 s
def energyDerivative (ε y α β : ℝ) (N : ℕ) (b C : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (s : ℝ) : ℂ :=
  finiteDerivative ε y α β N b C P 0 s+
    (1/2:ℂ)*finiteDerivative ε y α β N b C P 1 s+
    (1/4:ℂ)*finiteDerivative ε y α β N b C P 2 s

theorem energyKernel_re (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    (energyKernel ε y α β N b C P s).re =
      ∫ q, profileEnergyDensity α β (scale ε y s) (finiteProfile Finset.univ b C P) q := by
  have hi (n : ℕ) : Integrable (fun q : Transverse =>
      ‖profileFactor α β (scale ε y s) (finiteProfile Finset.univ b C P) n q‖^2) volume := by
    have hm := finiteFactor_memLp α β ε y s hα hβ hw hε hy N b C P n
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  unfold energyKernel
  simp only [Complex.add_re,Complex.mul_re]
  norm_num
  rw [finiteKernel_re α β ε y s hα hβ hw hε hy,
    finiteKernel_re α β ε y s hα hβ hw hε hy,
    finiteKernel_re α β ε y s hα hβ hw hε hy]
  simp_rw [profileEnergy_sum]
  have hsum := integral_add ((hi 0).add ((hi 1).const_mul (1/2:ℝ)))
    ((hi 2).const_mul (1/4:ℝ))
  simp only [Pi.add_apply] at hsum
  rw [hsum,integral_add (hi 0) ((hi 1).const_mul (1/2:ℝ)),
    integral_const_mul,integral_const_mul]

theorem energyKernel_derivative (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    HasDerivAt (energyKernel ε y α β N b C P)
      (energyDerivative ε y α β N b C P s) s :=
  ((finiteKernel_derivative α β ε y s hα hβ hw hε hy N b C P 0).add
    ((finiteKernel_derivative α β ε y s hα hβ hw hε hy N b C P 1).const_mul (1/2:ℂ))).add
    ((finiteKernel_derivative α β ε y s hα hβ hw hε hy N b C P 2).const_mul (1/4:ℂ))

#print axioms finiteFactor_memLp
#print axioms finiteKernel_gram
#print axioms finiteKernel_re
#print axioms finiteKernel_derivative
#print axioms energyKernel_re
#print axioms energyKernel_derivative
end
end UnifiedTheory.Audit.KFCausalNeutralFiniteGram
