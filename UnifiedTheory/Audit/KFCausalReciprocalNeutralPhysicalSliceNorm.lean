/- The positive joint Gram form controls the actual transverse
wavefunction norm. This is an integral identity, not a pointwise
identification of the physical and Laplace representations. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalCauchy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralPhysicalSliceNorm
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalNeutralSliceIntegrability (factor factor_memLp)
open KFCausalReciprocalNeutralKernel (density kernel)
open KFCausalReciprocalNeutralPositiveForm (pairing positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalQuarticPlaneDomination (potential potential_positive)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalReciprocalNeutralLaplace (jointMeasure)

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c b : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

def wave (q : Transverse) : ℂ := ∑ i, c i*factor α β (w i) r (b i) (P i) 0 q
def weighted (q : Transverse) : ℝ := potential (pointField q)*‖wave n α β w r c b P q‖^2

theorem weighted_expansion (q : Transverse) :
    (weighted n α β w r c b P q:ℂ) = ∑ i, ∑ j, (conj (c i)*c j)*
      density α β (w i) (w j) r (exponentialProfile (b i) 1 (P i)) (exponentialProfile (b j) 1 (P j)) q := by
  rw [weighted,Complex.ofReal_mul,Complex.ofReal_pow,← Complex.conj_mul']
  unfold wave
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [factor,density,KFCausalReciprocalCrossKernel.density,pow_zero,one_mul,map_mul]
  ring

theorem norm_square_le_weighted (q : Transverse) :
    ‖wave n α β w r c b P q‖^2 ≤ weighted n α β w r c b P q := by
  have hp : 1 ≤ potential (pointField q) := by
    unfold potential
    nlinarith [sq_nonneg (pointField q),sq_nonneg ((pointField q)^2)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (sq_nonneg ‖wave n α β w r c b P q‖)

theorem weighted_nonnegative (q : Transverse) : 0 ≤ weighted n α β w r c b P q :=
  mul_nonneg (potential_positive _).le (sq_nonneg _)

variable (ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i)

include hα hβ hwidth hε hy hw in
theorem wave_memLp : MemLp (wave n α β w (scale ε y s) c b P) 2 volume :=
  memLp_finset_sum Finset.univ (fun i _ =>
    (factor_memLp α β ε y s (w i) hα hβ hwidth hε hy (hw i) (b i) (P i) 0).const_mul (c i))

include hα hβ hwidth hε hy hw in
theorem weighted_integrable : Integrable (weighted n α β w (scale ε y s) c b P) := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ =>
      (KFCausalReciprocalNeutralSliceIntegrability.density_integrable α β ε y s (w i) (w j)
        hα hβ hwidth hε hy (hw i) (hw j) (b i) (b j) (P i) (P j)).const_mul (conj (c i)*c j)))
  have he : Integrable (fun q => (weighted n α β w (scale ε y s) c b P q:ℂ)) :=
    hi.congr (Filter.Eventually.of_forall (fun q => (weighted_expansion n α β w _ c b P q).symm))
  exact he.re

include hα hβ hwidth hε hy hw in
theorem weighted_integral_pairing :
    ((∫ q, weighted n α β w (scale ε y s) c b P q : ℝ):ℂ) =
      pairing n α β w (scale ε y s) c c (fun i => exponentialProfile (b i) 1 (P i)) := by
  have hi (i j : Fin n) :=
    (KFCausalReciprocalNeutralSliceIntegrability.density_integrable α β ε y s (w i) (w j)
      hα hβ hwidth hε hy (hw i) (hw j) (b i) (b j) (P i) (P j)).const_mul (conj (c i)*c j)
  rw [← integral_complex_ofReal]
  simp_rw [weighted_expansion]
  rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j),integral_const_mul]
  rfl

include hα hβ hwidth hε hy hw in
theorem weighted_integral_joint :
    (∫ q, weighted n α β w (scale ε y s) c b P q) =
      Real.pi/4*∫ q, positiveDensity n α β w (scale ε y s) c
        (fun i => exponentialProfile (b i) 1 (P i)) q ∂jointMeasure := by
  apply Complex.ofReal_injective
  rw [weighted_integral_pairing n α β w c b P ε y s hα hβ hwidth hε hy hw]
  exact KFCausalReciprocalNeutralActualPositive.pairing_positive_integral n α β ε y s w b c P
    hα hβ hwidth hε hy hw

include hα hβ hwidth hε hy hw in
theorem norm_integral_le_joint :
    (∫ q, ‖wave n α β w (scale ε y s) c b P q‖^2) ≤
      Real.pi/4*∫ q, positiveDensity n α β w (scale ε y s) c
        (fun i => exponentialProfile (b i) 1 (P i)) q ∂jointMeasure := by
  rw [← weighted_integral_joint n α β w c b P ε y s hα hβ hwidth hε hy hw]
  have hm := wave_memLp n α β w c b P ε y s hα hβ hwidth hε hy hw
  exact integral_mono ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)
    (weighted_integrable n α β w c b P ε y s hα hβ hwidth hε hy hw)
    (norm_square_le_weighted n α β w _ c b P)

#print axioms weighted_expansion
#print axioms norm_square_le_weighted
#print axioms weighted_nonnegative
#print axioms wave_memLp
#print axioms weighted_integrable
#print axioms weighted_integral_pairing
#print axioms weighted_integral_joint
#print axioms norm_integral_le_joint
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralPhysicalSliceNorm
