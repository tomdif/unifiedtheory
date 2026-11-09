/- Exact clock transport of a finite Hermitian kernel with independent
Gaussian clock widths. Kernel and coefficient derivatives are separated;
no response bound or endpoint condition is built into this identity. -/
import UnifiedTheory.Audit.KFCausalClockResponseTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalFiniteClockKernel
noncomputable section
open scoped ComplexConjugate
open KFCausalClockResponseTransport (clock coefficient pair weakPair weakSlope)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)

def form (n : ℕ) (K : Fin n → Fin n → ℂ) (c d : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, (conj (c i)*d j)*K i j

theorem form_conj (n : ℕ) (K : Fin n → Fin n → ℂ) (c d : Fin n → ℂ)
    (hK : ∀ i j, conj (K i j) = K j i) : conj (form n K c d) = form n K d c := by
  unfold form
  simp only [map_sum,map_mul,starRingEnd_self_apply,hK]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem form_const_right (n : ℕ) (K : Fin n → Fin n → ℂ) (c d : Fin n → ℂ) (z : ℂ) :
    form n K c (fun i => z*d i) = z*form n K c d := by
  unfold form
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def coefficients (n : ℕ) (ε y : ℝ) (a : Fin n → ℝ) (c : Fin n → ℂ) (s : ℝ) (i : Fin n) : ℂ :=
  c i*clockAmplitude ε (a i) 0 y s
def weakCoefficients (n : ℕ) (ε y : ℝ) (a : Fin n → ℝ) (c : Fin n → ℂ) (s : ℝ) (i : Fin n) : ℂ :=
  weakSlope ε (a i) 0 y s*coefficients n ε y a c s i
def weakForm (n : ℕ) (ε y : ℝ) (a : Fin n → ℝ) (c : Fin n → ℂ)
    (K : Fin n → Fin n → ℂ) (s : ℝ) : ℂ :=
  form n K (coefficients n ε y a c s) (weakCoefficients n ε y a c s)+
    form n K (weakCoefficients n ε y a c s) (coefficients n ε y a c s)

theorem form_pair (n : ℕ) (ε y : ℝ) (a : Fin n → ℝ) (c : Fin n → ℂ)
    (K : Fin n → Fin n → ℂ) (s : ℝ) :
    form n K (coefficients n ε y a c s) (coefficients n ε y a c s) =
      ∑ i, ∑ j, (conj (c i)*c j)*K i j*pair ε (a i) (a j) 0 0 y s := by
  unfold form
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [coefficients,pair,map_mul,Complex.star_def]
  ring

theorem weakForm_expansion (n : ℕ) (ε y : ℝ) (a : Fin n → ℝ) (c : Fin n → ℂ)
    (K : Fin n → Fin n → ℂ) (s : ℝ) :
    weakForm n ε y a c K s =
      ∑ i, ∑ j, (conj (c i)*c j)*K i j*weakPair ε (a i) (a j) 0 0 y s := by
  unfold weakForm form
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [coefficients,weakCoefficients,weakPair,pair,map_mul,Complex.star_def]
  ring

theorem weakForm_re (n : ℕ) (ε y : ℝ) (a : Fin n → ℝ) (c : Fin n → ℂ)
    (K : Fin n → Fin n → ℂ) (s : ℝ) (hK : ∀ i j, conj (K i j) = K j i) :
    (weakForm n ε y a c K s).re =
      2*(form n K (coefficients n ε y a c s) (weakCoefficients n ε y a c s)).re := by
  rw [weakForm,← form_conj n K _ _ hK,Complex.add_re,Complex.conj_re]
  ring

theorem boundary_derivative (n : ℕ) (ε y : ℝ) (a : Fin n → ℝ) (c : Fin n → ℂ)
    (K : ℝ → Fin n → Fin n → ℂ) (K' : Fin n → Fin n → ℂ) (s : ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hK : ∀ i j, HasDerivAt (fun u => K u i j) (K' i j) s) :
    HasDerivAt (fun u => form n (K u) (coefficients n ε y a c u) (coefficients n ε y a c u)/(clock ε u:ℂ))
      (weakForm n ε y a c (K s) s-
        (coefficient ε y s:ℂ)*form n (K s) (coefficients n ε y a c s) (coefficients n ε y a c s)+
        form n K' (coefficients n ε y a c s) (coefficients n ε y a c s)/(clock ε s:ℂ)) s := by
  have hd := HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) =>
    HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) =>
      (KFCausalClockResponseTransport.boundary_derivative ε (a i) (a j) 0 0 y s hε hy
        (fun u => K u i j) (K' i j) (hK i j)).const_mul (conj (c i)*c j)))
  convert hd using 1
  · funext u
    rw [form_pair]
    simp only [Finset.sum_apply,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · have hr (i j : Fin n) :
        (conj (c i)*c j)*(K s i j*weakPair ε (a i) (a j) 0 0 y s-
          pair ε (a i) (a j) 0 0 y s*((coefficient ε y s:ℂ)*K s i j-K' i j/(clock ε s:ℂ))) =
        (conj (c i)*c j)*K s i j*weakPair ε (a i) (a j) 0 0 y s-
          (coefficient ε y s:ℂ)*((conj (c i)*c j)*K s i j*pair ε (a i) (a j) 0 0 y s)+
          ((conj (c i)*c j)*K' i j*pair ε (a i) (a j) 0 0 y s)/(clock ε s:ℂ) := by ring
    rw [weakForm_expansion,form_pair,form_pair]
    simp_rw [hr]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_div]

theorem boundary_real_derivative (n : ℕ) (ε y : ℝ) (a : Fin n → ℝ) (c : Fin n → ℂ)
    (K : ℝ → Fin n → Fin n → ℂ) (K' : Fin n → Fin n → ℂ) (s : ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hK : ∀ i j, HasDerivAt (fun u => K u i j) (K' i j) s)
    (hH : ∀ i j, conj (K s i j) = K s j i) :
    HasDerivAt (fun u => (form n (K u) (coefficients n ε y a c u) (coefficients n ε y a c u)).re/clock ε u)
      (2*(form n (K s) (coefficients n ε y a c s) (weakCoefficients n ε y a c s)).re-
        coefficient ε y s*(form n (K s) (coefficients n ε y a c s) (coefficients n ε y a c s)).re+
        (form n K' (coefficients n ε y a c s) (coefficients n ε y a c s)).re/clock ε s) s := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (boundary_derivative n ε y a c K K' s hε hy hK)
  simpa only [Function.comp_def,Complex.reCLM_apply,Complex.div_ofReal_re,Complex.add_re,Complex.sub_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,weakForm_re n ε y a c _ s hH] using hd

#print axioms form_conj
#print axioms form_const_right
#print axioms form_pair
#print axioms weakForm_expansion
#print axioms weakForm_re
#print axioms boundary_derivative
#print axioms boundary_real_derivative
end
end UnifiedTheory.Audit.KFCausalFiniteClockKernel
