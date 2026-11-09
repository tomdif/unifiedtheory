/- The full-clock transport identity is the actual ordered-potential
response of the finite joint state, not a surrogate scalar functional.
No family-independent upper bound on the transport term is inferred. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralWholeClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralPotentialTransport
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalClockResponseTransport (weakSlope weakPair pair)
open KFCausalReciprocalNeutralPhysicalPair (clockKernel)
open KFCausalReciprocalNeutralWholeClock (kernels weakResponse reducedResponse)
open KFCausalReciprocalNeutralSuperposition (output momentumOutput)
open KFCausalNeutralFinitePairing (sum_inner_pairs)

theorem hermitian_real_response (N : ℕ) (M : Fin N → Fin N → ℂ) (L : Fin N → ℂ)
    (hM : ∀ i j, conj (M i j) = M j i) :
    (∑ i, ∑ j, M i j*(conj (L i)+L j)).re = 2*(∑ i, ∑ j, L j*M i j).re := by
  have hl : (∑ i, ∑ j, conj (L i)*M i j) = conj (∑ i, ∑ j, L j*M i j) := by
    simp only [map_sum,map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hM]
  have hs : (∑ i, ∑ j, M i j*(conj (L i)+L j)) =
      (∑ i, ∑ j, conj (L i)*M i j)+(∑ i, ∑ j, L j*M i j) := by
    simp only [mul_add,Finset.sum_add_distrib,mul_comm]
  rw [hs,hl,Complex.add_re,Complex.conj_re]
  ring

theorem momentum_scalar (h : ℝ) (hh : h ≠ 0) (z : ℂ) :
    (-2/h)*((-Complex.I*(h:ℂ))*z).im = 2*z.re := by
  simp [Complex.mul_im,Complex.mul_re]
  field_simp

theorem clockKernel_conj (ε h a₁ a₂ w₁ w₂ p₁ p₂ : ℝ) (C₁ C₂ b₁ b₂ : ℂ)
    (P₁ P₂ : Polynomial ℂ) (s : ℝ) :
    conj (clockKernel ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ s) =
      clockKernel ε h a₂ a₁ w₂ w₁ p₂ p₁ C₂ C₁ b₂ b₁ P₂ P₁ s := by
  have hf (b : ℂ) (P : Polynomial ℂ) : KFCausalReciprocalNeutralPhysicalPair.neutralProfile b P =
      KFCausalNeutralExponentialProfiles.exponentialProfile b 1 P := by
    funext z
    simp [KFCausalReciprocalNeutralPhysicalPair.neutralProfile,KFCausalNeutralExponentialProfiles.exponentialProfile]
  simp only [clockKernel,KFCausalReciprocalNeutralPhysicalPair.coefficient,hf,map_mul,
    KFCausalReciprocalNeutralCrossDifferentiation.kernel_conj,starRingEnd_self_apply]
  ring

variable (N : ℕ) (ε h : ℝ) (a w p : Fin N → ℝ) (C b : Fin N → ℂ)
  (P : Fin N → Polynomial ℂ)
local notation "Z" => fun i j => clockKernel ε h (a i) (a j) (w i) (w j) (p i) (p j)
  (C i) (C j) (b i) (b j) (P i) (P j)

def momentumSum (s : ℝ) : ℂ := ∑ i, ∑ j,
  KFCausalPolynomialOrderedMomentumDensity.clockSlope ε (a j) h (p j) (s,0)*Z i j s

theorem weak_matrix (s : ℝ) : weakResponse N ε h a w p C b P s =
    2*(∑ i, ∑ j, weakSlope ε (a j) (p j) (-h/2) s*Z i j s).re := by
  have hf (d : ℂ) (Q : Polynomial ℂ) : KFCausalReciprocalNeutralPhysicalPair.neutralProfile d Q =
      KFCausalNeutralExponentialProfiles.exponentialProfile d 1 Q := by
    funext z
    simp [KFCausalReciprocalNeutralPhysicalPair.neutralProfile,KFCausalNeutralExponentialProfiles.exponentialProfile]
  have he : weakResponse N ε h a w p C b P s =
      (∑ i, ∑ j, Z i j s*(conj (weakSlope ε (a i) (p i) (-h/2) s)+
        weakSlope ε (a j) (p j) (-h/2) s)).re := by
    unfold weakResponse KFCausalFiniteMatrixClockTransport.weak
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [kernels,KFCausalReciprocalNeutralCrossDifferentiation.actual,weakPair,pair,
      clockKernel,KFCausalReciprocalNeutralPhysicalPair.coefficient,
      hf,map_mul,Complex.star_def]
    ring
  rw [he]
  exact hermitian_real_response N (fun i j => Z i j s)
    (fun i => weakSlope ε (a i) (p i) (-h/2) s)
    (fun i j => clockKernel_conj ε h (a i) (a j) (w i) (w j) (p i) (p j)
      (C i) (C j) (b i) (b j) (P i) (P j) s)

theorem weak_momentum_density (hh : h ≠ 0) (s : ℝ) : weakResponse N ε h a w p C b P s =
    (-2/h)*(momentumSum N ε h a w p C b P s).im := by
  have he : momentumSum N ε h a w p C b P s = (-Complex.I*(h:ℂ))*
      (∑ i, ∑ j, weakSlope ε (a j) (p j) (-h/2) s*Z i j s) := by
    simp only [momentumSum,KFCausalPolynomialOrderedMomentumDensity.clockSlope,
      Finset.mul_sum,mul_assoc]
  rw [weak_matrix,he,momentum_scalar h hh]

variable (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "U" => output N ε h a w p C b P hε ha hh hw hb
local notation "V" => momentumOutput N ε h a w p C b P hε ha hh hw hb

def potentialResponse : ℝ := (-2/h)*(inner ℂ (U 7) (V 7)+
  inner ℂ (U 5) (V 5)/2+inner ℂ (U 6) (V 6)/4).im

include hε ha hh hw hb in
theorem momentumSum_integrable : Integrable (momentumSum N ε h a w p C b P) :=
  integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
    KFCausalReciprocalNeutralPairing.momentumClockKernel_integrable ε h (a i) (a j)
      (w i) (w j) (p i) (p j) (C i) (C j) (b i) (b j) (P i) (P j)
      hε (ha i) (ha j) hh (hw i) (hw j) hb))

theorem potentialResponse_weak_integral : potentialResponse N ε h a w p C b P hε ha hh hw hb =
    ∫ s, weakResponse N ε h a w p C b P s := by
  have hi (i j : Fin N) := KFCausalReciprocalNeutralPairing.momentumClockKernel_integrable ε h (a i) (a j)
    (w i) (w j) (p i) (p j) (C i) (C j) (b i) (b j) (P i) (P j)
    hε (ha i) (ha j) hh (hw i) (hw j) hb
  have he : (∫ s, momentumSum N ε h a w p C b P s) =
      inner ℂ (U 7) (V 7)+inner ℂ (U 5) (V 5)/2+inner ℂ (U 6) (V 6)/4 := by
    unfold momentumSum
    rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum Finset.univ (fun j _ => hi i j))]
    simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j),
      ← KFCausalReciprocalNeutralPairing.momentum_pair_clock_kernel ε h _ _ _ _ _ _ _ _ _ _ _ _
        hε (ha _) (ha _) hh (hw _) (hw _) hb]
    simp only [Finset.sum_add_distrib,← Finset.sum_div]
    rw [sum_inner_pairs,sum_inner_pairs,sum_inner_pairs]
    rfl
  have hs : weakResponse N ε h a w p C b P = fun s => (-2/h)*(momentumSum N ε h a w p C b P s).im :=
    funext (weak_momentum_density N ε h a w p C b P hh)
  have him : (∫ s, (momentumSum N ε h a w p C b P s).im) =
      (∫ s, momentumSum N ε h a w p C b P s).im :=
    integral_im (momentumSum_integrable N ε h a w p C b P hε ha hh hw hb)
  rw [hs,integral_const_mul,him,he]
  rfl

theorem potentialResponse_reduced_integral : potentialResponse N ε h a w p C b P hε ha hh hw hb =
    ∫ s, reducedResponse N ε h a w p C b P s :=
  (potentialResponse_weak_integral N ε h a w p C b P hε ha hh hw hb).trans
    (KFCausalReciprocalNeutralWholeClock.full_clock_identity N ε h a w p C b P hε hh hw hb ha)

#print axioms hermitian_real_response
#print axioms momentum_scalar
#print axioms clockKernel_conj
#print axioms weak_matrix
#print axioms weak_momentum_density
#print axioms momentumSum_integrable
#print axioms potentialResponse_weak_integral
#print axioms potentialResponse_reduced_integral
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralPotentialTransport
