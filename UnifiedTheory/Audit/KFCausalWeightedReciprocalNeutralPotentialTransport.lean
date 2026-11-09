/- The weighted full-clock identity is attached to actual Hilbert output
and momentum-output pairings. All three physical channels and all finite
interference terms remain. Absolute integrability is derived first. -/
import UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralPhysicalPair
import UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralWholeClock
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPotentialTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralPotentialTransport
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalClockResponseTransport (weakSlope weakPair pair)
open KFCausalWeightedReciprocalNeutralPhysicalPair (clockKernel)
open KFCausalWeightedReciprocalNeutralWholeClock
  (kernels clockPairing positiveSlice weakResponse reducedResponse)
open KFCausalReciprocalNeutralSuperposition (output momentumOutput)
open KFCausalNeutralFinitePairing (sum_inner_pairs)
open KFCausalReciprocalNeutralPotentialTransport (hermitian_real_response momentum_scalar)

variable (mass2 quartic vacuum : ℝ) (N : ℕ) (ε h : ℝ) (a w p : Fin N → ℝ)
  (C b : Fin N → ℂ) (P : Fin N → Polynomial ℂ)
local notation "Z" => fun i j => clockKernel ε h (a i) (a j) (w i) (w j) (p i) (p j)
  (C i) (C j) (b i) (b j) (P i) (P j) mass2 quartic vacuum

theorem clockPairing_sum (s : ℝ) : clockPairing mass2 quartic vacuum N ε h a w p C b P s=
    ∑ i, ∑ j, Z i j s := by
  unfold clockPairing KFCausalFiniteMatrixClockTransport.value
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [kernels,pair,clockKernel,KFCausalReciprocalNeutralPhysicalPair.coefficient,
    map_mul,Complex.star_def]
  ring

private theorem clockKernel_conj (i j : Fin N) (s : ℝ) : conj (Z i j s)=Z j i s := by
  simp only [clockKernel,KFCausalReciprocalNeutralPhysicalPair.coefficient,map_mul,
    KFCausalWeightedReciprocalNeutralCross.actual_conj,starRingEnd_self_apply]
  ring

def momentumSum (s : ℝ) : ℂ := ∑ i, ∑ j,
  KFCausalPolynomialOrderedMomentumDensity.clockSlope ε (a j) h (p j) (s,0)*Z i j s

theorem weak_matrix (s : ℝ) : weakResponse mass2 quartic vacuum N ε h a w p C b P s=
    2*(∑ i, ∑ j, weakSlope ε (a j) (p j) (-h/2) s*Z i j s).re := by
  have he : weakResponse mass2 quartic vacuum N ε h a w p C b P s=
      (∑ i, ∑ j, Z i j s*(conj (weakSlope ε (a i) (p i) (-h/2) s)+
        weakSlope ε (a j) (p j) (-h/2) s)).re := by
    unfold weakResponse KFCausalFiniteMatrixClockTransport.weak
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [kernels,weakPair,pair,clockKernel,KFCausalReciprocalNeutralPhysicalPair.coefficient,
      map_mul,Complex.star_def]
    ring
  rw [he]
  exact hermitian_real_response N (fun i j => Z i j s)
    (fun i => weakSlope ε (a i) (p i) (-h/2) s)
    (fun i j => clockKernel_conj mass2 quartic vacuum N ε h a w p C b P i j s)

theorem weak_momentum_density (hh : h ≠ 0) (s : ℝ) :
    weakResponse mass2 quartic vacuum N ε h a w p C b P s=
      (-2/h)*(momentumSum mass2 quartic vacuum N ε h a w p C b P s).im := by
  have he : momentumSum mass2 quartic vacuum N ε h a w p C b P s=(-Complex.I*(h:ℂ))*
      (∑ i, ∑ j, weakSlope ε (a j) (p j) (-h/2) s*Z i j s) := by
    simp only [momentumSum,KFCausalPolynomialOrderedMomentumDensity.clockSlope,Finset.mul_sum,mul_assoc]
  rw [weak_matrix,he,momentum_scalar h hh]

variable (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "U" => output N ε h a w p C b P hε ha hh hw hb
local notation "V" => momentumOutput N ε h a w p C b P hε ha hh hw hb

def potentialEnergy : ℝ := vacuum*‖U 7‖^2+mass2*‖U 5‖^2/2+quartic*‖U 6‖^2/4
def potentialResponse : ℝ := (-2/h)*((vacuum:ℂ)*inner ℂ (U 7) (V 7)+
  (mass2:ℂ)*inner ℂ (U 5) (V 5)/2+(quartic:ℂ)*inner ℂ (U 6) (V 6)/4).im

include hε ha hh hw hb in
theorem clockPairing_integrable : Integrable (clockPairing mass2 quartic vacuum N ε h a w p C b P) := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ =>
      KFCausalWeightedReciprocalNeutralPhysicalPair.clockKernel_integrable ε h (a i) (a j)
        (w i) (w j) (p i) (p j) (C i) (C j) (b i) (b j) (P i) (P j)
        hε (ha i) (ha j) hh (hw i) (hw j) hb mass2 quartic vacuum))
  exact hi.congr (Filter.Eventually.of_forall (fun s =>
    (clockPairing_sum mass2 quartic vacuum N ε h a w p C b P s).symm))

include hε ha hh hw hb in
theorem positiveSlice_integrable : Integrable (positiveSlice mass2 quartic vacuum N ε h a w p C b P) :=
  (clockPairing_integrable mass2 quartic vacuum N ε h a w p C b P hε ha hh hw hb).re

private theorem potentialEnergy_clockPairing :
    (potentialEnergy mass2 quartic vacuum N ε h a w p C b P hε ha hh hw hb:ℂ)=
      ∫ s, clockPairing mass2 quartic vacuum N ε h a w p C b P s := by
  have hi (i j : Fin N) := KFCausalWeightedReciprocalNeutralPhysicalPair.clockKernel_integrable
    ε h (a i) (a j) (w i) (w j) (p i) (p j) (C i) (C j) (b i) (b j) (P i) (P j)
      hε (ha i) (ha j) hh (hw i) (hw j) hb mass2 quartic vacuum
  simp_rw [clockPairing_sum]
  rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j),
    ← KFCausalWeightedReciprocalNeutralPhysicalPair.ordered_pair_clock_kernel
      ε h _ _ _ _ _ _ _ _ _ _ _ _ hε (ha _) (ha _) hh (hw _) (hw _) hb mass2 quartic vacuum]
  simp only [Finset.sum_add_distrib,← Finset.sum_div,← Finset.mul_sum]
  rw [sum_inner_pairs,sum_inner_pairs,sum_inner_pairs]
  simp only [inner_self_eq_norm_sq_to_K]
  unfold potentialEnergy output
  push_cast
  rfl

theorem potentialEnergy_integral :
    potentialEnergy mass2 quartic vacuum N ε h a w p C b P hε ha hh hw hb=
      ∫ s, positiveSlice mass2 quartic vacuum N ε h a w p C b P s := by
  have he := congrArg Complex.re
    (potentialEnergy_clockPairing mass2 quartic vacuum N ε h a w p C b P hε ha hh hw hb)
  rw [Complex.ofReal_re] at he
  change _ = RCLike.re (∫ s, clockPairing mass2 quartic vacuum N ε h a w p C b P s) at he
  rw [← integral_re
    (clockPairing_integrable mass2 quartic vacuum N ε h a w p C b P hε ha hh hw hb)] at he
  exact he

include hε ha hh hw hb in
private theorem momentumSum_integrable : Integrable (momentumSum mass2 quartic vacuum N ε h a w p C b P) :=
  integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
    KFCausalWeightedReciprocalNeutralPhysicalPair.momentumClockKernel_integrable ε h (a i) (a j)
      (w i) (w j) (p i) (p j) (C i) (C j) (b i) (b j) (P i) (P j)
      hε (ha i) (ha j) hh (hw i) (hw j) hb mass2 quartic vacuum))

theorem potentialResponse_weak_integral :
    potentialResponse mass2 quartic vacuum N ε h a w p C b P hε ha hh hw hb=
      ∫ s, weakResponse mass2 quartic vacuum N ε h a w p C b P s := by
  have hi (i j : Fin N) := KFCausalWeightedReciprocalNeutralPhysicalPair.momentumClockKernel_integrable
    ε h (a i) (a j) (w i) (w j) (p i) (p j) (C i) (C j) (b i) (b j) (P i) (P j)
      hε (ha i) (ha j) hh (hw i) (hw j) hb mass2 quartic vacuum
  have he : (∫ s, momentumSum mass2 quartic vacuum N ε h a w p C b P s)=
      (vacuum:ℂ)*inner ℂ (U 7) (V 7)+(mass2:ℂ)*inner ℂ (U 5) (V 5)/2+
        (quartic:ℂ)*inner ℂ (U 6) (V 6)/4 := by
    unfold momentumSum
    rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum Finset.univ (fun j _ => hi i j))]
    simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j),
      ← KFCausalWeightedReciprocalNeutralPhysicalPair.momentum_pair_clock_kernel
        ε h _ _ _ _ _ _ _ _ _ _ _ _ hε (ha _) (ha _) hh (hw _) (hw _) hb mass2 quartic vacuum]
    simp only [Finset.sum_add_distrib,← Finset.sum_div,← Finset.mul_sum]
    rw [sum_inner_pairs,sum_inner_pairs,sum_inner_pairs]
    rfl
  have hs : weakResponse mass2 quartic vacuum N ε h a w p C b P=fun s =>
      (-2/h)*(momentumSum mass2 quartic vacuum N ε h a w p C b P s).im :=
    funext (weak_momentum_density mass2 quartic vacuum N ε h a w p C b P hh)
  rw [hs,integral_const_mul]
  change _ = (-2/h)*(∫ s, RCLike.im (momentumSum mass2 quartic vacuum N ε h a w p C b P s))
  rw [integral_im
    (momentumSum_integrable mass2 quartic vacuum N ε h a w p C b P hε ha hh hw hb),he]
  rfl

theorem potentialResponse_reduced_integral :
    potentialResponse mass2 quartic vacuum N ε h a w p C b P hε ha hh hw hb=
      ∫ s, reducedResponse mass2 quartic vacuum N ε h a w p C b P s :=
  (potentialResponse_weak_integral mass2 quartic vacuum N ε h a w p C b P hε ha hh hw hb).trans
    (KFCausalWeightedReciprocalNeutralWholeClock.full_clock_identity
      mass2 quartic vacuum N ε h a w p C b P hε hh hw hb ha)

#print axioms clockPairing_sum
#print axioms weak_matrix
#print axioms weak_momentum_density
#print axioms clockPairing_integrable
#print axioms positiveSlice_integrable
#print axioms potentialEnergy_integral
#print axioms potentialResponse_weak_integral
#print axioms potentialResponse_reduced_integral
end
end UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralPotentialTransport
