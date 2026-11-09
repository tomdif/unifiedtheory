/- The clock transport identity for a complete finite matrix kernel.
Independent clock amplitudes remain inside the sums. The boundary term
is explicit, and no uniform kernel estimate is assumed or concluded. -/
import UnifiedTheory.Audit.KFCausalClockResponseTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalFiniteMatrixClockTransport
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalClockResponseTransport (clock coefficient pair weakPair)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude_smooth)

variable (N : ℕ) (ε y : ℝ) (a p : Fin N → ℝ) (C : Fin N → ℂ)
  (K : Fin N → Fin N → ℝ → ℂ)

def value (s : ℝ) : ℂ :=
  ∑ i, ∑ j, (conj (C i)*C j)*K i j s*pair ε (a i) (a j) (p i) (p j) y s
def transport (s : ℝ) : ℂ :=
  ∑ i, ∑ j, (conj (C i)*C j)*(pair ε (a i) (a j) (p i) (p j) y s*deriv (K i j) s)
def weak (s : ℝ) : ℂ :=
  ∑ i, ∑ j, (conj (C i)*C j)*(K i j s*weakPair ε (a i) (a j) (p i) (p j) y s)
def reduced (s : ℝ) : ℂ :=
  (coefficient ε y s:ℂ)*value N ε y a p C K s-transport N ε y a p C K s/(clock ε s:ℂ)
def boundary (s : ℝ) : ℂ := value N ε y a p C K s/(clock ε s:ℂ)

theorem boundary_sum (s : ℝ) : boundary N ε y a p C K s =
    ∑ i, ∑ j, (conj (C i)*C j)*(K i j s*pair ε (a i) (a j) (p i) (p j) y s/(clock ε s:ℂ)) := by
  simp only [boundary,value,Finset.sum_div,mul_div_assoc,mul_assoc]

theorem derivative_sum (s : ℝ) :
    (∑ i, ∑ j, (conj (C i)*C j)*(K i j s*weakPair ε (a i) (a j) (p i) (p j) y s-
      pair ε (a i) (a j) (p i) (p j) y s*((coefficient ε y s:ℂ)*K i j s-
        deriv (K i j) s/(clock ε s:ℂ)))) =
      weak N ε y a p C K s-reduced N ε y a p C K s := by
  have he (i j : Fin N) :
      (conj (C i)*C j)*(K i j s*weakPair ε (a i) (a j) (p i) (p j) y s-
        pair ε (a i) (a j) (p i) (p j) y s*((coefficient ε y s:ℂ)*K i j s-
          deriv (K i j) s/(clock ε s:ℂ))) =
        (conj (C i)*C j)*(K i j s*weakPair ε (a i) (a j) (p i) (p j) y s)-
          (coefficient ε y s:ℂ)*((conj (C i)*C j)*K i j s*pair ε (a i) (a j) (p i) (p j) y s)+
          ((conj (C i)*C j)*(pair ε (a i) (a j) (p i) (p j) y s*deriv (K i j) s))/(clock ε s:ℂ) := by ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_div]
  unfold weak reduced value transport
  ring

variable (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hK : ∀ i j, ContDiff ℝ 1 (K i j))

include hε hy hK in
theorem boundary_derivative (s : ℝ) :
    HasDerivAt (boundary N ε y a p C K)
      (weak N ε y a p C K s-reduced N ε y a p C K s) s := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (KFCausalClockResponseTransport.boundary_derivative ε (a i) (a j) (p i) (p j) y s hε hy
        (K i j) (deriv (K i j) s)
        (((hK i j).differentiable (by norm_num)).differentiableAt.hasDerivAt)).const_mul (conj (C i)*C j)))
  simpa only [← boundary_sum,derivative_sum] using hd

include hε hy hK in
theorem value_continuous : Continuous (value N ε y a p C K) := by
  apply continuous_finset_sum _
  intro i _
  apply continuous_finset_sum _
  intro j _
  exact (continuous_const.mul (hK i j).continuous).mul
    (((clockAmplitude_smooth ε (a i) (p i) y hε hy).continuous.star).mul
      (clockAmplitude_smooth ε (a j) (p j) y hε hy).continuous)

include hε hy hK in
theorem transport_continuous : Continuous (transport N ε y a p C K) := by
  apply continuous_finset_sum _
  intro i _
  apply continuous_finset_sum _
  intro j _
  exact continuous_const.mul
    ((((clockAmplitude_smooth ε (a i) (p i) y hε hy).continuous.star).mul
      (clockAmplitude_smooth ε (a j) (p j) y hε hy).continuous).mul
        (hK i j).continuous_deriv_one)

include hε hy hK in
theorem weak_continuous : Continuous (weak N ε y a p C K) := by
  have hi := KFCausalShiftedGaussianLongitudinalDifferential.inverseClock_continuous ε y hε hy
  have hz := (KFCausalClockFloorRelativeShift.argument_smooth ε y).continuous
  have hs (i : Fin N) : Continuous (KFCausalClockResponseTransport.weakSlope ε (a i) (p i) y) := by
    unfold KFCausalClockResponseTransport.weakSlope
    fun_prop
  apply continuous_finset_sum _
  intro i _
  apply continuous_finset_sum _
  intro j _
  exact continuous_const.mul ((hK i j).continuous.mul
    (((((clockAmplitude_smooth ε (a i) (p i) y hε hy).continuous.star).mul
      (clockAmplitude_smooth ε (a j) (p j) y hε hy).continuous)).mul ((hs i).star.add (hs j))))

include hε hy hK in
theorem reduced_continuous : Continuous (reduced N ε y a p C K) := by
  have hi := KFCausalShiftedGaussianLongitudinalDifferential.inverseClock_continuous ε y hε hy
  have hc : Continuous (clock ε) := by unfold clock; fun_prop
  have hn (s : ℝ) : clock ε s ≠ 0 := by unfold clock; positivity
  have hb : Continuous (coefficient ε y) :=
    (continuous_const.div hc hn).sub
      (Complex.continuous_re.comp (hi.add (continuous_const.mul (hi.pow 2))))
  exact ((Complex.continuous_ofReal.comp hb).mul
    (value_continuous N ε y a p C K hε hy hK)).sub
    ((transport_continuous N ε y a p C K hε hy hK).div
      (Complex.continuous_ofReal.comp hc) (fun s => Complex.ofReal_ne_zero.mpr (hn s)))

include hε hy hK in
theorem interval_response (l r : ℝ) :
    (∫ s in l..r, weak N ε y a p C K s) =
      boundary N ε y a p C K r-boundary N ε y a p C K l+
        ∫ s in l..r, reduced N ε y a p C K s := by
  have hw : IntervalIntegrable (weak N ε y a p C K) volume l r :=
    (weak_continuous N ε y a p C K hε hy hK).intervalIntegrable l r
  have hr : IntervalIntegrable (reduced N ε y a p C K) volume l r :=
    (reduced_continuous N ε y a p C K hε hy hK).intervalIntegrable l r
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ Set.uIcc l r) => boundary_derivative N ε y a p C K hε hy hK s) (hw.sub hr)
  rw [intervalIntegral.integral_sub hw hr] at he
  exact sub_eq_iff_eq_add.mp he

#print axioms boundary_sum
#print axioms derivative_sum
#print axioms boundary_derivative
#print axioms value_continuous
#print axioms transport_continuous
#print axioms weak_continuous
#print axioms reduced_continuous
#print axioms interval_response
end
end UnifiedTheory.Audit.KFCausalFiniteMatrixClockTransport
