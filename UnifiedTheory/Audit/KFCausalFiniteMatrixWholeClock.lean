/- Full clock integration by parts from packet-dependent absolute kernel
bounds. No relative uniform response estimate or endpoint limit is assumed. -/
import UnifiedTheory.Audit.KFCausalFiniteMatrixClockTransport
import UnifiedTheory.Audit.KFCausalGaussianClockResponseIntegrability
import UnifiedTheory.Audit.KFCausalGaussianResponseIntegrability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalFiniteMatrixWholeClock
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalFiniteMatrixClockTransport
open KFCausalClockResponseTransport (clock pair weakPair weakSlope coefficient)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalShiftedClockAmplitude (clockAmplitude_memLp)
open KFCausalGaussianClockResponseIntegrability (weak_amplitude_memLp)

theorem pair_integrable (ε a b p q y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b)
    (hy : |y| ≤ Real.pi*ε/3) : Integrable (pair ε a b p q y) :=
  (clockAmplitude_memLp ε a p y hε ha hy).star.integrable_mul
    (clockAmplitude_memLp ε b q y hε hb hy)

theorem weakPair_integrable (ε a b p q y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b)
    (hy : |y| ≤ Real.pi*ε/3) : Integrable (weakPair ε a b p q y) := by
  have h1 := (weak_amplitude_memLp ε a p y hε ha hy).star.integrable_mul
    (clockAmplitude_memLp ε b q y hε hb hy)
  have h2 := (clockAmplitude_memLp ε a p y hε ha hy).star.integrable_mul
    (weak_amplitude_memLp ε b q y hε hb hy)
  convert h1.add h2 using 1
  funext s
  simp only [weakPair,pair,Pi.add_apply,Pi.mul_apply,Pi.star_apply,star_mul]
  ring

variable (N : ℕ) (ε y : ℝ) (a p : Fin N → ℝ) (C : Fin N → ℂ)
  (K : Fin N → Fin N → ℝ → ℂ)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (ha : ∀ i, 0 < a i)
  (hK : ∀ i j, ContDiff ℝ 1 (K i j))
  (hV : ∀ i j, ∃ M : ℝ, ∀ s, ‖K i j s‖ ≤ M)
  (hD : ∀ i j, ∃ M : ℝ, ∀ s, ‖deriv (K i j) s/(clock ε s:ℂ)‖ ≤ M)

include hε hy ha hK hV in
theorem value_integrable : Integrable (value N ε y a p C K) := by
  apply integrable_finset_sum _
  intro i _
  apply integrable_finset_sum _
  intro j _
  obtain ⟨M,hm⟩ := hV i j
  have hi := ((pair_integrable ε (a i) (a j) (p i) (p j) y hε (ha i) (ha j) hy).bdd_mul
    (hK i j).continuous.aestronglyMeasurable (Filter.Eventually.of_forall hm)).const_mul (conj (C i)*C j)
  simpa only [mul_assoc] using hi

include hε hy ha hK hV in
theorem weak_integrable : Integrable (weak N ε y a p C K) := by
  apply integrable_finset_sum _
  intro i _
  apply integrable_finset_sum _
  intro j _
  obtain ⟨M,hm⟩ := hV i j
  exact ((weakPair_integrable ε (a i) (a j) (p i) (p j) y hε (ha i) (ha j) hy).bdd_mul
    (hK i j).continuous.aestronglyMeasurable (Filter.Eventually.of_forall hm)).const_mul (conj (C i)*C j)

include hε hy ha hK hD in
theorem normalized_transport_integrable :
    Integrable (fun s => transport N ε y a p C K s/(clock ε s:ℂ)) := by
  have hc : Continuous (fun s => (clock ε s:ℂ)) := by unfold clock; fun_prop
  have hn (s : ℝ) : (clock ε s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by unfold clock; positivity)
  have hi (i j : Fin N) : Integrable (fun s => (conj (C i)*C j)*
      (pair ε (a i) (a j) (p i) (p j) y s*(deriv (K i j) s/(clock ε s:ℂ)))) := by
    obtain ⟨M,hm⟩ := hD i j
    exact ((pair_integrable ε (a i) (a j) (p i) (p j) y hε (ha i) (ha j) hy).mul_bdd
      ((hK i j).continuous_deriv_one.div hc hn).aestronglyMeasurable
      (Filter.Eventually.of_forall hm)).const_mul _
  have hs := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hi i j))
  simpa only [transport,Finset.sum_div,mul_div_assoc] using hs

include hε hy ha hK hV hD in
theorem reduced_integrable : Integrable (reduced N ε y a p C K) :=
  ((value_integrable N ε y a p C K hε hy ha hK hV).bdd_mul
    (Complex.continuous_ofReal.comp
      (KFCausalGaussianResponseIntegrability.coefficient_continuous ε y hε hy)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s => KFCausalGaussianResponseIntegrability.coefficient_bound ε y s hε hy))).sub
      (normalized_transport_integrable N ε y a p C K hε hy ha hK hD)

include hε hy ha hK hV in
theorem boundary_integrable : Integrable (boundary N ε y a p C K) := by
  have hc : Continuous (fun s => (clock ε s:ℂ)⁻¹) := by
    apply Continuous.inv₀
    · unfold clock; fun_prop
    · intro s; exact Complex.ofReal_ne_zero.mpr (by unfold clock; positivity)
  have hb (s : ℝ) : ‖(clock ε s:ℂ)⁻¹‖ ≤ 1/ε := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by unfold clock; positivity),← one_div]
    exact one_div_le_one_div_of_le hε (by unfold clock; linarith [Real.exp_pos s])
  simpa only [boundary,div_eq_mul_inv] using
    (value_integrable N ε y a p C K hε hy ha hK hV).mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)

include hε hy ha hK hV hD in
theorem full_clock_identity : (∫ s, weak N ε y a p C K s) = ∫ s, reduced N ε y a p C K s := by
  have hw := weak_integrable N ε y a p C K hε hy ha hK hV
  have hr := reduced_integrable N ε y a p C K hε hy ha hK hV hD
  have he := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun s => boundary_derivative N ε y a p C K hε hy hK s) (hw.sub hr)
    (boundary_integrable N ε y a p C K hε hy ha hK hV)
  rw [integral_sub hw hr] at he
  exact sub_eq_zero.mp he

#print axioms pair_integrable
#print axioms weakPair_integrable
#print axioms value_integrable
#print axioms weak_integrable
#print axioms normalized_transport_integrable
#print axioms reduced_integrable
#print axioms boundary_integrable
#print axioms full_clock_identity
end
end UnifiedTheory.Audit.KFCausalFiniteMatrixWholeClock
