/- Local L2 envelopes for moving coefficients, real field shifts and
imaginary translations. Constants may depend on the finite family and
compact parameter interval; no state-independent response estimate is
assumed here. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierField
import UnifiedTheory.Audit.KFCausalTransverseClockDifferentiation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalNeutralFourierMovingEnvelope
noncomputable section
open MeasureTheory
open KFCausalNeutralFourierShift (line packet_strip_bound)
open KFCausalNeutralFourierField (fieldLine)
open KFCausalNeutralLinePackets (entire)
open KFCausalNeutralLineDomain (family)
open KFCausalNeutralTranslationEnvelope (radius gaussianRadius)

variable (n : ℕ) (β : ℝ) (hβ : 0 < β) (b : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
include hβ

theorem line_bound (M : Fin n → ℝ) (hM : ∀ i, 0 ≤ M i) (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : Fin n → ℂ) (x y : ℝ),
      (∀ i, ‖c i‖ ≤ M i) → |y| ≤ R →
      ‖line n β b c P y x‖ ≤ B*Real.exp (-(β/4)*x^2) := by
  choose B hB hb using fun i => packet_strip_bound β hβ (b i) (P i) R hR
  refine ⟨∑ i, M i*B i,Finset.sum_nonneg (fun i _ => mul_nonneg (hM i) (hB i)),?_⟩
  intro c x y hc hy
  change ‖∑ i, c i*entire β (b i) (P i) ((x:ℂ)+(y:ℂ)*Complex.I)‖ ≤ _
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul,mul_assoc]
  exact mul_le_mul (hc i) (hb i x y hy) (norm_nonneg _) (hM i)

theorem field_envelope (j : ℕ) (M : Fin n → ℝ) (hM : ∀ i, 0 ≤ M i)
    (A R : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R) :
    ∃ D : ℝ → ℝ, Continuous D ∧ MemLp D 2 volume ∧ (∀ x, 0 ≤ D x) ∧
      ∀ (c : Fin n → ℂ) (a y x : ℝ), (∀ i, ‖c i‖ ≤ M i) → |a| ≤ A → |y| ≤ R →
        ‖fieldLine n β b c P j a y x‖ ≤ D x := by
  obtain ⟨B,hB,hb⟩ := line_bound n β hβ b P M hM R hR
  let K := (A+1)^j*B
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg (by linarith) j) hB
  refine ⟨fun x => K*gaussianRadius (β/2) j x,?_,
    (KFCausalNeutralTranslationEnvelope.gaussianRadius_memLp (β/2) (by positivity) j).const_mul K,?_,?_⟩
  · unfold gaussianRadius radius
    fun_prop
  · intro x
    unfold gaussianRadius radius
    positivity
  · intro c a y x hc ha hy
    have hn : ‖((x+a:ℝ):ℂ)‖ ≤ (A+1)*radius x := by
      simpa only [Complex.ofReal_add] using
        KFCausalNeutralTranslationEnvelope.translated_radius A hA (a:ℂ)
          (by simpa only [Complex.norm_real,Real.norm_eq_abs] using ha) x
    have hr : 0 ≤ radius x := (KFCausalNeutralTranslationEnvelope.radius_one_le x).trans' (by norm_num)
    have hp := pow_le_pow_left₀ (norm_nonneg _) hn j
    have hh := mul_le_mul hp (hb c x y hc hy) (norm_nonneg _) (by positivity : 0 ≤ ((A+1)*radius x)^j)
    unfold fieldLine
    rw [norm_mul,norm_pow]
    apply hh.trans_eq
    unfold K gaussianRadius
    rw [mul_pow]
    have he : β/2/2 = β/4 := by ring
    rw [he]
    ring

omit n β hβ b P in
theorem real_local_bound (a : ℝ → ℝ) (ha : Continuous a) (s : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc (s-1) (s+1), |a t| ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn ha.continuousOn
  exact ⟨max 0 M,le_max_left _ _,fun t ht => (hM t ht).trans (le_max_right _ _)⟩

theorem moving_envelope (j : ℕ) (C : ℝ → Fin n → ℂ) (a y : ℝ → ℝ)
    (hC : ∀ i, Continuous (fun t => C t i)) (ha : Continuous a) (hy : Continuous y) (s : ℝ) :
    ∃ D : ℝ → ℝ, Continuous D ∧ MemLp D 2 volume ∧ (∀ x, 0 ≤ D x) ∧
      ∀ t ∈ Set.Icc (s-1) (s+1), ∀ x,
        ‖fieldLine n β b (C t) P j (a t) (y t) x‖ ≤ D x := by
  choose M hM hb using fun i =>
    KFCausalTransverseClockDifferentiation.continuous_local_bound (fun t => C t i) (hC i) s
  obtain ⟨A,hA,haB⟩ := real_local_bound a ha s
  obtain ⟨R,hR,hyB⟩ := real_local_bound y hy s
  obtain ⟨D,hD,hD₂,hD₀,hd⟩ := field_envelope n β hβ b P j M hM A R hA hR
  exact ⟨D,hD,hD₂,hD₀,fun t ht x => hd (C t) (a t) (y t) x
    (fun i => hb i t ht) (haB t ht) (hyB t ht)⟩

#print axioms line_bound
#print axioms field_envelope
#print axioms real_local_bound
#print axioms moving_envelope
end
end UnifiedTheory.Audit.KFCausalNeutralFourierMovingEnvelope
