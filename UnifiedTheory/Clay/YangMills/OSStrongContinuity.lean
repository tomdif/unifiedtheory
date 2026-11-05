/- Continuous kernel entries give strongly continuous, symmetric, positive
contractions on the reconstructed reflected Hilbert space. -/
import UnifiedTheory.Clay.YangMills.OSKernelShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSStrongContinuity
noncomputable section
open PositiveKernelForm KernelHilbertCompletion OSKernelShift
open scoped NNReal Topology

variable {ι : Type*} (K : PositiveKernel ι) (S : ShiftData K)

theorem kernel_pair (s t : ℝ≥0) (i j : ι) :
    K.value (S.shift s i,S.shift t j) = K.value (S.shift (s+t) i,j) := by
  rw [S.symmetric, S.add, ← S.symmetric]

theorem operator_symmetric (t : ℝ≥0) (v w : Hilbert K) :
    inner ℂ (operator K S t v) w = inner ℂ v (operator K S t w) := by
  refine (denseRange_embed K).induction_on v
    (isClosed_eq ((operator K S t).continuous.inner continuous_const)
      (continuous_id.inner continuous_const)) ?_
  intro x
  refine (denseRange_embed K).induction_on w
    (isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner (operator K S t).continuous)) ?_
  intro y
  rw [operator_embed, operator_embed, inner_embed, inner_embed]
  exact formal_symmetric K S t x y

theorem operator_positive (t : ℝ≥0) (v : Hilbert K) :
    0 ≤ (inner ℂ v (operator K S t v)).re := by
  have ht : t/2+t/2=t := by ring
  rw [← ht, ← operator_add, ← operator_symmetric]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem canonical_continuous
    (hc : ∀ i j, Continuous (fun t : ℝ≥0 => K.value (S.shift t i,j))) (i : ι) :
    Continuous (fun t : ℝ≥0 => canonical K (S.shift t i)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have he (t : ℝ≥0) : ‖canonical K (S.shift t i)-canonical K (S.shift s i)‖^2 =
      (K.value (S.shift (t+t) i,i)-K.value (S.shift (t+s) i,i) -
        K.value (S.shift (s+t) i,i)+K.value (S.shift (s+s) i,i)).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    change (inner ℂ (canonical K (S.shift t i)-canonical K (S.shift s i))
      (canonical K (S.shift t i)-canonical K (S.shift s i))).re = _
    simp only [inner_sub_left, inner_sub_right, canonical_inner, kernel_pair]
    simp only [Complex.sub_re, Complex.add_re]
    ring
  have hn : Continuous (fun t : ℝ≥0 =>
      ‖canonical K (S.shift t i)-canonical K (S.shift s i)‖) := by
    have hc' : Continuous (fun t : ℝ≥0 =>
        K.value (S.shift (t+t) i,i)-K.value (S.shift (t+s) i,i) -
          K.value (S.shift (s+t) i,i)+K.value (S.shift (s+s) i,i)) :=
      ((((hc i i).comp (continuous_id.add continuous_id)).sub
        ((hc i i).comp (continuous_id.add continuous_const))).sub
        ((hc i i).comp (continuous_const.add continuous_id))).add continuous_const
    have h := (Complex.continuous_re.comp hc').sqrt
    convert h using 1
    ext t
    dsimp only [Function.comp_def]
    rw [← he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_self, norm_zero] using hn.tendsto s

theorem embed_continuous
    (hc : ∀ i j, Continuous (fun t : ℝ≥0 => K.value (S.shift t i,j))) (x : Formal K) :
    Continuous (fun t : ℝ≥0 => operator K S t (embed K x)) := by
  classical
  induction x using Finsupp.induction with
  | zero =>
    simpa only [map_zero] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : Hilbert K)))
  | @single_add i c x hi hc' ih =>
    have he : embed K (Finsupp.single i c) = c • canonical K i := by
      change embed K (Finsupp.single i c) = c • embed K (Finsupp.single i 1)
      rw [← map_smul]
      congr 1
      change (Finsupp.single i c : ι →₀ ℂ) = c • Finsupp.single i 1
      simp
    simp only [map_add, he, map_smul, operator_canonical]
    exact (continuous_const.smul (canonical_continuous K S hc i)).add ih

/-- The dense test space and contraction estimate propagate continuity to every
state of the actual completed null quotient. -/
theorem operator_continuous
    (hc : ∀ i j, Continuous (fun t : ℝ≥0 => K.value (S.shift t i,j))) (v : Hilbert K) :
    Continuous (fun t : ℝ≥0 => operator K S t v) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨x,hx⟩ := (denseRange_embed K).exists_dist_lt v (show 0 < ε/3 by linarith)
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp
    (embed_continuous K S hc x).continuousAt (ε/3) (by linarith)
  refine ⟨δ,hδ,fun t ht => ?_⟩
  have hcontract (r : ℝ≥0) (a b : Hilbert K) :
      dist (operator K S r a) (operator K S r b) ≤ dist a b := by
    simp only [dist_eq_norm, ← map_sub]
    exact operator_contraction K S r (a-b)
  calc
    dist (operator K S t v) (operator K S s v) ≤
        dist (operator K S t v) (operator K S t (embed K x)) +
        dist (operator K S t (embed K x)) (operator K S s (embed K x)) +
        dist (operator K S s (embed K x)) (operator K S s v) :=
      by
        have h₁ := dist_triangle (operator K S t v) (operator K S t (embed K x))
          (operator K S s v)
        have h₂ := dist_triangle (operator K S t (embed K x))
          (operator K S s (embed K x)) (operator K S s v)
        linarith
    _ ≤ dist v (embed K x) +
        dist (operator K S t (embed K x)) (operator K S s (embed K x)) +
        dist (embed K x) v :=
      by linarith [hcontract t v (embed K x), hcontract s (embed K x) v]
    _ < ε := by
      have hd' := hd ht
      have hx' : dist (embed K x) v < ε/3 := by simpa only [dist_comm] using hx
      linarith

end
end UnifiedTheory.Clay.YangMills.OSStrongContinuity
