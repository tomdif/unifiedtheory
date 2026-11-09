/- Bounded form vectors converge weakly when their injective physical
embedding converges strongly. The dense test family is derived. -/
import UnifiedTheory.Audit.KFCausalMassGram
import UnifiedTheory.Audit.KFCausalWeakEnergyContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalWeakEmbeddingLimit
noncomputable section
open Filter
open scoped Topology
variable {V H E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem weak_of_dense_tests (J : E → V) (hJ : DenseRange J) (u : ℕ → V) (x : V)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ n, ‖u n‖ ≤ M)
    (hw : ∀ v, Tendsto (fun n => inner ℂ (u n) (J v)) atTop (𝓝 (inner ℂ x (J v)))) :
    ∀ y, Tendsto (fun n => inner ℂ (u n) y) atTop (𝓝 (inner ℂ x y)) := by
  intro y
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hd : 0 < 2*(M+‖x‖+1) := by positivity
  obtain ⟨z,⟨v,rfl⟩,hv⟩ := Metric.mem_closure_iff.mp (hJ y) (δ/(2*(M+‖x‖+1))) (div_pos hδ hd)
  have hv' : ‖y-J v‖ < δ/(2*(M+‖x‖+1)) := by simpa only [dist_eq_norm] using hv
  have hs := (lt_div_iff₀ hd).mp hv'
  have hh := Metric.tendsto_nhds.mp (hw v) (δ/2) (by positivity)
  filter_upwards [hh] with n hn
  have hn' : ‖inner ℂ (u n-x) (J v)‖ < δ/2 := by
    simpa only [dist_eq_norm,inner_sub_left] using hn
  have hu : ‖u n-x‖ ≤ M+‖x‖ := by linarith only [norm_sub_le (u n) x,hb n]
  have hi := (norm_inner_le_norm (𝕜 := ℂ) (u n-x) (y-J v)).trans
    (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
  have he : inner ℂ (u n-x) y = inner ℂ (u n-x) (J v)+inner ℂ (u n-x) (y-J v) := by
    rw [inner_sub_right]
    ring
  rw [dist_eq_norm,← inner_sub_left,he]
  have ht := norm_add_le (inner ℂ (u n-x) (J v)) (inner ℂ (u n-x) (y-J v))
  nlinarith only [ht,hi,hn',hs,norm_nonneg (y-J v)]

theorem weak_of_embedding [CompleteSpace V] [CompleteSpace H]
    (J : V →L[ℂ] H) (hJ : Function.Injective J) (u : ℕ → V) (x : V)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ n, ‖u n‖ ≤ M)
    (hp : Tendsto (fun n => J (u n)) atTop (𝓝 (J x))) :
    ∀ y, Tendsto (fun n => inner ℂ (u n) y) atTop (𝓝 (inner ℂ x y)) := by
  apply weak_of_dense_tests (UnifiedTheory.Audit.KFCausalBoundedFormCurve.gram J)
    (UnifiedTheory.Audit.KFCausalMassGram.gram_dense J hJ) u x M hM hb
  intro v
  simpa only [UnifiedTheory.Audit.KFCausalMassGram.gram_right_pairing] using
    hp.inner (𝕜 := ℂ) (tendsto_const_nhds (x := J v))

theorem real_pairing_limit (L : V →L[ℂ] H) (u : ℕ → V) (v : V) (b : ℕ → ℝ) (c : ℝ)
    (hu : Tendsto u atTop (𝓝 v)) (hb : ∀ n, b n = (inner ℂ (L (u n)) (L v)).re)
    (hc : ‖L v‖^2 = c) : Tendsto b atTop (𝓝 c) := by
  have hs := (L.continuous.tendsto v).comp hu
  have hi : Tendsto (fun n => (inner ℂ (L (u n)) (L v)).re) atTop (𝓝 ((inner ℂ (L v) (L v)).re)) :=
    (Complex.continuous_re.tendsto (inner ℂ (L v) (L v))).comp
    (hs.inner (𝕜 := ℂ) (tendsto_const_nhds (x := L v)))
  have he : (inner ℂ (L v) (L v)).re = ‖L v‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) (L v)
  rw [he,hc] at hi
  exact hi.congr' (Eventually.of_forall (fun n => (hb n).symm))

#print axioms weak_of_dense_tests
#print axioms weak_of_embedding
#print axioms real_pairing_limit
end
end UnifiedTheory.Audit.KFCausalWeakEmbeddingLimit
