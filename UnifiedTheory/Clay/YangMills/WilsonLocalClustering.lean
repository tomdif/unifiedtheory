/- Spatial clustering for the actual periodic Wilson law, obtained from
proved update locality, disjoint-support cancellation and actual L2 decay.
This is not an identification of the sampler clock with physical time. -/
import UnifiedTheory.Clay.YangMills.WilsonParallelL2
import UnifiedTheory.Clay.YangMills.WilsonDisjointDirichlet
import UnifiedTheory.Clay.YangMills.WilsonSupportPropagation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonLocalClustering
noncomputable section
open MeasureTheory WilsonParallelContraction WilsonParallelPoincare
open WilsonIndependentBlocks ParallelOscillation WilsonSupportPropagation

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

omit [Fact (1 < n)] in
theorem centered_dependsOn (β : ℝ) (F : C(State n, ℝ)) (A : Finset (Link n))
    (hF : DependsOn (F : State n → ℝ) (A : Set (Link n))) :
    DependsOn (centered n β F : State n → ℝ) (A : Set (Link n)) := by
  intro U V hUV
  change F U - (∫ W, F W ∂law n β) = F V - (∫ W, F W ∂law n β)
  rw [hF hUV]

omit [Fact (1 < n)] in
theorem centered_norm_eq_sqrt_variance (β : ℝ) (F : C(State n, ℝ)) :
    ‖ContinuousMap.toLp 2 (law n β) ℝ (centered n β F)‖ =
      Real.sqrt (∫ U, (F U - ∫ V, F V ∂law n β)^2 ∂law n β) := by
  have hs := ContinuousUpdateGap.embedding_square (law n β) (centered n β F)
  have he : ‖ContinuousMap.toLp 2 (law n β) ℝ (centered n β F)‖ ^ 2 =
      ∫ U, (F U - ∫ V, F V ∂law n β)^2 ∂law n β := by
    simpa only [ContinuousUpdateGap.pairing, centered, ContinuousMap.sub_apply,
      ContinuousMap.const_apply, pow_two] using hs
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

/-- Exact telescoping through the actual random-color update. The geometric
premise is separation of finite plaquette-neighborhoods, not a decay premise. -/
theorem pairing_eq_iterate (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F G : C(State n, ℝ)) (A B : Finset (Link n))
    (hF : DependsOn (F : State n → ℝ) (A : Set (Link n)))
    (hG : DependsOn (G : State n → ℝ) (B : Set (Link n)))
    (d : ℕ) (hsep : ∀ j, j < d → Disjoint (neighborhood n A j) B) :
    (∫ U, F U * G U ∂law n β) =
      ∫ U, updateIterate (update n β heven) d F U * G U ∂law n β := by
  induction d with
  | zero => rfl
  | succ d ih =>
    calc
      _ = ∫ U, updateIterate (update n β heven) d F U * G U ∂law n β :=
        ih (fun j hj => hsep j (Nat.lt_succ_of_lt hj))
      _ = _ := WilsonDisjointDirichlet.disjoint_pairing_eq_update n β heven
        (neighborhood n A d) B (hsep d (Nat.lt_succ_self d)) _ G
        (iterate_dependsOn n β hβ heven F A hF d) hG

/-- Volume-independent geometric covariance decay for the genuine periodic
Wilson law. At 0≤β<1/36 its explicit rate is strictly below one. -/
theorem covariance_decay (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F G : C(State n, ℝ)) (A B : Finset (Link n))
    (hF : DependsOn (F : State n → ℝ) (A : Set (Link n)))
    (hG : DependsOn (G : State n → ℝ) (B : Set (Link n)))
    (d : ℕ) (hsep : ∀ j, j < d → Disjoint (neighborhood n A j) B) :
    |∫ U, (F U - ∫ V, F V ∂law n β) * (G U - ∫ V, G V ∂law n β) ∂law n β| ≤
      rate β ^ d * Real.sqrt (∫ U, (F U - ∫ V, F V ∂law n β)^2 ∂law n β) *
        Real.sqrt (∫ U, (G U - ∫ V, G V ∂law n β)^2 ∂law n β) := by
  change |∫ U, centered n β F U * centered n β G U ∂law n β| ≤ _
  rw [pairing_eq_iterate n β hβ heven _ _ A B
    (centered_dependsOn n β F A hF) (centered_dependsOn n β G B hG) d hsep]
  have h := WilsonParallelL2.centered_pairing_decay n β hβ heven
    (centered n β F) (centered n β G) (centered_mean n β F) d
  simpa only [centered_norm_eq_sqrt_variance] using h

/-- A single terminal-neighborhood separation suffices for all earlier layers. -/
theorem covariance_decay_of_neighborhood (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F G : C(State n, ℝ)) (A B : Finset (Link n))
    (hF : DependsOn (F : State n → ℝ) (A : Set (Link n)))
    (hG : DependsOn (G : State n → ℝ) (B : Set (Link n)))
    (d : ℕ) (hsep : Disjoint (neighborhood n A d) B) :
    |∫ U, (F U - ∫ V, F V ∂law n β) * (G U - ∫ V, G V ∂law n β) ∂law n β| ≤
      rate β ^ (d + 1) * Real.sqrt (∫ U, (F U - ∫ V, F V ∂law n β)^2 ∂law n β) *
        Real.sqrt (∫ U, (G U - ∫ V, G V ∂law n β)^2 ∂law n β) := by
  apply covariance_decay n β hβ heven F G A B hF hG (d + 1)
  intro j hj
  exact hsep.mono_left (neighborhood_mono n A (Nat.lt_succ_iff.mp hj))


/-- The final covariance bound explicitly names the original Wilson measure.
The support hypotheses are on its proved positive-link coordinate pullbacks. -/
theorem original_wilson_covariance_decay (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F G : C(RegulatedGauge.Configuration (PeriodicLattice4.Vertex n) Q, ℝ))
    (A B : Finset (Link n))
    (hF : DependsOn (pullback n F : State n → ℝ) (A : Set (Link n)))
    (hG : DependsOn (pullback n G : State n → ℝ) (B : Set (Link n)))
    (d : ℕ) (hsep : ∀ j, j < d → Disjoint (neighborhood n A j) B) :
    let ρ := PeriodicLattice4.wilsonLaw n Q WilsonSingleLinkStaples.character β 2
    |∫ U, (F U - ∫ V, F V ∂ρ) * (G U - ∫ V, G V ∂ρ) ∂ρ| ≤
      rate β ^ d * Real.sqrt (∫ U, (F U - ∫ V, F V ∂ρ)^2 ∂ρ) *
        Real.sqrt (∫ U, (G U - ∫ V, G V ∂ρ)^2 ∂ρ) := by
  let ρ := PeriodicLattice4.wilsonLaw n Q WilsonSingleLinkStaples.character β 2
  have hmF : (∫ U, pullback n F U ∂law n β) = ∫ U, F U ∂ρ :=
    (WilsonCoordinateLaw.wilson_preserving n β).integral_comp
      (WilsonCoordinateLaw.configEquiv n).measurableEmbedding F
  have hmG : (∫ U, pullback n G U ∂law n β) = ∫ U, G U ∂ρ :=
    (WilsonCoordinateLaw.wilson_preserving n β).integral_comp
      (WilsonCoordinateLaw.configEquiv n).measurableEmbedding G
  have hvF : (∫ U, (pullback n F U - ∫ V, F V ∂ρ)^2 ∂law n β) =
      ∫ U, (F U - ∫ V, F V ∂ρ)^2 ∂ρ :=
    (WilsonCoordinateLaw.wilson_preserving n β).integral_comp
      (WilsonCoordinateLaw.configEquiv n).measurableEmbedding
      (fun U => (F U - ∫ V, F V ∂ρ)^2)
  have hvG : (∫ U, (pullback n G U - ∫ V, G V ∂ρ)^2 ∂law n β) =
      ∫ U, (G U - ∫ V, G V ∂ρ)^2 ∂ρ :=
    (WilsonCoordinateLaw.wilson_preserving n β).integral_comp
      (WilsonCoordinateLaw.configEquiv n).measurableEmbedding
      (fun U => (G U - ∫ V, G V ∂ρ)^2)
  have hc : (∫ U, (pullback n F U - ∫ V, F V ∂ρ) *
      (pullback n G U - ∫ V, G V ∂ρ) ∂law n β) =
        ∫ U, (F U - ∫ V, F V ∂ρ) * (G U - ∫ V, G V ∂ρ) ∂ρ :=
    (WilsonCoordinateLaw.wilson_preserving n β).integral_comp
      (WilsonCoordinateLaw.configEquiv n).measurableEmbedding
      (fun U => (F U - ∫ V, F V ∂ρ) * (G U - ∫ V, G V ∂ρ))
  have h := covariance_decay n β hβ heven (pullback n F) (pullback n G)
    A B hF hG d hsep
  rw [hmF, hmG, hc, hvF, hvG] at h
  exact h

end
end UnifiedTheory.Clay.YangMills.WilsonLocalClustering
