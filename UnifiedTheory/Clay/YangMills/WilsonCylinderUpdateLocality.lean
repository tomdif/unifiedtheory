/- Actual support propagation and disjoint-support cross-energy cancellation
for the open Wilson cylinder's random-color Gibbs update. Auxiliary update
steps are not physical time; the geometric time support is proved separately. -/
import UnifiedTheory.Clay.YangMills.WilsonCylinderContraction
import UnifiedTheory.Clay.YangMills.WilsonSupportPropagation
import UnifiedTheory.Clay.YangMills.CoordinateSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCylinderUpdateLocality
noncomputable section
open MeasureTheory RegulatedGauge WilsonCylinderGeometry WilsonSingleLinkStaples
open WilsonCylinderConditionalInfluence WilsonCylinderContraction WilsonCylinderColors
open FiniteIncidenceInfluence FiniteProductInfluence ParallelOscillation CompactGibbsBlockUpdate

variable (n L : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n L) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (Plaquette n L) := Classical.decEq _
local instance colorDecidableEq : DecidableEq Color := Classical.decEq _
local instance coordinateProbability (β : ℝ) (a : Link n L) (U : State n L) :
    IsProbabilityMeasure (coordinateLaw n L β U a) := coordinateLaw_probability n L β U a

theorem subset_layer (A : Finset (Link n L)) : A ⊆ layer n L A :=
  fun _ ha => (mem_layer n L A _).mpr (Or.inl ha)

/-- No shared plaquette can connect the support to a coordinate outside its actual layer. -/
theorem multiplicity_zero_of_outside (A : Finset (Link n L)) (a b : Link n L)
    (ha : a ∈ A) (hb : b ∉ layer n L A) :
    FiniteIncidenceInfluence.multiplicity (incidentLinks n L) a b = 0 := by
  unfold FiniteIncidenceInfluence.multiplicity sharedFaces
  split_ifs with hab
  · rfl
  · apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨p, hp⟩
    have hpa := (mem_incidentFaces _ _ _).mp (Finset.mem_inter.mp hp).1
    have hpb := (mem_incidentFaces _ _ _).mp (Finset.mem_inter.mp hp).2
    exact hb ((mem_layer n L A b).mpr (Or.inr ⟨a, ha, p, hpa, hpb⟩))

theorem coefficient_zero_of_outside (β : ℝ) (A : Finset (Link n L)) (a b : Link n L)
    (ha : a ∈ A) (hb : b ∉ layer n L A) :
    coefficient (incidentLinks n L) β a b = 0 := by
  rw [coefficient, multiplicity_zero_of_outside n L A a b ha hb]
  simp

/-- The proved sparse conditional influences have no budget outside one face-neighbor layer. -/
theorem colorBound_zero_of_outside (β : ℝ) (A : Finset (Link n L)) (d : Link n L → ℝ)
    (hd : ∀ a, a ∉ A → d a = 0) (b : Link n L) (hb : b ∉ layer n L A) :
    colorBound (Color := Color) (coefficient (incidentLinks n L) β) d b = 0 := by
  have hbA : b ∉ A := fun ha => hb (subset_layer n L A ha)
  have hs : ∑ a, coefficient (incidentLinks n L) β a b * d a = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a ∈ A
    · rw [coefficient_zero_of_outside n L β A a b ha hb, zero_mul]
    · rw [hd a ha, mul_zero]
  simp only [colorBound, hd b hbA, hs, mul_zero, add_zero]

/-- Actual update locality follows from geometry and proved conditional influence, not a premise. -/
theorem update_dependsOn (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(State n L, ℝ)) (A : Finset (Link n L))
    (hF : DependsOn (F : State n L → ℝ) (A : Set (Link n L))) :
    DependsOn (update n L β heven F : State n L → ℝ) (layer n L A : Set (Link n L)) := by
  let d : Link n L → ℝ := fun a => if a ∈ A then 2 * ‖F‖ else 0
  have hd : ∀ a, a ∉ A → d a = 0 := fun a ha => if_neg ha
  have hosc : OscBound (update n L β heven F)
      (colorBound (Color := Color) (coefficient (incidentLinks n L) β) d) := by
    intro j x y hxy
    rw [update_eq_colorAverage, update_eq_colorAverage]
    exact color_oscillation (fun a U => coordinateLaw n L β U a)
      (color n L heven) (coefficient (incidentLinks n L) β)
      (WilsonCylinderContraction.localInfluence n L β hβ)
      F d (WilsonSupportPropagation.supported_oscillation F A hF) j x y hxy
  exact WilsonSupportPropagation.dependsOn_of_oscBound _ _ hosc (layer n L A)
    (colorBound_zero_of_outside n L β A d hd)

/-- Every actual auxiliary iterate stays in its finite actual cylinder neighborhood. -/
theorem iterate_dependsOn (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(State n L, ℝ)) (A : Finset (Link n L))
    (hF : DependsOn (F : State n L → ℝ) (A : Set (Link n L))) (k : ℕ) :
    DependsOn (updateIterate (update n L β heven) k F : State n L → ℝ)
      (neighborhood n L A k : Set (Link n L)) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    exact update_dependsOn n L β hβ heven (updateIterate (update n L β heven) k F)
      (neighborhood n L A k) ih

/-- Disjointly supported observables factor under every actual independent Wilson block update. -/
theorem blockAverage_mul_of_disjoint (β : ℝ) (B : Finset (Link n L))
    (hB : Independent n L B) (S T : Finset (Link n L)) (hST : Disjoint S T)
    (F G : C(State n L, ℝ)) (hF : DependsOn (F : State n L → ℝ) (S : Set (Link n L)))
    (hG : DependsOn (G : State n L → ℝ) (T : Set (Link n L))) :
    blockAverage (compactHaar Q) (stateAction n L β) B (F * G) =
      blockAverage (compactHaar Q) (stateAction n L β) B F *
        blockAverage (compactHaar Q) (stateAction n L β) B G := by
  ext U
  simp only [ContinuousMap.mul_apply]
  rw [WilsonCylinderParallelKernel.blockAverage_eq_parallelAverage n L β U B hB (F * G),
    WilsonCylinderParallelKernel.blockAverage_eq_parallelAverage n L β U B hB F,
    WilsonCylinderParallelKernel.blockAverage_eq_parallelAverage n L β U B hB G]
  exact CoordinateSupport.integral_mul_of_disjoint
    (ParallelOscillation.updateMarginal (fun a V => coordinateLaw n L β V a) B U)
    S T hST F G F.continuous G.continuous hF hG

/-- Projection and stationarity turn the conditional product identity into a pairing identity. -/
theorem block_pairing_of_disjoint (β : ℝ) (B : Finset (Link n L))
    (hB : Independent n L B) (S T : Finset (Link n L)) (hST : Disjoint S T)
    (F G : C(State n L, ℝ)) (hF : DependsOn (F : State n L → ℝ) (S : Set (Link n L)))
    (hG : DependsOn (G : State n L → ℝ) (T : Set (Link n L))) :
    (∫ U, F U * blockAverage (compactHaar Q)
      (stateAction n L β) B G U ∂law n L β) =
        ∫ U, F U * G U ∂law n L β := by
  have hs := blockAverage_stationary (compactHaar Q)
    (stateAction n L β) B (F * G)
  rw [blockAverage_mul_of_disjoint n L β B hB S T hST F G hF hG] at hs
  have hr := blockAverage_reversible (compactHaar Q)
    (stateAction n L β) B F
    (blockAverage (compactHaar Q) (stateAction n L β) B G)
  rw [blockAverage_idempotent] at hr
  exact hr.trans hs

/-- A random color update has zero cross-energy between disjointly supported tests. -/
theorem update_pairing_of_disjoint (β : ℝ) (heven : 2 ∣ n)
    (S T : Finset (Link n L)) (hST : Disjoint S T)
    (F G : C(State n L, ℝ)) (hF : DependsOn (F : State n L → ℝ) (S : Set (Link n L)))
    (hG : DependsOn (G : State n L → ℝ) (T : Set (Link n L))) :
    (∫ U, F U * update n L β heven G U ∂law n L β) =
      ∫ U, F U * G U ∂law n L β := by
  have he (U : State n L) : F U * update n L β heven G U =
      (1 / 8 : ℝ) * ∑ c : Color, F U *
        blockAverage (compactHaar Q) (stateAction n L β)
          (colorBlock n L heven c) G U := by
    rw [update_apply, ← mul_assoc, mul_comm (F U) (1 / 8), mul_assoc, Finset.mul_sum]
  simp_rw [he]
  rw [integral_const_mul]
  have hi (c : Color) : Integrable (fun U : State n L => F U *
      blockAverage (compactHaar Q) (stateAction n L β)
        (colorBlock n L heven c) G U) (law n L β) :=
    (F.continuous.mul (blockAverage (compactHaar Q) (stateAction n L β)
      (colorBlock n L heven c) G).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [integral_finset_sum Finset.univ (fun c _ => hi c)]
  simp_rw [block_pairing_of_disjoint n L β _ (colorBlock_independent n L heven _) S T hST F G hF hG]
  simp only [Finset.sum_const, Finset.card_univ, color_card, nsmul_eq_mul]
  ring

/-- The requested exact cross-Dirichlet cancellation in the original Wilson law. -/
theorem cross_dirichlet_zero (β : ℝ) (heven : 2 ∣ n)
    (S T : Finset (Link n L)) (hST : Disjoint S T)
    (F G : C(State n L, ℝ)) (hF : DependsOn (F : State n L → ℝ) (S : Set (Link n L)))
    (hG : DependsOn (G : State n L → ℝ) (T : Set (Link n L))) :
    (∫ U, F U * (G U - update n L β heven G U) ∂law n L β) = 0 := by
  have hi : Integrable (fun U : State n L => F U * G U) (law n L β) :=
    (F.continuous.mul G.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun U : State n L => F U * update n L β heven G U) (law n L β) :=
    (F.continuous.mul (update n L β heven G).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [mul_sub]
  rw [integral_sub hi hj, update_pairing_of_disjoint n L β heven S T hST F G hF hG, sub_self]

/-- Reversibility moves the exact cancellation to the first observable for telescoping. -/
theorem disjoint_pairing_eq_update (β : ℝ) (heven : 2 ∣ n)
    (S T : Finset (Link n L)) (hST : Disjoint S T)
    (F G : C(State n L, ℝ)) (hF : DependsOn (F : State n L → ℝ) (S : Set (Link n L)))
    (hG : DependsOn (G : State n L → ℝ) (T : Set (Link n L))) :
    (∫ U, F U * G U ∂law n L β) =
      ∫ U, update n L β heven F U * G U ∂law n L β := by
  rw [← update_reversible]
  exact (update_pairing_of_disjoint n L β heven S T hST F G hF hG).symm

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderUpdateLocality
