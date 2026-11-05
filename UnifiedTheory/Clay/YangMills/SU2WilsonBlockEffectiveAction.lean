/- Exact source-dependent effective action of an independent Wilson block.
The retained interaction is a sum of nonlinear Haar potentials with the
necessary reference-action correction. It is not assumed to remain Wilson. -/
import UnifiedTheory.Clay.YangMills.SU2WilsonBlockApproximation
import UnifiedTheory.Clay.YangMills.SU2InducedAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2WilsonBlockEffectiveAction
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonIndependentBlocks
open WilsonSingleLinkStaples SU2WilsonBlockApproximation SU2HaarTilt SU2InducedAction
open scoped Quaternion RealInnerProductSpace

section Product
variable {I X : Type*} [Fintype I] [TopologicalSpace X] [CompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem log_integral_affine_sum (A : I → X → ℝ) (hA : ∀ i, Continuous (A i)) (c : ℝ) :
    -(Real.log (∫ V : I → X, Real.exp (-(c + ∑ i, A i (V i)))
      ∂Measure.pi (fun _ => μ))) =
      c + ∑ i, -(Real.log (∫ q, Real.exp (-A i q) ∂μ)) := by
  have h := WilsonSeparatedSources.affine_log_partition_product μ A
    (fun _ _ => 0) hA (fun _ => continuous_const) c 0 0
  simp only [CompactGibbsSource.partition, CompactGibbsSource.weight,
    CompactGibbsSource.action, zero_mul, sub_zero, add_zero] at h
  rw [h, neg_add, neg_neg, Finset.sum_neg_distrib]

end Product

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

def staple (S : Finset (Edge (Vertex n)))
    (e : {e : Edge (Vertex n) // e ∈ S}) (b : WilsonBlockMarginal.Outside (G := Q) S) : ℍ :=
  exteriorStaple n (edgeCoord n e.val).1 (edgeCoord n e.val).2 (linkExterior n S e b)

def weightedStaple (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ)
    (e : {e : Edge (Vertex n) // e ∈ S}) (b : WilsonBlockMarginal.Outside (G := Q) S) : ℍ :=
  exteriorWeightedStaple n (edgeCoord n e.val).1 (edgeCoord n e.val).2
    (linkExterior n S e b) f

def referenceAction (S : Finset (Edge (Vertex n))) (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (b : WilsonBlockMarginal.Outside (G := Q) S) (t : ℝ) : ℝ :=
  WilsonBlockIntegration.action n Q character β 2 (baseConfiguration n S b) -
    t * WilsonBlockIntegration.source n Q character 2 f (baseConfiguration n S b)

def linkPotential (S : Finset (Edge (Vertex n))) (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (b : WilsonBlockMarginal.Outside (G := Q) S)
    (e : {e : Edge (Vertex n) // e ∈ S}) (t : ℝ) : ℝ :=
  β * exteriorSourceConstant n (edgeCoord n e.val).1 (edgeCoord n e.val).2
      (linkExterior n S e b) (fun _ => 1) -
    t * exteriorSourceConstant n (edgeCoord n e.val).1 (edgeCoord n e.val).2
      (linkExterior n S e b) f +
    potential 1 (β • staple n S e b - t • weightedStaple n S f e b)

def effectiveAction (S : Finset (Edge (Vertex n))) (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (b : WilsonBlockMarginal.Outside (G := Q) S) (t : ℝ) : ℝ :=
  GibbsMarginalTower.effectiveAction (WilsonBlockMarginal.insideMeasure S haar)
    (fun z => WilsonBlockMarginal.splitAction n Q character β 2 S z -
      t * WilsonSeparatedSources.splitSource n Q character 2 S f z) b

/-- Each actual single-link increment is a constant plus the shifted Haar action. -/
theorem local_increment (S : Finset (Edge (Vertex n))) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (b : WilsonBlockMarginal.Outside (G := Q) S)
    (e : {e : Edge (Vertex n) // e ∈ S}) (t : ℝ) (q : Q) :
    (WilsonBlockIntegration.action n Q character β 2
      (Function.update (baseConfiguration n S b) e.val q) -
      WilsonBlockIntegration.action n Q character β 2 (baseConfiguration n S b)) -
    t * (WilsonBlockIntegration.source n Q character 2 f
      (Function.update (baseConfiguration n S b) e.val q) -
      WilsonBlockIntegration.source n Q character 2 f (baseConfiguration n S b)) =
      β * exteriorSourceConstant n (edgeCoord n e.val).1 (edgeCoord n e.val).2
          (linkExterior n S e b) (fun _ => 1) -
        t * exteriorSourceConstant n (edgeCoord n e.val).1 (edgeCoord n e.val).2
          (linkExterior n S e b) f - referenceAction n S β f b t -
        2 * ⟪(q : ℍ), β • staple n S e b - t • weightedStaple n S f e b⟫ := by
  rw [← link_assemble_eq_update n S e b q]
  rw [WilsonBlockIntegration.action, action_assemble, source_assemble]
  simp only [referenceAction, staple, weightedStaple, inner_sub_right,
    real_inner_smul_right]
  ring

/-- Exact nonlinear retained interaction, including all source-dependent constants. -/
theorem effectiveAction_eq_sum (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (b : WilsonBlockMarginal.Outside (G := Q) S) (t : ℝ) :
    effectiveAction n S β f b t = referenceAction n S β f b t +
      ∑ e : {e : Edge (Vertex n) // e ∈ S},
        (linkPotential n S β f b e t - referenceAction n S β f b t) := by
  let U := baseConfiguration n S b
  let A : {e : Edge (Vertex n) // e ∈ S} → Q → ℝ := fun e q =>
    (WilsonBlockIntegration.action n Q character β 2 (Function.update U e.val q) -
      WilsonBlockIntegration.action n Q character β 2 U) -
    t * (WilsonBlockIntegration.source n Q character 2 f (Function.update U e.val q) -
      WilsonBlockIntegration.source n Q character 2 f U)
  have hA (e : {e : Edge (Vertex n) // e ∈ S}) : Continuous (A e) := by
    have hu := WilsonSeparatedSources.edge_update_continuous n Q U e.val
    exact (((continuous_orientedWilsonAction _ Q character character_continuous
      (base n) (loops n) β 2).comp hu).sub continuous_const).sub
        (continuous_const.mul (((WilsonBlockIntegration.source_continuous n Q character
          character_continuous 2 f).comp hu).sub continuous_const))
  have he (V : WilsonBlockMarginal.Inside (G := Q) S) :
      WilsonBlockMarginal.splitAction n Q character β 2 S (b, V) -
        t * WilsonSeparatedSources.splitSource n Q character 2 S f (b, V) =
      referenceAction n S β f b t + ∑ e, A e (V e) := by
    rw [WilsonBlockMarginal.splitAction,
      WilsonSeparatedSources.inside_action_sum n Q character β 2 S hS b V,
      WilsonSeparatedSources.inside_source_sum n Q character 2 f S hS b V]
    simp only [A, U, referenceAction, baseConfiguration, mul_sub,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  change -(Real.log (∫ V, Real.exp (-(WilsonBlockMarginal.splitAction n Q character β 2 S
    (b, V) - t * WilsonSeparatedSources.splitSource n Q character 2 S f (b, V)))
    ∂WilsonBlockMarginal.insideMeasure S haar)) = _
  simp_rw [he]
  rw [log_integral_affine_sum haar A hA]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  let C := β * exteriorSourceConstant n (edgeCoord n e.val).1 (edgeCoord n e.val).2
      (linkExterior n S e b) (fun _ => 1) -
    t * exteriorSourceConstant n (edgeCoord n e.val).1 (edgeCoord n e.val).2
      (linkExterior n S e b) f - referenceAction n S β f b t
  let V := β • staple n S e b - t • weightedStaple n S f e b
  have hi (q : Q) : Real.exp (-A e q) = Real.exp (-C) * tiltWeight 1 V q := by
    dsimp only [A, U]
    rw [local_increment]
    unfold tiltWeight C V
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hi]
  rw [integral_const_mul]
  change -Real.log (Real.exp (-C) * tiltPartition 1 V) = _
  rw [Real.log_mul (Real.exp_ne_zero _) (tiltPartition_pos _ _).ne', Real.log_exp]
  dsimp only [C, V, linkPotential, potential]
  ring

omit [Fact (1 < n)] in
theorem referenceAction_hasDerivAt (S : Finset (Edge (Vertex n))) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (b : WilsonBlockMarginal.Outside (G := Q) S) (t : ℝ) :
    HasDerivAt (referenceAction n S β f b)
      (-WilsonBlockIntegration.source n Q character 2 f (baseConfiguration n S b)) t := by
  simpa only [referenceAction, one_mul, zero_sub] using
    (hasDerivAt_const t
      (WilsonBlockIntegration.action n Q character β 2 (baseConfiguration n S b))).sub
      ((hasDerivAt_id t).mul_const
        (WilsonBlockIntegration.source n Q character 2 f (baseConfiguration n S b)))

omit [Fact (1 < n)] in
theorem linkPotential_hasDerivAt (S : Finset (Edge (Vertex n))) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (b : WilsonBlockMarginal.Outside (G := Q) S)
    (e : {e : Edge (Vertex n) // e ∈ S}) (t : ℝ) :
    HasDerivAt (linkPotential n S β f b e)
      (-exteriorSourceConstant n (edgeCoord n e.val).1 (edgeCoord n e.val).2
        (linkExterior n S e b) f +
        2 * tiltMean 1 (β • staple n S e b - t • weightedStaple n S f e b)
          (weightedStaple n S f e b)) t :=
  affine_source_first _ _ _ _ _

theorem effectiveAction_deriv (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (b : WilsonBlockMarginal.Outside (G := Q) S) (t : ℝ) :
    deriv (effectiveAction n S β f b) t =
      -WilsonBlockIntegration.source n Q character 2 f (baseConfiguration n S b) +
      ∑ e : {e : Edge (Vertex n) // e ∈ S},
        (deriv (linkPotential n S β f b e) t +
          WilsonBlockIntegration.source n Q character 2 f (baseConfiguration n S b)) := by
  rw [funext (effectiveAction_eq_sum n S hS β f b)]
  have hr := referenceAction_hasDerivAt n S β f b t
  have hl (e : {e : Edge (Vertex n) // e ∈ S}) :=
    (linkPotential_hasDerivAt n S β f b e t).differentiableAt.hasDerivAt.sub hr
  simpa only [sub_neg_eq_add] using (hr.add (HasDerivAt.fun_sum
    (u := Finset.univ) (fun e _ => hl e))).deriv

/-- The full block's source Hessian is the exact sum of actual tilted variances. -/
theorem effectiveAction_second (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (b : WilsonBlockMarginal.Outside (G := Q) S) (t : ℝ) :
    deriv (fun s => deriv (effectiveAction n S β f b) s) t =
      -4 * ∑ e : {e : Edge (Vertex n) // e ∈ S},
        covariance 1 (β • staple n S e b - t • weightedStaple n S f e b)
          (weightedStaple n S f e b) (weightedStaple n S f e b) := by
  rw [funext (effectiveAction_deriv n S hS β f b)]
  have hl (e : {e : Edge (Vertex n) // e ∈ S}) :
      HasDerivAt (fun s => deriv (linkPotential n S β f b e) s)
        (-4 * covariance 1 (β • staple n S e b - t • weightedStaple n S f e b)
          (weightedStaple n S f e b) (weightedStaple n S f e b)) t :=
    affine_source_second _ _ _ _ _
  have hd := (hasDerivAt_const t
    (-WilsonBlockIntegration.source n Q character 2 f (baseConfiguration n S b))).add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun e _ => (hl e).add_const
      (WilsonBlockIntegration.source n Q character 2 f (baseConfiguration n S b))))
  simpa only [zero_add, ← Finset.mul_sum] using hd.deriv

omit [Fact (1 < n)] in
/-- Independence bounds the total squared weighted staples without a volume factor. -/
theorem weightedStaple_square_budget (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (f : PlaquetteIndex n → ℝ)
    (b : WilsonBlockMarginal.Outside (G := Q) S) :
    (∑ e : {e : Edge (Vertex n) // e ∈ S}, ‖weightedStaple n S f e b‖ ^ 2) ≤
      (∑ p, |f p|)^2 := by
  have hsum : (∑ e : {e : Edge (Vertex n) // e ∈ S}, ‖weightedStaple n S f e b‖) ≤
      ∑ p, |f p| := by
    apply (Finset.sum_le_sum (fun e _ => exteriorWeightedStaple_norm_le n
      (edgeCoord n e.val).1 (edgeCoord n e.val).2 (linkExterior n S e b) f)).trans
    exact WilsonBlockWeightBudget.inside_weight_budget n S (by
      intro a ha a' ha' haa'
      exact hS a (by simpa only [Finset.mem_image] using ha)
        a' (by simpa only [Finset.mem_image] using ha') haa') f
  exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hsum 2)

theorem effectiveAction_curvature_bounds (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (b : WilsonBlockMarginal.Outside (G := Q) S) (t : ℝ) :
    -4 * (∑ p, |f p|)^2 ≤ deriv (fun s => deriv (effectiveAction n S β f b) s) t ∧
      deriv (fun s => deriv (effectiveAction n S β f b) s) t ≤ 0 := by
  rw [effectiveAction_second n S hS]
  have hnonneg := Finset.sum_nonneg (s := Finset.univ)
    (fun (e : {e : Edge (Vertex n) // e ∈ S}) _ => covariance_self_nonneg 1
      (β • staple n S e b - t • weightedStaple n S f e b) (weightedStaple n S f e b))
  have hupper := (Finset.sum_le_sum (s := Finset.univ)
    (fun (e : {e : Edge (Vertex n) // e ∈ S}) _ => covariance_self_le 1
      (β • staple n S e b - t • weightedStaple n S f e b) (weightedStaple n S f e b))).trans
        (weightedStaple_square_budget n S hS f b)
  constructor <;> linarith

end
end UnifiedTheory.Clay.YangMills.SU2WilsonBlockEffectiveAction
