/- The actual Wilson ground-law block heat-bath Dirichlet form is controlled
by the actual ground-state transfer Dirichlet form. The optimized constant
depends on coupling and the changed block cardinality, not total volume.
No auxiliary mixing, coverage, clock normalization, or continuum gap is assumed. -/
import UnifiedTheory.Clay.YangMills.HeatBathTwoEdge
import UnifiedTheory.Clay.YangMills.WilsonGroundHeatBath

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonHeatBathComparison
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

/-- The actual normalized full-kernel transition as a jointly continuous density. -/
def transitionMap (β : ℝ) (hβ : 0 ≤ β) : C(Slice n × Slice n, ℝ) :=
  ⟨fun uv => WilsonGroundLocalComparison.transition n β hβ uv.1 uv.2, by
    unfold WilsonGroundLocalComparison.transition GroundStateDirichlet.transition
    exact ((kernelMap n β).continuous.mul
      ((WilsonGroundLocalComparison.ground n β hβ).continuous.comp continuous_snd)).div
      (continuous_const.mul
        ((WilsonGroundLocalComparison.ground n β hβ).continuous.comp continuous_fst))
      (fun uv => mul_ne_zero
        (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1.ne'
        (WilsonGroundLocalComparison.ground_pos n β hβ uv.1).ne')⟩

/-- Twice the conditional transfer energy, computed from the actual transition. -/
def localIncrement (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : Slice n → ℝ :=
  HeatBathTwoEdge.increment (measure n) (transitionMap n β hβ) f

theorem localIncrement_continuous (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    Continuous (localIncrement n β hβ f) :=
  HeatBathTwoEdge.increment_continuous (measure n) (transitionMap n β hβ) f

/-- The actual normalized transfer Dirichlet form under the constructed squared ground profile. -/
def transferEnergy (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : ℝ :=
  (1 / 2 : ℝ) * ∫ u, (WilsonGroundLocalComparison.ground n β hβ u) ^ 2 *
    localIncrement n β hβ f u ∂measure n

/-- The energy is exactly the existing ground-state Dirichlet form, not a comparison law. -/
theorem transferEnergy_eq_dirichlet (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    transferEnergy n β hβ f = GroundStateDirichlet.dirichlet (measure n)
      (kernelMap n β) (WilsonGroundLocalComparison.ground n β hβ) ‖transfer n β‖ f := by
  have hlam := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  rw [GroundStateDirichlet.dirichlet_identity (measure n) (kernelMap n β)
    (kernelMap n β).continuous (kernelMap_symm n β)
    (WilsonGroundLocalComparison.ground n β hβ)
    (WilsonGroundLocalComparison.ground n β hβ).continuous ‖transfer n β‖ hlam.ne'
    (WilsonGroundLocalComparison.ground_equation n β hβ) f f.continuous]
  have hi : Integrable (fun uv : Slice n × Slice n =>
      GroundStateDirichlet.edgeDensity (kernelMap n β)
        (WilsonGroundLocalComparison.ground n β hβ) ‖transfer n β‖ uv *
          (f uv.1 - f uv.2) ^ 2)
        ((WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    have hc := GroundStateDirichlet.edgeDensity_continuous (kernelMap n β)
      (kernelMap n β).continuous (WilsonGroundLocalComparison.ground n β hβ)
      (WilsonGroundLocalComparison.ground n β hβ).continuous ‖transfer n β‖
    fun_prop
  rw [integral_prod _ hi]
  unfold transferEnergy localIncrement HeatBathTwoEdge.increment
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  have he := GroundStateDirichlet.detailed_balance (kernelMap n β)
    (WilsonGroundLocalComparison.ground n β hβ) ‖transfer n β‖ hlam u v
  change (WilsonGroundLocalComparison.ground n β hβ u) ^ 2 *
    (WilsonGroundLocalComparison.transition n β hβ u v * (f u - f v) ^ 2) = _
  rw [← mul_assoc]
  exact congrArg (fun x : ℝ => x * (f u - f v) ^ 2) he

/-- The exact finite-block heat-bath comparison, with the optimized two-edge constant. -/
theorem heatBathEnergy_le_transferEnergy (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) :
    WilsonGroundHeatBath.heatBathEnergy n β hβ S f ≤
      (1 + Real.exp (12 * β * (S.card : ℝ))) ^ 2 * transferEnergy n β hβ f := by
  let p : C(WilsonGroundHeatBath.Outside n S × WilsonGroundHeatBath.Inside n S, ℝ) :=
    ⟨WilsonGroundHeatBath.weight n β hβ S, WilsonGroundHeatBath.weight_continuous n β hβ S⟩
  let t := Real.exp (12 * β * (S.card : ℝ))
  have ht : 0 < t := Real.exp_pos _
  have ht2 : t ^ 2 = Real.exp (24 * β * (S.card : ℝ)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hrow (r : WilsonGroundHeatBath.Outside n S)
      (a b : WilsonGroundHeatBath.Inside n S) (v : Slice n) :
      transitionMap n β hβ (WilsonBlockMarginal.assemble S (r, a), v) ≤
        t ^ 2 * transitionMap n β hβ (WilsonBlockMarginal.assemble S (r, b), v) := by
    rw [ht2]
    apply WilsonGroundLocalComparison.transition_block n β hβ S
    intro e he
    simp only [WilsonBlockMarginal.assemble_outside S _ e he]
  have h := HeatBathTwoEdge.comparison (WilsonGroundHeatBath.outsideHaar n S)
    (WilsonGroundHeatBath.insideHaar n S) (measure n) p
    (WilsonGroundHeatBath.weight_positive n β hβ S)
    (WilsonBlockMarginal.assemble S) (WilsonBlockMarginal.assemble_continuous S)
    (transitionMap n β hβ) f
    (fun uv => (WilsonGroundLocalComparison.transition_pos n β hβ uv.1 uv.2).le)
    (WilsonGroundLocalComparison.transition_mass n β hβ) t ht hrow
  have hs : (∫ r, ∫ a, WilsonGroundHeatBath.weight n β hβ S (r, a) *
      localIncrement n β hβ f (WilsonBlockMarginal.assemble S (r, a))
        ∂WilsonGroundHeatBath.insideHaar n S ∂WilsonGroundHeatBath.outsideHaar n S) =
      ∫ u, (WilsonGroundLocalComparison.ground n β hβ u) ^ 2 *
        localIncrement n β hβ f u ∂measure n := by
    have hi : Integrable (fun z => WilsonGroundHeatBath.weight n β hβ S z *
        localIncrement n β hβ f (WilsonBlockMarginal.assemble S z))
        ((WilsonGroundHeatBath.outsideHaar n S).prod (WilsonGroundHeatBath.insideHaar n S)) :=
      ((WilsonGroundHeatBath.weight_continuous n β hβ S).mul
        ((localIncrement_continuous n β hβ f).comp
          (WilsonBlockMarginal.assemble_continuous S))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [← integral_prod _ hi]
    exact (WilsonBlockMarginal.assemble_preserving S (RegulatedGauge.compactHaar Q)).integral_comp
      (WilsonBlockMarginal.assemble S).measurableEmbedding
      (fun u => (WilsonGroundLocalComparison.ground n β hβ u) ^ 2 * localIncrement n β hβ f u)
  change WilsonGroundHeatBath.heatBathEnergy n β hβ S f ≤
    (1 + t) ^ 2 * ((1 / 2 : ℝ) * ∫ r, ∫ a, WilsonGroundHeatBath.weight n β hβ S (r, a) *
      localIncrement n β hβ f (WilsonBlockMarginal.assemble S (r, a))
        ∂WilsonGroundHeatBath.insideHaar n S ∂WilsonGroundHeatBath.outsideHaar n S) at h
  rw [hs] at h
  exact h

/-- Actual heat-bath energy versus the already defined full-transfer ground-state Dirichlet form. -/
theorem heatBathEnergy_le_dirichlet (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ)) :
    WilsonGroundHeatBath.heatBathEnergy n β hβ S f ≤
      (1 + Real.exp (12 * β * (S.card : ℝ))) ^ 2 *
        GroundStateDirichlet.dirichlet (measure n) (kernelMap n β)
          (WilsonGroundLocalComparison.ground n β hβ) ‖transfer n β‖ f := by
  rw [← transferEnergy_eq_dirichlet n β hβ f]
  exact heatBathEnergy_le_transferEnergy n β hβ S f

end
end UnifiedTheory.Clay.YangMills.WilsonHeatBathComparison
