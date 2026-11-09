/- The temporal-gauge identity improves the actual heat-bath/transfer
comparison on gauge-invariant observables. The right hand side is still the
original full Wilson transfer energy, with no change of physical clock. -/
import UnifiedTheory.Clay.YangMills.WilsonTemporalInfluence
import UnifiedTheory.Clay.YangMills.WilsonHeatBathComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonGaugeHeatBathComparison
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab WilsonTemporalInfluence

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def rawTransitionMap (beta : ℝ) (hbeta : 0 ≤ beta) : C(Slice n × Slice n, ℝ) :=
  ⟨fun uv => WilsonTemporalGauge.rawTransition n beta hbeta uv.1 uv.2,
    rawTransition_continuous n beta hbeta⟩

theorem rawIncrement_eq_full (beta : ℝ) (hbeta : 0 ≤ beta) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (u : Slice n) :
    HeatBathTwoEdge.increment (measure n) (rawTransitionMap n beta hbeta) f u =
      WilsonHeatBathComparison.localIncrement n beta hbeta f u :=
  (invariant_increment n beta hbeta f hinv u).symm

/-- The physical invariant sector has the smaller exp(4 beta |S|) two-edge
factor. It compares the actual heat-bath energy to the original full transfer. -/
theorem heatBathEnergy_le_full_transfer (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    WilsonGroundHeatBath.heatBathEnergy n beta hbeta S f ≤
      (1 + Real.exp (4 * beta * (S.card : ℝ))) ^ 2 *
        WilsonHeatBathComparison.transferEnergy n beta hbeta f := by
  classical
  let p : C(WilsonGroundHeatBath.Outside n S × WilsonGroundHeatBath.Inside n S, ℝ) :=
    ⟨WilsonGroundHeatBath.weight n beta hbeta S,
      WilsonGroundHeatBath.weight_continuous n beta hbeta S⟩
  let t := Real.exp (4 * beta * (S.card : ℝ))
  have ht : 0 < t := Real.exp_pos _
  have ht2 : t ^ 2 = Real.exp (8 * beta * (S.card : ℝ)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hrow (r : WilsonGroundHeatBath.Outside n S)
      (a b : WilsonGroundHeatBath.Inside n S) (v : Slice n) :
      rawTransitionMap n beta hbeta (WilsonBlockMarginal.assemble S (r, a), v) ≤
        t ^ 2 * rawTransitionMap n beta hbeta (WilsonBlockMarginal.assemble S (r, b), v) := by
    rw [ht2]
    apply rawTransition_comparison n beta hbeta S
    intro e he
    simp only [WilsonBlockMarginal.assemble_outside S _ e he]
  have h := HeatBathTwoEdge.comparison (WilsonGroundHeatBath.outsideHaar n S)
    (WilsonGroundHeatBath.insideHaar n S) (measure n) p
    (WilsonGroundHeatBath.weight_positive n beta hbeta S)
    (WilsonBlockMarginal.assemble S) (WilsonBlockMarginal.assemble_continuous S)
    (rawTransitionMap n beta hbeta) f
    (fun uv => (WilsonTemporalGauge.rawTransition_pos n beta hbeta uv.1 uv.2).le)
    (WilsonTemporalGauge.rawTransition_mass n beta hbeta) t ht hrow
  simp_rw [rawIncrement_eq_full n beta hbeta f hinv] at h
  have hs : (∫ r, ∫ a, WilsonGroundHeatBath.weight n beta hbeta S (r, a) *
      WilsonHeatBathComparison.localIncrement n beta hbeta f (WilsonBlockMarginal.assemble S (r, a))
        ∂WilsonGroundHeatBath.insideHaar n S ∂WilsonGroundHeatBath.outsideHaar n S) =
      ∫ u, (WilsonGroundLocalComparison.ground n beta hbeta u) ^ 2 *
        WilsonHeatBathComparison.localIncrement n beta hbeta f u ∂measure n := by
    have hi : Integrable (fun z => WilsonGroundHeatBath.weight n beta hbeta S z *
        WilsonHeatBathComparison.localIncrement n beta hbeta f (WilsonBlockMarginal.assemble S z))
        ((WilsonGroundHeatBath.outsideHaar n S).prod (WilsonGroundHeatBath.insideHaar n S)) :=
      ((WilsonGroundHeatBath.weight_continuous n beta hbeta S).mul
        ((WilsonHeatBathComparison.localIncrement_continuous n beta hbeta f).comp
          (WilsonBlockMarginal.assemble_continuous S))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [← integral_prod _ hi]
    exact (WilsonBlockMarginal.assemble_preserving S (RegulatedGauge.compactHaar Q)).integral_comp
      (WilsonBlockMarginal.assemble S).measurableEmbedding
      (fun u => (WilsonGroundLocalComparison.ground n beta hbeta u) ^ 2 *
        WilsonHeatBathComparison.localIncrement n beta hbeta f u)
  change WilsonGroundHeatBath.heatBathEnergy n beta hbeta S f ≤
    (1 + t) ^ 2 * ((1 / 2 : ℝ) * ∫ r, ∫ a, WilsonGroundHeatBath.weight n beta hbeta S (r, a) *
      WilsonHeatBathComparison.localIncrement n beta hbeta f (WilsonBlockMarginal.assemble S (r, a))
        ∂WilsonGroundHeatBath.insideHaar n S ∂WilsonGroundHeatBath.outsideHaar n S) at h
  rw [hs] at h
  exact h

theorem heatBathEnergy_le_full_dirichlet (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (SpatialVertex n × Fin 3)) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    WilsonGroundHeatBath.heatBathEnergy n beta hbeta S f ≤
      (1 + Real.exp (4 * beta * (S.card : ℝ))) ^ 2 *
        GroundStateDirichlet.dirichlet (measure n) (kernelMap n beta)
          (WilsonGroundLocalComparison.ground n beta hbeta) ‖transfer n beta‖ f := by
  rw [← WilsonHeatBathComparison.transferEnergy_eq_dirichlet n beta hbeta f]
  exact heatBathEnergy_le_full_transfer n beta hbeta S f hinv

end
end UnifiedTheory.Clay.YangMills.WilsonGaugeHeatBathComparison
