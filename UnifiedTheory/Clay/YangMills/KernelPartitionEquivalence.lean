/- Equal or ordered actual endpoint partitions control compact positive
operator norms. Boundary constants are removed by their exponential rates. -/
import UnifiedTheory.Clay.YangMills.KernelEndpointNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.KernelPartitionEquivalence
noncomputable section
open MeasureTheory CompactKernelOperator FiniteKernelChain FiniteKernelGrowth
open KernelEndpointNorm WilsonPositiveGroundState

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem norm_le (K L : C(X × X, ℝ)) (hpos : (operator μ K).IsPositive)
    (hK : ∀ x y, 0 ≤ K (x, y)) (B C : C(X, ℝ)) (hB : ∀ x, 0 < B x)
    (hZ : ∀ k, endpoint μ K k B B ≤ endpoint μ L k C C) :
    ‖operator μ K‖ ≤ ‖operator μ L‖ := by
  by_cases hz : operator μ K = 0
  · simpa only [hz, norm_zero] using norm_nonneg (operator μ L)
  obtain ⟨c,hc,hfloor⟩ := KernelPartitionNorm.positive_floor B hB
  obtain ⟨a,A,ha,hA,hlower⟩ := endpoint_lower_rate μ K hpos hz hK B c hc hfloor
  apply rate_le (norm_nonneg (operator μ L)) ha
    (C := A * ‖ContinuousMap.toLp 2 μ ℂ (complexify C)‖^2)
  intro k
  calc
    _ ≤ A * endpoint μ K k B B := hlower k
    _ ≤ A * endpoint μ L k C C := mul_le_mul_of_nonneg_left (hZ k) hA
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (endpoint_upper_norm μ L C k) hA

theorem norm_eq (K L : C(X × X, ℝ))
    (hKpos : (operator μ K).IsPositive) (hLpos : (operator μ L).IsPositive)
    (hK : ∀ x y, 0 ≤ K (x, y)) (hL : ∀ x y, 0 ≤ L (x, y))
    (B C : C(X, ℝ)) (hB : ∀ x, 0 < B x) (hC : ∀ x, 0 < C x)
    (hZ : ∀ k, endpoint μ K k B B = endpoint μ L k C C) :
    ‖operator μ K‖ = ‖operator μ L‖ :=
  le_antisymm (norm_le μ K L hKpos hK B C hB (fun k => (hZ k).le))
    (norm_le μ L K hLpos hL C B hC (fun k => (hZ k).symm.le))

end
end UnifiedTheory.Clay.YangMills.KernelPartitionEquivalence
