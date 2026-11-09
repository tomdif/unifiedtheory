/- Exact clustered sums of the actual packet derivative coordinates.
The extra broad-mode width is handled by the finite charged jet identity. -/
import UnifiedTheory.Audit.KFCausalNarrowPacketMomentumGraphs
import UnifiedTheory.Audit.KFCausalClusteredChargedJetIdentity
import UnifiedTheory.Audit.KFCausalNarrowFourierChargedBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalClusteredPacketDerivativeCoordinates
noncomputable section
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalPairedModeCoordinates (scale)
open KFCausalClusteredWidthProfiles (widths coefficients)
open KFCausalNarrowFourierPackets (coordinateDensity chargedRadius)
open KFCausalNarrowPacketMomentumGraphs (differentialCoordinates broadCoefficient)
open KFCausalNarrowFourierChargedBounds (charged slope)
open KFCausalNeutralLinePackets (step packet)

theorem density_sum (n : ℕ) (δ α β : ℝ) (hδ : 0 < δ) (b : ℂ) (P : Polynomial ℂ)
    (g : ℝ → ℂ) (z : Block 2 × Block 4) :
    (∑ k, coefficients n δ k*coordinateDensity α β (widths n δ k) b P g z) =
      (Real.pi/α:ℝ)*charged n δ α β b P g z := by
  calc
    _ = ((Real.pi/α:ℝ)*g (z.2 0))*
        KFCausalReciprocalWedgeLaplace.laplaceSum (n+1) (widths n δ) (coefficients n δ) (chargedRadius α z:ℂ)*
        packet β b P (z.2 3) := by
      unfold KFCausalReciprocalWedgeLaplace.laplaceSum
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      unfold coordinateDensity
      push_cast
      ring
    _ = _ := by rw [KFCausalClusteredWidthProfiles.laplaceSum_exact n δ hδ]; unfold charged; ring

theorem width_density_sum (n : ℕ) (δ α β : ℝ) (hδ : 0 < δ) (b : ℂ) (P : Polynomial ℂ)
    (g : ℝ → ℂ) (z : Block 2 × Block 4) :
    (∑ k, coefficients n δ k*(widths n δ k:ℂ)*coordinateDensity α β (widths n δ k) b P g z) =
      -(Real.pi/α:ℝ)*slope n δ α β b P g z := by
  calc
    _ = ((Real.pi/α:ℝ)*g (z.2 0))*KFCausalClusteredChargedJetIdentity.widthSquareSum n δ (chargedRadius α z:ℂ)*
        packet β b P (z.2 3) := by
      unfold KFCausalClusteredChargedJetIdentity.widthSquareSum
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      unfold coordinateDensity
      push_cast
      ring
    _ = _ := by rw [KFCausalClusteredChargedJetIdentity.widthSquareSum_eq n δ hδ]; unfold KFCausalNarrowFourierChargedBounds.slope; ring

def blockDifferential (n : ℕ) (δ α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (j : Fin 4) (z : Block 2 × Block 4) : ℂ :=
  ![(4*(Real.pi:ℂ)*Complex.I*scale)*(Real.pi/α:ℝ)*(z.1 0:ℂ)*charged n δ α β b P g z,
    (4*(scale:ℂ)*α)*(Real.pi/α:ℝ)*(z.2 2:ℂ)*slope n δ α β b P g z+
      (Real.pi/α:ℝ)*charged n δ α β b (step β b P) g z,
    (4*(scale:ℂ)*α)*(Real.pi/α:ℝ)*(z.2 1:ℂ)*slope n δ α β b P g z,
    (4*(Real.pi:ℂ)*Complex.I*scale)*(Real.pi/α:ℝ)*(z.1 1:ℂ)*charged n δ α β b P g z] j

theorem differential_sum (n : ℕ) (δ α β : ℝ) (hδ : 0 < δ) (b : ℂ) (P : Polynomial ℂ)
    (g : ℝ → ℂ) (j : Fin 4) (z : Block 2 × Block 4) :
    (∑ k, coefficients n δ k*differentialCoordinates α β (widths n δ k) b P g j z) =
      blockDifferential n δ α β b P g j z := by
  have hL (i : Fin 2) :
      (∑ k, coefficients n δ k*((4*(Real.pi:ℂ)*Complex.I*scale)*(z.1 i:ℂ)*coordinateDensity α β (widths n δ k) b P g z)) =
      (4*(Real.pi:ℂ)*Complex.I*scale)*(Real.pi/α:ℝ)*(z.1 i:ℂ)*charged n δ α β b P g z := by
    calc
      _ = ((4*(Real.pi:ℂ)*Complex.I*scale)*(z.1 i:ℂ))*
          ∑ k, coefficients n δ k*coordinateDensity α β (widths n δ k) b P g z := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = _ := by rw [density_sum n δ α β hδ]; ring
  have hR (i : Fin 2) :
      (∑ k, coefficients n δ k*(broadCoefficient α (widths n δ k)*(z.2 i.castSucc.succ:ℂ)*coordinateDensity α β (widths n δ k) b P g z)) =
      (4*(scale:ℂ)*α)*(Real.pi/α:ℝ)*(z.2 i.castSucc.succ:ℂ)*slope n δ α β b P g z := by
    calc
      _ = ((-4*(scale:ℂ)*α)*(z.2 i.castSucc.succ:ℂ))*
          ∑ k, coefficients n δ k*(widths n δ k:ℂ)*coordinateDensity α β (widths n δ k) b P g z := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        unfold broadCoefficient
        push_cast
        ring
      _ = _ := by rw [width_density_sum n δ α β hδ]; ring
  fin_cases j
  · exact hL 0
  · change (∑ k, coefficients n δ k*(broadCoefficient α (widths n δ k)*(z.2 2:ℂ)*coordinateDensity α β (widths n δ k) b P g z+
        coordinateDensity α β (widths n δ k) b (step β b P) g z)) = _
    simp only [mul_add,Finset.sum_add_distrib]
    exact congrArg₂ (·+·) (hR 1) (density_sum n δ α β hδ b (step β b P) g z)
  · exact hR 0
  · exact hL 1

#print axioms density_sum
#print axioms width_density_sum
#print axioms differential_sum
end
end UnifiedTheory.Audit.KFCausalClusteredPacketDerivativeCoordinates
