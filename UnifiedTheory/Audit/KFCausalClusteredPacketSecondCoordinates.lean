/- Exact finite correlated second-derivative blocks. The broad second
derivative uses the proved width-cube sum and keeps every neutral cross term. -/
import UnifiedTheory.Audit.KFCausalNarrowPacketSecondMomentumGraphs
import UnifiedTheory.Audit.KFCausalNarrowFourierSecondJetLimit
import UnifiedTheory.Audit.KFCausalClusteredPacketDerivativeCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalClusteredPacketSecondCoordinates
noncomputable section
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalPairedModeCoordinates (scale)
open KFCausalClusteredWidthProfiles (widths coefficients)
open KFCausalNarrowFourierPackets (coordinateDensity chargedRadius)
open KFCausalNarrowPacketSecondStates (secondCoordinates)
open KFCausalNarrowFourierChargedBounds (charged slope)
open KFCausalNarrowFourierSecondJetLimit (secondSlope)
open KFCausalClusteredPacketDerivativeCoordinates (density_sum width_density_sum)
open KFCausalNeutralLinePackets (step packet)

theorem square_width_density_sum (n : ℕ) (δ α β : ℝ) (hδ : 0 < δ) (b : ℂ) (P : Polynomial ℂ)
    (g : ℝ → ℂ) (z : Block 2 × Block 4) :
    (∑ k, coefficients n δ k*(widths n δ k:ℂ)^2*coordinateDensity α β (widths n δ k) b P g z) =
      (Real.pi/α:ℝ)*secondSlope n δ α β b P g z := by
  calc
    _ = ((Real.pi/α:ℝ)*g (z.2 0))*KFCausalClusteredWidthSecondJet.widthCubeSum n δ (chargedRadius α z:ℂ)*
        packet β b P (z.2 3) := by
      unfold KFCausalClusteredWidthSecondJet.widthCubeSum
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      unfold coordinateDensity
      push_cast
      ring
    _ = _ := by rw [KFCausalClusteredWidthSecondJet.widthCubeSum_eq n δ hδ]; unfold secondSlope; ring

def blockSecond (n : ℕ) (δ α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (j : Fin 4) (z : Block 2 × Block 4) : ℂ :=
  ![-8*(Real.pi:ℂ)^2*(Real.pi/α:ℝ)*(z.1 0:ℂ)^2*charged n δ α β b P g z,
    (4*(α:ℂ)*(Real.pi/α:ℝ))*slope n δ α β b P g z+
      (8*(α:ℂ)^2*(Real.pi/α:ℝ))*(z.2 2:ℂ)^2*secondSlope n δ α β b P g z+
      (8*(scale:ℂ)*α*(Real.pi/α:ℝ))*(z.2 2:ℂ)*slope n δ α β b (step β b P) g z+
      (Real.pi/α:ℝ)*charged n δ α β b (step β b (step β b P)) g z,
    (4*(α:ℂ)*(Real.pi/α:ℝ))*slope n δ α β b P g z+
      (8*(α:ℂ)^2*(Real.pi/α:ℝ))*(z.2 1:ℂ)^2*secondSlope n δ α β b P g z,
    -8*(Real.pi:ℂ)^2*(Real.pi/α:ℝ)*(z.1 1:ℂ)^2*charged n δ α β b P g z] j

theorem second_sum (n : ℕ) (δ α β : ℝ) (hδ : 0 < δ) (b : ℂ) (P : Polynomial ℂ)
    (g : ℝ → ℂ) (j : Fin 4) (z : Block 2 × Block 4) :
    (∑ k, coefficients n δ k*secondCoordinates α β (widths n δ k) b P g j z) =
      blockSecond n δ α β b P g j z := by
  have hL (i : Fin 2) :
      (∑ k, coefficients n δ k*(-8*(Real.pi:ℂ)^2*(z.1 i:ℂ)^2*coordinateDensity α β (widths n δ k) b P g z)) =
      -8*(Real.pi:ℂ)^2*(Real.pi/α:ℝ)*(z.1 i:ℂ)^2*charged n δ α β b P g z := by
    calc
      _ = (-8*(Real.pi:ℂ)^2*(z.1 i:ℂ)^2)*∑ k, coefficients n δ k*coordinateDensity α β (widths n δ k) b P g z := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = _ := by rw [density_sum n δ α β hδ]; ring
  have hR (i : Fin 2) :
      (∑ k, coefficients n δ k*((-4*(α*widths n δ k:ℝ)+8*(α*widths n δ k:ℝ)^2*(z.2 i.castSucc.succ:ℂ)^2)*
        coordinateDensity α β (widths n δ k) b P g z)) =
      (4*(α:ℂ)*(Real.pi/α:ℝ))*slope n δ α β b P g z+
        (8*(α:ℂ)^2*(Real.pi/α:ℝ))*(z.2 i.castSucc.succ:ℂ)^2*secondSlope n δ α β b P g z := by
    calc
      _ = (-4*(α:ℂ))*(∑ k, coefficients n δ k*(widths n δ k:ℂ)*coordinateDensity α β (widths n δ k) b P g z)+
          (8*(α:ℂ)^2*(z.2 i.castSucc.succ:ℂ)^2)*(∑ k, coefficients n δ k*(widths n δ k:ℂ)^2*coordinateDensity α β (widths n δ k) b P g z) := by
        rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        push_cast
        ring
      _ = _ := by rw [width_density_sum n δ α β hδ,square_width_density_sum n δ α β hδ]; ring
  have hN :
      (∑ k, coefficients n δ k*((-8*(scale:ℂ)*(α*widths n δ k:ℝ)*(z.2 2:ℂ))*
        coordinateDensity α β (widths n δ k) b (step β b P) g z)) =
      (8*(scale:ℂ)*α*(Real.pi/α:ℝ))*(z.2 2:ℂ)*slope n δ α β b (step β b P) g z := by
    calc
      _ = (-8*(scale:ℂ)*α*(z.2 2:ℂ))*∑ k, coefficients n δ k*(widths n δ k:ℂ)*
          coordinateDensity α β (widths n δ k) b (step β b P) g z := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        push_cast
        ring
      _ = _ := by rw [width_density_sum n δ α β hδ]; ring
  fin_cases j
  · exact hL 0
  · change (∑ k, coefficients n δ k*((-4*(α*widths n δ k:ℝ)+8*(α*widths n δ k:ℝ)^2*(z.2 2:ℂ)^2)*
        coordinateDensity α β (widths n δ k) b P g z+
        (-8*(scale:ℂ)*(α*widths n δ k:ℝ)*(z.2 2:ℂ))*coordinateDensity α β (widths n δ k) b (step β b P) g z+
        coordinateDensity α β (widths n δ k) b (step β b (step β b P)) g z)) = _
    simp only [mul_add,Finset.sum_add_distrib]
    exact congrArg₂ (·+·) (congrArg₂ (·+·) (hR 1) hN) (density_sum n δ α β hδ b (step β b (step β b P)) g z)
  · exact hR 0
  · exact hL 1

#print axioms square_width_density_sum
#print axioms second_sum
end
end UnifiedTheory.Audit.KFCausalClusteredPacketSecondCoordinates
