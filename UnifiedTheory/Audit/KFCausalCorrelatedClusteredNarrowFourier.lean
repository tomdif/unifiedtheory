/- Exact unitary representatives of the existing finite clustered physical
vectors. The Fourier normalization cancels the reciprocal clustered width,
leaving the charged difference quotient with all correlated blocks retained. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierPackets
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockVectors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredNarrowFourier
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalNarrowFourierCoordinates (mixedCoordinates)
open KFCausalNarrowFourierPackets (configurationDensity coordinateDensity chargedRadius)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredClockVectors (profile vector vector_coe)
open KFCausalClusteredWidthProfiles (quotient)
open KFCausalNeutralLinePackets (packet)

variable {m : ℕ} (f : Family m) (c : ℝ → Fin m → ℂ) (α β : ℝ)

def coordinateProfile (δ : ℝ) (z : Block 2 × Block 4) : ℂ :=
  ∑ j, coefficients f δ j*coordinateDensity α β (widths f δ j) (sources f j) (polynomials f j)
    (fun s => c s (index f j).1) z

def limitProfile (z : Block 2 × Block 4) : ℂ :=
  ∑ i, ((Real.pi/α:ℝ)*f.amplitude i*c (z.2 0) i)*
    (Complex.exp (-(chargedRadius α z:ℂ))*(chargedRadius α z:ℂ)^(f.degree i))*
    packet β (f.source i) (f.polynomial i) (z.2 3)

theorem profile_expansion (δ : ℝ) (x : Configuration) :
    profile f c α β δ x = ∑ j, coefficients f δ j*
      configurationDensity α β (widths f δ j) (sources f j) (polynomials f j)
        (fun s => c s (index f j).1) x := by
  rw [KFCausalCorrelatedClusteredClockVectors.profile_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [KFCausalNarrowFourierPackets.factor_zero]
  unfold configurationDensity
  ring

theorem coordinate_blocks (δ : ℝ) (z : Block 2 × Block 4) :
    coordinateProfile f c α β δ z = ∑ i, ((Real.pi/α:ℝ)*f.amplitude i*c (z.2 0) i)*
      KFCausalReciprocalWedgeLaplace.laplaceSum (f.degree i+1)
        (KFCausalClusteredWidthProfiles.widths (f.degree i) δ)
        (KFCausalClusteredWidthProfiles.coefficients (f.degree i) δ) (chargedRadius α z:ℂ)*
      packet β (f.source i) (f.polynomial i) (z.2 3) := by
  unfold coordinateProfile coordinateDensity coefficients widths sources polynomials
  rw [sum_index f (fun j =>
    (f.amplitude j.1*KFCausalClusteredWidthProfiles.coefficients (f.degree j.1) δ j.2)*
    (((Real.pi/α)*KFCausalClusteredWidthProfiles.widths (f.degree j.1) δ j.2:ℝ)*c (z.2 0) j.1*
      Complex.exp (-(KFCausalClusteredWidthProfiles.widths (f.degree j.1) δ j.2:ℂ)*(chargedRadius α z:ℂ))*
      packet β (f.source j.1) (f.polynomial j.1) (z.2 3)))]
  apply Finset.sum_congr rfl
  intro i _
  unfold KFCausalReciprocalWedgeLaplace.laplaceSum
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

theorem coordinate_exact (δ : ℝ) (hδ : 0 < δ) (z : Block 2 × Block 4) :
    coordinateProfile f c α β δ z = ∑ i, ((Real.pi/α:ℝ)*f.amplitude i*c (z.2 0) i)*
      (Complex.exp (-(chargedRadius α z:ℂ))*quotient δ (chargedRadius α z:ℂ)^(f.degree i))*
      packet β (f.source i) (f.polynomial i) (z.2 3) := by
  simp only [coordinate_blocks,KFCausalClusteredWidthProfiles.laplaceSum_exact _ δ hδ]

theorem coordinate_tendsto (z : Block 2 × Block 4) :
    Tendsto (fun δ => coordinateProfile f c α β δ z) (𝓝[>] 0) (𝓝 (limitProfile f c α β z)) := by
  simp only [coordinate_blocks,limitProfile]
  exact tendsto_finset_sum _ (fun i _ =>
    ((KFCausalClusteredWidthProfiles.laplaceSum_tendsto (f.degree i) (chargedRadius α z:ℂ)).const_mul _).mul_const _)

theorem coordinate_norm_bound (hα : 0 < α) (δ : ℝ) (hδ : 0 < δ) (z : Block 2 × Block 4) :
    ‖coordinateProfile f c α β δ z‖ ≤ ∑ i,
      ‖((Real.pi/α:ℝ)*f.amplitude i*c (z.2 0) i)*
        (Complex.exp (-(chargedRadius α z:ℂ))*(chargedRadius α z:ℂ)^(f.degree i))*
        packet β (f.source i) (f.polynomial i) (z.2 3)‖ := by
  rw [coordinate_blocks]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hz : 0 ≤ (chargedRadius α z:ℂ).re := KFCausalNarrowFourierPackets.chargedRadius_nonnegative α hα z
  have hb := KFCausalClusteredWidthProfiles.laplaceSum_norm_le (f.degree i) δ hδ (chargedRadius α z:ℂ) hz
  simp only [norm_mul,norm_pow,Complex.norm_exp,Complex.neg_re]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) (norm_nonneg _)

variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hc : ∀ i, Continuous (fun s => c s i)) (hc2 : ∀ i, MemLp (fun s => c s i) 2 volume)

def packetState (δ : ℝ) (hδ : 0 < δ) (j : Fin (count f)) : Hilbert :=
  KFCausalNarrowFourierPackets.state α β (widths f δ j) hα hβ
    (lt_of_lt_of_le zero_lt_one (widths_admissible f δ hδ.le j))
    (sources f j) (polynomials f j) (fun s => c s (index f j).1) (hc _) (hc2 _)

theorem vector_sum (δ : ℝ) (hδ : 0 < δ) :
    vector f c α β hα hβ hw hc2 δ = ∑ j, coefficients f δ j • packetState f c α β hα hβ hc hc2 δ hδ j := by
  apply Lp.ext
  have hs := KFCausalFiniteLpRepresentatives.weighted_sum_coe volume (coefficients f δ)
    (packetState f c α β hα hβ hc hc2 δ hδ)
    (fun j => configurationDensity α β (widths f δ j) (sources f j) (polynomials f j)
      (fun s => c s (index f j).1))
    (fun j => KFCausalNarrowFourierPackets.state_configuration_coe α β (widths f δ j) hα hβ
      (lt_of_lt_of_le zero_lt_one (widths_admissible f δ hδ.le j))
      (sources f j) (polynomials f j) (fun s => c s (index f j).1) (hc _) (hc2 _))
  filter_upwards [vector_coe f c α β hα hβ hw hc2 δ hδ,hs] with x hx hs
  rw [hx,hs,profile_expansion]

include hc in
theorem vector_coordinates_coe (δ : ℝ) (hδ : 0 < δ) :
    mixedCoordinates (vector f c α β hα hβ hw hc2 δ) =ᵐ[volume]
      coordinateProfile f c α β δ := by
  rw [vector_sum f c α β hα hβ hw hc hc2 δ hδ,map_sum]
  simp only [map_smul]
  exact KFCausalFiniteLpRepresentatives.weighted_sum_coe volume (coefficients f δ)
    (fun j => mixedCoordinates (packetState f c α β hα hβ hc hc2 δ hδ j))
    (fun j => coordinateDensity α β (widths f δ j) (sources f j) (polynomials f j)
      (fun s => c s (index f j).1))
    (fun j => KFCausalNarrowFourierPackets.state_coordinates_coe α β (widths f δ j) hα hβ
      (lt_of_lt_of_le zero_lt_one (widths_admissible f δ hδ.le j))
      (sources f j) (polynomials f j) (fun s => c s (index f j).1) (hc _) (hc2 _))

#print axioms profile_expansion
#print axioms coordinate_blocks
#print axioms coordinate_exact
#print axioms coordinate_tendsto
#print axioms coordinate_norm_bound
#print axioms vector_sum
#print axioms vector_coordinates_coe
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredNarrowFourier
