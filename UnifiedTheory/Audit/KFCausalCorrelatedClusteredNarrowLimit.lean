/- Identify the already constructed physical clustered limit with its
explicit narrow Fourier polynomial representative. This is an actual unitary
Hilbert-space identity, including arbitrary correlated neutral profiles. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredNarrowFourier
import UnifiedTheory.Audit.KFCausalNarrowFourierChargedBounds
import UnifiedTheory.Audit.KFCausalDominatedRepresentedL2Limit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredNarrowLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalNarrowFourierCoordinates (mixedCoordinates)
open KFCausalNarrowFourierChargedBounds (moment moment_memLp)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredNarrowFourier (coordinateProfile limitProfile coordinate_tendsto vector_coordinates_coe)
open KFCausalCorrelatedClusteredClockVectors (vector limitingVector vector_tendsto)

variable {m : ℕ} (f : Family m) (c : ℝ → Fin m → ℂ) (α β : ℝ)

def block (i : Fin m) (z : Block 2 × Block 4) : ℂ :=
  ((Real.pi/α:ℝ)*f.amplitude i)*moment (f.degree i) α β (f.source i) (f.polynomial i) (fun s => c s i) z

theorem block_identity (i : Fin m) (z : Block 2 × Block 4) :
    block f c α β i z = ((Real.pi/α:ℝ)*f.amplitude i*c (z.2 0) i)*
      (Complex.exp (-(KFCausalNarrowFourierPackets.chargedRadius α z:ℂ))*
        (KFCausalNarrowFourierPackets.chargedRadius α z:ℂ)^(f.degree i))*
      KFCausalNeutralLinePackets.packet β (f.source i) (f.polynomial i) (z.2 3) := by
  unfold block moment
  ring

theorem limitProfile_blocks (z : Block 2 × Block 4) : limitProfile f c α β z = ∑ i, block f c α β i z := by
  simp only [block_identity,limitProfile]

variable (hα : 0 < α) (hβ : 0 < β)
  (hc : ∀ i, Continuous (fun s => c s i)) (hc2 : ∀ i, MemLp (fun s => c s i) 2 volume)

include hα hβ hc hc2 in
theorem block_memLp (i : Fin m) : MemLp (block f c α β i) 2 volume :=
  (moment_memLp (f.degree i) α β hα hβ (f.source i) (f.polynomial i) (fun s => c s i) (hc i) (hc2 i)).const_mul _

include hα hβ hc hc2 in
theorem limitProfile_memLp : MemLp (limitProfile f c α β) 2 volume := by
  have hm := memLp_finset_sum Finset.univ (fun i _ => block_memLp f c α β hα hβ hc hc2 i)
  exact hm.ae_eq (Filter.Eventually.of_forall (fun z => (limitProfile_blocks f c α β z).symm))

variable (hw : 32*β ≤ α)

theorem coordinates_tendsto :
    Tendsto (fun δ => mixedCoordinates (vector f c α β hα hβ hw hc2 δ)) (𝓝[>] 0)
      (𝓝 ((limitProfile_memLp f c α β hα hβ hc hc2).toLp (limitProfile f c α β))) := by
  apply KFCausalDominatedRepresentedL2Limit.represented_tendsto _ (coordinateProfile f c α β) _ _
    (fun z => ∑ i, ‖block f c α β i z‖)
    (memLp_finset_sum Finset.univ (fun i _ => (block_memLp f c α β hα hβ hc hc2 i).norm))
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact vector_coordinates_coe f c α β hα hβ hw hc hc2 δ hδ
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [] with z
    have hn : 0 ≤ ∑ i, ‖block f c α β i z‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hn]
    simpa only [block_identity] using
      KFCausalCorrelatedClusteredNarrowFourier.coordinate_norm_bound f c α β hα δ hδ z
  · exact Filter.Eventually.of_forall (coordinate_tendsto f c α β)

theorem limitingVector_coordinates :
    mixedCoordinates (limitingVector f c α β hα hβ hw hc2 hc) =
      (limitProfile_memLp f c α β hα hβ hc hc2).toLp (limitProfile f c α β) := by
  exact tendsto_nhds_unique
    ((mixedCoordinates.continuous.tendsto _).comp (vector_tendsto f c α β hα hβ hw hc2 hc))
    (coordinates_tendsto f c α β hα hβ hc hc2 hw)

theorem limitingVector_coe :
    mixedCoordinates (limitingVector f c α β hα hβ hw hc2 hc) =ᵐ[volume] limitProfile f c α β := by
  rw [limitingVector_coordinates f c α β hα hβ hc hc2 hw]
  exact MemLp.coeFn_toLp _

#print axioms block_identity
#print axioms limitProfile_blocks
#print axioms block_memLp
#print axioms limitProfile_memLp
#print axioms coordinates_tendsto
#print axioms limitingVector_coordinates
#print axioms limitingVector_coe
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredNarrowLimit
