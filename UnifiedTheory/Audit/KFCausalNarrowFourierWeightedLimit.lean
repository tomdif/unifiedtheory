/- Actual L2 convergence of the coordinate-weighted charged quotient and
first charged derivative. Both finite representatives and their dominating
L2 functions are derived, not postulated. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierWeightedBounds
import UnifiedTheory.Audit.KFCausalDominatedRepresentedL2Limit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNarrowFourierWeightedLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open KFCausalNarrowFourierPackets (chargedRadius)
open KFCausalNarrowFourierChargedBounds (charged moment slope limitSlope charged_tendsto slope_tendsto)
open KFCausalNarrowFourierWeightedBounds

variable (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
  (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)
  (w : Block 2 × Block 4 → ℂ) (hw : Continuous w) (C : ℝ) (hC : 0 ≤ C)
  (hb : ∀ z, ‖w z‖ ≤ C*(1+chargedRadius α z)) (n : ℕ)

def chargedVector (δ : ℝ) : ProductHilbert 2 4 := if hδ : 0 < δ then
  (weighted_charged_memLp α β hα hβ b P g hc hg w hw C hC hb n δ hδ).toLp
    (fun z => w z*charged n δ α β b P g z) else 0

def slopeVector (δ : ℝ) : ProductHilbert 2 4 := if hδ : 0 < δ then
  (weighted_slope_memLp α β hα hβ b P g hc hg w hw C hC hb n δ hδ).toLp
    (fun z => w z*slope n δ α β b P g z) else 0

theorem chargedVector_coe (δ : ℝ) (hδ : 0 < δ) :
    chargedVector α β hα hβ b P g hc hg w hw C hC hb n δ =ᵐ[volume]
      fun z => w z*charged n δ α β b P g z := by
  rw [chargedVector,dif_pos hδ]
  exact MemLp.coeFn_toLp _

theorem slopeVector_coe (δ : ℝ) (hδ : 0 < δ) :
    slopeVector α β hα hβ b P g hc hg w hw C hC hb n δ =ᵐ[volume]
      fun z => w z*slope n δ α β b P g z := by
  rw [slopeVector,dif_pos hδ]
  exact MemLp.coeFn_toLp _

theorem chargedVector_tendsto :
    Tendsto (chargedVector α β hα hβ b P g hc hg w hw C hC hb n) (𝓝[>] 0)
      (𝓝 ((weighted_moment_memLp α β hα hβ b P g hc hg w hw C hC hb n).toLp
        (fun z => w z*moment n α β b P g z))) := by
  apply KFCausalDominatedRepresentedL2Limit.represented_tendsto _ _ _ _
    (envelope α β b P g C n) (envelope_memLp α β hα hβ b P g hc hg C n)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact chargedVector_coe α β hα hβ b P g hc hg w hw C hC hb n δ hδ
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs,abs_of_nonneg (envelope_nonnegative α β b P g C hC n z)] using
      weighted_charged_bound α β hα b P g w C hb n δ hδ z
  · exact Filter.Eventually.of_forall (fun z => (charged_tendsto n α β b P g z).const_mul (w z))

theorem slopeVector_tendsto :
    Tendsto (slopeVector α β hα hβ b P g hc hg w hw C hC hb n) (𝓝[>] 0)
      (𝓝 ((weighted_limitSlope_memLp α β hα hβ b P g hc hg w hw C hC hb n).toLp
        (fun z => w z*limitSlope n α β b P g z))) := by
  apply KFCausalDominatedRepresentedL2Limit.represented_tendsto _ _ _ _
    (fun z => (n:ℝ)*envelope α β b P g C (n-1) z+envelope α β b P g C n z)
    (((envelope_memLp α β hα hβ b P g hc hg C (n-1)).const_mul (n:ℝ)).add
      (envelope_memLp α β hα hβ b P g hc hg C n))
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact slopeVector_coe α β hα hβ b P g hc hg w hw C hC hb n δ hδ
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [] with z
    have he : 0 ≤ (n:ℝ)*envelope α β b P g C (n-1) z+envelope α β b P g C n z :=
      add_nonneg (mul_nonneg (Nat.cast_nonneg n) (envelope_nonnegative α β b P g C hC (n-1) z))
        (envelope_nonnegative α β b P g C hC n z)
    simpa only [Real.norm_eq_abs,abs_of_nonneg he] using weighted_slope_bound α β hα b P g w C hb n δ hδ z
  · exact Filter.Eventually.of_forall (fun z => (slope_tendsto n α β b P g z).const_mul (w z))

#print axioms chargedVector_coe
#print axioms slopeVector_coe
#print axioms chargedVector_tendsto
#print axioms slopeVector_tendsto
end
end UnifiedTheory.Audit.KFCausalNarrowFourierWeightedLimit
