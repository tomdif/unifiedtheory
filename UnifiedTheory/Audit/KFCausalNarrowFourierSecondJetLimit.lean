/- Derived L2 envelopes and strong limits for coordinate-weighted second
charged derivatives. The local spacing bound suffices for the right limit. -/
import UnifiedTheory.Audit.KFCausalClusteredWidthSecondJet
import UnifiedTheory.Audit.KFCausalNarrowFourierWeightedLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalNarrowFourierSecondJetLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open KFCausalNarrowFourierPackets (chargedRadius)
open KFCausalNarrowFourierChargedBounds (moment)
open KFCausalNarrowFourierWeightedBounds
open KFCausalNeutralLinePackets (packet)
open KFCausalClusteredWidthSecondJet (secondJet limitSecondJet)

def secondSlope (n : ℕ) (δ α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (z : Block 2 × Block 4) : ℂ := g (z.2 0)*secondJet n δ (chargedRadius α z)*packet β b P (z.2 3)
def limitSecondSlope (n : ℕ) (α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (z : Block 2 × Block 4) : ℂ := g (z.2 0)*limitSecondJet n (chargedRadius α z)*packet β b P (z.2 3)

theorem secondSlope_bound (n : ℕ) (δ α β : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hα : 0 < α)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (z : Block 2 × Block 4) :
    ‖secondSlope n δ α β b P g z‖ ≤ (n:ℝ)*(n-1:ℕ)*‖moment (n-2) α β b P g z‖+
      3*(n:ℝ)*‖moment (n-1) α β b P g z‖+‖moment n α β b P g z‖ := by
  have hz : 0 ≤ (chargedRadius α z:ℂ).re := KFCausalNarrowFourierPackets.chargedRadius_nonnegative α hα z
  have hj := KFCausalClusteredWidthSecondJet.secondJet_norm_le n δ hδ hδ1 (chargedRadius α z:ℂ) hz
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj (norm_nonneg (g (z.2 0))))
    (norm_nonneg (packet β b P (z.2 3)))
  simp only [secondSlope,moment,norm_mul,norm_pow,Complex.norm_exp,Complex.neg_re]
  convert hb using 1
  ring

theorem limitSecondSlope_moments (n : ℕ) (α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (z : Block 2 × Block 4) :
    limitSecondSlope n α β b P g z = (n:ℂ)*(n-1:ℕ)*moment (n-2) α β b P g z-
      2*(n:ℂ)*moment (n-1) α β b P g z+moment n α β b P g z := by
  unfold limitSecondSlope limitSecondJet moment
  ring

theorem secondSlope_tendsto (n : ℕ) (α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (z : Block 2 × Block 4) :
    Tendsto (fun δ => secondSlope n δ α β b P g z) (𝓝[>] 0) (𝓝 (limitSecondSlope n α β b P g z)) :=
  ((KFCausalClusteredWidthSecondJet.secondJet_tendsto n (chargedRadius α z:ℂ)).const_mul (g (z.2 0))).mul_const
    (packet β b P (z.2 3))

variable (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
  (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)
  (w : Block 2 × Block 4 → ℂ) (hw : Continuous w) (C : ℝ) (hC : 0 ≤ C)
  (hb : ∀ z, ‖w z‖ ≤ C*(1+chargedRadius α z)) (n : ℕ)

def secondEnvelope (z : Block 2 × Block 4) : ℝ :=
  (n:ℝ)*(n-1:ℕ)*envelope α β b P g C (n-2) z+
    3*(n:ℝ)*envelope α β b P g C (n-1) z+envelope α β b P g C n z

include hC in
theorem secondEnvelope_nonnegative (z : Block 2 × Block 4) : 0 ≤ secondEnvelope α β b P g C n z := by
  have he := envelope_nonnegative α β b P g C hC
  unfold secondEnvelope
  exact add_nonneg (add_nonneg (mul_nonneg (by positivity) (he (n-2) z))
    (mul_nonneg (by positivity) (he (n-1) z))) (he n z)

include hα hβ hc hg in
theorem secondEnvelope_memLp : MemLp (secondEnvelope α β b P g C n) 2 volume :=
  (((envelope_memLp α β hα hβ b P g hc hg C (n-2)).const_mul ((n:ℝ)*(n-1:ℕ))).add
    ((envelope_memLp α β hα hβ b P g hc hg C (n-1)).const_mul (3*(n:ℝ)))).add
    (envelope_memLp α β hα hβ b P g hc hg C n)

include hα hb in
theorem weighted_secondSlope_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (z : Block 2 × Block 4) :
    ‖w z*secondSlope n δ α β b P g z‖ ≤ secondEnvelope α β b P g C n z := by
  have hs := mul_le_mul_of_nonneg_left (secondSlope_bound n δ α β hδ hδ1 hα b P g z) (norm_nonneg (w z))
  have h1 := weighted_moment_bound α β hα b P g w C hb (n-2) z
  have h2 := weighted_moment_bound α β hα b P g w C hb (n-1) z
  have h3 := weighted_moment_bound α β hα b P g w C hb n z
  simp only [norm_mul] at h1 h2 h3 ⊢
  unfold secondEnvelope
  nlinarith only [hs,h3,mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (n:ℝ)*(n-1:ℕ)),
    mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 3*(n:ℝ))]

include hα hβ hc hg hw hC hb in
theorem weighted_limitSecondSlope_memLp : MemLp (fun z => w z*limitSecondSlope n α β b P g z) 2 volume := by
  have hm := (((weighted_moment_memLp α β hα hβ b P g hc hg w hw C hC hb (n-2)).const_mul ((n:ℂ)*(n-1:ℕ))).sub
    ((weighted_moment_memLp α β hα hβ b P g hc hg w hw C hC hb (n-1)).const_mul (2*(n:ℂ)))).add
    (weighted_moment_memLp α β hα hβ b P g hc hg w hw C hC hb n)
  apply hm.ae_eq
  filter_upwards [] with z
  simp only [Pi.add_apply,Pi.sub_apply,limitSecondSlope_moments]
  ring

include hα hβ hc hg hw hC hb in
theorem weighted_secondSlope_memLp (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    MemLp (fun z => w z*secondSlope n δ α β b P g z) 2 volume := by
  have hcont : Continuous (fun z => w z*secondSlope n δ α β b P g z) := by
    unfold secondSlope secondJet chargedRadius KFCausalClusteredWidthProfiles.quotient
      packet KFCausalNeutralLinePackets.entire
    fun_prop
  apply (secondEnvelope_memLp α β hα hβ b P g hc hg C n).of_le hcont.aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs,abs_of_nonneg (secondEnvelope_nonnegative α β b P g C hC n z)] using
    weighted_secondSlope_bound α β hα b P g w C hb n δ hδ hδ1 z

def secondVector (δ : ℝ) : ProductHilbert 2 4 := if hδ : 0 < δ ∧ δ ≤ 1 then
  (weighted_secondSlope_memLp α β hα hβ b P g hc hg w hw C hC hb n δ hδ.1 hδ.2).toLp
    (fun z => w z*secondSlope n δ α β b P g z) else 0

theorem secondVector_coe (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    secondVector α β hα hβ b P g hc hg w hw C hC hb n δ =ᵐ[volume]
      fun z => w z*secondSlope n δ α β b P g z := by
  rw [secondVector,dif_pos ⟨hδ,hδ1⟩]
  exact MemLp.coeFn_toLp _

theorem secondVector_tendsto :
    Tendsto (secondVector α β hα hβ b P g hc hg w hw C hC hb n) (𝓝[>] 0)
      (𝓝 ((weighted_limitSecondSlope_memLp α β hα hβ b P g hc hg w hw C hC hb n).toLp
        (fun z => w z*limitSecondSlope n α β b P g z))) := by
  apply KFCausalDominatedRepresentedL2Limit.represented_tendsto _ _ _ _
    (secondEnvelope α β b P g C n) (secondEnvelope_memLp α β hα hβ b P g hc hg C n)
  · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with δ hδ
    exact secondVector_coe α β hα hβ b P g hc hg w hw C hC hb n δ hδ.1 hδ.2.le
  · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with δ hδ
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs,abs_of_nonneg (secondEnvelope_nonnegative α β b P g C hC n z)] using
      weighted_secondSlope_bound α β hα b P g w C hb n δ hδ.1 hδ.2.le z
  · exact Filter.Eventually.of_forall (fun z => (secondSlope_tendsto n α β b P g z).const_mul (w z))

#print axioms secondSlope_bound
#print axioms limitSecondSlope_moments
#print axioms secondSlope_tendsto
#print axioms secondEnvelope_nonnegative
#print axioms secondEnvelope_memLp
#print axioms weighted_secondSlope_bound
#print axioms weighted_limitSecondSlope_memLp
#print axioms weighted_secondSlope_memLp
#print axioms secondVector_coe
#print axioms secondVector_tendsto
end
end UnifiedTheory.Audit.KFCausalNarrowFourierSecondJetLimit
