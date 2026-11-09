/- Coordinate-weighted L2 envelopes for the narrow Fourier charged
profiles and their first charged derivatives. A linear-growth weight covers
both frequency and broad-position factors; neutral derivatives stay packets. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierChargedBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNarrowFourierWeightedBounds
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalNarrowFourierPackets (chargedRadius)
open KFCausalNarrowFourierChargedBounds

variable (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
  (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)
  (w : Block 2 × Block 4 → ℂ) (hw : Continuous w) (C : ℝ) (hC : 0 ≤ C)
  (hb : ∀ z, ‖w z‖ ≤ C*(1+chargedRadius α z))

def envelope (n : ℕ) (z : Block 2 × Block 4) : ℝ :=
  C*(‖moment n α β b P g z‖+‖moment (n+1) α β b P g z‖)

include hC in
theorem envelope_nonnegative (n : ℕ) (z : Block 2 × Block 4) :
    0 ≤ envelope α β b P g C n z := by unfold envelope; positivity

include hα hβ hc hg in
theorem envelope_memLp (n : ℕ) : MemLp (envelope α β b P g C n) 2 volume :=
  (((moment_memLp n α β hα hβ b P g hc hg).norm).add
    ((moment_memLp (n+1) α β hα hβ b P g hc hg).norm)).const_mul C

include hα in
theorem moment_succ_norm (n : ℕ) (z : Block 2 × Block 4) :
    ‖moment (n+1) α β b P g z‖ = chargedRadius α z*‖moment n α β b P g z‖ := by
  simp only [moment,pow_succ,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (KFCausalNarrowFourierPackets.chargedRadius_nonnegative α hα z)]
  ring

include hα hb in
theorem weighted_moment_bound (n : ℕ) (z : Block 2 × Block 4) :
    ‖w z*moment n α β b P g z‖ ≤ envelope α β b P g C n z := by
  rw [norm_mul,envelope,moment_succ_norm α β hα b P g n z]
  have hh := mul_le_mul_of_nonneg_right (hb z) (norm_nonneg (moment n α β b P g z))
  nlinarith only [hh]

include hα hβ hc hg hw hC hb in
theorem weighted_moment_memLp (n : ℕ) : MemLp (fun z => w z*moment n α β b P g z) 2 volume := by
  have hcont : Continuous (fun z => w z*moment n α β b P g z) := by
    unfold moment chargedRadius KFCausalNeutralLinePackets.packet KFCausalNeutralLinePackets.entire
    fun_prop
  apply (envelope_memLp α β hα hβ b P g hc hg C n).of_le hcont.aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs,abs_of_nonneg (envelope_nonnegative α β b P g C hC n z)] using
    weighted_moment_bound α β hα b P g w C hb n z

include hα hb in
theorem weighted_charged_bound (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (z : Block 2 × Block 4) :
    ‖w z*charged n δ α β b P g z‖ ≤ envelope α β b P g C n z := by
  calc
    _ ≤ ‖w z*moment n α β b P g z‖ := by
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (charged_bound n δ α β hδ hα b P g z) (norm_nonneg _)
    _ ≤ _ := weighted_moment_bound α β hα b P g w C hb n z

include hα hb in
theorem weighted_slope_bound (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (z : Block 2 × Block 4) :
    ‖w z*slope n δ α β b P g z‖ ≤
      (n:ℝ)*envelope α β b P g C (n-1) z+envelope α β b P g C n z := by
  have hs := mul_le_mul_of_nonneg_left (slope_bound n δ α β hδ hα b P g z) (norm_nonneg (w z))
  have h1 := weighted_moment_bound α β hα b P g w C hb (n-1) z
  have h2 := weighted_moment_bound α β hα b P g w C hb n z
  simp only [norm_mul] at h1 h2 ⊢
  nlinarith [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)]

theorem limitSlope_moments (n : ℕ) (z : Block 2 × Block 4) :
    limitSlope n α β b P g z = (n:ℂ)*moment (n-1) α β b P g z-moment n α β b P g z := by
  unfold limitSlope moment KFCausalClusteredWidthChargedJet.limitJet
  ring

include hα hβ hc hg hw hC hb in
theorem weighted_limitSlope_memLp (n : ℕ) : MemLp (fun z => w z*limitSlope n α β b P g z) 2 volume := by
  have hm := ((weighted_moment_memLp α β hα hβ b P g hc hg w hw C hC hb (n-1)).const_mul (n:ℂ)).sub
    (weighted_moment_memLp α β hα hβ b P g hc hg w hw C hC hb n)
  apply hm.ae_eq
  filter_upwards [] with z
  simp only [Pi.sub_apply,limitSlope_moments]
  ring

include hα hβ hc hg hw hC hb in
theorem weighted_charged_memLp (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    MemLp (fun z => w z*charged n δ α β b P g z) 2 volume := by
  have hcont : Continuous (fun z => w z*charged n δ α β b P g z) := by
    unfold charged chargedRadius KFCausalClusteredWidthProfiles.quotient
      KFCausalNeutralLinePackets.packet KFCausalNeutralLinePackets.entire
    fun_prop
  apply (envelope_memLp α β hα hβ b P g hc hg C n).of_le hcont.aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs,abs_of_nonneg (envelope_nonnegative α β b P g C hC n z)] using
    weighted_charged_bound α β hα b P g w C hb n δ hδ z

include hα hβ hc hg hw hC hb in
theorem weighted_slope_memLp (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    MemLp (fun z => w z*slope n δ α β b P g z) 2 volume := by
  have hcont : Continuous (fun z => w z*slope n δ α β b P g z) := by
    unfold KFCausalNarrowFourierChargedBounds.slope KFCausalClusteredWidthChargedJet.jet chargedRadius KFCausalClusteredWidthProfiles.quotient
      KFCausalNeutralLinePackets.packet KFCausalNeutralLinePackets.entire
    fun_prop
  have hm := ((envelope_memLp α β hα hβ b P g hc hg C (n-1)).const_mul (n:ℝ)).add
    (envelope_memLp α β hα hβ b P g hc hg C n)
  apply hm.of_le hcont.aestronglyMeasurable
  filter_upwards [] with z
  have he : 0 ≤ (n:ℝ)*envelope α β b P g C (n-1) z+envelope α β b P g C n z :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg n) (envelope_nonnegative α β b P g C hC (n-1) z))
      (envelope_nonnegative α β b P g C hC n z)
  simpa only [Pi.add_apply,Pi.mul_apply,Real.norm_eq_abs,abs_of_nonneg he] using
    weighted_slope_bound α β hα b P g w C hb n δ hδ z

#print axioms envelope_nonnegative
#print axioms envelope_memLp
#print axioms moment_succ_norm
#print axioms weighted_moment_bound
#print axioms weighted_moment_memLp
#print axioms weighted_charged_bound
#print axioms weighted_slope_bound
#print axioms limitSlope_moments
#print axioms weighted_limitSlope_memLp
#print axioms weighted_charged_memLp
#print axioms weighted_slope_memLp
end
end UnifiedTheory.Audit.KFCausalNarrowFourierWeightedBounds
