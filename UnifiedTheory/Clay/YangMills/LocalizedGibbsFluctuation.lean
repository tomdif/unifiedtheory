/- Local fluctuation bounds near a minimum of the actual compact Gibbs
action. A comparison with the global partition bound requires control only
on two small sets, not a global action-oscillation bound. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.LocalizedGibbsFluctuation
noncomputable section
open MeasureTheory Filter CompactGibbsContinuity

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- On a set whose energy is at most C above the global minimum, the Gibbs
expectation of a nonnegative observable has a localized Haar lower bound. -/
theorem localized_lower (S : X → ℝ) (hS : Continuous S) (s0 C : ℝ)
    (hmin : ∀ x, s0 ≤ S x) (A : Set X) (hA : MeasurableSet A)
    (hlocal : ∀ x ∈ A, S x ≤ s0 + C)
    (Q : X → ℝ) (hQ : Continuous Q) (hQ0 : ∀ x, 0 ≤ Q x)
    (q : ℝ) (hq : 0 ≤ q) (hfloor : ∀ x ∈ A, q ≤ Q x) :
    μ.real A * Real.exp (-C) * q ≤ ∫ x, Q x ∂law μ S := by
  let w := fun x => Real.exp (-S x)
  have hw : Continuous w := Real.continuous_exp.comp hS.neg
  have hiw : Integrable w μ := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun x => w x * Q x) μ :=
    (hw.mul hQ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz : 0 < ∫ x, w x ∂μ := partition_positive μ S hS
  have hpart : (∫ x, w x ∂μ) ≤ Real.exp (-s0) := by
    calc
      _ ≤ ∫ _x : X, Real.exp (-s0) ∂μ :=
        integral_mono hiw (integrable_const _) (fun x => Real.exp_le_exp.mpr (neg_le_neg (hmin x)))
      _ = _ := by simp
  have hnum : Real.exp (-(s0 + C)) * q * μ.real A ≤ ∫ x, w x * Q x ∂μ := by
    calc
      _ = ∫ _x in A, Real.exp (-(s0 + C)) * q ∂μ := by simp [mul_comm, mul_left_comm]
      _ ≤ ∫ x in A, w x * Q x ∂μ := by
        apply setIntegral_mono_on (integrableOn_const) hi.integrableOn hA
        intro x hx
        exact mul_le_mul (Real.exp_le_exp.mpr (neg_le_neg (hlocal x hx)))
          (hfloor x hx) hq (Real.exp_pos _).le
      _ ≤ ∫ x, w x * Q x ∂μ :=
        setIntegral_le_integral hi (Eventually.of_forall (fun x => mul_nonneg (Real.exp_pos _).le (hQ0 x)))
  rw [law, LocalGibbsComparison.weighted_integral μ w hw.measurable
    (fun x => (Real.exp_pos _).le) hz Q]
  apply (le_div_iff₀ hz).mpr
  calc
    (μ.real A * Real.exp (-C) * q) * (∫ x, w x ∂μ) ≤
        (μ.real A * Real.exp (-C) * q) * Real.exp (-s0) :=
      mul_le_mul_of_nonneg_left hpart (by positivity)
    _ = Real.exp (-(s0 + C)) * q * μ.real A := by
      have he : Real.exp (-C) * Real.exp (-s0) = Real.exp (-(s0 + C)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (Real.exp (-C) * Real.exp (-s0)) * q * μ.real A := by ring
        _ = _ := by rw [he]
    _ ≤ _ := hnum

/-- Two low-energy sets with separated observable values force a centered
second moment for EVERY center. In particular the actual mean is allowed.
The mass is a single-set lower bound, not a product of two tiny masses. -/
theorem two_caps_lower (S : X → ℝ) (hS : Continuous S) (s0 C : ℝ)
    (hmin : ∀ x, s0 ≤ S x) (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hlocalA : ∀ x ∈ A, S x ≤ s0 + C) (hlocalB : ∀ x ∈ B, S x ≤ s0 + C)
    (F : X → ℂ) (hF : Continuous F) (alpha beta : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hsep : 4 * r ≤ ‖alpha - beta‖)
    (hFA : ∀ x ∈ A, ‖F x - alpha‖ ≤ r) (hFB : ∀ x ∈ B, ‖F x - beta‖ ≤ r)
    (mass : ℝ) (hmass : mass ≤ μ.real A) (hmassB : mass ≤ μ.real B) (center : ℂ) :
    mass * Real.exp (-C) * r^2 ≤ ∫ x, ‖F x - center‖^2 ∂law μ S := by
  have hfar : 2 * r ≤ ‖alpha - center‖ ∨ 2 * r ≤ ‖beta - center‖ := by
    by_contra h
    push_neg at h
    have ht : ‖alpha - beta‖ ≤ ‖alpha - center‖ + ‖beta - center‖ := by
      simpa only [norm_sub_rev beta center] using norm_sub_le_norm_sub_add_norm_sub alpha center beta
    linarith
  have hcap (D : Set X) (hD : MeasurableSet D) (hlocal : ∀ x ∈ D, S x ≤ s0 + C)
      (value : ℂ) (hnear : ∀ x ∈ D, ‖F x - value‖ ≤ r)
      (hfar : 2 * r ≤ ‖value - center‖) (hm : mass ≤ μ.real D) :
      mass * Real.exp (-C) * r^2 ≤ ∫ x, ‖F x - center‖^2 ∂law μ S := by
    have hpoint (x : X) (hx : x ∈ D) : r ≤ ‖F x - center‖ := by
      have ht : ‖value - center‖ ≤ ‖F x - value‖ + ‖F x - center‖ := by
        simpa only [norm_sub_rev value (F x)] using norm_sub_le_norm_sub_add_norm_sub value (F x) center
      linarith [hnear x hx]
    have hh := localized_lower μ S hS s0 C hmin D hD hlocal
      (fun x => ‖F x - center‖^2) ((hF.sub continuous_const).norm.pow 2)
      (fun x => sq_nonneg _) (r^2) (sq_nonneg _)
      (fun x hx => pow_le_pow_left₀ hr (hpoint x hx) 2)
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le) (sq_nonneg _)).trans hh
  rcases hfar with ha | hb
  · exact hcap A hA hlocalA alpha hFA ha hmass
  · exact hcap B hB hlocalB beta hFB hb hmassB

end
end UnifiedTheory.Clay.YangMills.LocalizedGibbsFluctuation
