/- Joint localization pays the actual two-step residual once. No independence
or spatial disjointness is assumed for the source-dependent cutoffs. -/
import UnifiedTheory.Clay.YangMills.CompactCutoffCover
import UnifiedTheory.Clay.YangMills.WilsonHighFieldReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCutoffCover
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay CompactDensityEntropy WilsonHighFieldReduction

variable (n : ℕ) [NeZero n]

theorem cutoff_output (β : ℝ) (hβ : 0 ≤ β) (χ : C(Slice n, ℝ)) (q : ℝ) (hq : 0 ≤ q)
    (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hd : ∀ h : C(Slice n, ℝ), (∀ u, χ u = 0 → h u = 0) →
      mass n β hβ (step n β hβ h) ≤ q*mass n β hβ h) (f : C(Slice n, ℝ)) :
    mass n β hβ (χ*step n β hβ f) ≤ q*mass n β hβ f := by
  let k := χ*step n β hβ f
  let h := χ*k
  have hid : pairing n β hβ h (step n β hβ f) = mass n β hβ k := by
    unfold pairing mass
    apply integral_congr_ae
    filter_upwards with u
    simp only [h, k, ContinuousMap.mul_apply]
    ring
  have hc := pairing_sq n β hβ (step n β hβ h) f
  rw [← pairing_step, hid] at hc
  have hh := hd h (by intro u hu; change χ u*k u = 0; rw [hu, zero_mul])
  have hb := hc.trans (mul_le_mul_of_nonneg_right
    (hh.trans (mul_le_mul_of_nonneg_left (cutoff_mass_le n β hβ χ k hχ) hq))
    (mass_nonneg n β hβ f))
  have hk := mass_nonneg n β hβ k
  by_cases hz : mass n β hβ k = 0
  · change mass n β hβ k ≤ _
    rw [hz]
    exact mul_nonneg hq (mass_nonneg n β hβ f)
  · have hp : 0 < mass n β hβ k := lt_of_le_of_ne hk (Ne.symm hz)
    change mass n β hβ k ≤ _
    nlinarith

theorem mass_split (β : ℝ) (hβ : 0 ≤ β) (χ f h : C(Slice n, ℝ)) :
    mass n β hβ (χ*f) ≤ 2*mass n β hβ (χ*(f-h))+2*mass n β hβ (χ*h) := by
  letI := groundLaw_probability n β hβ
  have hi := integral_mono
    (continuous_integrable (groundLaw n β hβ) _ ((χ*f).continuous.pow 2))
    (((continuous_integrable (groundLaw n β hβ) _ ((χ*(f-h)).continuous.pow 2)).const_mul 2).add
      ((continuous_integrable (groundLaw n β hβ) _ ((χ*h).continuous.pow 2)).const_mul 2))
    (fun u => show (χ u*f u)^2 ≤ 2*(χ u*(f u-h u))^2+2*(χ u*h u)^2 by
      nlinarith [sq_nonneg (χ u*(f u-2*h u))])
  simp only [Pi.add_apply] at hi
  rw [integral_add, integral_const_mul, integral_const_mul] at hi
  · exact hi
  · exact (continuous_integrable (groundLaw n β hβ) _ ((χ*(f-h)).continuous.pow 2)).const_mul 2
  · exact (continuous_integrable (groundLaw n β hβ) _ ((χ*h).continuous.pow 2)).const_mul 2

variable {I : Type*} [Fintype I]

theorem sum_mass_integral (β : ℝ) (hβ : 0 ≤ β) (χ : I → C(Slice n, ℝ))
    (f : C(Slice n, ℝ)) :
    (∑ i, mass n β hβ (χ i*f)) = ∫ u, ∑ i, ((χ i*f) u)^2 ∂groundLaw n β hβ := by
  letI := groundLaw_probability n β hβ
  exact (integral_finset_sum _ (fun i _ =>
    continuous_integrable (groundLaw n β hβ) _ ((χ i*f).continuous.pow 2))).symm

theorem sum_mass_le (β : ℝ) (hβ : 0 ≤ β) (χ : I → C(Slice n, ℝ))
    (hχ : ∀ u, ∑ i, (χ i u) ^ 2 ≤ 1) (f : C(Slice n, ℝ)) :
    ∑ i, mass n β hβ (χ i*f) ≤ mass n β hβ f := by
  letI := groundLaw_probability n β hβ
  rw [sum_mass_integral]
  apply integral_mono
    (integrable_finset_sum _ (fun i _ =>
      continuous_integrable (groundLaw n β hβ) _ ((χ i*f).continuous.pow 2)))
    (continuous_integrable (groundLaw n β hβ) _ (f.continuous.pow 2))
  intro u
  simpa only [ContinuousMap.mul_apply, mul_pow, ← Finset.sum_mul, one_mul] using
    mul_le_mul_of_nonneg_right (hχ u) (sq_nonneg (f u))

/-- The loss coefficient is independent of the size and overlap of the cover. -/
theorem joint_localization (β : ℝ) (hβ : 0 ≤ β) (χ : I → C(Slice n, ℝ))
    (hχ : ∀ u, ∑ i, (χ i u) ^ 2 ≤ 1) (q : I → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hout : ∀ i f, mass n β hβ (χ i * step n β hβ f) ≤ q i * mass n β hβ f)
    (f : C(Slice n, ℝ)) :
    (∑ i, mass n β hβ (χ i*f)) ≤
      2*loss n β hβ f+2*(∑ i, q i)*mass n β hβ f := by
  let P2 := step n β hβ (step n β hβ f)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => mass_split n β hβ (χ i) f P2)
  have ha := (sum_mass_le n β hβ χ hχ (f-P2)).trans (residual_le_loss n β hβ f)
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    (hout i (step n β hβ f)).trans
      (mul_le_mul_of_nonneg_left (mass_step_le n β hβ f) (hq i)))
  change (∑ i, mass n β hβ (χ i*P2)) ≤ ∑ i, q i * mass n β hβ f at hb
  rw [← Finset.sum_mul] at hb
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  linarith

theorem event_le_sum_mass (β : ℝ) (hβ : 0 ≤ β) (χ : I → C(Slice n, ℝ))
    (E : Set (Slice n)) (hE : MeasurableSet E)
    (hcover : ∀ u ∈ E, ∑ i, (χ i u) ^ 2 = 1) (f : C(Slice n, ℝ)) :
    (∫ u, E.indicator (fun v => (f v)^2) u ∂groundLaw n β hβ) ≤
      ∑ i, mass n β hβ (χ i*f) := by
  letI := groundLaw_probability n β hβ
  rw [sum_mass_integral]
  apply integral_mono
    ((continuous_integrable (groundLaw n β hβ) _ (f.continuous.pow 2)).indicator hE)
    (integrable_finset_sum _ (fun i _ =>
      continuous_integrable (groundLaw n β hβ) _ ((χ i*f).continuous.pow 2)))
  intro u
  by_cases hu : u ∈ E
  · rw [Set.indicator_of_mem hu]
    simp only [ContinuousMap.mul_apply, mul_pow, ← Finset.sum_mul, hcover u hu, one_mul, le_refl]
  · rw [Set.indicator_of_notMem hu]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

end
end UnifiedTheory.Clay.YangMills.WilsonCutoffCover
