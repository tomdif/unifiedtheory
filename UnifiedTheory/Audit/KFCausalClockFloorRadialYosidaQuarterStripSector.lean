/- Quarter-strip sectoriality (`|Im| ≤ Re`) of the complex radial symbol, the
shifted radial Yosida cutoff, and the shifted radial resolvent cutoff for
`|q.im| ≤ π * ε / 8` (corresponding to `y = -h / 2` when `|h| ≤ π * ε / 4`),
together with nonnegativity of the real parts of their squares and quadratic
accretivity of the iterated shifted multiplier and resolvent operators. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaOrderedTransport
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventShifted

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaQuarterStripSector
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanConfiguration (Space FrequencyHilbert)
open KFCausalEuclideanClockSplit (TailSpace)
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalComplexClockChart (targetStrip)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalClockInverseStripBounds (inverse_im_bound)
open KFCausalClockFloorRadialYosidaStrip
  (base cutoff radialComplex multiplier sixth_strip_subset)
open KFCausalClockFloorRadialYosidaOrderedTransport
  (family family_line_continuous family_bound family_symbol)
open KFCausalClockFloorRadialResolventShifted
  (coordinates line shifted_coe)
open KFCausalMixedStripExponentialGraph (unitary)
open KFCausalClockFloorDefectCoordinates (straightening)

theorem re_nonneg_of_abs_im_le_re (w : ℂ) (hw : |w.im| ≤ w.re) : 0 ≤ w.re :=
  (abs_nonneg w.im).trans hw

theorem re_mul_self_nonneg_of_abs_im_le_re (w : ℂ) (hw : |w.im| ≤ w.re) :
    0 ≤ (w * w).re := by
  obtain ⟨h1, h2⟩ := abs_le.mp hw
  simp only [Complex.mul_re]
  nlinarith

theorem re_sq_nonneg_of_abs_im_le_re (w : ℂ) (hw : |w.im| ≤ w.re) :
    0 ≤ (w ^ 2).re := by
  simpa only [pow_two] using re_mul_self_nonneg_of_abs_im_le_re w hw

private theorem abs_le_of_nonneg_of_sq_sub_sq_nonneg (a b : ℝ) (ha : 0 ≤ a)
    (h : 0 ≤ a ^ 2 - b ^ 2) : |b| ≤ a := by
  have hsq : b ^ 2 ≤ a ^ 2 := by linarith
  simpa only [abs_of_nonneg ha] using sq_le_sq.mp hsq

private theorem abs_div_le_div_of_nonneg (a b d : ℝ) (hd : 0 ≤ d)
    (h1 : -b ≤ a) (h2 : a ≤ b) : |a / d| ≤ b / d := by
  rw [abs_div, abs_of_nonneg hd]
  exact div_le_div_of_nonneg_right (abs_le.mpr ⟨h1, h2⟩) hd

theorem exp_sector_pi_div_four (u : ℂ) (hu : |u.im| ≤ Real.pi / 4) :
    |(Complex.exp u).im| ≤ (Complex.exp u).re := by
  obtain ⟨hl, hr⟩ := abs_le.mp hu
  have hc : 0 ≤ Real.cos u.im := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hc2 : 0 ≤ Real.cos (2 * u.im) := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [Real.cos_two_mul'] at hc2
  have hsc : |Real.sin u.im| ≤ Real.cos u.im :=
    abs_le_of_nonneg_of_sq_sub_sq_nonneg (Real.cos u.im) (Real.sin u.im) hc hc2
  rw [Complex.exp_im, Complex.exp_re, abs_mul, abs_of_pos (Real.exp_pos u.re)]
  exact mul_le_mul_of_nonneg_left hsc (Real.exp_pos u.re).le

theorem exp_quarter_sector (s : ℂ) (hs : |s.im| ≤ Real.pi / 8) :
    |(Complex.exp s).im| ≤ (Complex.exp s).re ∧
      |((Complex.exp s) ^ 2).im| ≤ ((Complex.exp s) ^ 2).re := by
  obtain ⟨hl, hr⟩ := abs_le.mp hs
  have hs4 : |s.im| ≤ Real.pi / 4 := abs_le.mpr ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have h2s : |(s + s).im| ≤ Real.pi / 4 := by
    rw [Complex.add_im]
    exact abs_le.mpr ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  refine ⟨exp_sector_pi_div_four s hs4, ?_⟩
  rw [pow_two, ← Complex.exp_add]
  exact exp_sector_pi_div_four (s + s) h2s

theorem div_sector_of_real_nonneg (A : ℝ) (hA : 0 ≤ A) (u : ℂ) (hu : |u.im| ≤ u.re) :
    |((A : ℂ) / u).im| ≤ ((A : ℂ) / u).re := by
  obtain ⟨h1, h2⟩ := abs_le.mp hu
  have hd : 0 ≤ Complex.normSq u := Complex.normSq_nonneg u
  simp only [Complex.div_im, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, zero_div, add_zero, zero_sub]
  rw [abs_neg]
  exact abs_div_le_div_of_nonneg (A * u.im) (A * u.re) (Complex.normSq u) hd
    (by nlinarith) (by nlinarith)

theorem base_sector (ε A B : ℝ) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (z : ℂ) (hz : |z.im| ≤ z.re) (hz2 : |(z ^ 2).im| ≤ (z ^ 2).re) :
    |(base ε A B z).im| ≤ (base ε A B z).re := by
  obtain ⟨hz_l, hz_r⟩ := abs_le.mp hz
  obtain ⟨hz2_l, hz2_r⟩ := abs_le.mp hz2
  have hu : |(z * (z + (ε : ℂ))).im| ≤ (z * (z + (ε : ℂ))).re := by
    have heq : z * (z + (ε : ℂ)) = z ^ 2 + (ε : ℂ) * z := by ring
    rw [heq]
    simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero]
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have h1 : |((A : ℂ) / (z * (z + (ε : ℂ)))).im| ≤ ((A : ℂ) / (z * (z + (ε : ℂ)))).re :=
    div_sector_of_real_nonneg A hA (z * (z + (ε : ℂ))) hu
  have h2 : |((B : ℂ) * z / (z + (ε : ℂ))).im| ≤ ((B : ℂ) * z / (z + (ε : ℂ))).re := by
    have hd : 0 ≤ Complex.normSq (z + (ε : ℂ)) := Complex.normSq_nonneg _
    simp only [Complex.div_im, Complex.div_re, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero]
    rw [← sub_div, ← add_div]
    exact abs_div_le_div_of_nonneg _ _ (Complex.normSq (z + (ε : ℂ))) hd
      (by nlinarith [mul_nonneg hB hε, mul_nonneg hB (sq_nonneg z.re), mul_nonneg hB (sq_nonneg z.im)])
      (by nlinarith [mul_nonneg hB hε, mul_nonneg hB (sq_nonneg z.re), mul_nonneg hB (sq_nonneg z.im)])
  obtain ⟨h1_l, h1_r⟩ := abs_le.mp h1
  obtain ⟨h2_l, h2_r⟩ := abs_le.mp h2
  unfold base
  simp only [Complex.div_ofNat_im, Complex.div_ofNat_re, Complex.add_im, Complex.add_re]
  exact abs_div_le_div_of_nonneg _ _ 2 (by norm_num) (by linarith) (by linarith)

theorem cutoff_sector (N : ℝ) (hN : 0 < N) (w : ℂ) (hw : |w.im| ≤ w.re) :
    |(cutoff N w).im| ≤ (cutoff N w).re := by
  obtain ⟨hw_l, hw_r⟩ := abs_le.mp hw
  have hd : 0 ≤ Complex.normSq ((N : ℂ) + w) := Complex.normSq_nonneg _
  unfold cutoff
  simp only [Complex.div_im, Complex.div_re, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, zero_add]
  rw [← sub_div, ← add_div]
  exact abs_div_le_div_of_nonneg _ _ (Complex.normSq ((N : ℂ) + w)) hd
    (by nlinarith [sq_nonneg w.re, sq_nonneg w.im, sq_nonneg N])
    (by nlinarith [sq_nonneg w.re, sq_nonneg w.im, sq_nonneg N])

theorem cutoff_complement_eq (N : ℝ) (hN : 0 < N) (w : ℂ) (hw : 0 ≤ w.re) :
    1 - (N⁻¹ : ℂ) * cutoff N w = (N : ℂ) / ((N : ℂ) + w) := by
  have hNne : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have hd : (N : ℂ) + w ≠ 0 := by
    intro he
    have hi := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hi
    linarith
  unfold cutoff
  field_simp [hNne, hd]
  ring

theorem cutoff_complement_sector (N : ℝ) (hN : 0 < N) (w : ℂ) (hw : |w.im| ≤ w.re) :
    |(1 - (N⁻¹ : ℂ) * cutoff N w).im| ≤ (1 - (N⁻¹ : ℂ) * cutoff N w).re := by
  rw [cutoff_complement_eq N hN w (re_nonneg_of_abs_im_le_re w hw)]
  apply div_sector_of_real_nonneg N hN.le ((N : ℂ) + w)
  obtain ⟨hw_l, hw_r⟩ := abs_le.mp hw
  simp only [Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re, zero_add]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem eighth_strip_subset_sixth (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi * ε / 8) : |q.im| ≤ Real.pi * ε / 6 := by
  nlinarith [Real.pi_pos]

theorem eighth_strip_subset (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi * ε / 8) : q ∈ targetStrip ε :=
  sixth_strip_subset ε hε q (eighth_strip_subset_sixth ε hε q hq)

theorem inverse_im_eighth (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi * ε / 8) : |(complexInverse ε q).im| ≤ Real.pi / 8 :=
  (inverse_im_bound ε hε q (eighth_strip_subset ε hε q hq)).trans
    ((div_le_iff₀ hε).mpr (by nlinarith))

theorem radialComplex_sector (ε : ℝ) (hε : 0 < ε) (h : ℝ) (q : ℂ)
    (hq : |q.im| ≤ Real.pi * ε / 8) (x : Block 2 × Block 4) :
    |(radialComplex ε h q x).im| ≤ (radialComplex ε h q x).re := by
  have hs := exp_quarter_sector (complexInverse ε q) (inverse_im_eighth ε hε q hq)
  exact base_sector ε _ _ hε.le (by positivity) (by positivity) _ hs.1 hs.2

theorem radialComplex_sq_re_nonneg (ε : ℝ) (hε : 0 < ε) (h : ℝ) (q : ℂ)
    (hq : |q.im| ≤ Real.pi * ε / 8) (x : Block 2 × Block 4) :
    0 ≤ ((radialComplex ε h q x) ^ 2).re :=
  re_sq_nonneg_of_abs_im_le_re _ (radialComplex_sector ε hε h q hq x)

theorem multiplier_sector (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (q : ℂ)
    (hq : |q.im| ≤ Real.pi * ε / 8) (x : Block 2 × Block 4) :
    |(multiplier ε h N q x).im| ≤ (multiplier ε h N q x).re :=
  cutoff_sector N hN _ (radialComplex_sector ε hε h q hq x)

theorem multiplier_sq_re_nonneg (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (q : ℂ)
    (hq : |q.im| ≤ Real.pi * ε / 8) (x : Block 2 × Block 4) :
    0 ≤ ((multiplier ε h N q x) ^ 2).re :=
  re_sq_nonneg_of_abs_im_le_re _ (multiplier_sector ε hε h N hN q hq x)

theorem family_sector (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (q : ℂ)
    (hq : |q.im| ≤ Real.pi * ε / 8) (z : TailSpace) :
    |(family ε h N q z).im| ≤ (family ε h N q z).re :=
  multiplier_sector ε hε h N hN q hq _

theorem family_sq_re_nonneg (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (q : ℂ)
    (hq : |q.im| ≤ Real.pi * ε / 8) (z : TailSpace) :
    0 ≤ ((family ε h N q z) ^ 2).re :=
  re_sq_nonneg_of_abs_im_le_re _ (family_sector ε hε h N hN q hq z)

theorem resolvent_multiplier_sector (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (q : ℂ)
    (hq : |q.im| ≤ Real.pi * ε / 8) (x : Block 2 × Block 4) :
    |(1 - (N⁻¹ : ℂ) * multiplier ε h N q x).im| ≤
      (1 - (N⁻¹ : ℂ) * multiplier ε h N q x).re :=
  cutoff_complement_sector N hN _ (radialComplex_sector ε hε h q hq x)

theorem resolvent_multiplier_sq_re_nonneg (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (q : ℂ)
    (hq : |q.im| ≤ Real.pi * ε / 8) (x : Block 2 × Block 4) :
    0 ≤ ((1 - (N⁻¹ : ℂ) * multiplier ε h N q x) ^ 2).re :=
  re_sq_nonneg_of_abs_im_le_re _ (resolvent_multiplier_sector ε hε h N hN q hq x)

theorem symbol_sector (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi * ε / 8) (x : Space) :
    |(KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y x).im| ≤
      (KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y x).re :=
  family_sector ε hε h N hN ((x 0 : ℂ) + (y : ℂ) * Complex.I) (by simpa using hy) _

theorem line_sector (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi * ε / 8) (x : Space) :
    |(line ε h N y x).im| ≤ (line ε h N y x).re := by
  rw [line, family_symbol]
  exact resolvent_multiplier_sector ε hε h N hN ((x 0 : ℂ) + (y : ℂ) * Complex.I)
    (by simpa using hy) _

theorem y_eighth_le_sixth (ε : ℝ) (hε : 0 < ε) (y : ℝ)
    (hy : |y| ≤ Real.pi * ε / 8) : |y| ≤ Real.pi * ε / 6 := by
  nlinarith [Real.pi_pos]

theorem quarter_shift_bound (ε h : ℝ) (hq : |h| ≤ Real.pi * ε / 4) :
    |-h / 2| ≤ Real.pi * ε / 8 := by
  rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem quarter_le_third (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hq : |h| ≤ Real.pi * ε / 4) : |h| ≤ Real.pi * ε / 3 := by
  nlinarith [Real.pi_pos]

theorem sixth_le_quarter (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hs : |h| ≤ Real.pi * ε / 6) : |h| ≤ Real.pi * ε / 4 := by
  nlinarith [Real.pi_pos]

private theorem multiplier_sq_accretive {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (m : X → ℂ) (f g k : Lp ℂ 2 μ) (hm : ∀ x, |((m x).im)| ≤ (m x).re)
    (hg : g =ᵐ[μ] fun x => m x * f x)
    (hk : k =ᵐ[μ] fun x => m x * g x) : 0 ≤ (inner ℂ f k).re := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) f k)
  change (∫ x, (inner ℂ (f x) (k x)).re ∂μ) = (∫ x, inner ℂ (f x) (k x) ∂μ).re at he
  rw [L2.inner_def, ← he]
  apply integral_nonneg_of_ae
  filter_upwards [hg, hk] with x hxg hxk
  rw [hxk, hxg, ← mul_assoc]
  change 0 ≤ (inner ℂ (f x) ((m x * m x) • f x)).re
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  change 0 ≤ ((m x * m x) * ((‖f x‖ : ℝ) : ℂ) ^ 2).re
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (re_mul_self_nonneg_of_abs_im_le_re (m x) (hm x)) (sq_nonneg _)

theorem shifted_sq_accretive (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy6 : |y| ≤ Real.pi * ε / 6) (hy8 : |y| ≤ Real.pi * ε / 8) (f : Hilbert) :
    0 ≤ (inner ℂ f
      (KFCausalClockFloorRadialYosidaOrderedTransport.shifted ε hε h N hN y hy6
        (KFCausalClockFloorRadialYosidaOrderedTransport.shifted ε hε h N hN y hy6 f))).re := by
  let S := KFCausalClockFloorRadialYosidaOrderedTransport.shifted ε hε h N hN y hy6
  have he := multiplier_sq_accretive
    (KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y)
    (straightening ε hε (unitary ε hε f))
    (straightening ε hε (unitary ε hε (S f)))
    (straightening ε hε (unitary ε hε (S (S f))))
    (symbol_sector ε hε h N hN y hy8)
    (KFCausalMixedStripExponentialGraph.action_coe ε hε (family ε h N) (Real.pi * ε / 6) N
      (family_line_continuous ε hε h N hN) hN.le (family_bound ε hε h N hN) y hy6 f)
    (KFCausalMixedStripExponentialGraph.action_coe ε hε (family ε h N) (Real.pi * ε / 6) N
      (family_line_continuous ε hε h N hN) hN.le (family_bound ε hε h N hN) y hy6 (S f))
  simpa only [LinearIsometryEquiv.inner_map_map] using he

theorem resolvent_shifted_accretive (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy6 : |y| ≤ Real.pi * ε / 6) (f : Hilbert) :
    0 ≤ (inner ℂ f
      (KFCausalClockFloorRadialResolventShifted.shifted ε hε h N hN y hy6 f)).re := by
  let S := KFCausalClockFloorRadialResolventShifted.shifted ε hε h N hN y hy6
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) (coordinates ε hε f) (coordinates ε hε (S f)))
  change (∫ x, (inner ℂ ((coordinates ε hε f) x) ((coordinates ε hε (S f)) x)).re) =
    (∫ x, inner ℂ ((coordinates ε hε f) x) ((coordinates ε hε (S f)) x)).re at he
  rw [← (coordinates ε hε).inner_map_map f (S f), L2.inner_def, ← he]
  apply integral_nonneg_of_ae
  filter_upwards [shifted_coe ε hε h N hN y hy6 f] with x hx
  rw [hx]
  change 0 ≤ (inner ℂ ((coordinates ε hε f) x) (line ε h N y x • (coordinates ε hε f) x)).re
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  change 0 ≤ (line ε h N y x * ((‖(coordinates ε hε f) x‖ : ℝ) : ℂ) ^ 2).re
  rw [← Complex.ofReal_pow]
  have hre : 0 ≤ (line ε h N y x).re := by
    rw [line, family_symbol, multiplier, cutoff_complement_eq N hN _
      (KFCausalClockFloorRadialYosidaStrip.radialComplex_re ε hε h _ (by simpa using hy6) _)]
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      zero_mul, zero_div, add_zero]
    exact div_nonneg (mul_nonneg hN.le (add_nonneg hN.le
      (KFCausalClockFloorRadialYosidaStrip.radialComplex_re ε hε h _ (by simpa using hy6) _)))
      (Complex.normSq_nonneg _)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg hre (sq_nonneg _)

theorem resolvent_shifted_sq_accretive (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy6 : |y| ≤ Real.pi * ε / 6) (hy8 : |y| ≤ Real.pi * ε / 8) (f : Hilbert) :
    0 ≤ (inner ℂ f
      (KFCausalClockFloorRadialResolventShifted.shifted ε hε h N hN y hy6
        (KFCausalClockFloorRadialResolventShifted.shifted ε hε h N hN y hy6 f))).re := by
  let S := KFCausalClockFloorRadialResolventShifted.shifted ε hε h N hN y hy6
  have he := multiplier_sq_accretive
    (line ε h N y)
    (coordinates ε hε f)
    (coordinates ε hε (S f))
    (coordinates ε hε (S (S f)))
    (line_sector ε hε h N hN y hy8)
    (shifted_coe ε hε h N hN y hy6 f)
    (shifted_coe ε hε h N hN y hy6 (S f))
  simpa only [LinearIsometryEquiv.inner_map_map] using he

#print axioms re_nonneg_of_abs_im_le_re
#print axioms re_mul_self_nonneg_of_abs_im_le_re
#print axioms re_sq_nonneg_of_abs_im_le_re
#print axioms exp_sector_pi_div_four
#print axioms exp_quarter_sector
#print axioms div_sector_of_real_nonneg
#print axioms base_sector
#print axioms cutoff_sector
#print axioms cutoff_complement_eq
#print axioms cutoff_complement_sector
#print axioms eighth_strip_subset_sixth
#print axioms eighth_strip_subset
#print axioms inverse_im_eighth
#print axioms radialComplex_sector
#print axioms radialComplex_sq_re_nonneg
#print axioms multiplier_sector
#print axioms multiplier_sq_re_nonneg
#print axioms family_sector
#print axioms family_sq_re_nonneg
#print axioms resolvent_multiplier_sector
#print axioms resolvent_multiplier_sq_re_nonneg
#print axioms symbol_sector
#print axioms line_sector
#print axioms y_eighth_le_sixth
#print axioms quarter_shift_bound
#print axioms quarter_le_third
#print axioms sixth_le_quarter
#print axioms shifted_sq_accretive
#print axioms resolvent_shifted_accretive
#print axioms resolvent_shifted_sq_accretive
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaQuarterStripSector
