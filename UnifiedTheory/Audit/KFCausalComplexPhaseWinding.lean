/- The current source-clock phase winds through pi arbitrarily close to
the real straightened clock axis, inside the established analytic strip.
This is a coefficient calculation, not a spectral-domain no-go theorem. -/
import UnifiedTheory.Audit.KFCausalComplexClockWeights
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalComplexPhaseWinding
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalComplexClockWeights

def radius (ε θ : ℝ) : ℝ := ε * Real.sin θ / (Real.pi - θ)
def sourcePoint (ε θ : ℝ) : ℂ := (Real.log (radius ε θ) : ℂ) + (θ : ℂ) * Complex.I
def clockPoint (ε θ : ℝ) : ℂ := complexChart ε (sourcePoint ε θ)

theorem radius_pos (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ) (hπ : θ ≤ Real.pi/4) :
    0 < radius ε θ := by
  have ht : θ < Real.pi := by linarith [Real.pi_pos]
  exact div_pos (mul_pos hε (Real.sin_pos_of_pos_of_lt_pi hθ ht)) (sub_pos.mpr ht)

theorem sourcePoint_re (ε θ : ℝ) : (sourcePoint ε θ).re = Real.log (radius ε θ) := by
  simp [sourcePoint]

theorem sourcePoint_im (ε θ : ℝ) : (sourcePoint ε θ).im = θ := by
  simp [sourcePoint]

theorem sourcePoint_mem (ε θ : ℝ) (hθ : 0 < θ) (hπ : θ ≤ Real.pi/4) :
    sourcePoint ε θ ∈ openStrip := by
  change |(sourcePoint ε θ).im| < Real.pi/2
  rw [sourcePoint_im, abs_of_pos hθ]
  linarith [Real.pi_pos]

theorem complexPhase_im (ε : ℝ) (z : ℂ) :
    (complexPhase ε z).im = z.im + ε * Real.exp (-z.re) * Real.sin z.im := by
  simp [complexPhase, Complex.exp_im, Real.sin_neg]
  ring

theorem sourcePoint_phase_im (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ)
    (hπ : θ ≤ Real.pi/4) : (complexPhase ε (sourcePoint ε θ)).im = Real.pi := by
  rw [complexPhase_im, sourcePoint_re, sourcePoint_im, Real.exp_neg,
    Real.exp_log (radius_pos ε θ hε hθ hπ)]
  have hs := (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos] : θ < Real.pi)).ne'
  dsimp [radius]
  field_simp
  ring

theorem clockPoint_im (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ)
    (hπ : θ ≤ Real.pi/4) :
    (clockPoint ε θ).im = ε * Real.sin θ ^ 2 / (Real.pi - θ) + ε * θ := by
  rw [clockPoint, complexChart_im, sourcePoint_re, sourcePoint_im,
    Real.exp_log (radius_pos ε θ hε hθ hπ)]
  dsimp [radius]
  ring

theorem clockPoint_im_bounds (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ)
    (hπ : θ ≤ Real.pi/4) :
    0 < (clockPoint ε θ).im ∧ (clockPoint ε θ).im ≤ 2 * ε * θ := by
  rw [clockPoint_im ε θ hε hθ hπ]
  have hd : 0 < Real.pi - θ := by linarith [Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos] : θ < Real.pi)
  have hsq : Real.sin θ ^ 2 ≤ θ ^ 2 :=
    (sq_le_sq₀ hs.le hθ.le).mpr (Real.sin_le hθ.le)
  have hb : Real.sin θ ^ 2 / (Real.pi - θ) ≤ θ := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  constructor
  · positivity
  · have hm := mul_le_mul_of_nonneg_left hb hε.le
    rw [← mul_div_assoc] at hm
    nlinarith

theorem clockPoint_mem (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ)
    (hπ : θ ≤ Real.pi/4) : clockPoint ε θ ∈ targetStrip ε := by
  obtain ⟨hp, hb⟩ := clockPoint_im_bounds ε θ hε hθ hπ
  change |(clockPoint ε θ).im| ≤ Real.pi*ε/2
  rw [abs_of_pos hp]
  nlinarith

theorem fieldCoefficient_chart (ε : ℝ) (hε : 0 < ε) (z : ℂ) (hz : z ∈ closedStrip) :
    fieldCoefficient ε 2 (complexChart ε z) = Complex.exp (complexPhase ε z) := by
  rw [fieldCoefficient, complexInverse_left ε hε z hz]
  norm_num

theorem clockPoint_coefficient_re (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ)
    (hπ : θ ≤ Real.pi/4) :
    (fieldCoefficient ε 2 (clockPoint ε θ)).re =
      -Real.exp (complexPhase ε (sourcePoint ε θ)).re := by
  rw [clockPoint, fieldCoefficient_chart ε hε _ (show |(sourcePoint ε θ).im| ≤ Real.pi/2 from le_of_lt (sourcePoint_mem ε θ hθ hπ)),
    Complex.exp_re, sourcePoint_phase_im ε θ hε hθ hπ, Real.cos_pi]
  ring

theorem exists_negative_coefficient_above (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ q : ℂ, q ∈ targetStrip ε ∧ 0 < q.im ∧ q.im < δ ∧
      (fieldCoefficient ε 2 q).re < 0 := by
  let θ := min (δ/(4*ε)) (Real.pi/4)
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  have hπ : θ ≤ Real.pi/4 := min_le_right _ _
  have hδθ : θ ≤ δ/(4*ε) := min_le_left _ _
  have hbδ := (le_div_iff₀ (by positivity : 0 < 4*ε)).mp hδθ
  obtain ⟨hp,hb⟩ := clockPoint_im_bounds ε θ hε hθ hπ
  refine ⟨clockPoint ε θ, clockPoint_mem ε θ hε hθ hπ, hp, by nlinarith, ?_⟩
  rw [clockPoint_coefficient_re ε θ hε hθ hπ]
  exact neg_neg_of_pos (Real.exp_pos _)

theorem complexChart_conj (ε : ℝ) (z : ℂ) :
    complexChart ε ((starRingEnd ℂ) z) = (starRingEnd ℂ) (complexChart ε z) := by
  simp [complexChart, Complex.exp_conj]

theorem complexPhase_conj (ε : ℝ) (z : ℂ) :
    complexPhase ε ((starRingEnd ℂ) z) = (starRingEnd ℂ) (complexPhase ε z) := by
  simp only [complexPhase, map_sub, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg]

theorem fieldCoefficient_conj (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    fieldCoefficient ε 2 ((starRingEnd ℂ) q) = (starRingEnd ℂ) (fieldCoefficient ε 2 q) := by
  let z := complexInverse ε q
  have hz : z ∈ closedStrip := (show |z.im| ≤ Real.pi/2 from le_of_lt (complexInverse_mem ε hε q hq))
  have hzc : (starRingEnd ℂ) z ∈ closedStrip := by
    change |((starRingEnd ℂ) z : ℂ).im| ≤ Real.pi/2
    simpa only [Complex.conj_im, abs_neg] using hz
  have he : complexChart ε z = q := complexInverse_right ε hε q hq
  rw [← he, ← complexChart_conj, fieldCoefficient_chart ε hε _ hzc,
    fieldCoefficient_chart ε hε _ hz, complexPhase_conj]
  exact Complex.exp_conj _

theorem exists_negative_coefficient_below (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ q : ℂ, q ∈ targetStrip ε ∧ -δ < q.im ∧ q.im < 0 ∧
      (fieldCoefficient ε 2 q).re < 0 := by
  obtain ⟨q,hq,hp,hb,hn⟩ := exists_negative_coefficient_above ε δ hε hδ
  refine ⟨(starRingEnd ℂ) q, ?_, ?_, ?_, ?_⟩
  · change |((starRingEnd ℂ) q : ℂ).im| ≤ Real.pi*ε/2
    simpa only [Complex.conj_im, abs_neg] using (show |q.im| ≤ Real.pi*ε/2 from hq)
  · simpa only [Complex.conj_im, neg_lt_neg_iff] using hb
  · simpa only [Complex.conj_im, neg_lt_zero] using hp
  · rw [fieldCoefficient_conj ε hε q hq, Complex.conj_re]
    exact hn

#print axioms radius_pos
#print axioms sourcePoint_re
#print axioms sourcePoint_im
#print axioms sourcePoint_mem
#print axioms complexPhase_im
#print axioms sourcePoint_phase_im
#print axioms clockPoint_im
#print axioms clockPoint_im_bounds
#print axioms clockPoint_mem
#print axioms fieldCoefficient_chart
#print axioms clockPoint_coefficient_re
#print axioms exists_negative_coefficient_above
#print axioms complexChart_conj
#print axioms complexPhase_conj
#print axioms fieldCoefficient_conj
#print axioms exists_negative_coefficient_below

end
end UnifiedTheory.Audit.KFCausalComplexPhaseWinding
