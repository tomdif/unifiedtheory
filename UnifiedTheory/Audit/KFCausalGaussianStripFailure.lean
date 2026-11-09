/- Fubini upgrades the bad Gaussian slices to failure of joint clock-
gravity L2 integrability on horizontal lines arbitrarily close to the
real axis. No assertion about the full spectral energy domain follows
without a separate analytic-continuation necessity theorem. -/
import UnifiedTheory.Audit.KFCausalGaussianSliceDomain
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalGaussianStripFailure
noncomputable section
open MeasureTheory Set Filter
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockWeights
open UnifiedTheory.Audit.KFCausalComplexPhaseWinding
open UnifiedTheory.Audit.KFCausalGaussianSliceDomain

theorem gaussian_family_nonnegative (b c : ℝ → ℂ) (hb : Continuous b)
    (hc : ∀ q, c q ≠ 0)
    (hm : MemLp (fun z : ℝ × ℝ => c z.1 * gaussian (b z.1) z.2) 2 volume) :
    ∀ q, 0 ≤ (b q).re := by
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).mp hm
  rw [Measure.volume_eq_prod ℝ ℝ] at hi
  have hp : ∀ᵐ q : ℝ, 0 ≤ (b q).re := by
    filter_upwards [hi.prod_right_ae] with q hq
    have hs : MemLp (fun x : ℝ => c q * gaussian (b q) x) 2 volume :=
      (memLp_two_iff_integrable_sq_norm
        (continuous_const.mul (gaussian_continuous (b q))).aestronglyMeasurable).mpr hq
    exact ((scalar_gaussian_memLp_iff (c q) (b q) (hc q)).mp hs).le
  intro q
  have hq := (Measure.dense_of_ae hp) q
  have hclosed : IsClosed {x : ℝ | 0 ≤ (b x).re} :=
    isClosed_le continuous_const (Complex.continuous_re.comp hb)
  rwa [hclosed.closure_eq] at hq

theorem gaussian_family_not_memLp (b c : ℝ → ℂ) (hb : Continuous b)
    (hc : ∀ q, c q ≠ 0) (q : ℝ) (hq : (b q).re < 0) :
    ¬ MemLp (fun z : ℝ × ℝ => c z.1 * gaussian (b z.1) z.2) 2 volume := by
  intro hm
  exact (not_lt.mpr (gaussian_family_nonnegative b c hb hc hm q)) hq

theorem gaussian_spectator_family_not_memLp {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] [NeZero μ] (b : ℝ → ℂ) (hb : Continuous b)
    (q : ℝ) (hq : (b q).re < 0) (c : ℝ → S → ℂ) (hc : ∀ x s, c x s ≠ 0) :
    ¬ MemLp (fun z : (ℝ × ℝ) × S => c z.1.1 z.2 * gaussian (b z.1.1) z.1.2)
      2 ((volume : Measure (ℝ × ℝ)).prod μ) := by
  intro hm
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).mp hm
  have ha : ∀ᵐ s ∂μ, False := by
    filter_upwards [hi.prod_left_ae, hm.1.prodMk_right] with s hs hsm
    exact gaussian_family_not_memLp b (fun x => c x s) hb (fun x => hc x s) q hq
      ((memLp_two_iff_integrable_sq_norm hsm).mpr hs)
  obtain ⟨s,hs⟩ := ha.exists
  exact hs

theorem coefficient_line_continuous (ε α y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/2) :
    Continuous (fun q : ℝ => (α:ℂ)*fieldCoefficient ε 2 ((q:ℂ)+(y:ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hz : (q:ℂ)+(y:ℂ)*Complex.I ∈ targetStrip ε := by
    change |((q:ℂ)+(y:ℂ)*Complex.I).im| ≤ Real.pi*ε/2
    simpa using hy
  have he : ContinuousAt (fun x : ℝ => fieldCoefficient ε 2 ((x:ℂ)+(y:ℂ)*Complex.I)) q :=
    (fieldCoefficient_analytic ε 2 hε _ hz).continuousAt.comp
      (f := fun x : ℝ => (x:ℂ)+(y:ℂ)*Complex.I) (by fun_prop)
  exact continuousAt_const.mul he

def horizontalFamily (ε α y : ℝ) (c : ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  c z.1 * dilationGaussian ε α ((z.1:ℂ)+(y:ℂ)*Complex.I) z.2

theorem horizontalFamily_not_memLp (ε α : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (q : ℂ) (hq : q ∈ targetStrip ε) (hn : (fieldCoefficient ε 2 q).re < 0)
    (c : ℝ → ℂ) (hc : ∀ x, c x ≠ 0) :
    ¬ MemLp (horizontalFamily ε α q.im c) 2 volume := by
  apply gaussian_family_not_memLp _ c
    (coefficient_line_continuous ε α q.im hε hq) hc q.re
  rw [Complex.re_add_im]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg hα hn

theorem horizontal_spectator_family_not_memLp {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] [NeZero μ] (ε α : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (q : ℂ) (hq : q ∈ targetStrip ε) (hn : (fieldCoefficient ε 2 q).re < 0)
    (c : ℝ → S → ℂ) (hc : ∀ x s, c x s ≠ 0) :
    ¬ MemLp (fun z : (ℝ × ℝ) × S => c z.1.1 z.2 *
      dilationGaussian ε α ((z.1.1:ℂ)+(q.im:ℂ)*Complex.I) z.1.2)
      2 ((volume : Measure (ℝ × ℝ)).prod μ) := by
  apply gaussian_spectator_family_not_memLp μ _
    (coefficient_line_continuous ε α q.im hε hq) q.re _ c hc
  rw [Complex.re_add_im]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg hα hn

theorem exists_nonL2_horizontal_above (ε α δ : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (hδ : 0 < δ) :
    ∃ y : ℝ, 0 < y ∧ y < δ ∧ |y| ≤ Real.pi*ε/2 ∧
      ∀ c : ℝ → ℂ, (∀ x, c x ≠ 0) → ¬ MemLp (horizontalFamily ε α y c) 2 volume := by
  obtain ⟨q,hq,hp,hb,hn⟩ := exists_negative_coefficient_above ε δ hε hδ
  exact ⟨q.im,hp,hb,hq,fun c hc => horizontalFamily_not_memLp ε α hε hα q hq hn c hc⟩

theorem exists_nonL2_horizontal_below (ε α δ : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (hδ : 0 < δ) :
    ∃ y : ℝ, -δ < y ∧ y < 0 ∧ |y| ≤ Real.pi*ε/2 ∧
      ∀ c : ℝ → ℂ, (∀ x, c x ≠ 0) → ¬ MemLp (horizontalFamily ε α y c) 2 volume := by
  obtain ⟨q,hq,hb,hn,hr⟩ := exists_negative_coefficient_below ε δ hε hδ
  exact ⟨q.im,hb,hn,hq,fun c hc => horizontalFamily_not_memLp ε α hε hα q hq hr c hc⟩

#print axioms gaussian_family_nonnegative
#print axioms gaussian_family_not_memLp
#print axioms gaussian_spectator_family_not_memLp
#print axioms coefficient_line_continuous
#print axioms horizontalFamily_not_memLp
#print axioms horizontal_spectator_family_not_memLp
#print axioms exists_nonL2_horizontal_above
#print axioms exists_nonL2_horizontal_below

end
end UnifiedTheory.Audit.KFCausalGaussianStripFailure
