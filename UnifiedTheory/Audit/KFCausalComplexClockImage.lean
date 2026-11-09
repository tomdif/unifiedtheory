/- Closedness of the clock-chart image and exclusion of the vertical
strip boundary above the required horizontal strip. No uniform continuity
of the exponential on an unbounded strip is assumed. -/
import UnifiedTheory.Audit.KFCausalComplexClockCoercivity
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalComplexClockImage
noncomputable section
open Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockCoercivity

theorem complexChart_closed_image (ε : ℝ) (hε : 0 < ε) :
    IsClosed (complexChart ε '' closedStrip) := by
  apply IsSeqClosed.isClosed
  intro u q hu hq
  choose z hz he using hu
  have hc : CauchySeq z := by
    apply Metric.cauchySeq_iff.mpr
    intro δ hδ
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hq.cauchySeq (ε*δ) (mul_pos hε hδ)
    refine ⟨N,fun m hm n hn => ?_⟩
    have hb := complexChart_norm_lower ε (z n) (z m) (hz n) (hz m)
    rw [he m,he n] at hb
    have hu' := hN m hm n hn
    rw [dist_eq_norm] at hu' ⊢
    exact (mul_lt_mul_iff_right₀ hε).mp (by nlinarith [hb.trans_lt hu'])
  obtain ⟨w,hw⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨w,closedStrip_closed.mem_of_tendsto hw (Eventually.of_forall hz),?_⟩
  apply tendsto_nhds_unique ((complexChart_continuous ε).tendsto w |>.comp hw)
  simpa only [Function.comp_def,he] using hq

theorem target_preimage_interior (ε : ℝ) (z : ℂ)
    (hz : z ∈ closedStrip) (hq : complexChart ε z ∈ targetStrip ε) : z ∈ openStrip := by
  change |z.im| ≤ Real.pi/2 at hz
  change |(complexChart ε z).im| ≤ Real.pi*ε/2 at hq
  change |z.im| < Real.pi/2
  apply lt_of_le_of_ne hz
  intro he
  have hb := abs_le.mp hq
  by_cases hp : 0 ≤ z.im
  · rw [abs_of_nonneg hp] at he
    rw [complexChart_im,he,Real.sin_pi_div_two,mul_one] at hb
    nlinarith [Real.exp_pos z.re]
  · have hn : z.im= -(Real.pi/2) := by rw [abs_of_neg (lt_of_not_ge hp)] at he; linarith
    rw [complexChart_im,hn,Real.sin_neg,Real.sin_pi_div_two] at hb
    nlinarith [Real.exp_pos z.re]

theorem complexChart_open_image (ε : ℝ) (hε : 0 < ε) :
    IsOpen (complexChart ε '' openStrip) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro q ⟨z,hz,rfl⟩
  have hc : z ∈ closedStrip := (show |z.im| < Real.pi/2 from hz).le
  have hd : deriv (complexChart ε) z ≠ 0 := by
    rw [(complexChart_derivative ε z).deriv]
    exact complexChart_derivative_ne_zero ε hε z hc
  rw [← (complexChart_analytic ε z).hasStrictDerivAt.map_nhds_eq hd]
  exact image_mem_map (openStrip_open.mem_nhds hz)

theorem targetStrip_convex (ε : ℝ) : Convex ℝ (targetStrip ε) := by
  intro x hx y hy a b ha hb hab
  change |x.im| ≤ Real.pi*ε/2 at hx
  change |y.im| ≤ Real.pi*ε/2 at hy
  change |(a • x+b • y).im| ≤ Real.pi*ε/2
  simp only [Complex.add_im,Complex.smul_im,smul_eq_mul]
  obtain ⟨hx₁,hx₂⟩ := abs_le.mp hx
  obtain ⟨hy₁,hy₂⟩ := abs_le.mp hy
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg ha (sub_nonneg.mpr hx₁),
    mul_nonneg ha (sub_nonneg.mpr hx₂),mul_nonneg hb (sub_nonneg.mpr hy₁),
    mul_nonneg hb (sub_nonneg.mpr hy₂)]

theorem complexChart_surjOn_strip (ε : ℝ) (hε : 0 < ε) :
    targetStrip ε ⊆ complexChart ε '' openStrip := by
  letI : PreconnectedSpace (targetStrip ε) :=
    Subtype.preconnectedSpace (targetStrip_convex ε).isPreconnected
  let s : Set (targetStrip ε) := Subtype.val ⁻¹' (complexChart ε '' closedStrip)
  have he : s = Subtype.val ⁻¹' (complexChart ε '' openStrip) := by
    ext q
    constructor
    · rintro ⟨z,hz,hzq⟩
      exact ⟨z,target_preimage_interior ε z hz (hzq.symm ▸ q.property),hzq⟩
    · rintro ⟨z,hz,hzq⟩
      exact ⟨z,(show |z.im| < Real.pi/2 from hz).le,hzq⟩
  have hs : IsClopen s := ⟨(complexChart_closed_image ε hε).preimage continuous_subtype_val,
    he ▸ (complexChart_open_image ε hε).preimage continuous_subtype_val⟩
  have hq : (1:ℂ) ∈ targetStrip ε := by
    change |(1:ℂ).im| ≤ Real.pi*ε/2
    simp only [Complex.one_im,abs_zero]
    positivity
  have hn : s.Nonempty := ⟨⟨1,hq⟩,0,by change |(0:ℂ).im| ≤ Real.pi/2; simp; positivity,
    by simp [complexChart]⟩
  intro q hq'
  have hm : (⟨q,hq'⟩ : targetStrip ε) ∈ s := by rw [hs.eq_univ hn]; trivial
  rw [he] at hm
  exact hm

#print axioms complexChart_closed_image
#print axioms target_preimage_interior
#print axioms complexChart_open_image
#print axioms targetStrip_convex
#print axioms complexChart_surjOn_strip

end
end UnifiedTheory.Audit.KFCausalComplexClockImage
