/- A derived local difference-quotient bound upgrades pointwise derivatives
to strong L2 derivatives in the interior of the interpolation interval.
Clipping extends the curve to real parameters without requiring L2 states
outside the proved interval. -/
import UnifiedTheory.Audit.KFCausalDominatedL2Derivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace UnifiedTheory.Audit.KFCausalIntervalL2Derivative
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def clip (t : ℝ) : Icc (0:ℝ) 1 := projIcc 0 1 zero_le_one t

theorem clip_eq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : (clip t:ℝ) = t := by
  rw [clip,projIcc_of_mem zero_le_one ht]

def curve (F : ℝ → X → ℂ) (hF : ∀ t ∈ Icc (0:ℝ) 1, MemLp (F t) 2 μ) (t : ℝ) : Lp ℂ 2 μ :=
  (hF (clip t) (clip t).property).toLp (F (clip t))

theorem curve_coe (F : ℝ → X → ℂ) (hF : ∀ t ∈ Icc (0:ℝ) 1, MemLp (F t) 2 μ) (t : ℝ) :
    curve F hF t =ᵐ[μ] F (clip t) := (hF (clip t) (clip t).property).coeFn_toLp

theorem curve_value (F : ℝ → X → ℂ) (hF : ∀ t ∈ Icc (0:ℝ) 1, MemLp (F t) 2 μ)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : curve F hF t = (hF t ht).toLp (F t) := by
  apply Lp.ext
  filter_upwards [curve_coe F hF t,(hF t ht).coeFn_toLp] with x hx hy
  rw [hx,hy,clip_eq t ht]

omit [MeasurableSpace X] in
theorem quotient_bound (F G : ℝ → X → ℂ) (B : X → ℂ)
    (hd : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, HasDerivAt (fun u => F u x) (G t x) t)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, ‖G t x‖ ≤ ‖B x‖)
    (a u : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (hu : a+u ∈ Icc (0:ℝ) 1) (hn : u ≠ 0) (x : X) :
    ‖u⁻¹ • (F (a+u) x-F a x)‖ ≤ ‖B x‖ := by
  have hs := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => F t x) (f' := fun t => G t x)
    (fun t ht => (hd t ht x).hasDerivWithinAt) (fun t ht => hb t ht x)
    (convex_Icc (0:ℝ) 1) ha hu
  rw [add_sub_cancel_left,Real.norm_eq_abs] at hs
  rw [norm_smul,Real.norm_eq_abs,abs_inv]
  have hh := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (abs_nonneg u))
  have he : |u|⁻¹*(‖B x‖*|u|) = ‖B x‖ := by
    rw [mul_left_comm,inv_mul_cancel₀ (abs_pos.mpr hn).ne',mul_one]
  exact hh.trans_eq he

theorem strong_derivative (F G : ℝ → X → ℂ)
    (hF : ∀ t ∈ Icc (0:ℝ) 1, MemLp (F t) 2 μ)
    (B : X → ℂ) (hB : MemLp B 2 μ)
    (hd : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, HasDerivAt (fun u => F u x) (G t x) t)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, ‖G t x‖ ≤ ‖B x‖)
    (a : ℝ) (ha : a ∈ Ioo (0:ℝ) 1) (hG : MemLp (G a) 2 μ) :
    HasDerivAt (curve F hF) (hG.toLp (G a)) a := by
  have hac : a ∈ Icc (0:ℝ) 1 := ⟨ha.1.le,ha.2.le⟩
  have he : ∀ᶠ u in 𝓝 (0:ℝ), a+u ∈ Ioo (0:ℝ) 1 := by
    have hc : ContinuousAt (fun u : ℝ => a+u) 0 := continuous_const.add continuous_id |>.continuousAt
    exact hc.preimage_mem_nhds (by simpa using Ioo_mem_nhds ha.1 ha.2)
  have hd0 : HasDerivAt (fun u : ℝ => curve F hF (a+u)) (hG.toLp (G a)) 0 := by
    apply KFCausalDominatedL2Derivative.hasDerivAt_represented
      (fun u => curve F hF (a+u)) (fun u x => F (clip (a+u)) x)
      (fun u => curve_coe F hF (a+u)) (G a) hG (fun x => ‖B x‖)
      ((memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).mp hB)
    · have hn : ∀ᶠ u in 𝓝[≠] (0:ℝ), a+u ∈ Ioo (0:ℝ) 1 := nhdsWithin_le_nhds he
      filter_upwards [hn,self_mem_nhdsWithin] with u hu hne
      have huc : a+u ∈ Icc (0:ℝ) 1 := ⟨hu.1.le,hu.2.le⟩
      filter_upwards [] with x
      rw [clip_eq (a+u) huc,add_zero,clip_eq a hac]
      exact quotient_bound F G B hd hb a u hac huc hne x
    · filter_upwards [] with x
      have hda : HasDerivAt (fun t : ℝ => F t x) (G a x) (a+0) := by simpa using hd a hac x
      have hcomp : HasDerivAt (fun u : ℝ => F (a+u) x) (G a x) 0 := by
        simpa only [Function.comp_def,one_smul] using hda.scomp 0 ((hasDerivAt_id (0:ℝ)).const_add a)
      apply hcomp.congr_of_eventuallyEq
      filter_upwards [he] with u hu
      rw [clip_eq (a+u) ⟨hu.1.le,hu.2.le⟩]
  have hd' : HasDerivAt (fun u : ℝ => curve F hF (a+u)) (hG.toLp (G a)) (a-a) := by
    simpa only [sub_self] using hd0
  have hfunc : (fun u : ℝ => curve F hF (a+(u-a))) = curve F hF := by
    funext u
    congr 1
    ring
  simpa only [Function.comp_def,one_smul,hfunc] using
    hd'.scomp (h := fun u : ℝ => u-a) a ((hasDerivAt_id a).sub_const a)

#print axioms clip_eq
#print axioms curve_coe
#print axioms curve_value
#print axioms quotient_bound
#print axioms strong_derivative
end
end UnifiedTheory.Audit.KFCausalIntervalL2Derivative
