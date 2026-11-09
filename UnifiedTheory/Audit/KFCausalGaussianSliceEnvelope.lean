/- Uniform-in-clock transverse L2 bounds for the actual relative Gaussian
and its physical field powers zero, one and two. Source and width constants
are explicit. This is not a bound uniform over all quantum states. -/
import UnifiedTheory.Audit.KFCausalGaussianKernelResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalGaussianSliceEnvelope
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse flow_initial)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (relative relative_bound scale scale_smooth)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
  (Grouped packet quadratic quadratic_re_nonnegative)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
  (coherentPacket coherentPacket_bound sourceConstant)
open UnifiedTheory.Audit.KFCausalClockFloorShearIntegrals
  (packet_memLp packet_square_integral_bound transverseConstant transverseConstant_nonnegative)
open UnifiedTheory.Audit.KFCausalClockFloorFieldBounds (momentBound momentBound_positive)
open UnifiedTheory.Audit.KFCausalClockFloorFieldMoments (field_packet_bound packet_half_norm)
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
  (transverseGrouping transverseGrouping_apply transverseGrouping_preserves_volume)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile profile_smooth)
open UnifiedTheory.Audit.KFCausalGaussianKernelResponse (transverse)

def slice (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ) (l : Transverse →L[ℝ] ℝ)
    (n : Fin 3) (s : ℝ) (q : Transverse) : ℂ :=
  (l q:ℂ)^n.val*transverse ε y α β b C q s

def factor (α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ) (l : Transverse →L[ℝ] ℝ) : ℝ :=
  ‖C‖*Real.exp (sourceConstant α β b/2)*(1+2*‖l‖^2*momentBound (α/2) (β/2))

def squareConstant (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (l : Transverse →L[ℝ] ℝ) : ℝ :=
  (factor α β b C l)^2*transverseConstant (α/4) (β/4)*Real.exp (2*|y|/ε)

theorem relative_strip (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    |(relative ε y s).im| ≤ Real.pi/3 := by
  exact ((Complex.abs_im_le_norm _).trans (relative_bound ε y s hε hy)).trans
    ((div_le_iff₀ hε).mpr (by nlinarith))

theorem relative_real_lower (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    -(|y|/ε) ≤ (relative ε y s).re :=
  (abs_le.mp ((Complex.abs_re_le_norm _).trans (relative_bound ε y s hε hy))).1

theorem factor_nonnegative (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (b : Fin 5 → ℂ) (C : ℂ) (l : Transverse →L[ℝ] ℝ) : 0 ≤ factor α β b C l := by
  have hm := momentBound_positive (α/2) (β/2) (by positivity) (by positivity)
  unfold factor
  positivity

theorem squareConstant_nonnegative (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (l : Transverse →L[ℝ] ℝ) : 0 ≤ squareConstant ε y α β b C l := by
  have hm := transverseConstant_nonnegative (α/4) (β/4)
  unfold squareConstant
  positivity

theorem transverse_packet (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ) (q : Transverse) (s : ℝ) :
    transverse ε y α β b C q s =
      C*coherentPacket α β b (relative ε y s) (transverseGrouping q) := by
  have hg : KFCausalClockFloorDisplacedShiftPhase.grouped q = transverseGrouping q := by
    rw [transverseGrouping_apply]
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  have he := KFCausalShiftedGaussianPhysicalProfile.recentered_packet α β b (relative ε y s) 0 q
  simp only [neg_zero,flow_initial,hg,Complex.ofReal_zero,sub_zero] at he
  simp only [transverse,profile,one_mul,scale]
  rw [he]

theorem slice_continuous (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (s : ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (slice ε y α β b C l n s) := by
  have ht : Continuous (fun q => transverse ε y α β b C q s) :=
    continuous_const.mul ((profile_smooth (fun _ => 1) (scale ε y) contDiff_const
      (scale_smooth ε y hε hy) α β b).continuous.comp (continuous_const.prodMk continuous_id))
  exact ((Complex.continuous_ofReal.comp l.continuous).pow n.val).mul ht

private theorem packet_half_le (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (z : ℂ) (hz : |z.im| ≤ Real.pi/3) (x : Grouped) :
    ‖packet (α/2) (β/2) z x‖ ≤ ‖packet (α/4) (β/4) z x‖ := by
  have hh := packet_half_norm (α/2) (β/2) z x
  rw [show α/2/2=α/4 by ring,show β/2/2=β/4 by ring] at hh
  rw [hh,packet,Complex.norm_exp,Complex.neg_re]
  apply Real.exp_le_exp.mpr
  have hn := quadratic_re_nonnegative (α/2) (β/2) (by positivity) (by positivity)
    (by linarith) z hz x.1 x.2
  linarith

theorem slice_bound (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (s : ℝ) (q : Transverse)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) :
    ‖slice ε y α β b C l n s q‖ ≤ factor α β b C l*
      ‖packet (α/4) (β/4) (relative ε y s) (transverseGrouping q)‖ := by
  have hz := relative_strip ε y s hε hy
  have he : Real.exp 0 ≤ Real.exp (Real.pi/3)*Real.exp (relative ε y s).re := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hr := relative_real_lower ε y s hε hy
    have hd : |y|/ε ≤ Real.pi/3 := (div_le_iff₀ hε).mpr (by nlinarith)
    linarith
  have hcoord : ![(transverseGrouping q).1 0,(transverseGrouping q).1 1,
      (transverseGrouping q).1 2,(transverseGrouping q).1 3,(transverseGrouping q).2] = q := by
    rw [transverseGrouping_apply]
    funext i
    fin_cases i <;> rfl
  have hf := field_packet_bound (α/2) (β/2) (by positivity) (by positivity)
    (by linarith) 0 (relative ε y s) hz he (transverseGrouping q) l
  rw [flow_initial,hcoord] at hf
  rw [show α/2/2=α/4 by ring,show β/2/2=β/4 by ring] at hf
  have hh := packet_half_le α β hα hβ hw (relative ε y s) hz (transverseGrouping q)
  have hp := coherentPacket_bound α β hα hβ hw b (relative ε y s) hz (transverseGrouping q)
  have hn : ‖(l q:ℂ)‖^n.val ≤ 1+‖(l q:ℂ)‖^2 := by
    have hnorm := norm_nonneg (l q:ℂ)
    fin_cases n <;> simp only [pow_zero,pow_one]
    all_goals nlinarith [sq_nonneg (‖(l q:ℂ)‖-1)]
  rw [slice,transverse_packet,norm_mul,norm_pow,norm_mul]
  calc
    _ ≤ (1+‖(l q:ℂ)‖^2)*(‖C‖*(Real.exp (sourceConstant α β b/2)*
      ‖packet (α/2) (β/2) (relative ε y s) (transverseGrouping q)‖)) :=
        mul_le_mul hn (mul_le_mul_of_nonneg_left hp (norm_nonneg C)) (by positivity) (by positivity)
    _ = ‖C‖*Real.exp (sourceConstant α β b/2)*
      (‖packet (α/2) (β/2) (relative ε y s) (transverseGrouping q)‖+
       ‖(l q:ℂ)^2*packet (α/2) (β/2) (relative ε y s) (transverseGrouping q)‖) := by
        simp only [norm_mul,norm_pow]
        ring
    _ ≤ ‖C‖*Real.exp (sourceConstant α β b/2)*
      (‖packet (α/4) (β/4) (relative ε y s) (transverseGrouping q)‖+
       (2*‖l‖^2*momentBound (α/2) (β/2))*
         ‖packet (α/4) (β/4) (relative ε y s) (transverseGrouping q)‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hh hf) (by positivity)
    _ = _ := by unfold factor; ring

private theorem packet_slice_memLp (ε y α β s : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) :
    MemLp (fun q => packet (α/4) (β/4) (relative ε y s) (transverseGrouping q)) 2 volume :=
  (packet_memLp (α/4) (β/4) (by positivity) (by positivity) (by linarith)
    (relative ε y s) (relative_strip ε y s hε hy)).comp_measurePreserving
      transverseGrouping_preserves_volume

theorem slice_memLp (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (s : ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) :
    MemLp (slice ε y α β b C l n s) 2 volume := by
  apply ((packet_slice_memLp ε y α β s hε hy hα hβ hw).const_mul
    (factor α β b C l:ℂ)).of_le (slice_continuous ε y α β b C l n s hε hy).aestronglyMeasurable
  filter_upwards [] with q
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (factor_nonnegative α β hα hβ b C l)] using
      slice_bound ε y α β b C l n s q hε hy hα hβ hw

theorem slice_square_bound (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (s : ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) :
    (∫ q, ‖slice ε y α β b C l n s q‖^2) ≤ squareConstant ε y α β b C l := by
  have hm := slice_memLp ε y α β b C l n s hε hy hα hβ hw
  have hp := packet_slice_memLp ε y α β s hε hy hα hβ hw
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).mp hm
  have hj := (memLp_two_iff_integrable_sq_norm hp.1).mp hp
  have he : Real.exp (-2*(relative ε y s).re) ≤ Real.exp (2*|y|/ε) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ 2*(|y|/ε) := by linarith [relative_real_lower ε y s hε hy]
      _ = _ := by ring
  calc
    _ ≤ ∫ q, (factor α β b C l)^2*
      ‖packet (α/4) (β/4) (relative ε y s) (transverseGrouping q)‖^2 :=
      integral_mono hi (hj.const_mul _) (fun q => by
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
          (slice_bound ε y α β b C l n s q hε hy hα hβ hw) 2)
    _ = (factor α β b C l)^2*(∫ x : Grouped, ‖packet (α/4) (β/4) (relative ε y s) x‖^2) := by
      rw [integral_const_mul]
      exact congrArg (fun t : ℝ => (factor α β b C l)^2*t)
        (transverseGrouping_preserves_volume.integral_comp'
          (fun x : Grouped => ‖packet (α/4) (β/4) (relative ε y s) x‖^2))
    _ ≤ (factor α β b C l)^2*(transverseConstant (α/4) (β/4)*Real.exp (-2*(relative ε y s).re)) :=
      mul_le_mul_of_nonneg_left (packet_square_integral_bound (α/4) (β/4)
        (by positivity) (by positivity) (by linarith) (relative ε y s)
        (relative_strip ε y s hε hy)) (sq_nonneg _)
    _ ≤ (factor α β b C l)^2*(transverseConstant (α/4) (β/4)*Real.exp (2*|y|/ε)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he
        (transverseConstant_nonnegative _ _)) (sq_nonneg _)
    _ = _ := by unfold squareConstant; ring

#print axioms relative_strip
#print axioms relative_real_lower
#print axioms factor_nonnegative
#print axioms squareConstant_nonnegative
#print axioms transverse_packet
#print axioms slice_continuous
#print axioms slice_bound
#print axioms slice_memLp
#print axioms slice_square_bound
end
end UnifiedTheory.Audit.KFCausalGaussianSliceEnvelope
