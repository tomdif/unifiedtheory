/- An explicit periodic gauge transformation distributes a seam holonomy
among all links in its direction. This construction concerns flat slices. -/
import UnifiedTheory.Clay.YangMills.WilsonCenterContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonDistributedSeam
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonWindingLoop WilsonCenterTwist

variable (n : ℕ)

def uniform (i : Fin 3) (q : Q) : Slice n := fun e => if e.2 = i then q else 1

def distributingGauge (i : Fin 3) (q : Q) : SliceGauge n Q := fun x => q^((-x i).val)

theorem uniform_inv (i : Fin 3) (q : Q) : (uniform n i q)⁻¹ = uniform n i q⁻¹ := by
  funext e
  simp only [uniform, Pi.inv_apply]
  split_ifs <;> simp

theorem uniform_mul (i : Fin 3) (q r : Q) : uniform n i q * uniform n i r = uniform n i (q*r) := by
  funext e
  simp only [uniform, Pi.mul_apply]
  split_ifs <;> simp

theorem uniform_flat (i : Fin 3) (q : Q) (x : SpatialVertex n) (j k : Fin 3) :
    spatialHolonomy (uniform n i q) x j k = 1 := by
  simp only [spatialHolonomy, uniform]
  split_ifs <;> group

variable [NeZero n]

theorem val_neg_one : (-1 : ZMod n).val = n-1 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  subst n
  simp [ZMod.val_neg_one]

theorem val_neg_step (a : ZMod n) (ha : a ≠ 0) : (-(a+1)).val = (-a).val-1 := by
  have hp : 0 < (-a).val := ZMod.val_pos.mpr (neg_ne_zero.mpr ha)
  have hn : 1 < n := lt_of_le_of_lt hp (ZMod.val_lt (-a))
  have ho : (1 : ZMod n).val = 1 := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt hn)
  rw [show -(a+1) = -a-1 by ring, ZMod.val_sub (by omega), ho]

/-- The gauge is periodic, including both the seam and the period-one case. -/
theorem seam_gauge_uniform (i : Fin 3) (q : Q) :
    gaugeSlice (distributingGauge n i q) (seam n i (q^n)) = uniform n i q := by
  funext e
  rcases e with ⟨x,j⟩
  by_cases hji : j = i
  · subst j
    change q^((-x i).val) * (if i = i ∧ x i = 0 then q^n else 1) *
      (q^((-(spatialStep n x i) i).val))⁻¹ = (if i = i then q else 1)
    simp only [spatialStep, Pi.add_apply, Pi.single_eq_same, if_true, true_and]
    by_cases hx : x i = 0
    · rw [hx]
      simp only [neg_zero, ZMod.val_zero, pow_zero, ite_true, one_mul, zero_add,
        val_neg_one]
      have hn : n = (n-1)+1 := by have hp := NeZero.pos n; omega
      have he : q^n = q * q^(n-1) := by
        calc
          _ = q^((n-1)+1) := congrArg (fun k : ℕ => q^k) hn
          _ = _ := pow_succ' q (n-1)
      rw [he]
      group
    · rw [if_neg hx, val_neg_step n (x i) hx, mul_one]
      have hp : 0 < (-x i).val := ZMod.val_pos.mpr (neg_ne_zero.mpr hx)
      have he : (-x i).val = ((-x i).val-1)+1 := by omega
      conv_lhs => lhs; rw [he, pow_succ']
      group
  · have hs : (spatialStep n x j) i = x i := by simp [spatialStep, hji]
    simp [gaugeSlice, distributingGauge, seam, uniform, hji, hs]

theorem uniform_potential (i : Fin 3) (q : Q) :
    potential WilsonSingleLinkStaples.character 2 (uniform n i q) = 0 := by
  simp [potential, uniform_flat, WilsonSingleLinkStaples.character_re]

/-- Integer-holonomy roots are actual gauge transforms of the identity. -/
theorem kernel_uniform_one (i : Fin 3) (q : Q) (hq : q ^ n = 1) (β : ℝ) (v : Slice n) :
    kernelMap n β (uniform n i q, v) = kernelMap n β (1,v) := by
  rw [← seam_gauge_uniform]
  have hs : seam n i (q^n) = 1 := by funext e; simp [seam, hq]
  rw [hs]
  exact WilsonSlabGauge.kernel_gauge_left WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_classFunction
    WilsonSingleLinkStaples.character_inverse_re β 2 _ _ _

/-- A root of the central element represents exactly the original nontrivial seam orbit. -/
theorem kernel_uniform_center (i : Fin 3) (q : Q) (hq : q ^ n = -1) (β : ℝ) (v : Slice n) :
    kernelMap n β (uniform n i q, v) = kernelMap n β (twist n i 1,v) := by
  rw [← seam_gauge_uniform, hq]
  have hh := WilsonSlabGauge.kernel_gauge_left WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_classFunction WilsonSingleLinkStaples.character_inverse_re β 2
    (seam n i (-1)) v (distributingGauge n i q)
  simpa only [twist, mul_one] using hh

end
end UnifiedTheory.Clay.YangMills.WilsonDistributedSeam
