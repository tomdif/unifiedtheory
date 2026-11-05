/- On the identity gauge orbit, the full physical seam likelihood has
an exponent proportional to the linear period, rather than the raw seam
area. Output configurations are unrestricted. This is not a global bound
on the ground-supported input configurations. -/
import UnifiedTheory.Clay.YangMills.WilsonSeamRoot
import UnifiedTheory.Clay.YangMills.WilsonGaugeKernelCurvature

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonFlatSeamComparison
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonDistributedSeam WilsonCenterTwist
open WilsonJointRotation WilsonGroundLocalComparison
open WilsonSingleLinkStaples (character character_continuous character_re)

variable (n : ℕ) [NeZero n]

theorem identity_potential : potential character 2 (1 : Slice n) = 0 := by
  simp [potential, spatialHolonomy, character_re]

/-- Both opposite distributed rotations lie on the same nontrivial seam orbit. -/
theorem kernel_root_lower (i : Fin 3) (q : Q) (hq : q ^ n = -1)
    (β : ℝ) (hβ : 0 ≤ β) (v : Slice n) :
    Real.exp (-(β * cost n (uniform n i q))) * kernelMap n β (1,v) ≤
      kernelMap n β (twist n i 1,v) := by
  have hi : (q⁻¹)^n = -1 := by rw [inv_pow, hq]; simp
  have he : kernelMap n β (uniform n i q * 1,v) =
      kernelMap n β ((uniform n i q)⁻¹ * 1,v) := by
    simp only [mul_one, uniform_inv, kernel_uniform_center n i q hq,
      kernel_uniform_center n i q⁻¹ hi]
  have hh := WilsonGaugeKernelCurvature.kernel_equal_lower n β hβ (uniform n i q) 1 v
    (by simp only [mul_one, uniform_potential, identity_potential])
    (by simp only [mul_one, uniform_inv, uniform_potential, identity_potential]) he
  simpa only [mul_one, kernel_uniform_center n i q hq] using hh

/-- Centering the symmetric comparison at the root supplies the reverse bound. -/
theorem kernel_root_reverse (i : Fin 3) (q : Q) (hq : q ^ n = -1)
    (β : ℝ) (hβ : 0 ≤ β) (v : Slice n) :
    Real.exp (-(β * cost n (uniform n i q))) * kernelMap n β (twist n i 1,v) ≤
      kernelMap n β (1,v) := by
  have hq2 : (q*q)^n = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul, hq]
    simp
  have he : kernelMap n β (uniform n i q * uniform n i q,v) =
      kernelMap n β ((uniform n i q)⁻¹ * uniform n i q,v) := by
    rw [uniform_mul, inv_mul_cancel, kernel_uniform_one n i (q*q) hq2]
  have hh := WilsonGaugeKernelCurvature.kernel_equal_lower n β hβ
    (uniform n i q) (uniform n i q) v
    (by simp only [uniform_mul, uniform_potential])
    (by simp only [inv_mul_cancel, identity_potential, uniform_potential]) he
  simpa only [uniform_mul, kernel_uniform_center n i q hq,
    kernel_uniform_one n i (q*q) hq2] using hh

theorem kernel_lower (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (v : Slice n) :
    Real.exp (-(β * Real.pi^2 * n)) * kernelMap n β (1,v) ≤
      kernelMap n β (twist n i 1,v) := by
  have hc := mul_le_mul_of_nonneg_left (WilsonSeamRoot.root_cost n i) hβ
  have he : Real.exp (-(β * Real.pi^2 * n)) ≤
      Real.exp (-(β * cost n (uniform n i (WilsonSeamRoot.root n)))) :=
    Real.exp_le_exp.mpr (by nlinarith only [hc])
  exact (mul_le_mul_of_nonneg_right he
    (kernel_positive character character_continuous β 2 (1 : Slice n) v).le).trans
      (kernel_root_lower n i (WilsonSeamRoot.root n) (WilsonSeamRoot.root_power n) β hβ v)

theorem kernel_upper (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (v : Slice n) :
    kernelMap n β (twist n i 1,v) ≤ Real.exp (β * Real.pi^2 * n) * kernelMap n β (1,v) := by
  have hh := kernel_root_reverse n i (WilsonSeamRoot.root n)
    (WilsonSeamRoot.root_power n) β hβ v
  have hc := mul_le_mul_of_nonneg_left (WilsonSeamRoot.root_cost n i) hβ
  have ht := mul_le_mul_of_nonneg_left hh
    (Real.exp_pos (β * cost n (uniform n i (WilsonSeamRoot.root n)))).le
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at ht
  exact ht.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by nlinarith only [hc]))
    (kernel_positive character character_continuous β 2 (1 : Slice n) v).le)

/-- The original physical ground is retained and its input values cancel by center symmetry. -/
theorem transition_bounds (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (v : Slice n) :
    Real.exp (-(β * Real.pi^2 * n)) * transition n β hβ 1 v ≤
      transition n β hβ (twist n i 1) v ∧
    transition n β hβ (twist n i 1) v ≤
      Real.exp (β * Real.pi^2 * n) * transition n β hβ 1 v := by
  have hp : 0 ≤ ground n β hβ v / (‖transfer n β‖ * ground n β hβ 1) :=
    div_nonneg (ground_pos n β hβ v).le
      (mul_nonneg (norm_nonneg _) (ground_pos n β hβ 1).le)
  have hl := mul_le_mul_of_nonneg_right (kernel_lower n i β hβ v) hp
  have hu := mul_le_mul_of_nonneg_right (kernel_upper n i β hβ v) hp
  unfold transition GroundStateDirichlet.transition
  rw [ground_twist]
  constructor
  · simpa only [mul_div_assoc, mul_assoc] using hl
  · simpa only [mul_div_assoc, mul_assoc] using hu

/-- Full gauge-averaged likelihood, not the raw ratio with its attained area exponent. -/
theorem physical_likelihood_bounds (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (v : Slice n) :
    transition n β hβ (twist n i 1) v / transition n β hβ 1 v ∈
      Set.Icc (Real.exp (-(β * Real.pi^2 * n))) (Real.exp (β * Real.pi^2 * n)) := by
  have hh := transition_bounds n i β hβ v
  exact ⟨(le_div_iff₀ (transition_pos n β hβ 1 v)).mpr hh.1,
    (div_le_iff₀ (transition_pos n β hβ 1 v)).mpr hh.2⟩

/-- Every representative of the identity input orbit has the same bound.
The output configurations remain arbitrary. -/
theorem gauge_input_bounds (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β)
    (h : SliceGauge n Q) (v : Slice n) :
    transition n β hβ (twist n i (gaugeSlice h 1)) v /
      transition n β hβ (gaugeSlice h 1) v ∈
        Set.Icc (Real.exp (-(β * Real.pi^2 * n))) (Real.exp (β * Real.pi^2 * n)) := by
  rw [twist_gauge, WilsonPhysicalResponse.full_transition_gauge_left,
    WilsonPhysicalResponse.full_transition_gauge_left]
  exact physical_likelihood_bounds n i β hβ v

end
end UnifiedTheory.Clay.YangMills.WilsonFlatSeamComparison
