/- Explicit nonvanishing spectator weights admissible for the full energy graph.
Damping by the clock and by 1+frequency^2 makes all estimates elementary. -/
import UnifiedTheory.Audit.KFCausalJoinedModulatedWeights
import UnifiedTheory.Audit.KFCausalEuclideanGaussianCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalSpectatorCoreWeights
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalClockFloorFlow (clock)
open KFCausalEuclideanGaussianCore (gaussian gaussian_memLp gaussian_continuous gaussian_ne_zero)
open KFCausalModulatedLpTotality (state state_coe)
open KFCausalEuclideanFourierUniqueness (modulate)

theorem bounded_mul {E : Type*} [MeasurableSpace E] {μ : Measure E}
    (f a : E → ℂ) (hf : MemLp f 2 μ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖a x‖ ≤ C) : MemLp (fun x => a x*f x) 2 μ := by
  apply (hf.const_mul (C:ℂ)).of_le (ha.mul hf.1)
  filter_upwards [] with x
  simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (f x))

def clockWeight (ε : ℝ) (x : Block 1) : ℂ := Complex.ofReal ((clock ε (x 0))⁻¹)*gaussian x

def clockInverseWeight (ε : ℝ) (x : Block 1) : ℂ :=
  Complex.ofReal ((clock ε (x 0))⁻¹)*clockWeight ε x

def neutralWeight (x : Block 1) : ℂ := Complex.ofReal ((1+x 0^2)⁻¹)*gaussian x

def neutralSquareWeight (x : Block 1) : ℂ := (x 0:ℂ)^2*neutralWeight x

theorem clock_inv_bound (ε : ℝ) (hε : 0 < ε) (x : Block 1) :
    ‖Complex.ofReal ((clock ε (x 0))⁻¹)‖ ≤ ε⁻¹ := by
  have hC : 0 < clock ε (x 0) := KFCausalClockFloorCanonicalDefect.clock_positive ε _ hε.le
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hC)]
  apply inv_anti₀ hε
  unfold clock
  linarith [Real.exp_pos (x 0)]

theorem clock_inv_continuous (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun x : Block 1 => Complex.ofReal ((clock ε (x 0))⁻¹)) := by
  unfold clock
  fun_prop (disch := intro x; positivity)

theorem clock_memLp (ε : ℝ) (hε : 0 < ε) : MemLp (clockWeight ε) 2 :=
  bounded_mul gaussian _ gaussian_memLp (clock_inv_continuous ε hε).aestronglyMeasurable
    (ε⁻¹) (inv_nonneg.mpr hε.le) (clock_inv_bound ε hε)

theorem clockInverse_memLp (ε : ℝ) (hε : 0 < ε) : MemLp (clockInverseWeight ε) 2 :=
  bounded_mul (clockWeight ε) _ (clock_memLp ε hε)
    (clock_inv_continuous ε hε).aestronglyMeasurable
    (ε⁻¹) (inv_nonneg.mpr hε.le) (clock_inv_bound ε hε)

theorem neutral_memLp : MemLp neutralWeight 2 := by
  apply bounded_mul gaussian _ gaussian_memLp
    (show Continuous (fun x : Block 1 => Complex.ofReal ((1+x 0^2)⁻¹)) by
      fun_prop (disch := intro x; positivity)).aestronglyMeasurable 1 (by norm_num)
  intro x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact (inv_le_one₀ (by positivity)).mpr (by nlinarith [sq_nonneg (x 0)])

theorem neutralSquare_memLp : MemLp neutralSquareWeight 2 := by
  have he : neutralSquareWeight = fun x : Block 1 => ((x 0^2/(1+x 0^2):ℝ):ℂ)*gaussian x := by
    funext x
    simp only [neutralSquareWeight, neutralWeight, Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]
    ring
  rw [he]
  apply bounded_mul gaussian _ gaussian_memLp
    (show Continuous (fun x : Block 1 => ((x 0^2/(1+x 0^2):ℝ):ℂ)) by
      fun_prop (disch := intro x; positivity)).aestronglyMeasurable 1 (by norm_num)
  intro x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).mpr (by linarith)

theorem clock_nonzero (ε : ℝ) (hε : 0 < ε) (x : Block 1) : clockWeight ε x ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero
    (KFCausalClockFloorCanonicalDefect.clock_positive ε _ hε.le).ne')) (gaussian_ne_zero x)

theorem neutral_nonzero (x : Block 1) : neutralWeight x ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero (by positivity))) (gaussian_ne_zero x)

theorem clock_state (ε : ℝ) (hε : 0 < ε) (k : Block 1) :
    state gaussian gaussian_memLp k =ᵐ[volume] fun x =>
      (clock ε (x 0):ℂ)*(state (clockWeight ε) (clock_memLp ε hε) k) x := by
  filter_upwards [state_coe gaussian gaussian_memLp k,
    state_coe (clockWeight ε) (clock_memLp ε hε) k] with x h1 h2
  rw [h1,h2]
  unfold modulate clockWeight
  have hn : (clock ε (x 0):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (KFCausalClockFloorCanonicalDefect.clock_positive ε _ hε.le).ne'
  push_cast
  field_simp

theorem clockInverse_state (ε : ℝ) (hε : 0 < ε) (k : Block 1) :
    state (clockInverseWeight ε) (clockInverse_memLp ε hε) k =ᵐ[volume] fun x =>
      (clock ε (x 0):ℂ)⁻¹*(state (clockWeight ε) (clock_memLp ε hε) k) x := by
  filter_upwards [state_coe (clockInverseWeight ε) (clockInverse_memLp ε hε) k,
    state_coe (clockWeight ε) (clock_memLp ε hε) k] with x h1 h2
  rw [h1,h2]
  unfold modulate clockInverseWeight
  push_cast
  ring

theorem neutralSquare_state (k : Block 1) :
    state neutralSquareWeight neutralSquare_memLp k =ᵐ[volume] fun x =>
      (x 0:ℂ)^2*(state neutralWeight neutral_memLp k) x := by
  filter_upwards [state_coe neutralSquareWeight neutralSquare_memLp k,
    state_coe neutralWeight neutral_memLp k] with x h1 h2
  rw [h1,h2]
  unfold modulate neutralSquareWeight
  ring

#print axioms clock_memLp
#print axioms neutralSquare_memLp
#print axioms clock_state
end
end UnifiedTheory.Audit.KFCausalSpectatorCoreWeights
