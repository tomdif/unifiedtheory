/- Finite-increment monotonicity for the actual even charged moments.
The weight b^(2n+2) compensates every moment degree m+n with m≤2.
This is the termwise input for a nonnegative Gaussian series argument. -/
import UnifiedTheory.Audit.KFCausalChargedEvenMomentFamily
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedEvenMomentMonotonicity
noncomputable section
open Matrix Set
open scoped Topology
open KFCausalChargedEvenMomentImaginaryBound (gamma gammaSlope slope momentConstant)
open KFCausalChargedEvenMomentFamily (energy)

variable {ι : Type*} [Fintype ι]

def lineEnergy (α a : ℝ) (l : ℕ) (w : ι → ℝ) (c : ι → ℂ) (b : ℝ) : ℝ :=
  energy l (gamma α ((a:ℂ)+Complex.I*(b:ℂ))) w c

private theorem line_derivative (α a : ℝ) (hα : 0 < α) (l : ℕ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ) (b : ℝ) (hb : |b| < a) :
    HasDerivAt (lineEnergy α a l w c)
      (momentConstant l*(star (star c) ⬝ᵥ
        ((fun i j => slope l (gamma α ((a:ℂ)+Complex.I*(b:ℂ)))
          (gammaSlope α ((a:ℂ)+Complex.I*(b:ℂ))) (w i) (w j)) *ᵥ star c)).re) b := by
  have hr : |((a:ℂ)+Complex.I*(b:ℂ)).im| < ((a:ℂ)+Complex.I*(b:ℂ)).re := by simpa using hb
  have h := (KFCausalChargedEvenMomentFamily.actual_energy_derivative α _ hα hr l w hw c).scomp_of_eq b
    ((hasDerivAt_id b).sub_const b) (by simp)
  simp only [one_smul] at h
  convert h using 1
  funext t
  change energy l (gamma α ((a:ℂ)+Complex.I*(t:ℂ))) w c =
    energy l (gamma α (((a:ℂ)+Complex.I*(b:ℂ))+Complex.I*((t-b:ℝ):ℂ))) w c
  rw [show (a:ℂ)+Complex.I*(t:ℂ) =
    ((a:ℂ)+Complex.I*(b:ℂ))+Complex.I*((t-b:ℝ):ℂ) by push_cast; ring]

theorem line_differentiable (α a : ℝ) (hα : 0 < α) (l : ℕ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ) (b : ℝ) (hb : |b| < a) :
    DifferentiableAt ℝ (lineEnergy α a l w c) b :=
  (line_derivative α a hα l w hw c b hb).differentiableAt

theorem line_derivative_lower (α a : ℝ) (hα : 0 < α) (l : ℕ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ) (b : ℝ) (hb : |b| < a) :
    -((l+2:ℝ)/2)*lineEnergy α a l w c b ≤ b*deriv (lineEnergy α a l w c) b := by
  have hr : |((a:ℂ)+Complex.I*(b:ℂ)).im| < ((a:ℂ)+Complex.I*(b:ℂ)).re := by simpa using hb
  have h := KFCausalChargedEvenMomentFamily.actual_energy_derivative_lower α _ hα hr l w hw c
  rw [(KFCausalChargedEvenMomentFamily.actual_energy_derivative α _ hα hr l w hw c).deriv] at h
  rw [(line_derivative α a hα l w hw c b hb).deriv]
  simpa only [lineEnergy,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_add] using h

theorem scaled_derivative_nonnegative (α a : ℝ) (hα : 0 < α)
    (m n : ℕ) (hm : m ≤ 2) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ)
    (b : ℝ) (hb : 0 < b) (hba : b < a) :
    0 ≤ deriv (fun t => t^(2*n+2)*lineEnergy α a (m+n) w c t) b := by
  have hab : |b| < a := by simpa only [abs_of_pos hb] using hba
  have hD := (line_differentiable α a hα (m+n) w hw c b hab).hasDerivAt
  have hd := ((hasDerivAt_id b).pow (2*n+2)).mul hD
  change HasDerivAt (fun t => t^(2*n+2)*lineEnergy α a (m+n) w c t) _ b at hd
  have hE : 0 ≤ lineEnergy α a (m+n) w c b :=
    KFCausalChargedEvenMomentFamily.energy_nonnegative _ _ _ _
  have hL := line_derivative_lower α a hα (m+n) w hw c b hab
  have hmR : (m:ℝ) ≤ 2 := by exact_mod_cast hm
  have hcoef : 0 ≤ (2*n+2:ℝ)*lineEnergy α a (m+n) w c b+
      b*deriv (lineEnergy α a (m+n) w c) b := by
    push_cast at hL
    nlinarith [mul_nonneg (show 0 ≤ (3*n+2-m:ℝ) by nlinarith) hE]
  have hp : 0 ≤ b^(2*n+2)*((2*n+2:ℝ)*lineEnergy α a (m+n) w c b+
      b*deriv (lineEnergy α a (m+n) w c) b) := mul_nonneg (by positivity) hcoef
  have he : b*deriv (fun t => t^(2*n+2)*lineEnergy α a (m+n) w c t) b =
      b^(2*n+2)*((2*n+2:ℝ)*lineEnergy α a (m+n) w c b+
        b*deriv (lineEnergy α a (m+n) w c) b) := by
    rw [hd.deriv]
    rw [show 2*n+2-1=2*n+1 by omega]
    simp only [id_eq,Pi.pow_apply,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
    ring
  rw [← he] at hp
  exact nonneg_of_mul_nonneg_right hp hb

theorem scaled_monotone (α a : ℝ) (hα : 0 < α)
    (m n : ℕ) (hm : m ≤ 2) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ) :
    MonotoneOn (fun b => b^(2*n+2)*lineEnergy α a (m+n) w c b) (Ioo 0 a) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 a)
  · intro b hb
    have hD := line_differentiable α a hα (m+n) w hw c b
      (by simpa only [abs_of_pos hb.1] using hb.2)
    exact ((continuousAt_id.pow _).mul hD.continuousAt).continuousWithinAt
  · intro b hb
    have hbi := interior_subset hb
    exact (((differentiableAt_id.pow _).mul (line_differentiable α a hα (m+n) w hw c b
      (by simpa only [abs_of_pos hbi.1] using hbi.2)))).differentiableWithinAt
  · intro b hb
    have hbi := interior_subset hb
    exact scaled_derivative_nonnegative α a hα m n hm w hw c b hbi.1 hbi.2

#print axioms line_differentiable
#print axioms line_derivative_lower
#print axioms scaled_derivative_nonnegative
#print axioms scaled_monotone
end
end UnifiedTheory.Audit.KFCausalChargedEvenMomentMonotonicity
