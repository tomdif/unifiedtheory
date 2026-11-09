/- Exact clock and coupled longitudinal differentials of a relative
Gaussian. The logarithmic amplitude and scale derivatives are explicit
premises here; the actual shifted Gaussian supplies them separately. -/
import UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential
import UnifiedTheory.Audit.KFCausalClockFloorDifferentialMomentum
import UnifiedTheory.Audit.KFCausalCanonicalClockDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalRelativeGaussianClockDerivative
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (widths)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative (clockDerivative)
open UnifiedTheory.Audit.KFCausalClockFloorDifferentialMomentum (differential)
open UnifiedTheory.Audit.KFCausalClockFloorTransportDerivative (rate coupledVelocity_split)

theorem position_clock_derivative (r : ℝ → ℂ) (s : ℝ) (d : ℂ)
    (hr : HasDerivAt r (d*r s/2) s) (q : Transverse) (i : Fin 5) :
    HasDerivAt (fun t => position (r t) q i) (d*direction (r s) q i) s := by
  by_cases hi : i=4
  · subst i
    have hd := (((hr.sub_const 1).const_mul 2).mul_const ((q 2:ℂ)+(q 3:ℂ))).const_add (q 4:ℂ)
    convert hd using 1
    simp [direction]; ring
  · have hd := hr.mul_const (q i:ℂ)
    convert hd using 1
    · funext t; simp only [position,if_neg hi]
    · simp only [direction,if_neg hi]; ring

theorem profile_clock_derivative (A r : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ)
    (s : ℝ) (q : Transverse) (c d : ℂ)
    (hA : HasDerivAt A (c*A s) s) (hr : HasDerivAt r (d*r s/2) s) :
    HasDerivAt (fun t => profile A r α β b (t,q))
      ((c+d*slope r α β b (s,q))*profile A r α β b (s,q)) s := by
  have hl := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
      (position_clock_derivative r s d hr q i).const_mul (b i))
  have hq := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
      ((position_clock_derivative r s d hr q i).pow 2).const_mul (widths α β i:ℂ))
  have he : (∑ i, b i*(d*direction (r s) q i))-
      (∑ i, (widths α β i:ℂ)*(2*position (r s) q i*(d*direction (r s) q i))) =
        d*slope r α β b (s,q) := by
    rw [KFCausalRelativeGaussianDifferential.slope,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  convert hA.mul (hl.sub hq).cexp using 1
  simp only [Nat.cast_ofNat,show 2-1=1 from rfl,pow_one,Pi.sub_apply,Pi.pow_apply,he]
  unfold profile exponent
  ring

theorem clockDerivative_eq (A r : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hr : ContDiff ℝ 1 r)
    (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) (c d : ℂ)
    (hAc : HasDerivAt A (c*A x.1) x.1) (hrd : HasDerivAt r (d*r x.1/2) x.1) :
    clockDerivative (profile A r α β b) x =
      (c+d*slope r α β b x)*profile A r α β b x := by
  have hp := (((profile_smooth A r hA hr α β b).differentiable (by norm_num)) x).hasFDerivAt.comp_hasDerivAt
    x.1 ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  exact hp.unique (profile_clock_derivative A r α β b x.1 x.2 c d hAc hrd)

theorem longitudinal_differential (ε : ℝ) (A r : ℝ → ℂ)
    (hA : ContDiff ℝ 1 A) (hr : ContDiff ℝ 1 r)
    (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) (c d : ℂ)
    (hAc : HasDerivAt A (c*A x.1) x.1) (hrd : HasDerivAt r (d*r x.1/2) x.1) :
    differential ε (profile A r α β b) x =
      ((rate ε x.1:ℂ)+(Real.exp x.1+ε:ℂ)⁻¹*c)*profile A r α β b x+
        ((Real.exp x.1+ε:ℂ)⁻¹*(d+1))*
          (slope r α β b x*profile A r α β b x) := by
  have hclock := clockDerivative_eq A r hA hr α β b x c d hAc hrd
  have hshear := (profile_line_derivative A r α β b x).unique
    (((profile_smooth A r hA hr α β b).differentiable (by norm_num) x).hasFDerivAt.hasLineDerivAt
      ((0,velocity x.2):Configuration))
  unfold differential
  rw [coupledVelocity_split,map_add,map_smul,map_smul]
  change _+(((Real.exp x.1+ε)⁻¹:ℝ) • clockDerivative (profile A r α β b) x+
    ((Real.exp x.1+ε)⁻¹:ℝ) • _) = _
  rw [hclock,← hshear]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_add]
  ring

#print axioms position_clock_derivative
#print axioms profile_clock_derivative
#print axioms clockDerivative_eq
#print axioms longitudinal_differential
end
end UnifiedTheory.Audit.KFCausalRelativeGaussianClockDerivative
