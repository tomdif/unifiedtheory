/- The actual physical shear pairing is half the derivative of a bounded
weighted norm along an unforced shear path. Its monotonicity controls
the final pairing by the norm secant, removing the initial shear output. -/
import UnifiedTheory.Audit.KFCausalClockSecantMultiplier
import UnifiedTheory.Audit.KFCausalClockShearPositiveVariation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalShearNormSecant
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve (coefficientOperator)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root)
open UnifiedTheory.Audit.KFCausalClockSecantMultiplier (operator operator_norm_sq pairing_real)
open UnifiedTheory.Audit.KFCausalClockShearPositiveVariation (expectation)

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (hh : h ≠ 0)
  (U J : ℝ → Hilbert)
local notation "M" => operator ε h hε hb hh
local notation "Cclock" => coefficientOperator ε h hε hb hh
local notation "W" => root ε hε h hb hh
local notation "q" => expectation W U J

theorem norm_derivative (t : ℝ) (hd : HasDerivAt U (Cclock (J t)) t)
    (hg : (U t,J t) ∈ (shearMomentum h).graph) :
    HasDerivAt (fun r => ‖M (U r)‖^2) (2*q t) t := by
  have hM := ((M).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have he := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hM.inner ℂ hM)
  change HasDerivAt (fun r => (inner ℂ (M (U r)) (M (U r))).re)
    (inner ℂ (M (U t)) (M (Cclock (J t)))+inner ℂ (M (Cclock (J t))) (M (U t))).re t at he
  have hi : (inner ℂ (M (Cclock (J t))) (M (U t))).re =
      (inner ℂ (M (U t)) (M (Cclock (J t)))).re := inner_re_symm (𝕜 := ℂ) _ _
  convert he using 1
  · funext r
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (M (U r))).symm
  · rw [Complex.add_re,hi,
      pairing_real ε h hε hb hh (U t) (J t) hg]
    unfold expectation
    ring

theorem endpoint_secant (hc : Continuous U)
    (hd : ∀ t (_ht : t ∈ Ioo (0:ℝ) 1), HasDerivAt U (Cclock (J t)) t)
    (hg : ∀ t : Interval, (U t,J t) ∈ (shearMomentum h).graph)
    (hm : MonotoneOn q (Icc (0:ℝ) 1)) :
    (‖M (U 1)‖^2-‖M (U 0)‖^2)/2 ≤ q 1 := by
  have hN : Continuous (fun r => ‖M (U r)‖^2) := ((M).continuous.comp hc).norm.pow 2
  have hD (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :=
    norm_derivative ε h hε hb hh U J t (hd t ht) (hg ⟨t,ht.1.le,ht.2.le⟩)
  have he := (convex_Icc (0:ℝ) 1).image_sub_le_mul_sub_of_deriv_le hN.continuousOn
    (fun t ht => (hD t (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt)
    (C := 2*q 1) (fun t ht => by
      have ht' : t ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using ht
      rw [(hD t ht').deriv]
      exact mul_le_mul_of_nonneg_left (hm ⟨ht'.1.le,ht'.2.le⟩ ⟨zero_le_one,le_rfl⟩ ht'.2.le)
        (by norm_num : (0:ℝ) ≤ 2))
    0 ⟨le_rfl,zero_le_one⟩ 1 ⟨zero_le_one,le_rfl⟩ zero_le_one
  norm_num only [sub_zero,mul_one] at he
  linarith

theorem endpoint_norm_lower (hc : Continuous U)
    (hd : ∀ t (_ht : t ∈ Ioo (0:ℝ) 1), HasDerivAt U (Cclock (J t)) t)
    (hg : ∀ t : Interval, (U t,J t) ∈ (shearMomentum h).graph)
    (hm : MonotoneOn q (Icc (0:ℝ) 1)) : -(ε/8)*‖U 0‖^2 ≤ q 1 := by
  have he := endpoint_secant ε h hε hb hh U J hc hd hg hm
  have hn := operator_norm_sq ε h hε hb hh (U 0)
  nlinarith [sq_nonneg ‖M (U 1)‖]

#print axioms norm_derivative
#print axioms endpoint_secant
#print axioms endpoint_norm_lower
end
end UnifiedTheory.Audit.KFCausalShearNormSecant
