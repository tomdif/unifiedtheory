/- A pointwise square absorbs the real shear correction into the actual
longitudinal response. The remaining coefficient has fourth power in hbar;
its weight is D^5(1-D). No energy estimate or limit is inferred from it. -/
import UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalMatterScalarAbsorption
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect defect_positive response_bounds response_add_defect)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical (physicalSymbol)
open UnifiedTheory.Audit.KFCausalShiftedResponseComparison (stripFactor one_le_stripFactor)
open UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight (weight)

def coefficient (ε h : ℝ) : ℝ := 800*stripFactor^4*h^4/ε^5

theorem coefficient_nonneg (ε : ℝ) (hε : 0 < ε) (h : ℝ) : 0 ≤ coefficient ε h := by
  unfold coefficient
  positivity

theorem weighted_young (ε : ℝ) (hε : 0 < ε) (h D a b : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1) :
    2*((20*stripFactor*h^2/ε^3)*D^3*(1-D))*|a| *|b| ≤
      ((1/(2*stripFactor^2))*D*(1-D)/ε)*a^2+coefficient ε h*D^5*(1-D)*b^2 := by
  have hK : 0 < stripFactor := lt_of_lt_of_le (by norm_num) one_le_stripFactor
  have hR : 0 ≤ 1-D := sub_nonneg.mpr hD1
  have hq : 0 ≤ (1/(2*stripFactor^2))*D*(1-D)/ε := by positivity
  have hs := mul_nonneg hq
    (sq_nonneg (|a|-(40*stripFactor^3*h^2/ε^2)*D^2*|b|))
  have he : ((1/(2*stripFactor^2))*D*(1-D)/ε)*
      (|a|-(40*stripFactor^3*h^2/ε^2)*D^2*|b|)^2 =
      ((1/(2*stripFactor^2))*D*(1-D)/ε)*a^2+coefficient ε h*D^5*(1-D)*b^2-
        2*((20*stripFactor*h^2/ε^3)*D^3*(1-D))*|a| *|b| := by
    calc
      _ = ((1/(2*stripFactor^2))*D*(1-D)/ε)*|a|^2+
          coefficient ε h*D^5*(1-D)*|b|^2-
          2*((20*stripFactor*h^2/ε^3)*D^3*(1-D))*|a| *|b| := by
        unfold coefficient
        field_simp
        ring
      _ = _ := by rw [sq_abs,sq_abs]
  rw [he] at hs
  linarith only [hs]

theorem scalar_absorption (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hb : |h| ≤ 2*Real.pi*ε/3) (x : Configuration) (a b : ℝ) :
    |2*((defect ε x.1-(physicalSymbol ε h x).re)/ε)*a*b| ≤
      ((physicalSymbol ε h x*(1-physicalSymbol ε h x)).re/ε)*a^2+
        coefficient ε h*weight ε x*b^2 := by
  have hD := (defect_positive ε x.1 hε).le
  have hD1 : defect ε x.1 ≤ 1 := by
    have hr := response_bounds ε x.1 hε
    have he := response_add_defect ε x.1 hε.le
    linarith
  have hc : |(defect ε x.1-(physicalSymbol ε h x).re)/ε| ≤
      (20*stripFactor*h^2/ε^3)*(defect ε x.1)^3*(1-defect ε x.1) := by
    rw [abs_div,abs_of_pos hε]
    convert div_le_div_of_nonneg_right
      (KFCausalTwoEndpointCorrection.physical_real_difference ε hε h hb x) hε.le using 1
    ring
  have hp := div_le_div_of_nonneg_right
    (KFCausalLongitudinalResponseCoercivity.physical_momentum_lower ε hε h hb x) hε.le
  calc
    _ = 2*|(defect ε x.1-(physicalSymbol ε h x).re)/ε| *|a| *|b| := by
      rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ 2*((20*stripFactor*h^2/ε^3)*(defect ε x.1)^3*(1-defect ε x.1))*|a| *|b| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) (abs_nonneg a))
        (abs_nonneg b)
    _ ≤ ((1/(2*stripFactor^2))*defect ε x.1*(1-defect ε x.1)/ε)*a^2+
        coefficient ε h*(defect ε x.1)^5*(1-defect ε x.1)*b^2 :=
      weighted_young ε hε h (defect ε x.1) a b hD hD1
    _ ≤ _ := by
      unfold weight
      nlinarith only [mul_le_mul_of_nonneg_right hp (sq_nonneg a)]

#print axioms coefficient_nonneg
#print axioms weighted_young
#print axioms scalar_absorption
end
end UnifiedTheory.Audit.KFCausalMatterScalarAbsorption
