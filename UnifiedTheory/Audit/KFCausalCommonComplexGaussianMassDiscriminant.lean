/- The already proved purely imaginary response bounds discharge the
two even terms in the exact common-complex mass-channel reduction.
The remaining odd discriminant inequality is not assumed or proved. -/
import UnifiedTheory.Audit.KFCausalCommonComplexGaussianMassResponseReduction
import UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianWeightedTransport

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexGaussianMassDiscriminant
noncomputable section
open KFCausalCommonComplexGaussianMassResponseReduction (commonSource defect oddDefect)
open KFCausalWeightedReciprocalNeutralWholeClock (positiveSlice transportResponse)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C : Fin n → ℂ) (D : ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3)

include hε hh hw hb in
theorem even_defects_nonnegative (s : ℝ) :
    0 ≤ defect n ε h a w p C D 0 1 (536*fraction ε s) 0 s ∧
      0 ≤ defect n ε h a w p C D 2 0 (536*fraction ε s) 0 s := by
  have h0 := KFCausalCommonImaginaryGaussianWeightedTransport.transport_bound
    0 0 1 n ε h a w p C hε hh hw hb D (by norm_num) (by norm_num) (by norm_num) s
  have h2 := KFCausalCommonImaginaryGaussianWeightedTransport.transport_bound
    2 0 0 n ε h a w p C hε hh hw hb D (by norm_num) (by norm_num) (by norm_num) s
  simpa only [defect,commonSource,Complex.ofReal_zero,zero_add] using
    And.intro (sub_nonneg.mpr h0) (sub_nonneg.mpr h2)

include hε hh hw hb in
theorem actual_mass_bound_iff (s : ℝ) :
    (∀ A : ℝ,
      transportResponse 2 0 0 n ε h a w p C (fun _ => commonSource A D) (fun _ => 1) s ≤
        536*fraction ε s*
          positiveSlice 2 0 0 n ε h a w p C (fun _ => commonSource A D) (fun _ => 1) s) ↔
      (oddDefect n ε h a w p C D (536*fraction ε s) s)^2 ≤
        defect n ε h a w p C D 0 1 (536*fraction ε s) 0 s*
          defect n ε h a w p C D 2 0 (536*fraction ε s) 0 s := by
  rw [KFCausalCommonComplexGaussianMassResponseReduction.mass_response_all_sources_iff
    n ε h a w p C D hε hh hw hb (536*fraction ε s) s]
  have he := even_defects_nonnegative n ε h a w p C D hε hh hw hb s
  exact ⟨fun h => h.2.2,fun h => ⟨he.1,he.2,h⟩⟩

#print axioms even_defects_nonnegative
#print axioms actual_mass_bound_iff
end
end UnifiedTheory.Audit.KFCausalCommonComplexGaussianMassDiscriminant
