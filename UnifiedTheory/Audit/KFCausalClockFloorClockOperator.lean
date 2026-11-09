/- The maximal positive self-adjoint clock C=exp(s)+epsilon and its
exact inverse relation with the bounded defect D=epsilon/C. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
import UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockOperator
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier

theorem clockWeight_measurable (ε : ℝ) : Measurable (fun x : Configuration => clock ε x.1) := by
  unfold clock
  fun_prop

def clockOperator (ε : ℝ) (hε : 0 < ε) : Hilbert →ₗ.[ℂ] Hilbert :=
  positivePullback (LinearIsometryEquiv.refl ℂ Hilbert) (fun x => clock ε x.1)
    (clockWeight_measurable ε) (fun x => (clock_positive ε x.1 hε.le).le)

theorem clockOperator_selfAdjoint (ε : ℝ) (hε : 0 < ε) :
    IsSelfAdjoint (clockOperator ε hε) := pullback_selfAdjoint _ _ _ _

theorem clockOperator_positive (ε : ℝ) (hε : 0 < ε) (f : (clockOperator ε hε).domain) :
    0 ≤ (inner ℂ (clockOperator ε hε f) (f:Hilbert)).re := pullback_positive _ _ _ _ f

theorem clockOperator_graph (ε : ℝ) (hε : 0 < ε) (f g : Hilbert) :
    (f,g) ∈ (clockOperator ε hε).graph ↔
      g =ᵐ[volume] fun x => (clock ε x.1:ℂ)*f x := pullback_graph_iff _ _ _ _ _ _

theorem clock_defect_graph (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    (defectOperator ε hε f,(ε:ℂ) • f) ∈ (clockOperator ε hε).graph := by
  apply (clockOperator_graph ε hε _ _).mpr
  filter_upwards [defectOperator_coe ε hε f,Lp.coeFn_smul (ε:ℂ) f] with x hd hs
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hd,defect,Complex.ofReal_div]
  have hc : (clock ε x.1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (clock_positive ε x.1 hε.le).ne'
  field_simp

theorem defect_clock (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockOperator ε hε).graph) :
    defectOperator ε hε g = (ε:ℂ) • f := by
  apply Lp.ext
  filter_upwards [defectOperator_coe ε hε g,Lp.coeFn_smul (ε:ℂ) f,
    (clockOperator_graph ε hε f g).mp hfg] with x hd hs hg
  rw [hd,hs]
  simp only [Pi.smul_apply,smul_eq_mul,hg,defect,Complex.ofReal_div]
  have hc : (clock ε x.1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (clock_positive ε x.1 hε.le).ne'
  field_simp

theorem clockOperator_domain_range (ε : ℝ) (hε : 0 < ε) :
    ((clockOperator ε hε).domain : Set Hilbert) = Set.range (defectOperator ε hε) := by
  ext f
  constructor
  · intro hf
    refine ⟨(ε:ℂ)⁻¹ • clockOperator ε hε ⟨f,hf⟩,?_⟩
    rw [map_smul,defect_clock ε hε f _ ((clockOperator ε hε).mem_graph ⟨f,hf⟩),
      smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hε.ne'),one_smul]
  · rintro ⟨g,rfl⟩
    exact LinearPMap.mem_domain_of_mem_graph (clock_defect_graph ε hε g)

theorem defectOperator_denseRange (ε : ℝ) (hε : 0 < ε) :
    DenseRange (defectOperator ε hε) := by
  change Dense (Set.range (defectOperator ε hε))
  rw [← clockOperator_domain_range ε hε]
  exact (clockOperator_selfAdjoint ε hε).dense_domain

#print axioms clockWeight_measurable
#print axioms clockOperator_selfAdjoint
#print axioms clockOperator_positive
#print axioms clockOperator_graph
#print axioms clock_defect_graph
#print axioms defect_clock
#print axioms clockOperator_domain_range
#print axioms defectOperator_denseRange

end
end UnifiedTheory.Audit.KFCausalClockFloorClockOperator
