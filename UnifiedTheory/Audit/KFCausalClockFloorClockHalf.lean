/- Actual positive self-adjoint clock half and inverse half for the
optional clock C=exp(s)+epsilon. The inverse half has full L2 domain;
the exact inverse graph retains the unbounded half-clock domain. -/
import UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier
import UnifiedTheory.Audit.KFCausalConfigurationTestSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockHalf
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier

def halfWeight (ε : ℝ) (x : Configuration) : ℝ := Real.sqrt (Real.exp x.1+ε)
def inverseWeight (ε : ℝ) (x : Configuration) : ℝ := (halfWeight ε x)⁻¹

theorem halfWeight_measurable (ε : ℝ) : Measurable (halfWeight ε) := by
  unfold halfWeight
  fun_prop

theorem halfWeight_positive (ε : ℝ) (hε : 0 < ε) (x : Configuration) : 0 < halfWeight ε x := by
  unfold halfWeight
  positivity

theorem inverseWeight_measurable (ε : ℝ) : Measurable (inverseWeight ε) :=
  (halfWeight_measurable ε).inv

def clockHalf (ε : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  positivePullback (LinearIsometryEquiv.refl ℂ Hilbert) (halfWeight ε)
    (halfWeight_measurable ε) (fun _ => Real.sqrt_nonneg _)

def inverseClockHalf (ε : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  positivePullback (LinearIsometryEquiv.refl ℂ Hilbert) (inverseWeight ε)
    (inverseWeight_measurable ε) (fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem clockHalf_selfAdjoint (ε : ℝ) : IsSelfAdjoint (clockHalf ε) :=
  pullback_selfAdjoint _ _ _ _

theorem inverseClockHalf_selfAdjoint (ε : ℝ) : IsSelfAdjoint (inverseClockHalf ε) :=
  pullback_selfAdjoint _ _ _ _

theorem clockHalf_graph (ε : ℝ) (f g : Hilbert) :
    (f,g) ∈ (clockHalf ε).graph ↔ g =ᵐ[volume] fun x => (halfWeight ε x:ℂ)*f x :=
  pullback_graph_iff _ _ _ _ _ _

theorem inverseClockHalf_graph (ε : ℝ) (f g : Hilbert) :
    (f,g) ∈ (inverseClockHalf ε).graph ↔ g =ᵐ[volume] fun x => (inverseWeight ε x:ℂ)*f x :=
  pullback_graph_iff _ _ _ _ _ _

theorem inverseWeight_bound (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    inverseWeight ε x ≤ (Real.sqrt ε)⁻¹ := by
  apply inv_anti₀ (Real.sqrt_pos.mpr hε)
  apply Real.sqrt_le_sqrt
  linarith [Real.exp_pos x.1]

theorem inverse_product_memLp (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    MemLp (fun x => (inverseWeight ε x:ℂ)*f x) 2 volume := by
  have hm : AEStronglyMeasurable (fun x => (inverseWeight ε x:ℂ)*f x) volume :=
    ((Complex.measurable_ofReal.comp (inverseWeight_measurable ε)).aestronglyMeasurable).mul
      (Lp.memLp f).aestronglyMeasurable
  apply ((Lp.memLp f).const_mul (((Real.sqrt ε)⁻¹:ℝ):ℂ)).of_le hm
  filter_upwards [] with x
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (show 0 ≤ inverseWeight ε x from inv_nonneg.mpr (Real.sqrt_nonneg _)),
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_right (inverseWeight_bound ε hε x) (norm_nonneg _)

theorem inverseClockHalf_domain (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    f ∈ (inverseClockHalf ε).domain :=
  (pullback_domain_iff _ _ _ _ f).mpr (inverse_product_memLp ε hε f)

def inverseAction (ε : ℝ) (hε : 0 < ε) (f : Hilbert) : Hilbert :=
  inverseClockHalf ε ⟨f,inverseClockHalf_domain ε hε f⟩

theorem inverseAction_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    inverseAction ε hε f =ᵐ[volume] fun x => (Real.sqrt (Real.exp x.1+ε):ℂ)⁻¹*f x := by
  have h := (inverseClockHalf_graph ε f _).mp
    ((inverseClockHalf ε).mem_graph ⟨f,inverseClockHalf_domain ε hε f⟩)
  simpa only [inverseWeight,halfWeight,Complex.ofReal_inv] using h

theorem half_inverse_graph (ε : ℝ) (hε : 0 < ε) (f g : Hilbert) :
    (f,g) ∈ (clockHalf ε).graph ↔ (g,f) ∈ (inverseClockHalf ε).graph := by
  rw [clockHalf_graph,inverseClockHalf_graph]
  have hn (x : Configuration) : (halfWeight ε x:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (halfWeight_positive ε hε x).ne'
  constructor
  · intro h
    filter_upwards [h] with x hx
    rw [hx,inverseWeight,Complex.ofReal_inv,← mul_assoc,inv_mul_cancel₀ (hn x),one_mul]
  · intro h
    filter_upwards [h] with x hx
    rw [hx,inverseWeight,Complex.ofReal_inv,← mul_assoc,mul_inv_cancel₀ (hn x),one_mul]

theorem inverseAction_ne_zero (ε : ℝ) (hε : 0 < ε) (f : Hilbert) (hf : f ≠ 0) :
    inverseAction ε hε f ≠ 0 := by
  intro hz
  have h := (half_inverse_graph ε hε _ f).mpr
    ((inverseClockHalf ε).mem_graph ⟨f,inverseClockHalf_domain ε hε f⟩)
  change (inverseAction ε hε f,f) ∈ (clockHalf ε).graph at h
  rw [hz] at h
  have h0 : ((0:Hilbert),0) ∈ (clockHalf ε).graph := (clockHalf ε).graph.zero_mem
  exact hf ((clockHalf ε).mem_graph_snd_inj' h h0 rfl)

#print axioms halfWeight_measurable
#print axioms halfWeight_positive
#print axioms inverseWeight_measurable
#print axioms clockHalf_selfAdjoint
#print axioms inverseClockHalf_selfAdjoint
#print axioms clockHalf_graph
#print axioms inverseClockHalf_graph
#print axioms inverseWeight_bound
#print axioms inverse_product_memLp
#print axioms inverseClockHalf_domain
#print axioms inverseAction_coe
#print axioms half_inverse_graph
#print axioms inverseAction_ne_zero

end
end UnifiedTheory.Audit.KFCausalClockFloorClockHalf
