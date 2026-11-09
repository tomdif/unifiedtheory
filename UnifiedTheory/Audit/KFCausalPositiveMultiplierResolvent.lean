/- A positive unbounded multiplier is constructed from its bounded
reciprocal resolvent. The full graph and domain are proved, not supplied. -/
import UnifiedTheory.Audit.KFCausalContractiveMultiplier
import UnifiedTheory.Audit.KFCausalInverseResolventGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPositiveMultiplierResolvent
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalResolventHamiltonian
open UnifiedTheory.Audit.KFCausalInverseResolventGraph

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def reciprocal (w : X → ℝ) (x : X) : ℝ := (1+w x)⁻¹

omit [MeasurableSpace X] in
theorem reciprocal_positive (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x : X) :
    0 < reciprocal w x := inv_pos.mpr (by linarith [hw x])

omit [MeasurableSpace X] in
theorem reciprocal_le_one (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x : X) :
    reciprocal w x ≤ 1 := inv_le_one_of_one_le₀ (by linarith [hw x])

theorem reciprocal_measurable (w : X → ℝ) (hw : Measurable w) :
    Measurable (fun x => (reciprocal w x:ℂ)) :=
  Complex.continuous_ofReal.measurable.comp ((measurable_const.add hw).inv)

omit [MeasurableSpace X] in
theorem reciprocal_norm_le (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x : X) :
    ‖(reciprocal w x:ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (reciprocal_positive w hw x)]
  exact reciprocal_le_one w hw x

def resolvent (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  multiplyL (fun x => (reciprocal w x:ℂ)) (reciprocal_measurable w hm) (reciprocal_norm_le w hw)

theorem resolvent_coe (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 μ) :
    resolvent w hm hw f =ᵐ[μ] fun x => (reciprocal w x:ℂ)*f x :=
  multiplyL_coe _ _ _ f

theorem resolvent_injective (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) :
    Function.Injective (resolvent (μ := μ) w hm hw) :=
  multiplyL_injective _ _ _ (fun x => Complex.ofReal_ne_zero.mpr (reciprocal_positive w hw x).ne')

theorem resolvent_symmetric (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (f g : Lp ℂ 2 μ) : inner ℂ (resolvent w hm hw f) g = inner ℂ f (resolvent w hm hw g) :=
  multiplyL_symmetric _ _ _ (fun _ => Complex.conj_ofReal _) f g

theorem resolvent_dense (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) :
    DenseRange (resolvent (μ := μ) w hm hw) :=
  symmetric_injective_dense _ (resolvent_injective w hm hw) (resolvent_symmetric w hm hw)

def positiveMultiplier (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) :
    Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ :=
  inverseShift (resolvent w hm hw) (resolvent_injective w hm hw)

theorem multiplier_selfAdjoint (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) :
    IsSelfAdjoint (positiveMultiplier (μ := μ) w hm hw) :=
  inverseShift_selfAdjoint _ _ (resolvent_dense w hm hw) (resolvent_symmetric w hm hw)

theorem reciprocal_equation (a : ℝ) (ha : 0 ≤ a) (f g : ℂ) :
    (((1+a)⁻¹:ℝ):ℂ)*(g+f)=f ↔ g=(a:ℂ)*f := by
  have hn : ((1+a:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  rw [Complex.ofReal_inv]
  constructor
  · intro h
    have he := congrArg (fun z : ℂ => ((1+a:ℝ):ℂ)*z) h
    dsimp only at he
    rw [← mul_assoc,mul_inv_cancel₀ hn,one_mul] at he
    push_cast at he
    linear_combination he
  · intro h
    have he : g+f=((1+a:ℝ):ℂ)*f := by rw [h];push_cast;ring
    rw [he,← mul_assoc,inv_mul_cancel₀ hn,one_mul]

theorem multiplier_graph_iff (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (f g : Lp ℂ 2 μ) :
    (f,g) ∈ (positiveMultiplier w hm hw).graph ↔ g =ᵐ[μ] fun x => (w x:ℂ)*f x := by
  rw [positiveMultiplier,inverseShift_graph_iff]
  constructor
  · intro hr
    filter_upwards [resolvent_coe w hm hw (g+f),Lp.coeFn_add g f] with x hx hs
    apply (reciprocal_equation (w x) (hw x) (f x) (g x)).mp
    change (reciprocal w x:ℂ)*(g x+f x)=f x
    have he := congrArg (fun z : Lp ℂ 2 μ => z x) hr
    dsimp only at he
    rw [hx,hs] at he
    exact he
  · intro hf
    apply Lp.ext
    filter_upwards [resolvent_coe w hm hw (g+f),Lp.coeFn_add g f,hf] with x hx hs hg
    rw [hx,hs]
    exact (reciprocal_equation (w x) (hw x) (f x) (g x)).mpr hg

theorem multiplier_domain_iff (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (f : Lp ℂ 2 μ) :
    f ∈ (positiveMultiplier w hm hw).domain ↔ MemLp (fun x => (w x:ℂ)*f x) 2 μ := by
  constructor
  · intro hf
    exact (Lp.memLp (positiveMultiplier w hm hw ⟨f,hf⟩)).ae_eq
      ((multiplier_graph_iff w hm hw f _).mp ((positiveMultiplier w hm hw).mem_graph ⟨f,hf⟩))
  · intro hp
    exact LinearPMap.mem_domain_of_mem_graph
      ((multiplier_graph_iff w hm hw f (hp.toLp _)).mpr hp.coeFn_toLp)

theorem multiplier_dense (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) :
    Dense ((positiveMultiplier (μ := μ) w hm hw).domain : Set (Lp ℂ 2 μ)) :=
  (multiplier_selfAdjoint w hm hw).dense_domain

theorem multiplier_closed (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) :
    (positiveMultiplier (μ := μ) w hm hw).IsClosed := (multiplier_selfAdjoint w hm hw).isClosed

#print axioms resolvent
#print axioms resolvent_injective
#print axioms resolvent_symmetric
#print axioms resolvent_dense
#print axioms multiplier_selfAdjoint
#print axioms reciprocal_equation
#print axioms multiplier_graph_iff
#print axioms multiplier_domain_iff
#print axioms multiplier_dense
#print axioms multiplier_closed

end
end UnifiedTheory.Audit.KFCausalPositiveMultiplierResolvent
