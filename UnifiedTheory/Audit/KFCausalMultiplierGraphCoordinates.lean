/- Bounded coordinates for the entire graph of a maximal real multiplier.
These coordinates reduce graph-norm density to ordinary L2 density. -/
import UnifiedTheory.Audit.KFCausalContractiveMultiplier
import UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalMultiplierGraphCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier

def radius (t : ℝ) : ℝ := Real.sqrt (1+t^2)
def lowerWeight (t : ℝ) : ℝ := (radius t)⁻¹
def upperWeight (t : ℝ) : ℝ := t / radius t

theorem radius_positive (t : ℝ) : 0 < radius t := by unfold radius; positivity

theorem radius_square (t : ℝ) : (radius t)^2 = 1+t^2 :=
  Real.sq_sqrt (by positivity)

theorem lowerWeight_bound (t : ℝ) : |lowerWeight t| ≤ 1 := by
  have hr : 1 ≤ radius t := by
    have hs := radius_square t
    nlinarith [sq_nonneg t, (radius_positive t).le]
  rw [lowerWeight,abs_inv,abs_of_pos (radius_positive t)]
  exact (inv_le_one₀ (radius_positive t)).mpr hr

theorem upperWeight_bound (t : ℝ) : |upperWeight t| ≤ 1 := by
  rw [upperWeight,abs_div,abs_of_pos (radius_positive t)]
  apply (div_le_one (radius_positive t)).mpr
  nlinarith [radius_square t,sq_abs t,abs_nonneg t,(radius_positive t).le]

theorem weights_square (t : ℝ) : lowerWeight t ^ 2 + upperWeight t ^ 2 = 1 := by
  unfold lowerWeight upperWeight
  field_simp [(radius_positive t).ne']
  nlinarith [radius_square t]

theorem upperWeight_eq (t : ℝ) : upperWeight t = t*lowerWeight t := by
  rw [upperWeight,lowerWeight,div_eq_mul_inv]

theorem lowerWeight_radius (t : ℝ) : lowerWeight t * radius t = 1 :=
  inv_mul_cancel₀ (radius_positive t).ne'

theorem upperWeight_radius (t : ℝ) : upperWeight t * radius t = t :=
  div_mul_cancel₀ t (radius_positive t).ne'

theorem scalar_reconstruction (t : ℝ) (u v : ℂ) (hv : v=(t:ℂ)*u) :
    (lowerWeight t:ℂ)*((lowerWeight t:ℂ)*u+(upperWeight t:ℂ)*v)=u ∧
    (upperWeight t:ℂ)*((lowerWeight t:ℂ)*u+(upperWeight t:ℂ)*v)=v := by
  have hw : (lowerWeight t:ℂ)^2+(upperWeight t:ℂ)^2=1 := by exact_mod_cast weights_square t
  have hu : (upperWeight t:ℂ)=(t:ℂ)*(lowerWeight t:ℂ) := by exact_mod_cast upperWeight_eq t
  have h0 : (lowerWeight t:ℂ)*((lowerWeight t:ℂ)*u+(upperWeight t:ℂ)*v)=u := by
    rw [hv]
    calc
      _ = ((lowerWeight t:ℂ)^2+(upperWeight t:ℂ)^2)*u := by rw [hu]; ring
      _ = u := by rw [hw,one_mul]
  refine ⟨h0,?_⟩
  rw [hu,mul_assoc,← hu,h0,hv]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  (m : X → ℝ) (hm : Measurable m)

abbrev H := Lp ℂ 2 μ

def lower : H (μ := μ) →L[ℂ] H (μ := μ) :=
  multiplyL (fun x => (lowerWeight (m x):ℂ))
    (by unfold lowerWeight radius; fun_prop)
    (fun x => by simpa only [Complex.norm_real,Real.norm_eq_abs] using lowerWeight_bound (m x))

def upper : H (μ := μ) →L[ℂ] H (μ := μ) :=
  multiplyL (fun x => (upperWeight (m x):ℂ))
    (by unfold upperWeight radius; fun_prop)
    (fun x => by simpa only [Complex.norm_real,Real.norm_eq_abs] using upperWeight_bound (m x))

def lift : H (μ := μ) →L[ℂ] (H (μ := μ) × H (μ := μ)) := (lower m hm).prod (upper m hm)

def graph : Submodule ℂ (H (μ := μ) × H (μ := μ)) :=
  (realPullback (LinearIsometryEquiv.refl ℂ (H (μ := μ))) m hm).graph

theorem lower_coe (f : H (μ := μ)) : lower m hm f =ᵐ[μ] fun x => (lowerWeight (m x):ℂ)*f x :=
  multiplyL_coe _ _ _ f

theorem upper_coe (f : H (μ := μ)) : upper m hm f =ᵐ[μ] fun x => (upperWeight (m x):ℂ)*f x :=
  multiplyL_coe _ _ _ f

theorem graph_iff (f g : H (μ := μ)) :
    (f,g) ∈ graph m hm ↔ g =ᵐ[μ] fun x => (m x:ℂ)*f x :=
  realPullback_graph (LinearIsometryEquiv.refl ℂ (H (μ := μ))) m hm f g

theorem lift_mem_graph (f : H (μ := μ)) : lift m hm f ∈ graph m hm := by
  apply (graph_iff m hm _ _).mpr
  filter_upwards [lower_coe m hm f,upper_coe m hm f] with x h0 h1
  change (upper m hm f) x = (m x:ℂ)*(lower m hm f) x
  rw [h0,h1,upperWeight_eq,Complex.ofReal_mul,mul_assoc]

theorem lift_surjective_graph (f g : H (μ := μ)) (hfg : (f,g) ∈ graph m hm) :
    ∃ h : H (μ := μ), lift m hm h = (f,g) := by
  let h := lower m hm f + upper m hm g
  have he : ∀ᵐ x ∂μ, (lower m hm h) x=f x ∧ (upper m hm h) x=g x := by
    filter_upwards [lower_coe m hm h,upper_coe m hm h,Lp.coeFn_add (lower m hm f) (upper m hm g),
      lower_coe m hm f,upper_coe m hm g,(graph_iff m hm f g).mp hfg] with x h0 h1 hs hf hg hfg
    change h x = _ at hs
    rw [h0,h1,hs,Pi.add_apply,hf,hg]
    exact scalar_reconstruction (m x) (f x) (g x) hfg
  refine ⟨h,?_⟩
  apply Prod.ext
  · exact Lp.ext (he.mono (fun _ hx => hx.1))
  · exact Lp.ext (he.mono (fun _ hx => hx.2))

#print axioms radius_positive
#print axioms radius_square
#print axioms lowerWeight_bound
#print axioms upperWeight_bound
#print axioms weights_square
#print axioms lowerWeight_radius
#print axioms upperWeight_radius
#print axioms scalar_reconstruction
#print axioms lower_coe
#print axioms upper_coe
#print axioms graph_iff
#print axioms lift_mem_graph
#print axioms lift_surjective_graph

end
end UnifiedTheory.Audit.KFCausalMultiplierGraphCoordinates
