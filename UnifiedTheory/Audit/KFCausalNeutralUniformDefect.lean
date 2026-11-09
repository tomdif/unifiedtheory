/- One universal defect constant on the actual clock strip. This is a
neutral transport-jet bound at fixed clock geometry, not the derivative
of the full clock-dependent joint energy. -/
import UnifiedTheory.Audit.KFCausalNeutralQuarticTransportForms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralUniformDefect
noncomputable section
open MeasureTheory
open KFCausalNeutralLineDomain (Regular family)
open KFCausalNeutralLinePackets (step)
open KFCausalNeutralQuarticFormBound (energy first second)
open KFCausalNeutralQuarticTransportForms (velocity rate acceleration)
open KFCausalNeutralJointCurvatureForm (translated_family_derivative)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalQuarticPlaneDomination (potential)

def defectConstant : ℝ := 4*(18+8*(Real.exp (Real.pi/6))^2)

theorem defectConstant_positive : 0 < defectConstant := by unfold defectConstant; positivity

theorem geometry_bound (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    4*((fieldSlope (scale ε y s))^2+(2*(scale ε y s).im)^2) ≤ defectConstant := by
  have hn : ‖scale ε y s‖ ≤ Real.exp (Real.pi/6) := by
    apply (KFCausalClockFloorRelativeShift.scale_bound ε y s hε hy).trans
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : 0 < 2*ε)).mpr
    nlinarith
  have hs := mul_self_le_mul_self (norm_nonneg _) hn
  rw [← sq,Complex.sq_norm,Complex.normSq_apply] at hs
  unfold fieldSlope defectConstant
  nlinarith [sq_nonneg (3+2*(scale ε y s).re),sq_nonneg (scale ε y s).im]

theorem actual_form_bound (ε h s : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3)
    (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) (hd : ∀ x, HasDerivAt f (g x) x) :
    let r := scale ε (-h/2) s
    (first (2*r.im) (fieldSlope r) f g)^2-defectConstant*(energy f)^2 ≤
      energy f*second (2*r.im) (fieldSlope r) f g := by
  have hc := geometry_bound ε (-h/2) s hε (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)
  have he := KFCausalNeutralQuarticFormBound.curvature_form_bound
    (2*(scale ε (-h/2) s).im) (fieldSlope (scale ε (-h/2) s)) f g hf hg hd
  have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg (energy f))
  dsimp only
  nlinarith

def curve (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (z : ℂ) (η L x v : ℝ) : ℂ := family n β b c P ((x:ℂ)+z+velocity η L*(v:ℂ))

theorem curve_derivative (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (z : ℂ) (η L x v : ℝ) :
    HasDerivAt (curve n β b c P z η L x)
      (velocity η L*curve n β b c (fun i => step β (b i) (P i)) z η L x v) v := by
  have he := (KFCausalNeutralLineDomain.family_derivative n β b c P
    ((x:ℂ)+z+velocity η L*(v:ℂ))).comp (v:ℂ)
    (((hasDerivAt_id (v:ℂ)).const_mul (velocity η L)).const_add ((x:ℂ)+z))
  change HasDerivAt (fun t : ℝ => family n β b c P ((x:ℂ)+z+velocity η L*(t:ℂ)))
    (velocity η L*family n β b c (fun i => step β (b i) (P i)) ((x:ℂ)+z+velocity η L*(v:ℂ))) v
  simpa only [Function.comp_apply,id_eq,mul_one,mul_comm,one_mul] using he.comp_ofReal

theorem pointwise_energy_derivative (n : ℕ) (β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (z : ℂ) (η L x v : ℝ) :
    HasDerivAt (fun t => potential x*‖curve n β b c P z η L x t‖^2)
      (rate η L x (curve n β b c P z η L x v)
        (curve n β b c (fun i => step β (b i) (P i)) z η L x v)) v := by
  have he := (KFCausalNeutralQuarticBoundary.norm_square_derivative
    (curve n β b c P z η L x)
    (fun t => velocity η L*curve n β b c (fun i => step β (b i) (P i)) z η L x t)
    v (curve_derivative n β b c P z η L x v)).const_mul (potential x)
  simpa only [rate,mul_left_comm,mul_assoc] using he

theorem pointwise_rate_derivative (n : ℕ) (β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (z : ℂ) (η L x v : ℝ) :
    HasDerivAt (fun t => rate η L x (curve n β b c P z η L x t)
        (curve n β b c (fun i => step β (b i) (P i)) z η L x t))
      (acceleration η L x (curve n β b c P z η L x v)
        (curve n β b c (fun i => step β (b i) (P i)) z η L x v)
        (curve n β b c (fun i => step β (b i) (step β (b i) (P i))) z η L x v)) v := by
  have h1 := curve_derivative n β b c P z η L x v
  have h2 := (curve_derivative n β b c (fun i => step β (b i) (P i)) z η L x v).const_mul (velocity η L)
  have h2' : HasDerivAt
      (fun t => velocity η L*curve n β b c (fun i => step β (b i) (P i)) z η L x t)
      (velocity η L^2*curve n β b c (fun i => step β (b i) (step β (b i) (P i))) z η L x v) v := by
    simpa only [pow_two,mul_assoc] using h2
  exact (KFCausalNeutralQuarticTransportForms.pair_re_derivative
    (curve n β b c P z η L x)
    (fun t => velocity η L*curve n β b c (fun i => step β (b i) (P i)) z η L x t)
    (fun t => velocity η L^2*curve n β b c (fun i => step β (b i) (step β (b i) (P i))) z η L x t)
    v h1 h2').const_mul (2*potential x)

theorem family_integrated_jet_bound (n : ℕ) (β : ℝ) (hβ : 0 < β) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (z : ℂ) (ε h s : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) :
    let r := scale ε (-h/2) s
    let η := 2*r.im
    let L := fieldSlope r
    let f := fun x : ℝ => family n β b c P ((x:ℂ)+z)
    let g := fun x : ℝ => family n β b c (fun i => step β (b i) (P i)) ((x:ℂ)+z)
    let k := fun x : ℝ => family n β b c (fun i => step β (b i) (step β (b i) (P i))) ((x:ℂ)+z)
    (∫ x, rate η L x (f x) (g x))^2-defectConstant*(energy f)^2 ≤
      energy f*(∫ x, acceleration η L x (f x) (g x) (k x)) := by
  dsimp only
  rw [KFCausalNeutralQuarticTransportForms.rate_integral _ _ _ _
    (KFCausalNeutralLineDomain.family_regular n β hβ b c P z)
    (KFCausalNeutralLineDomain.family_regular n β hβ b c _ z)
    (translated_family_derivative n β b c P z),
    KFCausalNeutralQuarticTransportForms.acceleration_integral _ _ _ _ _
    (KFCausalNeutralLineDomain.family_regular n β hβ b c P z)
    (KFCausalNeutralLineDomain.family_regular n β hβ b c _ z)
    (KFCausalNeutralLineDomain.family_regular n β hβ b c _ z)
    (translated_family_derivative n β b c P z)
    (translated_family_derivative n β b c (fun i => step β (b i) (P i)) z)]
  exact actual_form_bound ε h s hε hb _ _
    (KFCausalNeutralLineDomain.family_regular n β hβ b c P z)
    (KFCausalNeutralLineDomain.family_regular n β hβ b c _ z)
    (translated_family_derivative n β b c P z)

theorem actual_joint_form_bound (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (w : Fin n → ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (z ζ : ℂ)
    (ε h s : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) :
    let r := scale ε (-h/2) s
    let f := fun x : ℝ => family n β b (KFCausalNeutralJointCurvatureForm.coefficients n w c z) P ((x:ℂ)+ζ)
    let g := fun x : ℝ => family n β b (KFCausalNeutralJointCurvatureForm.coefficients n w c z)
      (fun i => step β (b i) (P i)) ((x:ℂ)+ζ)
    (first (2*r.im) (fieldSlope r) f g)^2-defectConstant*(energy f)^2 ≤
      energy f*second (2*r.im) (fieldSlope r) f g := by
  exact actual_form_bound ε h s hε hb _ _
    (KFCausalNeutralLineDomain.family_regular n β hβ b _ P ζ)
    (KFCausalNeutralLineDomain.family_regular n β hβ b _ _ ζ)
    (translated_family_derivative n β b _ P ζ)

#print axioms defectConstant_positive
#print axioms geometry_bound
#print axioms actual_form_bound
#print axioms curve_derivative
#print axioms pointwise_energy_derivative
#print axioms pointwise_rate_derivative
#print axioms family_integrated_jet_bound
#print axioms actual_joint_form_bound
end
end UnifiedTheory.Audit.KFCausalNeutralUniformDefect
