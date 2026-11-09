/- Exact endpoint representations of the actual linked quadratic circle
energy and defect. Actual Gamma moment convergence gives a large-tilt
nonnegative defect uniformly in both field coefficients. -/
import UnifiedTheory.Audit.KFCausalAngularCosineEndpoint
import UnifiedTheory.Audit.KFCausalAngularMassMomentPolynomial
import UnifiedTheory.Audit.KFCausalAngularMassCircleCompact

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularMassCircleLoss
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
open KFCausalAngularGammaMomentBounds (kernel moment)
open KFCausalAngularMassCircle
open KFCausalAngularMassMomentPolynomial (polynomialKernel normalizedPolynomial)

theorem energy_endpoint (z s l : ℝ) (hz : 0<z) :
    energy z (l*(1-s/z)) l =
      (2*Real.exp z/Real.sqrt (2*z))*(l/z)^2*
        (∫ u in 0..(2*z), kernel 0 z u*(u-s)^2) := by
  have he := KFCausalAngularCosineEndpoint.integral_endpoint z hz
    (fun u : ℝ => (u-s)^2) (by fun_prop)
  calc
    energy z (l*(1-s/z)) l =
        (l/z)^2*(∫ theta in 0..(2*Real.pi),
          Real.exp (-z*Real.cos theta)*(z*(1+Real.cos theta)-s)^2) := by
      unfold energy
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro theta _
      unfold integrand
      field_simp
      ring_nf
    _ = _ := by rw [he]; ac_rfl

theorem normalizer_positive (z : ℝ) (hz : 0<z) : 0<moment 0 z := by
  have he := KFCausalAngularCosineEndpoint.integral_endpoint z hz
    (fun _ : ℝ => (1:ℝ)) continuous_const
  have hp := energy_positive z 1 0 (Or.inl one_ne_zero)
  have hi : energy z 1 0=(2*Real.exp z/Real.sqrt (2*z))*moment 0 z := by
    simpa only [energy,integrand,zero_mul,add_zero,one_pow,mul_one,moment] using he
  rw [hi] at hp
  exact (mul_pos_iff_of_pos_left (by positivity : 0<2*Real.exp z/Real.sqrt (2*z))).mp hp

theorem defect_endpoint (z s l : ℝ) (hz : 0<z) :
    defect z (l*(1-s/z)) l =
      (4*Real.exp z/Real.sqrt (2*z))*(l^2/z)*
        (∫ u in 0..(2*z), polynomialKernel z s u) := by
  let g : ℝ→ℝ := fun u => (1-u/z)*((u-s)^2+(u-s))
  have he := KFCausalAngularCosineEndpoint.integral_endpoint z hz g (by dsimp [g]; fun_prop)
  calc
    defect z (l*(1-s/z)) l =
        (2*l^2/z)*(∫ theta in 0..(2*Real.pi),
          Real.exp (-z*Real.cos theta)*g (z*(1+Real.cos theta))) := by
      unfold defect
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro theta _
      unfold defectIntegrand integrand fieldIntegrand
      dsimp [g]
      field_simp
      ring_nf
    _ = _ := by
      rw [he]
      have hi : (∫ u in 0..(2*z), kernel 0 z u*g u)=
          ∫ u in 0..(2*z), polynomialKernel z s u := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp [g,polynomialKernel]
        ring_nf
      rw [hi]
      ring_nf

theorem defect_normalized (z s l : ℝ) (hz : 0<z) :
    defect z (l*(1-s/z)) l =
      (4*Real.exp z/Real.sqrt (2*z))*(l^2/z)*moment 0 z*normalizedPolynomial z s := by
  rw [defect_endpoint z s l hz]
  unfold normalizedPolynomial
  field_simp [(normalizer_positive z hz).ne']

theorem eventually_nonnegative :
    ∀ᶠ z : ℝ in atTop, ∀ mu l : ℝ, 0≤defect z mu l := by
  filter_upwards [KFCausalAngularMassMomentPolynomial.eventually_coercive,
    eventually_gt_atTop (0:ℝ)] with z hz hz0
  have hn (mu l : ℝ) (hl : l≠0) : 0≤defect z mu l := by
    let s := z*(1-mu/l)
    have hm : l*(1-s/z)=mu := by dsimp [s]; field_simp; ring_nf
    rw [← hm,defect_normalized z s l hz0]
    have hp : 0≤normalizedPolynomial z s :=
      (by positivity : (0:ℝ)≤(1+s^2)/24).trans (hz.2 s)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hz.1.le) hp
  intro mu l
  by_cases hl : l=0
  · subst l
    have hc : Continuous (fun l : ℝ => defect z mu l) :=
      defect_continuous.comp (by fun_prop : Continuous (fun l : ℝ => (z,mu,l)))
    apply ge_of_tendsto (f := fun l : ℝ => defect z mu l)
      (x := 𝓝[>] (0:ℝ)) ((hc.tendsto 0).mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with l hl
    exact hn mu l (ne_of_gt hl)
  · exact hn mu l hl

theorem nonnegative_tilt_loss :
    ∃ C : ℝ, 0≤C ∧ ∀ z mu l : ℝ, 0≤z →
      0≤defect z mu l+C*energy z mu l := by
  obtain ⟨Z,hZ⟩ := (eventually_atTop.1 eventually_nonnegative)
  obtain ⟨C,hC,hbound⟩ := KFCausalAngularMassCircleCompact.compact_loss
    (max 0 Z) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro z mu l hz
  by_cases h : z≤max 0 Z
  · exact hbound z mu l ⟨hz,h⟩
  · exact add_nonneg (hZ z ((le_max_right 0 Z).trans (le_of_not_ge h)) mu l)
      (mul_nonneg hC (energy_nonnegative z mu l))

private theorem cosine_reflection (f : ℝ→ℝ) (hf : Continuous f) :
    (∫ theta in 0..(2*Real.pi), f (-Real.cos theta)) =
      ∫ theta in 0..(2*Real.pi), f (Real.cos theta) := by
  rw [KFCausalAngularCosineEndpoint.cosine_integral (fun x => f (-x)) (hf.comp continuous_neg),
    KFCausalAngularCosineEndpoint.cosine_integral f hf]
  have he := intervalIntegral.integral_comp_neg (a := (-1:ℝ)) (b := (1:ℝ))
    (fun x : ℝ => f x*(Real.sqrt (1-x^2))⁻¹)
  simp only [neg_neg,neg_sq] at he
  exact congrArg (fun x : ℝ => 2*x) he

theorem energy_reflection (z mu l : ℝ) : energy (-z) mu l=energy z mu (-l) := by
  let f : ℝ→ℝ := fun x => Real.exp (-z*x)*(mu-l*x)^2
  have he := cosine_reflection f (by dsimp [f]; fun_prop)
  convert he using 1 <;> apply intervalIntegral.integral_congr <;> intro theta _ <;>
    dsimp [energy,integrand,f] <;> congr 1 <;> ring_nf

theorem defect_reflection (z mu l : ℝ) : defect (-z) mu l=defect z mu (-l) := by
  let f : ℝ→ℝ := fun x => (-2*z*x)*Real.exp (-z*x)*(mu-l*x)^2+
    l*Real.exp (-z*x)*(2*x*(mu-l*x))
  have he := cosine_reflection f (by dsimp [f]; fun_prop)
  convert he using 1 <;> apply intervalIntegral.integral_congr <;> intro theta _ <;>
    dsimp [defect,defectIntegrand,integrand,fieldIntegrand,f] <;>
    simp only [neg_mul,mul_neg,neg_neg] <;> ring_nf

theorem global_loss :
    ∃ C : ℝ, 0≤C ∧ ∀ z mu l : ℝ,
      0≤defect z mu l+C*energy z mu l := by
  obtain ⟨C,hC,hbound⟩ := nonnegative_tilt_loss
  refine ⟨C,hC,?_⟩
  intro z mu l
  by_cases hz : 0≤z
  · exact hbound z mu l hz
  · have hb := hbound (-z) mu (-l) (by linarith)
    simpa only [energy_reflection,defect_reflection,neg_neg] using hb

theorem global_linked_loss :
    ∃ C : ℝ, 0≤C ∧ ∀ z mu l : ℝ,
      0≤2*tilt z mu l-l*deriv (fun x => energy z mu x) l+C*energy z mu l := by
  obtain ⟨C,hC,hbound⟩ := global_loss
  refine ⟨C,hC,?_⟩
  intro z mu l
  rw [(field_derivative z mu l).deriv,← defect_eq]
  exact hbound z mu l

#print axioms energy_endpoint
#print axioms normalizer_positive
#print axioms defect_endpoint
#print axioms defect_normalized
#print axioms eventually_nonnegative
#print axioms nonnegative_tilt_loss
#print axioms energy_reflection
#print axioms defect_reflection
#print axioms global_loss
#print axioms global_linked_loss
end
end UnifiedTheory.Audit.KFCausalAngularMassCircleLoss
