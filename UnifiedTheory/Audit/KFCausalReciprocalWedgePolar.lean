/- Nonnegative change of variables through polar radius squared and the
Laplace wedge. Tonelli identities avoid assuming integrability of a
target representation before it has been identified. -/
import UnifiedTheory.Audit.KFCausalReciprocalWedgeMeasure
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.JacobianOneDim

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalReciprocalWedgePolar
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalReciprocalWedgeGeometry (chart wedge)
open KFCausalReciprocalWedgeMeasure (linear quadrant)
open KFCausalReciprocalWedgePrefactor (jacobian)

private theorem square_image : (fun x : ℝ => x^2) '' Ioi 0 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change 0 < y at hy
    change 0 < y^2
    positivity
  · intro hx
    change 0 < x at hx
    exact ⟨Real.sqrt x,Real.sqrt_pos.mpr hx,Real.sq_sqrt hx.le⟩

theorem lintegral_square (g : ℝ → ℝ≥0∞) :
    (∫⁻ ρ : ℝ in Ioi 0, ENNReal.ofReal ρ*g (ρ^2)) =
      ENNReal.ofReal (1/2:ℝ)*∫⁻ x : ℝ in Ioi 0, g x := by
  have hd : ∀ x ∈ Ioi (0:ℝ), HasDerivWithinAt (fun y : ℝ => y^2) (2*x) (Ioi 0) x := by
    intro x _
    convert ((hasDerivAt_id x).pow 2).hasDerivWithinAt using 1
    simp
  have hi : InjOn (fun x : ℝ => x^2) (Ioi 0) := by
    intro x hx y hy he
    change 0 < x at hx
    change 0 < y at hy
    change x^2 = y^2 at he
    nlinarith
  have he := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hi g
  rw [square_image] at he
  rw [he,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  have hx0 : 0 < x := hx
  rw [abs_of_pos (by positivity : 0 < 2*x),ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [← mul_assoc,← mul_assoc,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  norm_num

theorem lintegral_polar_square (f : ℝ × ℝ → ℝ≥0∞) (g : ℝ → ℝ → ℝ≥0∞)
    (hg : Measurable (Function.uncurry g))
    (he : ∀ ρ θ : ℝ, f (ρ*Real.cos θ,ρ*Real.sin θ) = g (ρ^2) θ) :
    (∫⁻ p, f p) = ENNReal.ofReal (1/2:ℝ)*
      ∫⁻ θ : ℝ in Ioo (-Real.pi) Real.pi, ∫⁻ x : ℝ in Ioi 0, g x θ := by
  rw [← lintegral_comp_polarCoord_symm]
  change (∫⁻ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1*f (p.1*Real.cos p.2,p.1*Real.sin p.2)) = _
  simp_rw [he]
  rw [Measure.volume_eq_prod ℝ ℝ,setLIntegral_prod_symm
    (fun p : ℝ × ℝ => ENNReal.ofReal p.1*g (p.1^2) p.2) (by fun_prop)]
  have hsq (θ : ℝ) : (∫⁻ ρ : ℝ in Ioi 0, ENNReal.ofReal ρ*g (ρ^2) θ) =
      ENNReal.ofReal (1/2:ℝ)*∫⁻ x : ℝ in Ioi 0, g x θ := lintegral_square (fun x => g x θ)
  simp_rw [hsq]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem lintegral_quadrant (α : ℝ) (r : ℂ) (hα : α ≠ 0) (hA : area r ≠ 0)
    (ha : r.re ≠ 0) (hb : r.im ≠ 0) (f : ℂ → ℝ≥0∞) :
    (∫⁻ z in quadrant, f (linear α r z)) = ENNReal.ofReal (jacobian α r)*∫⁻ z in wedge α r, f z := by
  have hm := (KFCausalReciprocalWedgeMeasure.equivalence α r hα hA ha hb).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding.lintegral_map
    (μ := volume) ((wedge α r).indicator f)
  change (∫⁻ z, (wedge α r).indicator f z ∂Measure.map (linear α r) volume) =
    ∫⁻ z, (wedge α r).indicator f (linear α r z) at hm
  rw [KFCausalReciprocalWedgeMeasure.map_volume α r hα hA ha hb,lintegral_smul_measure] at hm
  simp only [smul_eq_mul,lintegral_indicator (KFCausalReciprocalWedgeMeasure.wedge_measurable α r),
    ← indicator_comp_right,KFCausalReciprocalWedgeMeasure.preimage_wedge α r hα hA ha hb,
    lintegral_indicator KFCausalReciprocalWedgeMeasure.quadrant_measurable] at hm
  exact hm.symm

theorem lintegral_pair_chart (α : ℝ) (r : ℂ) (hα : α ≠ 0) (hA : area r ≠ 0)
    (ha : r.re ≠ 0) (hb : r.im ≠ 0) (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : ℝ in Ioi 0, ∫⁻ y : ℝ in Ioi 0, f (chart α r x y)) =
      ENNReal.ofReal (jacobian α r)*∫⁻ z in wedge α r, f z := by
  have hm := Complex.volume_preserving_equiv_real_prod.symm.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding (fun z => f (linear α r z)) quadrant
  change (∫⁻ p : ℝ × ℝ in Ici 0 ×ˢ Ici 0, f (chart α r p.1 p.2)) =
    ∫⁻ z in quadrant, f (linear α r z) at hm
  rw [Measure.volume_eq_prod ℝ ℝ,setLIntegral_prod
    (fun p : ℝ × ℝ => f (chart α r p.1 p.2)) (by unfold chart; fun_prop)] at hm
  simp only [restrict_Ioi_eq_restrict_Ici]
  rw [hm,lintegral_quadrant α r hα hA ha hb]

#print axioms lintegral_square
#print axioms lintegral_polar_square
#print axioms lintegral_quadrant
#print axioms lintegral_pair_chart
end
end UnifiedTheory.Audit.KFCausalReciprocalWedgePolar
