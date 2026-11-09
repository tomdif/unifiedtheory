/- Circular polynomial Gaussian states for the actual anisotropic charged
coordinates z = c*k + i*y. The two widths are b*c^2 and b. -/
import UnifiedTheory.Audit.KFCausalCircularPolynomialBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalScaledCircularPolynomials
noncomputable section
open MeasureTheory MvPolynomial Module
open KFCausalEuclideanProductCoordinates
open KFCausalPlanePolynomialGaussian (Poly state state_injective state_dense_range packet)
open KFCausalCircularPolynomialBasis (exponent)

def scale (c : ℝ) : Poly →ₐ[ℂ] Poly := aeval ![C (c:ℂ)*X 0,X 1]

theorem scale_comp (c d : ℝ) : (scale c).comp (scale d) = scale (c*d) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [scale,AlgHom.comp_apply,Complex.ofReal_mul,map_mul]
  ring

theorem scale_one : scale 1 = AlgHom.id ℂ Poly := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [scale]

def scaleEquiv (c : ℝ) (hc : c ≠ 0) : Poly ≃ₐ[ℂ] Poly :=
  AlgEquiv.ofAlgHom (scale c) (scale c⁻¹)
    (by rw [scale_comp,mul_inv_cancel₀ hc,scale_one])
    (by rw [scale_comp,inv_mul_cancel₀ hc,scale_one])

theorem eval_scale (c : ℝ) (P : Poly) (x : Fin 2 → ℂ) :
    eval x (scale c P) = eval ![(c:ℂ)*x 0,x 1] P := by
  induction P using MvPolynomial.induction_on with
  | C z => simp [scale]
  | add P Q hp hq => simp only [map_add,hp,hq]
  | mul_X P i hp =>
    rw [map_mul,eval_mul,hp,eval_mul,eval_X]
    fin_cases i <;> simp [scale]

def polynomialBasis (c : ℝ) (hc : c ≠ 0) : Basis ℕ ℂ Poly :=
  KFCausalCircularPolynomialBasis.polynomialBasis.map (scaleEquiv c hc).toLinearEquiv

def coordinate (c : ℝ) (x : Block 2) : ℂ := (c:ℂ)*(x 0:ℂ)+Complex.I*(x 1:ℂ)

theorem polynomialBasis_eval (c : ℝ) (hc : c ≠ 0) (n : ℕ) (x : Block 2) :
    eval (fun i => (x i:ℂ)) (polynomialBasis c hc n) =
      coordinate c x^(exponent n 0)*star (coordinate c x)^(exponent n 1) := by
  change eval (fun i => (x i:ℂ))
    (scale c (KFCausalCircularPolynomialBasis.polynomialBasis n)) = _
  rw [eval_scale]
  have he := KFCausalCircularPolynomialBasis.polynomialBasis_eval n
    (WithLp.toLp 2 ![c*x 0,x 1])
  have hv : (fun i : Fin 2 => (![c*x 0,x 1] i:ℂ)) = ![(c:ℂ)*(x 0:ℂ),(x 1:ℂ)] := by
    funext i
    fin_cases i <;> simp
  simpa only [KFCausalCircularPolynomialBasis.coordinate,coordinate,WithLp.toLp_ofLp,
    Matrix.cons_val_zero,Matrix.cons_val_one,hv,Complex.ofReal_mul] using he

theorem width_positive (c b : ℝ) (hc : c ≠ 0) (hb : 0 < b) : 0 < b*c^2 :=
  mul_pos hb (sq_pos_of_ne_zero hc)

def states (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b) (n : ℕ) : BlockHilbert 2 :=
  state (b*c^2) b (width_positive c b hc hb) hb (polynomialBasis c hc n)

theorem states_independent (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b) :
    LinearIndependent ℂ (states c hc b hb) :=
  (polynomialBasis c hc).linearIndependent.map' (state (b*c^2) b (width_positive c b hc hb) hb)
    (LinearMap.ker_eq_bot.mpr (state_injective _ _ _ _))

theorem states_dense (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b) :
    (Submodule.span ℂ (Set.range (states c hc b hb))).topologicalClosure = ⊤ := by
  have he : Submodule.span ℂ (Set.range (states c hc b hb)) =
      (state (b*c^2) b (width_positive c b hc hb) hb).range := by
    rw [show Set.range (states c hc b hb) =
        (state (b*c^2) b (width_positive c b hc hb) hb) '' Set.range (polynomialBasis c hc) from
      Set.range_comp _ _]
    rw [← Submodule.map_span,(polynomialBasis c hc).span_eq,Submodule.map_top]
  rw [he,state_dense_range]

def weight (c b : ℝ) (x : Block 2) : ℂ :=
  KFCausalGaussianSliceDomain.gaussian (b*c^2) (x 0)*
    KFCausalGaussianSliceDomain.gaussian b (x 1)

theorem states_coe (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b) (n : ℕ) :
    states c hc b hb n =ᵐ[volume] fun x =>
      coordinate c x^(exponent n 0)*star (coordinate c x)^(exponent n 1)*weight c b x := by
  filter_upwards [KFCausalPlanePolynomialGaussian.state_coe _ _
    (width_positive c b hc hb) hb (polynomialBasis c hc n)] with x hx
  simpa only [packet,polynomialBasis_eval,weight,Complex.ofReal_mul,Complex.ofReal_pow] using hx

#print axioms scaleEquiv
#print axioms states_independent
#print axioms states_dense
#print axioms states_coe
end
end UnifiedTheory.Audit.KFCausalScaledCircularPolynomials
