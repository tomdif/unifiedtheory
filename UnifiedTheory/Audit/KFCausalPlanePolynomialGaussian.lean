/- Actual two-dimensional polynomial Gaussian states, with injective
polynomial embedding and no integrability assumption on the polynomial. -/
import UnifiedTheory.Audit.KFCausalHermiteProductBasis
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPlanePolynomialGaussian
noncomputable section
open MeasureTheory MvPolynomial
open KFCausalEuclideanProductCoordinates
open KFCausalGaussianSliceDomain (gaussian)
open KFCausalGaussianQuadraticFourier (moment moment_memLp)

abbrev Poly := MvPolynomial (Fin 2) ℂ

def splitPlane : Block 2 ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem splitPlane_preserves : MeasurePreserving splitPlane :=
  (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

def packet (a b : ℝ) (P : Poly) (x : Block 2) : ℂ :=
  eval (fun i => (x i:ℂ)) P * (gaussian a (x 0) * gaussian b (x 1))

theorem packet_continuous (a b : ℝ) (P : Poly) : Continuous (packet a b P) := by
  unfold packet gaussian
  exact ((MvPolynomial.continuous_eval P).comp (by fun_prop)).mul (by fun_prop)

theorem monomial_memLp (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (e : Fin 2 →₀ ℕ) :
    MemLp (packet a b (monomial e 1)) 2 volume := by
  have hm := (KFCausalL2TensorEmbedding.product_memLp volume volume
    (moment a (e 0)) (moment b (e 1)) (moment_memLp a ha _) (moment_memLp b hb _)).comp_measurePreserving
      splitPlane_preserves
  convert hm using 1
  funext x
  simp only [packet,eval_monomial,one_mul,
    Function.comp_apply,splitPlane,MeasurableEquiv.trans_apply]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),Fin.prod_univ_two]
  change (x 0:ℂ)^(e 0)*(x 1:ℂ)^(e 1)*(gaussian a (x 0)*gaussian b (x 1)) =
    moment a (e 0) (x 0)*moment b (e 1) (x 1)
  unfold moment
  ring

def monomialState (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (e : Fin 2 →₀ ℕ) : BlockHilbert 2 :=
  (monomial_memLp a b ha hb e).toLp (packet a b (monomial e 1))

def state (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Poly →ₗ[ℂ] BlockHilbert 2 :=
  (MvPolynomial.basisMonomials (Fin 2) ℂ).constr ℂ (monomialState a b ha hb)

theorem state_monomial (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (e : Fin 2 →₀ ℕ) :
    state a b ha hb (monomial e 1) = monomialState a b ha hb e := by
  simpa only [MvPolynomial.coe_basisMonomials] using
    (MvPolynomial.basisMonomials (Fin 2) ℂ).constr_basis ℂ (monomialState a b ha hb) e

theorem state_coe (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (P : Poly) : state a b ha hb P =ᵐ[volume] packet a b P := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hp hq =>
    rw [map_add]
    filter_upwards [Lp.coeFn_add (state a b ha hb P) (state a b ha hb Q),hp,hq] with x hx hp hq
    simpa only [Pi.add_apply,hp,hq,packet,eval_add,add_mul] using hx
  | monomial e c =>
    have he : monomial e c = c • monomial e (1:ℂ) := by
      rw [smul_monomial,smul_eq_mul,mul_one]
    rw [he,map_smul,state_monomial]
    filter_upwards [Lp.coeFn_smul c (monomialState a b ha hb e),
      (monomial_memLp a b ha hb e).coeFn_toLp] with x hx hm
    simpa only [Pi.smul_apply,smul_eq_mul,monomialState,hm,packet,smul_eval,mul_assoc] using hx

theorem packet_memLp (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (P : Poly) : MemLp (packet a b P) 2 volume :=
  (memLp_congr_ae (state_coe a b ha hb P)).mp (Lp.memLp (state a b ha hb P))

theorem state_injective (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Function.Injective (state a b ha hb) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro P hp
  have hae : packet a b P =ᵐ[volume] 0 :=
    (state_coe a b ha hb P).symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hp)
  have he : packet a b P = 0 := Measure.eq_of_ae_eq hae (packet_continuous a b P) continuous_zero
  apply MvPolynomial.funext_set (fun _ : Fin 2 => Set.range Complex.ofReal)
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro x hx
  have hxr (i : Fin 2) : ∃ y : ℝ, (y:ℂ) = x i := hx i (Set.mem_univ i)
  choose y hy using hxr
  have hz := congrFun he (WithLp.toLp 2 y)
  change eval (fun i => (y i:ℂ)) P * (gaussian a (y 0)*gaussian b (y 1)) = 0 at hz
  rw [show (fun i => (y i:ℂ)) = x from funext hy] at hz
  simpa only [eval_zero] using (mul_eq_zero.mp hz).resolve_right
    (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))

open KFCausalHermiteProductBasis
open KFCausalMeasureUnitaryPullback
open KFCausalL2TensorEmbedding (productState productState_coe)

def separate : Block 2 ≃ᵐ (Block 1 × Block 1) :=
  (mergeIsometry 1 1).symm.toMeasurableEquiv.trans (split 1 1)

theorem separate_preserves : MeasurePreserving separate :=
  (split_preserves_volume 1 1).comp (mergeIsometry 1 1).symm.measurePreserving

theorem join_coe (f : ProductHilbert 1 1) : joinCoordinates 1 1 f =ᵐ[volume] f ∘ separate := by
  filter_upwards [unitaryPullback_symm_coe (mergeIsometry 1 1).toMeasurableEquiv
      (mergeIsometry 1 1).measurePreserving (coordinates 1 1 f),
    (mergeIsometry 1 1).symm.measurePreserving.quasiMeasurePreserving.ae
      (coordinates_coe 1 1 f)] with x hx hy
  exact hx.trans hy

theorem scalar_product_coe (f g : KFCausalGaussianPolynomialTotality.ScalarHilbert) :
    joinCoordinates 1 1 (productState volume volume (lineCoordinates f) (lineCoordinates g))
      =ᵐ[volume] fun x => f (x 0)*g (x 1) := by
  have hp : productState volume volume (lineCoordinates f) (lineCoordinates g) =ᵐ[volume]
      fun y : Block 1 × Block 1 => f (y.1 0)*g (y.2 0) := by
    filter_upwards [productState_coe volume volume (lineCoordinates f) (lineCoordinates g),
      Measure.quasiMeasurePreserving_fst.ae
        (unitaryPullback_coe lineIsometry.toMeasurableEquiv lineIsometry.measurePreserving f),
      Measure.quasiMeasurePreserving_snd.ae
        (unitaryPullback_coe lineIsometry.toMeasurableEquiv lineIsometry.measurePreserving g)]
      with y hy hf hg
    exact hy.trans (congrArg₂ (· * ·) hf hg)
  filter_upwards [join_coe (productState volume volume (lineCoordinates f) (lineCoordinates g)),
    separate_preserves.quasiMeasurePreserving.ae hp] with x hx hy
  exact hx.trans hy

def separable (P Q : Polynomial ℂ) : Poly :=
  Polynomial.aeval (X 0) P * Polynomial.aeval (X 1) Q

theorem eval_univariate (P : Polynomial ℂ) (i : Fin 2) (x : Fin 2 → ℂ) :
    eval x (Polynomial.aeval (X i : Poly) P) = P.eval (x i) := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp only [map_add,Polynomial.eval_add,hp,hq]
  | monomial n c => simp [Polynomial.aeval_monomial,Polynomial.eval_monomial]

theorem separable_state (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (P Q : Polynomial ℂ) :
    state a b ha hb (separable P Q) = joinCoordinates 1 1
      (productState volume volume
        (lineCoordinates (KFCausalGaussianPolynomialTotality.polynomialState a ha P))
        (lineCoordinates (KFCausalGaussianPolynomialTotality.polynomialState b hb Q))) := by
  have hP := (Measure.quasiMeasurePreserving_fst.comp
    splitPlane_preserves.quasiMeasurePreserving).ae
      (KFCausalGaussianPolynomialTotality.polynomialState_coe a ha P)
  have hQ := (Measure.quasiMeasurePreserving_snd.comp
    splitPlane_preserves.quasiMeasurePreserving).ae
      (KFCausalGaussianPolynomialTotality.polynomialState_coe b hb Q)
  apply Lp.ext
  filter_upwards [state_coe a b ha hb (separable P Q),scalar_product_coe
    (KFCausalGaussianPolynomialTotality.polynomialState a ha P)
    (KFCausalGaussianPolynomialTotality.polynomialState b hb Q),hP,hQ] with x hx hy hp hq
  change KFCausalGaussianPolynomialTotality.polynomialState a ha P (x 0) =
    P.eval (x 0:ℂ)*gaussian a (x 0) at hp
  change KFCausalGaussianPolynomialTotality.polynomialState b hb Q (x 1) =
    Q.eval (x 1:ℂ)*gaussian b (x 1) at hq
  rw [hx,hy,hp,hq]
  simp only [packet,separable,eval_mul,eval_univariate]
  ring

theorem planeBasis_mem_range (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (i : ℕ × ℕ) :
    planeBasis a b ha hb i ∈ (state a b ha hb).range := by
  let P (w : ℝ) (hw : 0 < w) (n : ℕ) : Polynomial ℂ :=
    ((‖KFCausalHermiteL2Completeness.state w hw w 0 n‖⁻¹:ℝ):ℂ) •
      KFCausalNeutralHermiteDomain.multiplier w 0 n
  have he (w : ℝ) (hw : 0 < w) (n : ℕ) : lineBasis w hw n = lineCoordinates
      (KFCausalGaussianPolynomialTotality.polynomialState w hw (P w hw n)) := by
    rw [lineBasis,mapBasis_apply,KFCausalHermiteHilbertBasis.basis_apply]
    simp only [P,map_smul,KFCausalHermiteHilbertBasis.normalizedState,
      KFCausalHermiteL2Completeness.state]
  rcases i with ⟨i,j⟩
  rw [planeBasis_apply,he,he,← separable_state]
  exact LinearMap.mem_range_self _ _

theorem state_dense_range (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (state a b ha hb).range.topologicalClosure = ⊤ :=
  KFCausalProductHilbertExpansion.basis_closed_total (planeBasis a b ha hb) _
    (Submodule.isClosed_topologicalClosure _) (fun i =>
      Submodule.le_topologicalClosure _ (planeBasis_mem_range a b ha hb i))

#print axioms packet_memLp
#print axioms state_coe
#print axioms state_injective
#print axioms state_dense_range
end
end UnifiedTheory.Audit.KFCausalPlanePolynomialGaussian
