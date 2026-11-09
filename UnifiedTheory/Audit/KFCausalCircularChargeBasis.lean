/- A complete circular Gaussian basis for one actual charged plane.
Its charge is the difference of its two nonnegative polynomial degrees. -/
import UnifiedTheory.Audit.KFCausalScaledCircularPolynomials
import UnifiedTheory.Audit.KFCausalGramSchmidtEigenvectors
import UnifiedTheory.Audit.KFCausalChargedSpectatorCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCircularChargeBasis
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalMeasureUnitaryPullback
open KFCausalScaledCircularPolynomials (coordinate weight states states_coe states_independent states_dense)
open KFCausalCircularPolynomialBasis (exponent)

def rotate (θ : ℝ) (x : Block 2) : Block 2 := WithLp.toLp 2
  ![Real.cos θ*x 0-Real.sin θ*x 1,Real.sin θ*x 0+Real.cos θ*x 1]

theorem rotate_reverse (θ : ℝ) (x : Block 2) : rotate (-θ) (rotate θ x) = x := by
  ext i
  fin_cases i <;> simp [rotate]
  · linear_combination (x 0)*(Real.sin_sq_add_cos_sq θ)
  · linear_combination (x 1)*(Real.sin_sq_add_cos_sq θ)

def rotationEquiv (θ : ℝ) : Block 2 ≃ₗ[ℝ] Block 2 where
  toFun := rotate θ
  invFun := rotate (-θ)
  left_inv := rotate_reverse θ
  right_inv x := by simpa only [neg_neg] using rotate_reverse (-θ) x
  map_add' x y := by ext i; fin_cases i <;> simp [rotate] <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp [rotate] <;> ring

theorem rotation_inner (θ : ℝ) (x y : Block 2) :
    inner ℝ (rotationEquiv θ x) (rotationEquiv θ y) = inner ℝ x y := by
  simpa [PiLp.inner_apply,Fin.sum_univ_succ,rotationEquiv,rotate,RCLike.inner_apply] using
    KFCausalPairedRotation.pair_inner θ (y 0) (y 1) (x 0) (x 1)

def rotationIsometry (θ : ℝ) : Block 2 ≃ₗᵢ[ℝ] Block 2 where
  toLinearEquiv := rotationEquiv θ
  norm_map' := ((rotationEquiv θ).toLinearMap.isometryOfInner (rotation_inner θ)).norm_map

def dilate (c : ℝ) (x : Block 2) : Block 2 := WithLp.toLp 2 ![c*x 0,x 1]

def dilationEquiv (c : ℝ) (hc : c ≠ 0) : Block 2 ≃ₗ[ℝ] Block 2 where
  toFun := dilate c
  invFun := dilate c⁻¹
  left_inv x := by ext i; fin_cases i <;> simp [dilate,hc]
  right_inv x := by ext i; fin_cases i <;> simp [dilate,hc]
  map_add' x y := by ext i; fin_cases i <;> simp [dilate,mul_add]
  map_smul' d x := by ext i; fin_cases i <;> simp [dilate] <;> ring

def flow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) : Block 2 ≃ᵐ Block 2 :=
  KFCausalHaarConjugation.conjugate (dilationEquiv c hc).toContinuousLinearEquiv
    (rotationIsometry θ).toMeasurableEquiv

theorem flow_apply (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Block 2) :
    flow c hc θ x = dilate c⁻¹ (rotate θ (dilate c x)) := rfl

theorem flow_preserves (c : ℝ) (hc : c ≠ 0) (θ : ℝ) : MeasurePreserving (flow c hc θ) :=
  KFCausalHaarConjugation.conjugate_preserves volume _ _ (rotationIsometry θ).measurePreserving

def action (c : ℝ) (hc : c ≠ 0) (θ : ℝ) : BlockHilbert 2 ≃ₗᵢ[ℂ] BlockHilbert 2 :=
  unitaryPullback (flow c hc θ) (flow_preserves c hc θ)

theorem action_coe (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (f : BlockHilbert 2) :
    action c hc θ f =ᵐ[volume] f ∘ flow c hc θ := unitaryPullback_coe _ _ _

theorem coordinate_flow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Block 2) :
    coordinate c (flow c hc θ x) = Complex.exp ((θ:ℂ)*Complex.I)*coordinate c x := by
  apply Complex.ext <;>
    simp [coordinate,flow_apply,dilate,rotate,Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im,Complex.cos_ofReal_re,Complex.sin_ofReal_re] <;>
    field_simp <;> ring

theorem weight_normSq (c b : ℝ) (x : Block 2) :
    weight c b x = Complex.exp (-(b:ℂ)*(Complex.normSq (coordinate c x):ℂ)) := by
  rw [weight,KFCausalGaussianSliceDomain.gaussian,KFCausalGaussianSliceDomain.gaussian,
    ← Complex.exp_add]
  congr 1
  simp [coordinate,Complex.normSq_apply]
  ring

theorem weight_flow (c : ℝ) (hc : c ≠ 0) (b θ : ℝ) (x : Block 2) :
    weight c b (flow c hc θ x) = weight c b x := by
  rw [weight_normSq,weight_normSq,coordinate_flow]
  simp only [Complex.normSq_eq_norm_sq,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]

def charge (n : ℕ) : ℤ := (exponent n 0:ℤ)-(exponent n 1:ℤ)
def phase (q : ℤ) (θ : ℝ) : ℂ := Complex.exp (Complex.ofReal ((q:ℝ)*θ)*Complex.I)

theorem phase_unit (q : ℤ) (θ : ℝ) : phase q θ * star (phase q θ) = 1 := by
  rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  rw [phase,Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem phase_add (q r : ℤ) (θ : ℝ) : phase (q+r) θ = phase q θ*phase r θ := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem charge_pair (n m : ℕ) : charge (Nat.pair n m) = (n:ℤ)-(m:ℤ) := by
  simp [charge,KFCausalCircularPolynomialBasis.exponent,Nat.unpair_pair]

theorem phase_powers (n : ℕ) (θ : ℝ) :
    Complex.exp ((θ:ℂ)*Complex.I)^(exponent n 0)*
      star (Complex.exp ((θ:ℂ)*Complex.I))^(exponent n 1) = phase (charge n) θ := by
  rw [Complex.star_def,← Complex.exp_conj]
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  rw [← Complex.exp_nat_mul,← Complex.exp_nat_mul,← Complex.exp_add]
  unfold phase charge
  congr 1
  push_cast
  ring

theorem states_action (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b) (θ : ℝ) (n : ℕ) :
    action c hc θ (states c hc b hb n) = phase (charge n) θ • states c hc b hb n := by
  apply Lp.ext
  filter_upwards [action_coe c hc θ (states c hc b hb n),
    (flow_preserves c hc θ).quasiMeasurePreserving.ae (states_coe c hc b hb n),
    states_coe c hc b hb n,Lp.coeFn_smul (phase (charge n) θ) (states c hc b hb n)]
    with x hx hy hz hw
  rw [hx]
  simp only [Function.comp_apply]
  rw [hy,hw]
  simp only [Pi.smul_apply,smul_eq_mul,hz,coordinate_flow,weight_flow]
  calc
    _ = (Complex.exp ((θ:ℂ)*Complex.I)^(exponent n 0)*
        star (Complex.exp ((θ:ℂ)*Complex.I))^(exponent n 1))*
        (coordinate c x^(exponent n 0)*star (coordinate c x)^(exponent n 1)*weight c b x) := by
      simp only [mul_pow,star_mul]
      ring
    _ = _ := by rw [phase_powers]

def basis (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b) : HilbertBasis ℕ ℂ (BlockHilbert 2) :=
  KFCausalGramSchmidtEigenvectors.basis (states c hc b hb)
    (states_independent c hc b hb) (states_dense c hc b hb)

theorem basis_action (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b) (θ : ℝ) (n : ℕ) :
    action c hc θ (basis c hc b hb n) = phase (charge n) θ • basis c hc b hb n :=
  KFCausalGramSchmidtEigenvectors.basis_eigen (states c hc b hb)
    (states_independent c hc b hb) (states_dense c hc b hb)
    (action c hc θ) (fun n => phase (charge n) θ) (fun n => phase_unit (charge n) θ)
    (states_action c hc b hb θ) n

#print axioms flow_preserves
#print axioms coordinate_flow
#print axioms states_action
#print axioms basis
#print axioms basis_action
end
end UnifiedTheory.Audit.KFCausalCircularChargeBasis
