/- Every measurable complex spectator multiplier has the same maximal
L2 multiplication relation before and after the partial Fourier unitary.
Two bounded multipliers prove the statement without separate component
moment assumptions. -/
import UnifiedTheory.Audit.KFCausalPartialFourierMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalComplexSpectatorFourier
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalPartialFourier (leftFourier)
open KFCausalPartialFourierMultiplier

def denominator {m : ℕ} (v : Block m → ℂ) (x : Block m) : ℝ := 1+‖v x‖
def inverseSymbol {m : ℕ} (v : Block m → ℂ) (x : Block m) : ℂ := (denominator v x:ℂ)⁻¹
def numeratorSymbol {m : ℕ} (v : Block m → ℂ) (x : Block m) : ℂ := inverseSymbol v x*v x

private theorem denominator_positive {m : ℕ} (v : Block m → ℂ) (x : Block m) :
    0 < denominator v x := by unfold denominator; positivity

theorem inverse_measurable {m : ℕ} (v : Block m → ℂ) (hv : Measurable v) :
    Measurable (inverseSymbol v) := by
  unfold inverseSymbol denominator
  fun_prop

theorem inverse_bound {m : ℕ} (v : Block m → ℂ) (x : Block m) :
    ‖inverseSymbol v x‖ ≤ 1 := by
  simp only [inverseSymbol,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (denominator_positive v x)]
  exact inv_le_one_of_one_le₀ (by unfold denominator; linarith [norm_nonneg (v x)])

theorem numerator_measurable {m : ℕ} (v : Block m → ℂ) (hv : Measurable v) :
    Measurable (numeratorSymbol v) := (inverse_measurable v hv).mul hv

theorem numerator_bound {m : ℕ} (v : Block m → ℂ) (x : Block m) :
    ‖numeratorSymbol v x‖ ≤ 1 := by
  simp only [numeratorSymbol,norm_mul,inverseSymbol,norm_inv,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (denominator_positive v x)]
  rw [← div_eq_inv_mul]
  apply (div_le_iff₀ (denominator_positive v x)).mpr
  unfold denominator
  linarith

def inverseAction (n m : ℕ) (v : Block m → ℂ) (hv : Measurable v) :
    ProductHilbert n m →L[ℂ] ProductHilbert n m :=
  rightMultiplier n m (inverseSymbol v) (inverse_measurable v hv) (inverse_bound v)

def numeratorAction (n m : ℕ) (v : Block m → ℂ) (hv : Measurable v) :
    ProductHilbert n m →L[ℂ] ProductHilbert n m :=
  rightMultiplier n m (numeratorSymbol v) (numerator_measurable v hv) (numerator_bound v)

theorem relation_iff_bounded (n m : ℕ) (v : Block m → ℂ) (hv : Measurable v)
    (f g : ProductHilbert n m) :
    (g =ᵐ[volume] fun z => v z.2*f z) ↔ inverseAction n m v hv g = numeratorAction n m v hv f := by
  have hi := rightMultiplier_coe n m (inverseSymbol v) (inverse_measurable v hv) (inverse_bound v) g
  have hn := rightMultiplier_coe n m (numeratorSymbol v) (numerator_measurable v hv) (numerator_bound v) f
  change inverseAction n m v hv g =ᵐ[volume] (fun z => inverseSymbol v z.2*g z) at hi
  change numeratorAction n m v hv f =ᵐ[volume] (fun z => numeratorSymbol v z.2*f z) at hn
  constructor
  · intro he
    apply Lp.ext
    filter_upwards [hi,hn,he] with z hi hn he
    rw [hi,hn,he]
    exact (mul_assoc _ _ _).symm
  · intro he
    have he' : inverseAction n m v hv g =ᵐ[volume] numeratorAction n m v hv f :=
      Filter.Eventually.of_forall (fun z => congrArg (fun f : ProductHilbert n m => f z) he)
    filter_upwards [hi,hn,he'] with z hi hn he
    rw [hi,hn] at he
    have hz : inverseSymbol v z.2 ≠ 0 :=
      inv_ne_zero (Complex.ofReal_ne_zero.mpr (denominator_positive v z.2).ne')
    apply mul_left_cancel₀ hz
    rw [he]
    exact mul_assoc _ _ _

theorem leftFourier_relation_iff (n m : ℕ) (v : Block m → ℂ) (hv : Measurable v)
    (f g : ProductHilbert n m) :
    (leftFourier n m g =ᵐ[volume] fun z => v z.2*(leftFourier n m f) z) ↔
      (g =ᵐ[volume] fun z => v z.2*f z) := by
  rw [relation_iff_bounded n m v hv,relation_iff_bounded n m v hv]
  have hi (u : ProductHilbert n m) :
      leftFourier n m (inverseAction n m v hv u) = inverseAction n m v hv (leftFourier n m u) :=
    leftFourier_commutes _ _ _ _ _ u
  have hn (u : ProductHilbert n m) :
      leftFourier n m (numeratorAction n m v hv u) = numeratorAction n m v hv (leftFourier n m u) :=
    leftFourier_commutes _ _ _ _ _ u
  rw [← hi,← hn]
  exact (leftFourier n m).injective.eq_iff

#print axioms inverse_measurable
#print axioms inverse_bound
#print axioms numerator_measurable
#print axioms numerator_bound
#print axioms relation_iff_bounded
#print axioms leftFourier_relation_iff
end
end UnifiedTheory.Audit.KFCausalComplexSpectatorFourier
