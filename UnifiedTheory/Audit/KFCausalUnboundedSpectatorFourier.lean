/- The maximal multiplication relation for any measurable real spectator
symbol is preserved by the actual partial Fourier unitary. A bounded
resolvent proves both directions without a moment-domain assumption. -/
import UnifiedTheory.Audit.KFCausalPartialFourierMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalUnboundedSpectatorFourier
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalPartialFourier (leftFourier)
open KFCausalPartialFourierMultiplier

def resolvent {m : ℕ} (v : Block m → ℝ) (x : Block m) : ℂ :=
  ((v x : ℂ) + Complex.I)⁻¹

private theorem denominator_ne_zero (t : ℝ) : (t : ℂ) + Complex.I ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp at hi

theorem resolvent_measurable {m : ℕ} (v : Block m → ℝ) (hv : Measurable v) :
    Measurable (resolvent v) := by
  unfold resolvent
  fun_prop

theorem resolvent_bound {m : ℕ} (v : Block m → ℝ) (x : Block m) :
    ‖resolvent v x‖ ≤ 1 := by
  have hh : 1 ≤ ‖(v x : ℂ) + Complex.I‖ := by
    simpa using Complex.abs_im_le_norm ((v x : ℂ) + Complex.I)
  unfold resolvent
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ hh

def resolventAction (n m : ℕ) (v : Block m → ℝ) (hv : Measurable v) :
    ProductHilbert n m →L[ℂ] ProductHilbert n m :=
  rightMultiplier n m (resolvent v) (resolvent_measurable v hv) (resolvent_bound v)

theorem resolventAction_coe (n m : ℕ) (v : Block m → ℝ) (hv : Measurable v)
    (f : ProductHilbert n m) :
    resolventAction n m v hv f =ᵐ[volume] fun z => resolvent v z.2 * f z :=
  rightMultiplier_coe _ _ _ _ _ _

private theorem point_relation (t : ℝ) (f g : ℂ) :
    g = (t : ℂ)*f ↔ ((t : ℂ)+Complex.I)⁻¹*g = f-Complex.I*(((t : ℂ)+Complex.I)⁻¹*f) := by
  have hn := denominator_ne_zero t
  constructor
  · intro he
    rw [he]
    field_simp
    ring
  · intro he
    field_simp at he
    linear_combination he

theorem relation_iff_resolvent (n m : ℕ) (v : Block m → ℝ) (hv : Measurable v)
    (f g : ProductHilbert n m) :
    (g =ᵐ[volume] fun z => (v z.2 : ℂ)*f z) ↔
      resolventAction n m v hv g = f-Complex.I • resolventAction n m v hv f := by
  constructor
  · intro he
    apply Lp.ext
    filter_upwards [he,resolventAction_coe n m v hv g,resolventAction_coe n m v hv f,
      Lp.coeFn_sub f (Complex.I • resolventAction n m v hv f),
      Lp.coeFn_smul Complex.I (resolventAction n m v hv f)] with z hz hg hf hs hi
    rw [hg,hs]
    simp only [Pi.sub_apply]
    rw [hi]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hf]
    exact (point_relation (v z.2) (f z) (g z)).mp hz
  · intro he
    have ht : resolventAction n m v hv g =ᵐ[volume]
        fun z => f z-Complex.I*(resolvent v z.2*f z) := by
      filter_upwards [resolventAction_coe n m v hv f,
        Lp.coeFn_sub f (Complex.I • resolventAction n m v hv f),
        Lp.coeFn_smul Complex.I (resolventAction n m v hv f)] with z hf hs hi
      rw [he,hs]
      simp only [Pi.sub_apply]
      rw [hi]
      simp only [Pi.smul_apply,smul_eq_mul]
      rw [hf]
    filter_upwards [ht,resolventAction_coe n m v hv g] with z hz hg
    rw [hg] at hz
    exact (point_relation (v z.2) (f z) (g z)).mpr hz

theorem leftFourier_relation_iff (n m : ℕ) (v : Block m → ℝ) (hv : Measurable v)
    (f g : ProductHilbert n m) :
    (leftFourier n m g =ᵐ[volume] fun z => (v z.2 : ℂ)*(leftFourier n m f) z) ↔
      (g =ᵐ[volume] fun z => (v z.2 : ℂ)*f z) := by
  rw [relation_iff_resolvent n m v hv,relation_iff_resolvent n m v hv]
  have hc (u : ProductHilbert n m) :
      leftFourier n m (resolventAction n m v hv u) =
        resolventAction n m v hv (leftFourier n m u) :=
    leftFourier_commutes n m _ _ _ u
  rw [← hc,← hc,← map_smul,← map_sub]
  exact (leftFourier n m).injective.eq_iff

#print axioms resolvent_measurable
#print axioms resolvent_bound
#print axioms resolventAction_coe
#print axioms relation_iff_resolvent
#print axioms leftFourier_relation_iff
end
end UnifiedTheory.Audit.KFCausalUnboundedSpectatorFourier
