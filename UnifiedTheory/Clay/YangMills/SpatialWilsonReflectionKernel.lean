/- Full spatial Wilson reflection positivity for the actual periodic slice,
including arbitrary nonnegative reflection-invariant plaquette couplings.
The positive kernel is explicitly constructed from the midpoint factors. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonPlaquetteKernels

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonReflectionKernel
noncomputable section
open WilsonTimeSlab SpatialHalfEdgeSplit SpatialPlaquetteCutGeometry
open SpatialWilsonPlaquetteKernels WilsonSingleLinkStaples
open PositiveKernelForm PositiveKernelInsertion

variable (n : ℕ) [NeZero n]

def action (γ : Plaquette n → ℝ) (u : SpatialLinks (2 * n) Q) : ℝ :=
  ∑ p, γ p * defect n p u

def weight (γ : Plaquette n → ℝ) (u : SpatialLinks (2 * n) Q) : ℝ :=
  Real.exp (-action n γ u)

theorem action_reflection (γ : Plaquette n → ℝ)
    (hγ : ∀ p, γ (reflectPlaquette n p) = γ p) (u : SpatialLinks (2 * n) Q) :
    action n γ (reflection n Q u) = action n γ u := by
  unfold action
  calc
    _ = ∑ p, γ (reflectPlaquette n p) * defect n (reflectPlaquette n p) u := by
      apply Finset.sum_congr rfl
      intro p _
      rw [hγ]
      unfold defect
      rw [character_reflection n Q character character_classFunction character_inverse_re]
      rfl
    _ = _ := Equiv.sum_comp (plaquetteEquiv n) (fun p => γ p * defect n p u)

theorem action_swap (γ : Plaquette n → ℝ)
    (hγ : ∀ p, γ (reflectPlaquette n p) = γ p) (a b : Half n Q) :
    action n γ (assemble n Q (b,a)) = action n γ (assemble n Q (a,b)) := by
  rw [assemble_reflection n Q (a,b), action_reflection n γ hγ]

theorem weight_continuous (γ : Plaquette n → ℝ) : Continuous (weight n γ) := by
  unfold weight action
  exact Real.continuous_exp.comp
    (continuous_finset_sum Finset.univ (fun p _ =>
      continuous_const.mul (defect_continuous n p))).neg

def positiveKernel (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p) :
    PositiveKernel (Half n Q) :=
  finiteProduct (fun p => plaquetteKernel n p (γ p) (hγ p))

theorem positiveKernel_value (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p)
    (hr : ∀ p, γ (reflectPlaquette n p) = γ p) (a b : Half n Q) :
    (positiveKernel n γ hγ).value (a,b) = (weight n γ (assemble n Q (a,b)) : ℂ) := by
  rw [positiveKernel, finiteProduct_value]
  simp_rw [plaquetteKernel_value]
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  have he : (∑ p : Plaquette n, -(γ p / 2) *
      (defect n p (assemble n Q (a,b)) + defect n p (assemble n Q (b,a)))) =
      -(1 / 2) * (action n γ (assemble n Q (a,b)) +
        action n γ (assemble n Q (b,a))) := by
    unfold action
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he, action_swap n γ hr]
  ring

theorem positiveKernel_continuous (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p)
    (hr : ∀ p, γ (reflectPlaquette n p) = γ p) :
    Continuous (positiveKernel n γ hγ).value := by
  have hc := Complex.continuous_ofReal.comp
    ((weight_continuous n γ).comp (assemble_continuous n Q))
  exact hc.congr (fun z => (positiveKernel_value n γ hγ hr z.1 z.2).symm)

theorem constant_weight (s : ℝ) (u : SpatialLinks (2 * n) Q) :
    weight n (fun _ => s) u = spatialWeight character (2 * s) 2 u := by
  unfold weight action spatialWeight potential defect
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum]
  congr 1
  ring

/-- The original spatial potential, with coefficient beta/2 for every
plaquette, is an actual positive kernel in the two independent halves. -/
theorem spatialWeight_kernel (β : ℝ) (hβ : 0 ≤ β) (a b : Half n Q) :
    (positiveKernel n (fun _ => β / 2) (fun _ => by positivity)).value (a,b) =
      (spatialWeight character β 2 (assemble n Q (a,b)) : ℂ) := by
  rw [positiveKernel_value n _ _ (fun _ => rfl), constant_weight]
  congr 2
  ring

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonReflectionKernel
