/- The physical reciprocal Gram form is the positive wedge integral.
The radial and Laplace integrations are exchanged by Tonelli, with all
Jacobian and quartic coefficients retained. -/
import UnifiedTheory.Audit.KFCausalReciprocalWedgeCartesian
import UnifiedTheory.Audit.KFCausalReciprocalWedgePolar
import UnifiedTheory.Audit.KFCausalReciprocalWedgeWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalReciprocalWedgeRepresentation
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open KFCausalReciprocalWedgeCartesian (positiveDensity normalizer)
open KFCausalReciprocalWedgePlane (c0 c1 jointMeasure)
open KFCausalReciprocalWedgeGeometry (chart first wedge)
open KFCausalReciprocalWedgePrefactor (jacobian)
open KFCausalReciprocalWedgeLaplace (laplaceSum)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalWedgeWeight (polynomial moment weight)
open KFCausalReciprocalWedgeVelocity (neutralExponent)

def radialDensity (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (θ x y : ℝ) : ℝ :=
  Real.exp (Real.sin θ^2*(8*β*r.im^2*x))*
    polynomial (c0 β) (c1 β) (1/4) (Real.sin θ^2*(fieldSlope r)^2*x)*
      ‖laplaceSum n w c (chart α r x y)‖^2

def baseDensity (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (θ : ℝ) (z : ℂ) : ℝ :=
  Real.exp (Real.sin θ^2*neutralExponent α β r z)*
    polynomial (c0 β) (c1 β) (1/4) (moment α (Real.sin θ^2) r z)*‖laplaceSum n w c z‖^2

def wedgeDensity (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (θ : ℝ) (z : ℂ) : ℝ :=
  weight α β (Real.sin θ^2) (c0 β) (c1 β) (1/4) r z*‖laplaceSum n w c z‖^2

theorem polar_density (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (ρ θ y : ℝ) :
    positiveDensity n α β w r c ((ρ*Real.cos θ,ρ*Real.sin θ),y) =
      radialDensity n α β w r c θ (ρ^2) y := by
  have hr : (ρ*Real.cos θ)^2+(ρ*Real.sin θ)^2 = ρ^2 := by
    calc
      _ = ρ^2*(Real.cos θ^2+Real.sin θ^2) := by ring
      _ = ρ^2 := by rw [Real.cos_sq_add_sin_sq,mul_one]
  unfold positiveDensity radialDensity
  dsimp only
  rw [hr]
  rw [show 8*β*r.im^2*(ρ*Real.sin θ)^2 = Real.sin θ^2*(8*β*r.im^2*ρ^2) by ring]
  unfold KFCausalReciprocalWedgePlane.polynomial polynomial
  ring

theorem base_chart (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (hα : α ≠ 0) (hA : area r ≠ 0) (ha : r.re ≠ 0) (hb : r.im ≠ 0) (θ x y : ℝ) :
    baseDensity n α β w r c θ (chart α r x y) = radialDensity n α β w r c θ x y := by
  unfold baseDensity radialDensity neutralExponent moment
  rw [KFCausalReciprocalWedgeGeometry.first_chart α x y r hα hA ha hb]

theorem wedge_factor (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (θ : ℝ) (z : ℂ) :
    wedgeDensity n α β w r c θ z = jacobian α r*baseDensity n α β w r c θ z := by
  unfold wedgeDensity baseDensity weight
  ring

theorem radial_wedge_lintegral (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (hα : α ≠ 0) (hA : area r ≠ 0) (ha : r.re ≠ 0) (hb : r.im ≠ 0) (θ : ℝ) :
    (∫⁻ x : ℝ in Ioi 0, ∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (radialDensity n α β w r c θ x y)) =
      ∫⁻ z in wedge α r, ENNReal.ofReal (wedgeDensity n α β w r c θ z) := by
  have hm : Measurable (fun z => ENNReal.ofReal (baseDensity n α β w r c θ z)) := by
    unfold baseDensity neutralExponent moment first polynomial laplaceSum
    fun_prop
  simp_rw [← base_chart n α β w r c hα hA ha hb θ]
  rw [KFCausalReciprocalWedgePolar.lintegral_pair_chart α r hα hA ha hb _ hm]
  simp_rw [wedge_factor,ENNReal.ofReal_mul (show 0 ≤ jacobian α r by unfold jacobian; positivity)]
  exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

theorem positiveDensity_lintegral (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (hα : α ≠ 0) (hA : area r ≠ 0) (ha : r.re ≠ 0) (hb : r.im ≠ 0) :
    (∫⁻ p, ENNReal.ofReal (positiveDensity n α β w r c p) ∂jointMeasure) =
      ENNReal.ofReal (1/2:ℝ)*∫⁻ θ : ℝ in Ioo (-Real.pi) Real.pi,
        ∫⁻ z in wedge α r, ENNReal.ofReal (wedgeDensity n α β w r c θ z) := by
  have hp (y : ℝ) :
      (∫⁻ u : ℝ × ℝ, ENNReal.ofReal (positiveDensity n α β w r c (u,y))) =
        ENNReal.ofReal (1/2:ℝ)*∫⁻ θ : ℝ in Ioo (-Real.pi) Real.pi,
          ∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (radialDensity n α β w r c θ x y) := by
    apply KFCausalReciprocalWedgePolar.lintegral_polar_square
    · unfold Function.uncurry radialDensity polynomial laplaceSum chart
      fun_prop
    · intro ρ θ
      rw [polar_density]
  unfold jointMeasure
  rw [lintegral_prod_symm _ (by
    unfold positiveDensity KFCausalReciprocalWedgePlane.polynomial laplaceSum chart
    fun_prop)]
  simp_rw [hp]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [lintegral_lintegral_swap (by
    apply Measurable.aemeasurable
    apply Measurable.lintegral_prod_right
    unfold Function.uncurry radialDensity polynomial laplaceSum chart
    fun_prop)]
  apply lintegral_congr
  intro θ
  rw [lintegral_lintegral_swap (by
    unfold Function.uncurry radialDensity polynomial laplaceSum chart
    fun_prop)]
  exact radial_wedge_lintegral n α β w r c hα hA ha hb θ

theorem pairing_lintegral (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (hw : ∀ i, 1 ≤ w i) (hα : 0 < α) (hA : 0 < α*area r)
    (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) (ha : r.re ≠ 0) (hb : r.im ≠ 0) :
    ENNReal.ofReal (KFCausalReciprocalCrossGram.pairing n α β w r c c).re =
      ENNReal.ofReal (normalizer β/2)*∫⁻ θ : ℝ in Ioo (-Real.pi) Real.pi,
        ∫⁻ z in wedge α r, ENNReal.ofReal (wedgeDensity n α β w r c θ z) := by
  rw [KFCausalReciprocalWedgeCartesian.pairing_integral n α β w r c hw hA hC hβ,Complex.ofReal_re,
    ENNReal.ofReal_mul (KFCausalReciprocalWedgeCartesian.normalizer_pos β hβ).le,
    ofReal_integral_eq_lintegral_ofReal
      (KFCausalReciprocalWedgeCartesian.positiveDensity_integrable n α β w r c hw hA hC hβ)
      (Filter.Eventually.of_forall (KFCausalReciprocalWedgeCartesian.positiveDensity_nonneg n α β w r c hβ)),
    positiveDensity_lintegral n α β w r c hα.ne'
      (ne_of_gt ((mul_pos_iff_of_pos_left hα).mp hA)) ha hb,
    ← mul_assoc,← ENNReal.ofReal_mul (KFCausalReciprocalWedgeCartesian.normalizer_pos β hβ).le]
  congr 2
  ring

#print axioms polar_density
#print axioms base_chart
#print axioms wedge_factor
#print axioms radial_wedge_lintegral
#print axioms positiveDensity_lintegral
#print axioms pairing_lintegral
end
end UnifiedTheory.Audit.KFCausalReciprocalWedgeRepresentation
