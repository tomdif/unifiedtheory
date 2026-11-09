/- An exact neutral-plane marginal for arbitrary complex neutral profiles.
The argument uses their squared norm without differentiating the profile.
Integrability is established separately before using order on integrals. -/
import UnifiedTheory.Audit.KFCausalNeutralPlaneUniformGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralProfileMarginal
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position exponent)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalNeutralPlaneCoordinates
open UnifiedTheory.Audit.KFCausalNeutralPlaneMeasure
open UnifiedTheory.Audit.KFCausalNeutralPlaneMarginal
open UnifiedTheory.Audit.KFCausalQuarticPlaneDomination (potential)

def profileDensity (D β lam L : ℝ) (F : ℂ → ℂ) (x y : ℝ) : ℝ :=
  D*Real.exp (-2*β*x^2-lam*y^2)*potential (x+L*y)*‖F ((x:ℂ)+(y:ℂ)*Complex.I)‖^2

def profileEnergyDensity (α β : ℝ) (r : ℂ) (F : ℂ → ℂ) (q : Transverse) : ℝ :=
  ‖Complex.exp (exponent α β 0 r q)‖^2 *
    potential (pointField q) * ‖F (position r q 4)‖^2

theorem profileEnergy_change_variables (α β : ℝ) (r : ℂ) (hr : r.im ≠ 0)
    (F : ℂ → ℂ) :
    ∫ q, profileEnergyDensity α β r F q =
      (1/(4*|r.im|)) * ∫ u : Transverse,
        Real.exp (-quadratic α β r u) * potential (u 3+fieldSlope r*u 4) *
          ‖F ((u 3:ℂ)+(u 4:ℂ)*Complex.I)‖^2 := by
  rw [integral_coordinates r hr]
  simp only [profileEnergyDensity,gaussian_norm_reconstruct α β r hr,
    field_reconstruct r hr,neutral_position r hr]

theorem profile_factorization (α β : ℝ) (r : ℂ) (F : ℂ → ℂ) (u : Transverse) :
    Real.exp (-quadratic α β r u)*potential (u 3+fieldSlope r*u 4)*
      ‖F ((u 3:ℂ)+(u 4:ℂ)*Complex.I)‖^2 =
    Real.exp (-(2*α*(r.re^2-r.im^2))*(u 0)^2) *
      (Real.exp (-(2*α*(r.re^2-r.im^2))*(u 1)^2) *
      (Real.exp (-(α*(r.re^2-r.im^2))*(u 2)^2) *
        profileDensity 1 β (planeWidth α β r) (fieldSlope r) F (u 3) (u 4))) := by
  unfold profileDensity
  simp only [one_mul,← mul_assoc,← Real.exp_add]
  congr 2
  unfold quadratic
  ring

theorem profile_spectator_integral (α β : ℝ) (r : ℂ) (F : ℂ → ℂ) :
    (∫ u : Transverse, Real.exp (-quadratic α β r u)*
      potential (u 3+fieldSlope r*u 4)*‖F ((u 3:ℂ)+(u 4:ℂ)*Complex.I)‖^2) =
    (Real.sqrt (Real.pi/(2*α*(r.re^2-r.im^2))))^2 *
      Real.sqrt (Real.pi/(α*(r.re^2-r.im^2))) *
      ∫ v : Fin 2 → ℝ, profileDensity 1 β (planeWidth α β r) (fieldSlope r) F (v 0) (v 1) := by
  simp_rw [profile_factorization]
  change (∫ u : Fin (4+1) → ℝ,
    Real.exp (-(2*α*(r.re^2-r.im^2))*(u 0)^2) *
    (fun v : Fin 4 → ℝ =>
      Real.exp (-(2*α*(r.re^2-r.im^2))*(v 0)^2) *
      (Real.exp (-(α*(r.re^2-r.im^2))*(v 1)^2) *
        profileDensity 1 β (planeWidth α β r) (fieldSlope r) F (v 2) (v 3)))
      (fun i => u i.succ)) = _
  rw [integral_head_product 4 (fun x => Real.exp (-(2*α*(r.re^2-r.im^2))*x^2))
    (fun v => Real.exp (-(2*α*(r.re^2-r.im^2))*(v 0)^2) *
      (Real.exp (-(α*(r.re^2-r.im^2))*(v 1)^2) *
        profileDensity 1 β (planeWidth α β r) (fieldSlope r) F (v 2) (v 3))),
    integral_gaussian]
  change _ * (∫ u : Fin (3+1) → ℝ,
    Real.exp (-(2*α*(r.re^2-r.im^2))*(u 0)^2) *
    (fun v : Fin 3 → ℝ =>
      Real.exp (-(α*(r.re^2-r.im^2))*(v 0)^2) *
        profileDensity 1 β (planeWidth α β r) (fieldSlope r) F (v 1) (v 2))
      (fun i => u i.succ)) = _
  rw [integral_head_product 3 (fun x => Real.exp (-(2*α*(r.re^2-r.im^2))*x^2))
    (fun v => Real.exp (-(α*(r.re^2-r.im^2))*(v 0)^2) *
        profileDensity 1 β (planeWidth α β r) (fieldSlope r) F (v 1) (v 2)),
    integral_gaussian]
  change _ * (_ * (∫ u : Fin (2+1) → ℝ,
    Real.exp (-(α*(r.re^2-r.im^2))*(u 0)^2) *
    (fun v : Fin 2 → ℝ =>
        profileDensity 1 β (planeWidth α β r) (fieldSlope r) F (v 0) (v 1))
      (fun i => u i.succ))) = _
  rw [integral_head_product 2 (fun x => Real.exp (-(α*(r.re^2-r.im^2))*x^2))
    (fun v => profileDensity 1 β (planeWidth α β r) (fieldSlope r) F (v 0) (v 1)),
    integral_gaussian]
  ring

theorem profileEnergy_plane_integral (α β : ℝ) (r : ℂ) (hr : r.im ≠ 0)
    (F : ℂ → ℂ) :
    (∫ q, profileEnergyDensity α β r F q) =
      ∫ v : Fin 2 → ℝ,
        profileDensity (prefactor α r) β (planeWidth α β r) (fieldSlope r) F (v 0) (v 1) := by
  rw [profileEnergy_change_variables α β r hr,profile_spectator_integral]
  have he : (fun v : Fin 2 → ℝ =>
      profileDensity (prefactor α r) β (planeWidth α β r) (fieldSlope r) F (v 0) (v 1)) =
    fun v => prefactor α r * profileDensity 1 β (planeWidth α β r) (fieldSlope r) F (v 0) (v 1) := by
    funext v
    unfold profileDensity
    ring
  rw [he,integral_const_mul]
  unfold prefactor
  ring

#print axioms profileEnergy_change_variables
#print axioms profile_factorization
#print axioms profile_spectator_integral
#print axioms profileEnergy_plane_integral
end
end UnifiedTheory.Audit.KFCausalNeutralProfileMarginal
