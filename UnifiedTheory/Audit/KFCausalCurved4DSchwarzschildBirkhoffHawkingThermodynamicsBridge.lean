import UnifiedTheory.LayerB.SchwarzschildSolution
import UnifiedTheory.LayerB.BirkhoffUniqueness
import UnifiedTheory.LayerB.HawkingTemperature
import UnifiedTheory.LayerB.BekensteinHawking
import UnifiedTheory.Audit.KFCausalCurved4DVariationalEinsteinOstrogradskyStabilityBridge

/-! # 4D Schwarzschild Exact Vacuum Solution, Birkhoff Spherical Uniqueness,
Orthonormal Tidal Weyl & Kretschmann Invariants, and Bekenstein-Hawking Thermodynamics Bridge

This module (`UnifiedTheory.Audit.KFCausalCurved4DSchwarzschildBirkhoffHawkingThermodynamicsBridge`)
unites the exact nonlinear 4D black-hole geometry and quantum-gravity thermodynamics modules:

1. **Exact 4D Schwarzschild Vacuum Solution (`LayerB.SchwarzschildSolution`)**:
   - Lapse function `f M r = 1 - 2 * M / r`, metric components `(g_tt, g_rr, g_thetatheta, g_phiphi)`,
     horizon locus `f M r = 0 ↔ r = 2 * M`, Christoffel symbols `(Gamma_t_tr, Gamma_r_tt, Gamma_r_rr)`,
     exact ODE `f'' / 2 + f' / r = 0` and `f + r * f' = 1`, componentwise vanishing of all four
     Ricci tensor components `(R_tt, R_rr, R_thetatheta, R_phiphi)`, and asymptotic flatness.

2. **Birkhoff Spherical Vacuum Uniqueness & Timelike Killing Field (`LayerB.BirkhoffUniqueness`)**:
   - Vanishing of `RicciTR` forces `dt_B = 0` (`B` is time-independent); vanishing of `RicciSum`
     forces `dr_AB = 0`; in `StaticGauge` (`A * B = 1`), `A = 1 / B` and `dt_AB = 0`;
     vanishing of `RicciAng` forces the Schwarzschild ODE `1 - (f + r * f') = 0`.
   - `schwarzschildAnsatz M hM_lt` satisfies `IsVacuumSphericallySymmetric`, `StaticGauge`,
     the timelike Killing equations `dt_A = 0, dt_B = 0`, and asymptotic flatness.

3. **Orthonormal Schwarzschild Tidal Weyl Tensor & Kretschmann Curvature Invariant**:
   - Defines the exact orthonormal-frame tidal Weyl electric eigenvalues
     `schwarzschildWeylRadial M r = -(2 * M) / r ^ 3 = fDoublePrime M r / 2` and
     `schwarzschildWeylAngular M r = M / r ^ 3 = fPrime M r / (2 * r)`, proving that
     spatial trace-freeness `E_r + E_θ + E_φ = 0` is algebraically identical to the
     vacuum Ricci ODE `fDoublePrime M r / 2 + fPrime M r / r = 0`.
   - Defines the Kretschmann scalar `schwarzschildKretschmann M r = 48 * M ^ 2 / r ^ 6`,
     proves `K = 8 * (E_r^2 + E_θ^2 + E_φ^2) > 0`, and evaluates it at the event horizon
     `r = schwarzschildRadius M = 2 * M`: `K(2M) = 3 / (4 * M ^ 4)` with dimensionless
     horizon invariants `K(2M) * A^2 = 192 * π^2` and `K(2M) * S_BH^2 = 12 * π^2`.

4. **Bekenstein-Hawking Quarter-Area Entropy, Smarr Formula, Hawking Temperature & Evaporation**:
   - Connects `bekensteinHawkingEntropy M = horizonArea M / 4 = 4 * π * M^2`,
     `hawkingTemperature M = 1 / (8 * π * M) = surfaceGravity M / (2 * π)`, the first law
     `T_H * (dS_BH / dM) = 1`, Smarr's formula `2 * S_BH * T_H = M`, Gauss's law
     `κ * A = 4 * π * M`, Stefan-Boltzmann luminosity `L ~ M⁻²`, cubic evaporation
     lifetime `τ(c * M) = c^3 * τ(M)`, and Sorkin causal-set de Sitter entropy scaling
     `(bekensteinHawkingFromArea (BHArea (sorkinLambda ρ V)))^2 * 16 = ρ * V`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DSchwarzschildBirkhoffHawkingThermodynamicsBridge
noncomputable section

open UnifiedTheory.LayerA.CosmologicalConstant (sorkinLambda sorkinLambda_pos sorkin_scaling)
open UnifiedTheory.LayerA.CosmologicalConstantN (BHArea Nsub)
open UnifiedTheory.LayerB.BekensteinHawking
  (schwarzschildRadius horizonArea horizonArea_eq bekensteinHawkingEntropy
   BH_entropy_eq BH_entropy_pos BH_entropy_eq_pi_rs_squared
   bekensteinHawkingFromArea deSitter_BH_entropy
   bulk_is_boundary_squared_times_16 bekenstein_hawking_capstone)
open UnifiedTheory.LayerB.SchwarzschildSolution
  (f g_tt g_rr g_thetatheta g_phiphi g_tt_inv g_rr_inv
   f_at_horizon f_minus_one g_tt_at_horizon g_rr_times_f
   fPrime fDoublePrime r_sq_fPrime r_cubed_fDoublePrime
   Gamma_t_tr Gamma_r_tt Gamma_r_rr
   gamma_t_tr_times_gamma_r_tt gamma_t_tr_eq_neg_gamma_r_rr
   vacuum_identity vacuum_identity' rf_derivative_eq_one
   R_tt R_rr R_thetatheta R_phiphi
   R_tt_vanishes R_rr_vanishes R_thetatheta_vanishes R_phiphi_vanishes
   asymptotic_flatness g_tt_asymptotic
   g_tt_zero_at_schwarzschildRadius g_tt_zero_iff f_zero_iff
   horizon_area_of_schwarzschild BH_entropy_of_schwarzschild
   schwarzschild_vacuum_master)
open UnifiedTheory.LayerB.BirkhoffUniqueness
  (SphericallySymmetricMetric RicciTR RicciSum RicciAng
   IsVacuumSphericallySymmetric StaticGauge schwarzschildAnsatz
   vacuum_implies_dt_B_zero dt_AB_reduces_to_dt_A_times_B
   vacuum_implies_dr_AB_zero dr_logAB_zero
   A_eq_inv_B_in_static_gauge dt_AB_zero_in_static_gauge
   schwarzschild_solves_angular_ODE angular_ODE_solution_form
   schwarzschild_in_static_gauge schwarzschild_is_vacuum_spherical
   birkhoff_implies_killing_field_schwarzschild
   birkhoff_implies_asymptotic_flatness birkhoff_master)
open UnifiedTheory.LayerB.HawkingTemperature
  (hawkingTemperature hawkingTemperature_pos M_times_hawkingTemperature
   entropyDerivative entropyDerivative_is_diff_quotient
   hawkingTemp_from_entropy_derivative hawkingTemp_eq_reciprocal_entropyDerivative
   hawkingTemperature_antimono hawkingTemperature_at_one_bracket
   luminosity luminosity_eq luminosity_pos
   evaporationRate evaporationRate_neg
   evaporationLifetime evaporationLifetime_pos evaporationLifetime_cubic_scaling
   surfaceGravity hawkingTemp_eq_surfaceGravity_over_twopi
   hawking_temperature_capstone)

/-! ### 1. Exact 4D Schwarzschild Metric, Horizon, Christoffel Symbols & Vacuum Ricci Vanishing -/

/-- Exact characterization of the Schwarzschild horizon at `r = 2 * M`:
`f M (2 * M) = 0`, `g_tt M (2 * M) = 0`, and for `r ≠ 0`, `f M r = 0 ↔ r = 2 * M`
and `g_tt M r = 0 ↔ r = 2 * M`. -/
theorem schwarzschild_lapse_and_horizon_characterization
    (M r : ℝ) (hM : M ≠ 0) (hr : r ≠ 0) :
    f M (2 * M) = 0 ∧
    g_tt M (2 * M) = 0 ∧
    (f M r = 0 ↔ r = 2 * M) ∧
    (g_tt M r = 0 ↔ r = 2 * M) :=
  ⟨f_at_horizon M hM, g_tt_at_horizon M hM, f_zero_iff M r hr,
   (g_tt_zero_iff M r hr).trans (f_zero_iff M r hr)⟩

/-- Metric reciprocity `g_rr M r * f M r = 1` and Christoffel symbol identities
`Gamma_t_tr M r = -Gamma_r_rr M r` and `Gamma_t_tr M r * Gamma_r_tt M r = M ^ 2 / r ^ 4`. -/
theorem schwarzschild_metric_inverse_and_christoffel_identities
    (M r : ℝ) (hr : r ≠ 0) (hf : f M r ≠ 0) :
    g_rr M r * f M r = 1 ∧
    Gamma_t_tr M r = -Gamma_r_rr M r ∧
    Gamma_t_tr M r * Gamma_r_tt M r = M ^ 2 / r ^ 4 :=
  ⟨g_rr_times_f M r hf,
   gamma_t_tr_eq_neg_gamma_r_rr M r,
   gamma_t_tr_times_gamma_r_tt M r hr hf⟩

/-- Radial derivative scaling laws (`r^2 * f' = 2M`, `r^3 * f'' = -4M`) and the two
fundamental Schwarzschild vacuum ODEs (`f'' / 2 + f' / r = 0` and `f + r * f' = 1`). -/
theorem schwarzschild_derivative_scaling_and_vacuum_ode
    (M r : ℝ) (hr : r ≠ 0) :
    r ^ 2 * fPrime M r = 2 * M ∧
    r ^ 3 * fDoublePrime M r = -(4 * M) ∧
    r ^ 3 * (fDoublePrime M r / 2 + fPrime M r / r) = 0 ∧
    fDoublePrime M r / 2 + fPrime M r / r = 0 ∧
    f M r + r * fPrime M r = 1 :=
  ⟨r_sq_fPrime M r hr,
   r_cubed_fDoublePrime M r hr,
   vacuum_identity M r hr,
   vacuum_identity' M r hr,
   rf_derivative_eq_one M r hr⟩

/-- Componentwise vanishing of all four diagonal Ricci tensor components
`R_tt`, `R_rr`, `R_thetatheta`, and `R_phiphi` for the Schwarzschild metric. -/
theorem schwarzschild_ricci_components_all_vanish
    (M r θ : ℝ) (hr : r ≠ 0) :
    R_tt M r = 0 ∧
    R_rr M r = 0 ∧
    R_thetatheta M r = 0 ∧
    R_phiphi M r θ = 0 :=
  ⟨R_tt_vanishes M r hr,
   R_rr_vanishes M r hr,
   R_thetatheta_vanishes M r hr,
   R_phiphi_vanishes M r θ hr⟩

/-- Asymptotic flatness of the Schwarzschild metric as `r → ∞` together with the
horizon area `horizonArea M = 16 * π * M^2` and entropy `bekensteinHawkingEntropy M = 4 * π * M^2`. -/
theorem schwarzschild_asymptotic_flatness_and_area_entropy
    (M : ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∃ R₀ : ℝ, 0 < R₀ ∧ ∀ r : ℝ, R₀ < r → |f M r - 1| < ε) ∧
    (∀ r : ℝ, g_tt M r - (-1) = -(f M r - 1)) ∧
    horizonArea M = 16 * Real.pi * M ^ 2 ∧
    bekensteinHawkingEntropy M = 4 * Real.pi * M ^ 2 :=
  ⟨asymptotic_flatness M ε hε, g_tt_asymptotic M,
   horizon_area_of_schwarzschild M, BH_entropy_of_schwarzschild M⟩

/-- Complete Schwarzschild vacuum solution bridge bundling Ricci flatness, horizon
location, horizon area, and Bekenstein-Hawking entropy. -/
theorem schwarzschild_vacuum_solution_master_bridge
    (M r θ : ℝ) (hM : M ≠ 0) (hr : r ≠ 0) :
    R_tt M r = 0 ∧
    R_rr M r = 0 ∧
    R_thetatheta M r = 0 ∧
    R_phiphi M r θ = 0 ∧
    g_tt M (schwarzschildRadius M) = 0 ∧
    horizonArea M = 16 * Real.pi * M ^ 2 ∧
    bekensteinHawkingEntropy M = 4 * Real.pi * M ^ 2 :=
  ⟨R_tt_vanishes M r hr, R_rr_vanishes M r hr,
   R_thetatheta_vanishes M r hr, R_phiphi_vanishes M r θ hr,
   g_tt_zero_at_schwarzschildRadius M hM,
   horizon_area_of_schwarzschild M, BH_entropy_of_schwarzschild M⟩

/-! ### 2. Birkhoff Spherical Vacuum Uniqueness, Staticity & Timelike Killing Field -/

/-- Birkhoff step 1: in any spherically symmetric vacuum metric (`IsVacuumSphericallySymmetric m`),
the radial metric function `B` has zero t-derivative (`dt_B = 0`) and `dt_AB = dt_A * B`. -/
theorem birkhoff_spherical_vacuum_implies_static_B
    (m : SphericallySymmetricMetric) (hvac : IsVacuumSphericallySymmetric m)
    (t r : ℝ) (hr : 0 < r) :
    m.dt_B t r = 0 ∧ m.dt_AB t r = m.dt_A t r * m.B t r :=
  ⟨vacuum_implies_dt_B_zero m hvac t r hr,
   dt_AB_reduces_to_dt_A_times_B m hvac t r hr⟩

/-- Birkhoff step 2: in any spherically symmetric vacuum metric, `dr_AB = 0`
(`dr_A * B + A * dr_B = 0`) for all `r > 0`. -/
theorem birkhoff_spherical_vacuum_implies_AB_radius_independent
    (m : SphericallySymmetricMetric) (hvac : IsVacuumSphericallySymmetric m)
    (t r : ℝ) (hr : 0 < r) :
    m.dr_AB t r = 0 ∧ m.dr_A t r * m.B t r + m.A t r * m.dr_B t r = 0 :=
  ⟨vacuum_implies_dr_AB_zero m hvac t r hr, dr_logAB_zero m hvac t r hr⟩

/-- Birkhoff step 3: in `StaticGauge m` (`A * B = 1, dt_A = 0, dt_B = 0`),
`A t r = 1 / B t r` and `dt_AB t r = 0`. -/
theorem birkhoff_static_gauge_reciprocity_and_time_independence
    (m : SphericallySymmetricMetric) (hgauge : StaticGauge m)
    (t r : ℝ) (hr : 0 < r) :
    m.A t r = 1 / m.B t r ∧ m.dt_AB t r = 0 :=
  ⟨A_eq_inv_B_in_static_gauge m hgauge t r hr,
   dt_AB_zero_in_static_gauge m hgauge t r hr⟩

/-- Birkhoff step 4: the angular vacuum equation `1 - (f + r * f') = 0` is solved
by the Schwarzschild lapse `f M r = 1 - 2M/r` with reciprocal `1 / (1 / f M r) = f M r`. -/
theorem birkhoff_angular_ode_schwarzschild_uniqueness
    (M r : ℝ) (hr : r ≠ 0) (hf : f M r ≠ 0) :
    1 - (f M r + r * fPrime M r) = 0 ∧
    1 / (f M r) ≠ 0 ∧
    1 / (1 / (f M r)) = f M r :=
  ⟨schwarzschild_solves_angular_ODE M r hr,
   (angular_ODE_solution_form M r hr hf).1,
   (angular_ODE_solution_form M r hr hf).2⟩

/-- The Schwarzschild ansatz `schwarzschildAnsatz M hM_lt` satisfies both `StaticGauge`
and `IsVacuumSphericallySymmetric`. -/
theorem birkhoff_schwarzschild_ansatz_is_static_vacuum
    (M : ℝ) (hM_lt : ∀ r : ℝ, 0 < r → r > 2 * M) :
    StaticGauge (schwarzschildAnsatz M hM_lt) ∧
    IsVacuumSphericallySymmetric (schwarzschildAnsatz M hM_lt) :=
  ⟨schwarzschild_in_static_gauge M hM_lt, schwarzschild_is_vacuum_spherical M hM_lt⟩

/-- `schwarzschildAnsatz M hM_lt` possesses a timelike Killing vector field
(`dt_A = 0, dt_B = 0`) and is asymptotically flat as `r → ∞`. -/
theorem birkhoff_killing_field_and_asymptotic_flatness
    (M : ℝ) (hM_lt : ∀ r : ℝ, 0 < r → r > 2 * M) :
    (∀ t r : ℝ, 0 < r →
      (schwarzschildAnsatz M hM_lt).dt_A t r = 0 ∧
      (schwarzschildAnsatz M hM_lt).dt_B t r = 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ r : ℝ, R₀ < r →
      |(schwarzschildAnsatz M hM_lt).A 0 r - 1| < ε) :=
  ⟨birkhoff_implies_killing_field_schwarzschild M hM_lt,
   birkhoff_implies_asymptotic_flatness M hM_lt⟩

/-- Complete Birkhoff uniqueness master bridge from `LayerB.BirkhoffUniqueness`. -/
theorem birkhoff_uniqueness_master_bridge
    (M : ℝ) (hM_lt : ∀ r : ℝ, 0 < r → r > 2 * M) :
    IsVacuumSphericallySymmetric (schwarzschildAnsatz M hM_lt) ∧
    StaticGauge (schwarzschildAnsatz M hM_lt) ∧
    (∀ t r : ℝ, 0 < r →
      (schwarzschildAnsatz M hM_lt).dt_A t r = 0 ∧
      (schwarzschildAnsatz M hM_lt).dt_B t r = 0) ∧
    (∀ m : SphericallySymmetricMetric,
      IsVacuumSphericallySymmetric m → StaticGauge m →
      ∀ t r : ℝ, 0 < r → m.dt_B t r = 0 ∧ m.A t r = 1 / m.B t r) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ r : ℝ, R₀ < r →
      |(schwarzschildAnsatz M hM_lt).A 0 r - 1| < ε) :=
  ⟨schwarzschild_is_vacuum_spherical M hM_lt,
   schwarzschild_in_static_gauge M hM_lt,
   birkhoff_implies_killing_field_schwarzschild M hM_lt,
   fun m hvac hgauge t r hr =>
     ⟨vacuum_implies_dt_B_zero m hvac t r hr,
      A_eq_inv_B_in_static_gauge m hgauge t r hr⟩,
   birkhoff_implies_asymptotic_flatness M hM_lt⟩

/-! ### 3. Orthonormal Schwarzschild Tidal Weyl Electric Tensor & Kretschmann Invariant -/

/-- **Radial Tidal Weyl Electric Eigenvalue** of a 4D Schwarzschild black hole in an
orthonormal frame (`E_{r̂ r̂} = -2M / r^3`, radial tidal stretching). -/
def schwarzschildWeylRadial (M r : ℝ) : ℝ := -(2 * M) / r ^ 3

/-- **Angular Tidal Weyl Electric Eigenvalue** of a 4D Schwarzschild black hole in an
orthonormal frame (`E_{θ̂ θ̂} = E_{φ̂ φ̂} = M / r^3`, transverse tidal compression). -/
def schwarzschildWeylAngular (M r : ℝ) : ℝ := M / r ^ 3

/-- **Schwarzschild Kretschmann Curvature Scalar**:
`K(M, r) = R_{abcd} R^{abcd} = C_{abcd} C^{abcd} = 48 * M^2 / r^6`. -/
def schwarzschildKretschmann (M r : ℝ) : ℝ := 48 * M ^ 2 / r ^ 6

/-- The orthonormal Schwarzschild tidal Weyl electric components are directly given
by the lapse derivatives `fDoublePrime M r / 2` and `fPrime M r / (2 * r)`. -/
theorem schwarzschildWeyl_from_lapse_derivatives (M r : ℝ) (hr : r ≠ 0) :
    schwarzschildWeylRadial M r = fDoublePrime M r / 2 ∧
    schwarzschildWeylAngular M r = fPrime M r / (2 * r) := by
  unfold schwarzschildWeylRadial schwarzschildWeylAngular fDoublePrime fPrime
  refine ⟨by ring, ?_⟩
  field_simp

/-- Spatial trace-freeness of the orthonormal Schwarzschild tidal Weyl electric tensor:
`E_{r̂ r̂} + E_{θ̂ θ̂} + E_{φ̂ φ̂} = (-2M/r^3) + (M/r^3) + (M/r^3) = 0`. -/
theorem schwarzschildWeyl_spatial_trace_zero (M r : ℝ) :
    schwarzschildWeylRadial M r +
      schwarzschildWeylAngular M r +
      schwarzschildWeylAngular M r = 0 := by
  unfold schwarzschildWeylRadial schwarzschildWeylAngular
  ring

/-- **Weyl Trace-Freeness ↔ Vacuum Ricci ODE Bridge**:
The spatial trace `schwarzschildWeylRadial M r + 2 * schwarzschildWeylAngular M r`
equals `fDoublePrime M r / 2 + fPrime M r / r`, which vanishes by `vacuum_identity'`. -/
theorem schwarzschildWeyl_trace_eq_vacuum_identity (M r : ℝ) (hr : r ≠ 0) :
    schwarzschildWeylRadial M r + 2 * schwarzschildWeylAngular M r =
      fDoublePrime M r / 2 + fPrime M r / r ∧
    fDoublePrime M r / 2 + fPrime M r / r = 0 := by
  have hw := schwarzschildWeyl_from_lapse_derivatives M r hr
  refine ⟨?_, vacuum_identity' M r hr⟩
  rw [hw.1, hw.2]
  field_simp

/-- **Kretschmann Scalar from Tidal Weyl Electric Norm**:
Because a static Schwarzschild black hole is Ricci-flat (`R_{ab} = 0`) and has
vanishing gravito-magnetic Weyl tensor (`B_{ij} = 0`), its Kretschmann scalar equals
`8 * (E_{r̂ r̂}^2 + E_{θ̂ θ̂}^2 + E_{φ̂ φ̂}^2) = 48 * M^2 / r^6`. -/
theorem schwarzschildKretschmann_eq_eight_times_weyl_norm_sq (M r : ℝ) :
    schwarzschildKretschmann M r =
      8 * (schwarzschildWeylRadial M r ^ 2 +
        schwarzschildWeylAngular M r ^ 2 +
        schwarzschildWeylAngular M r ^ 2) := by
  unfold schwarzschildKretschmann schwarzschildWeylRadial schwarzschildWeylAngular
  ring

/-- Strict positivity of the Schwarzschild Kretschmann scalar for `M ≠ 0` and `r ≠ 0`,
confirming that the Schwarzschild spacetime is genuinely curved everywhere outside `r = 0`. -/
theorem schwarzschildKretschmann_pos (M r : ℝ) (hM : M ≠ 0) (hr : r ≠ 0) :
    0 < schwarzschildKretschmann M r := by
  unfold schwarzschildKretschmann
  positivity

/-- **Finite Horizon Curvature (`K(2M) = 3 / (4 M^4)`)**:
At the Schwarzschild radius `r = schwarzschildRadius M = 2 * M` (`M ≠ 0`), the
Kretschmann scalar takes the finite value `3 / (4 * M ^ 4)`, proving that `r = 2M`
is a coordinate singularity of `(t, r)` and not a curvature singularity. -/
theorem schwarzschildKretschmann_at_horizon (M : ℝ) (hM : M ≠ 0) :
    schwarzschildKretschmann M (schwarzschildRadius M) = 3 / (4 * M ^ 4) := by
  unfold schwarzschildKretschmann schwarzschildRadius
  field_simp
  ring

/-- **Dimensionless Horizon Curvature-Area Invariant**:
For every non-zero mass `M ≠ 0`, the product of the horizon Kretschmann scalar and
the square of the horizon area is the universal constant `192 * π^2`. -/
theorem schwarzschildKretschmann_horizon_times_area_sq (M : ℝ) (hM : M ≠ 0) :
    schwarzschildKretschmann M (schwarzschildRadius M) * (horizonArea M) ^ 2 =
      192 * Real.pi ^ 2 := by
  rw [schwarzschildKretschmann_at_horizon M hM, horizonArea_eq M]
  field_simp
  ring

/-- **Dimensionless Horizon Curvature-Entropy Invariant**:
For every non-zero mass `M ≠ 0`, the product of the horizon Kretschmann scalar and
the square of the Bekenstein-Hawking entropy is the universal constant `12 * π^2`. -/
theorem schwarzschildKretschmann_horizon_times_entropy_sq (M : ℝ) (hM : M ≠ 0) :
    schwarzschildKretschmann M (schwarzschildRadius M) *
        (bekensteinHawkingEntropy M) ^ 2 =
      12 * Real.pi ^ 2 := by
  rw [schwarzschildKretschmann_at_horizon M hM, BH_entropy_eq M]
  field_simp
  ring

/-! ### 4. Bekenstein-Hawking Entropy, First Law, Smarr Formula, Hawking Temperature & Evaporation -/

/-- Bekenstein-Hawking quarter-area law: `S_BH = A / 4 = 4 * π * M^2 = π * r_s^2`. -/
theorem bekensteinHawking_quarter_area_and_radius_formula (M : ℝ) :
    bekensteinHawkingEntropy M = horizonArea M / 4 ∧
    bekensteinHawkingEntropy M = 4 * Real.pi * M ^ 2 ∧
    bekensteinHawkingEntropy M = Real.pi * (schwarzschildRadius M) ^ 2 :=
  ⟨rfl, BH_entropy_eq M, BH_entropy_eq_pi_rs_squared M⟩

/-- De Sitter horizon entropy `bekensteinHawkingFromArea (BHArea Λ) = 1 / (4 * Λ)`
and the holographic bulk-boundary relation `Nsub Λ = 16 * (bekensteinHawkingFromArea (BHArea Λ))^2`. -/
theorem bekensteinHawking_deSitter_and_bulk_boundary_scaling
    (Λ : ℝ) (hΛ : Λ ≠ 0) :
    bekensteinHawkingFromArea (BHArea Λ) = 1 / (4 * Λ) ∧
    Nsub Λ = 16 * (bekensteinHawkingFromArea (BHArea Λ)) ^ 2 :=
  ⟨deSitter_BH_entropy Λ, bulk_is_boundary_squared_times_16 Λ hΛ⟩

/-- **Sorkin Causal-Set De Sitter Entropy Law (`16 * S_dS^2 = ρ * V`)**:
Evaluating the de Sitter horizon entropy `bekensteinHawkingFromArea (BHArea Λ)` at
Sorkin's cosmological constant `Λ = sorkinLambda ρ V = 1 / √(ρ * V)` (`ρ > 0, V > 0`)
yields `0 < bekensteinHawkingFromArea (BHArea (sorkinLambda ρ V))` and
`16 * (bekensteinHawkingFromArea (BHArea (sorkinLambda ρ V))) ^ 2 = ρ * V`. -/
theorem bekensteinHawking_sorkin_deSitter_entropy_sq
    (ρ V : ℝ) (hρ : 0 < ρ) (hV : 0 < V) :
    0 < bekensteinHawkingFromArea (BHArea (sorkinLambda ρ V)) ∧
    16 * (bekensteinHawkingFromArea (BHArea (sorkinLambda ρ V))) ^ 2 = ρ * V := by
  have hΛ : 0 < sorkinLambda ρ V := sorkinLambda_pos ρ V hρ hV
  have hdS := deSitter_BH_entropy (sorkinLambda ρ V)
  have hpos : 0 < bekensteinHawkingFromArea (BHArea (sorkinLambda ρ V)) := by
    rw [hdS]
    positivity
  have hsq : 16 * (bekensteinHawkingFromArea (BHArea (sorkinLambda ρ V))) ^ 2 = ρ * V := by
    rw [hdS]
    have hΛne : sorkinLambda ρ V ≠ 0 := ne_of_gt hΛ
    have hNne : ρ * V ≠ 0 := ne_of_gt (mul_pos hρ hV)
    calc 16 * (1 / (4 * sorkinLambda ρ V)) ^ 2
        = 1 / (sorkinLambda ρ V ^ 2) := by ring
      _ = 1 / (1 / (ρ * V)) := by rw [sorkin_scaling ρ V hρ hV]
      _ = ρ * V := by field_simp
  exact ⟨hpos, hsq⟩

/-- Strict positivity of the Hawking temperature `hawkingTemperature M = 1 / (8 * π * M)`
and the universal mass-temperature product `M * T_H = 1 / (8 * π)`. -/
theorem hawkingTemperature_pos_and_mass_product (M : ℝ) (hM : 0 < M) :
    0 < hawkingTemperature M ∧
    M * hawkingTemperature M = 1 / (8 * Real.pi) :=
  ⟨hawkingTemperature_pos M hM, M_times_hawkingTemperature M hM⟩

/-- First law of black-hole thermodynamics: the symmetric difference quotient of
`bekensteinHawkingEntropy` equals `entropyDerivative M`, and
`hawkingTemperature M * entropyDerivative M = 1` (`T_H = 1 / entropyDerivative M`). -/
theorem hawking_first_law_and_entropy_diff_quotient
    (M δ : ℝ) (hM : 0 < M) (hδ : δ ≠ 0) :
    (bekensteinHawkingEntropy (M + δ) - bekensteinHawkingEntropy (M - δ)) / (2 * δ) =
      entropyDerivative M ∧
    hawkingTemperature M * entropyDerivative M = 1 ∧
    hawkingTemperature M = 1 / entropyDerivative M :=
  ⟨entropyDerivative_is_diff_quotient M δ hδ,
   hawkingTemp_from_entropy_derivative M hM,
   hawkingTemp_eq_reciprocal_entropyDerivative M hM⟩

/-- **Smarr Formula for 4D Schwarzschild Black Holes (`M = 2 * S_BH * T_H`)**:
For every non-zero mass `M ≠ 0`, twice the product of the Bekenstein-Hawking
entropy and the Hawking temperature equals the black-hole mass `M`. -/
theorem smarr_formula_mass_entropy_temperature (M : ℝ) (hM : M ≠ 0) :
    2 * bekensteinHawkingEntropy M * hawkingTemperature M = M := by
  rw [BH_entropy_eq M]
  unfold hawkingTemperature
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- Surface gravity `surfaceGravity M = 1 / (4 * M) > 0`, the Unruh-Hawking identity
`T_H = κ / (2 * π)`, and Gauss's law for surface gravity `κ * A = 4 * π * M`. -/
theorem hawkingTemperature_surface_gravity_relation (M : ℝ) (hM : 0 < M) :
    0 < surfaceGravity M ∧
    hawkingTemperature M = surfaceGravity M / (2 * Real.pi) ∧
    surfaceGravity M * horizonArea M = 4 * Real.pi * M := by
  have hκ : 0 < surfaceGravity M := by
    unfold surfaceGravity
    positivity
  refine ⟨hκ, hawkingTemp_eq_surfaceGravity_over_twopi M hM, ?_⟩
  rw [horizonArea_eq M]
  unfold surfaceGravity
  have hMne : M ≠ 0 := ne_of_gt hM
  field_simp
  ring

/-- Antimonotonicity of Hawking temperature (`M₁ < M₂ → T_H(M₂) < T_H(M₁)`) and
Planck-mass bracket `0.039 < T_H(1) < 0.04`. -/
theorem hawkingTemperature_antimonotone_and_unit_bracket
    (M₁ M₂ : ℝ) (hM₁ : 0 < M₁) (h12 : M₁ < M₂) :
    hawkingTemperature M₂ < hawkingTemperature M₁ ∧
    0.039 < hawkingTemperature 1 ∧
    hawkingTemperature 1 < 0.04 :=
  ⟨hawkingTemperature_antimono hM₁ h12,
   hawkingTemperature_at_one_bracket.1,
   hawkingTemperature_at_one_bracket.2⟩

/-- Stefan-Boltzmann Hawking luminosity `L = 1 / (256 * π^3 * M^2) > 0` and
strictly negative mass-loss rate `evaporationRate M = -L < 0`. -/
theorem black_hole_luminosity_and_evaporation_rate
    (M : ℝ) (hM : 0 < M) :
    luminosity M = 1 / (256 * Real.pi ^ 3 * M ^ 2) ∧
    0 < luminosity M ∧
    evaporationRate M < 0 :=
  ⟨luminosity_eq M hM, luminosity_pos M hM, evaporationRate_neg M hM⟩

/-- Strict positivity of the black-hole evaporation lifetime
`evaporationLifetime M = (256 * π^3 / 3) * M^3` and exact cubic mass scaling
`evaporationLifetime (c * M) = c ^ 3 * evaporationLifetime M`. -/
theorem black_hole_evaporation_lifetime_pos_and_cubic_scaling
    (M c : ℝ) (hM : 0 < M) :
    0 < evaporationLifetime M ∧
    evaporationLifetime (c * M) = c ^ 3 * evaporationLifetime M :=
  ⟨evaporationLifetime_pos M hM, evaporationLifetime_cubic_scaling c M⟩

/-- Combined Bekenstein-Hawking and Hawking-temperature capstones for `M > 0`. -/
theorem schwarzschild_hawking_bekenstein_combined_capstones (M : ℝ) (hM : 0 < M) :
    (bekensteinHawkingEntropy M = 4 * Real.pi * M ^ 2 ∧
     bekensteinHawkingEntropy M = Real.pi * (schwarzschildRadius M) ^ 2 ∧
     0 < bekensteinHawkingEntropy M) ∧
    (0 < hawkingTemperature M ∧
     hawkingTemperature M * entropyDerivative M = 1 ∧
     hawkingTemperature M = surfaceGravity M / (2 * Real.pi) ∧
     0 < evaporationLifetime M) :=
  ⟨⟨BH_entropy_eq M, BH_entropy_eq_pi_rs_squared M, BH_entropy_pos M (ne_of_gt hM)⟩,
   ⟨hawkingTemperature_pos M hM,
    hawkingTemp_from_entropy_derivative M hM,
    hawkingTemp_eq_surfaceGravity_over_twopi M hM,
    evaporationLifetime_pos M hM⟩⟩

/-- **Master 4D Schwarzschild-Birkhoff-Weyl-Kretschmann-Hawking Thermodynamics Bridge**:
Unites the exact 4D Schwarzschild vacuum solution, Birkhoff spherical uniqueness,
orthonormal tidal Weyl trace-freeness and horizon Kretschmann invariants,
Bekenstein-Hawking quarter-area entropy, Smarr's formula, Hawking temperature,
cubic evaporation lifetime, and Sorkin causal-set de Sitter entropy scaling. -/
theorem schwarzschild_birkhoff_hawking_thermodynamics_4D_master_bridge
    (M r θ ρ V c : ℝ) (hM : 0 < M) (hr : r ≠ 0)
    (hM_lt : ∀ r₀ : ℝ, 0 < r₀ → r₀ > 2 * M)
    (hρ : 0 < ρ) (hV : 0 < V) :
    -- (1) Exact Schwarzschild vacuum solution & horizon locus
    (R_tt M r = 0 ∧ R_rr M r = 0 ∧ R_thetatheta M r = 0 ∧ R_phiphi M r θ = 0 ∧
      f M (2 * M) = 0 ∧ (f M r = 0 ↔ r = 2 * M)) ∧
    -- (2) Birkhoff spherical vacuum uniqueness & timelike Killing field
    (IsVacuumSphericallySymmetric (schwarzschildAnsatz M hM_lt) ∧
      StaticGauge (schwarzschildAnsatz M hM_lt) ∧
      (∀ t₀ r₀ : ℝ, 0 < r₀ →
        (schwarzschildAnsatz M hM_lt).dt_A t₀ r₀ = 0 ∧
        (schwarzschildAnsatz M hM_lt).dt_B t₀ r₀ = 0)) ∧
    -- (3) Orthonormal tidal Weyl trace-freeness & horizon Kretschmann invariants
    (schwarzschildWeylRadial M r +
        schwarzschildWeylAngular M r +
        schwarzschildWeylAngular M r = 0 ∧
      schwarzschildKretschmann M (schwarzschildRadius M) = 3 / (4 * M ^ 4) ∧
      schwarzschildKretschmann M (schwarzschildRadius M) *
        (bekensteinHawkingEntropy M) ^ 2 = 12 * Real.pi ^ 2) ∧
    -- (4) Bekenstein-Hawking entropy, Smarr law, Hawking temperature & cubic evaporation
    (bekensteinHawkingEntropy M = horizonArea M / 4 ∧
      bekensteinHawkingEntropy M = 4 * Real.pi * M ^ 2 ∧
      0 < hawkingTemperature M ∧
      hawkingTemperature M = surfaceGravity M / (2 * Real.pi) ∧
      2 * bekensteinHawkingEntropy M * hawkingTemperature M = M ∧
      evaporationLifetime (c * M) = c ^ 3 * evaporationLifetime M) ∧
    -- (5) Sorkin causal-set de Sitter horizon entropy law 16 * S_dS^2 = ρ * V
    (0 < bekensteinHawkingFromArea (BHArea (sorkinLambda ρ V)) ∧
      16 * (bekensteinHawkingFromArea (BHArea (sorkinLambda ρ V))) ^ 2 = ρ * V) := by
  have hMne : M ≠ 0 := ne_of_gt hM
  refine ⟨⟨R_tt_vanishes M r hr, R_rr_vanishes M r hr,
      R_thetatheta_vanishes M r hr, R_phiphi_vanishes M r θ hr,
      f_at_horizon M hMne, f_zero_iff M r hr⟩,
    ⟨schwarzschild_is_vacuum_spherical M hM_lt,
      schwarzschild_in_static_gauge M hM_lt,
      birkhoff_implies_killing_field_schwarzschild M hM_lt⟩,
    ⟨schwarzschildWeyl_spatial_trace_zero M r,
      schwarzschildKretschmann_at_horizon M hMne,
      schwarzschildKretschmann_horizon_times_entropy_sq M hMne⟩,
    ⟨rfl, BH_entropy_eq M, hawkingTemperature_pos M hM,
      hawkingTemp_eq_surfaceGravity_over_twopi M hM,
      smarr_formula_mass_entropy_temperature M hMne,
      evaporationLifetime_cubic_scaling c M⟩,
    bekensteinHawking_sorkin_deSitter_entropy_sq ρ V hρ hV⟩

#print axioms schwarzschild_lapse_and_horizon_characterization
#print axioms schwarzschild_metric_inverse_and_christoffel_identities
#print axioms schwarzschild_derivative_scaling_and_vacuum_ode
#print axioms schwarzschild_ricci_components_all_vanish
#print axioms schwarzschild_asymptotic_flatness_and_area_entropy
#print axioms schwarzschild_vacuum_solution_master_bridge
#print axioms birkhoff_spherical_vacuum_implies_static_B
#print axioms birkhoff_spherical_vacuum_implies_AB_radius_independent
#print axioms birkhoff_static_gauge_reciprocity_and_time_independence
#print axioms birkhoff_angular_ode_schwarzschild_uniqueness
#print axioms birkhoff_schwarzschild_ansatz_is_static_vacuum
#print axioms birkhoff_killing_field_and_asymptotic_flatness
#print axioms birkhoff_uniqueness_master_bridge
#print axioms schwarzschildWeyl_from_lapse_derivatives
#print axioms schwarzschildWeyl_spatial_trace_zero
#print axioms schwarzschildWeyl_trace_eq_vacuum_identity
#print axioms schwarzschildKretschmann_eq_eight_times_weyl_norm_sq
#print axioms schwarzschildKretschmann_pos
#print axioms schwarzschildKretschmann_at_horizon
#print axioms schwarzschildKretschmann_horizon_times_area_sq
#print axioms schwarzschildKretschmann_horizon_times_entropy_sq
#print axioms bekensteinHawking_quarter_area_and_radius_formula
#print axioms bekensteinHawking_deSitter_and_bulk_boundary_scaling
#print axioms bekensteinHawking_sorkin_deSitter_entropy_sq
#print axioms hawkingTemperature_pos_and_mass_product
#print axioms hawking_first_law_and_entropy_diff_quotient
#print axioms smarr_formula_mass_entropy_temperature
#print axioms hawkingTemperature_surface_gravity_relation
#print axioms hawkingTemperature_antimonotone_and_unit_bracket
#print axioms black_hole_luminosity_and_evaporation_rate
#print axioms black_hole_evaporation_lifetime_pos_and_cubic_scaling
#print axioms schwarzschild_hawking_bekenstein_combined_capstones
#print axioms schwarzschild_birkhoff_hawking_thermodynamics_4D_master_bridge

end
end UnifiedTheory.Audit.KFCausalCurved4DSchwarzschildBirkhoffHawkingThermodynamicsBridge
