/- Five-Operator `(T, P, G, S, H)` Six-Parameter `(a, b, c, d, e, f_param)` Higher-Power
Cross-Resolvent Hexagon Cocycles, Common-Domain Regularity, and Simultaneous Six-Parameter
Yosida Cross-Rate Bounds. -/
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorFiveParameterHigherPowerPentagonCocycleAndYosida

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorSixParameterHigherPowerHexagonCocycleAndYosida

noncomputable section

open scoped Topology InnerProduct
open KFCausalPositiveResolventBounds (Resolves)
open KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence
  (iteratedResolventPower iteratedIdentityPower)
open KFCausalClockFloorFiveOperatorHigherPowerSecondResolventCrossIdentity
  (FiveOperatorResolventSystem)
open KFCausalClockFloorFiveOperatorTwoParameterHigherPowerCrossResolvent
  (TwoParameterFiveOperatorSystem
   twoParam_iteratedResolventPower_cross_sub_norm_bound
   twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
   twoParam_cross_sub_succ_mem_first_domain
   twoParameterFiveOperator_common_domain_yosida_cross_rate_bounds)
open UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorThreeParameterHigherPowerCocycleAndYosida
  (ThreeParameterFiveOperatorSystem)
open UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorFourParameterHigherPowerCocycleAndYosida
  (FourParameterFiveOperatorSystem
   fourParam_iteratedResolventPower_quadrangle_cocycle
   fourParam_iteratedIdentityPower_quadrangle_cocycle
   fourParam_cross_sub_succ_mem_domains
   fourParam_iteratedResolventPower_quadrangle_norm_bounds
   fourParam_iteratedIdentityPower_quadrangle_rate_bounds
   fourParam_potential_growing_residual_hamiltonian_package
   fourParam_potential_static_residual_hamiltonian_package
   fourParameterFiveOperator_common_domain_yosida_rates)
open UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorFiveParameterHigherPowerPentagonCocycleAndYosida
  (FiveParameterFiveOperatorSystem
   fiveParam_iteratedResolventPower_pentagon_cocycle
   fiveParam_iteratedResolventPower_pentagon_norm_bounds
   fiveParam_iteratedIdentityPower_pentagon_rate_bounds
   fiveParam_potential_static_growing_residual_hamiltonian_package
   fiveParam_static_potential_growing_residual_hamiltonian_package
   fiveParameterFiveOperator_common_domain_yosida_rates)

section AbstractFiveOperatorSixParameterHexagon

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact 6-parameter `(a, b, c, d, e, f_param)` hexagon cocycle vanishing and 5-hop chain
decomposition for `iteratedResolventPower` and `iteratedIdentityPower`. -/
theorem sixParam_iteratedResolventPower_hexagon_cocycle
    (R₁ R₂ R₃ R₄ R₅ R₆ : H →L[ℂ] H) (a b c d e f_param : ℝ) (r : ℕ) (f : H) :
    (iteratedResolventPower R₁ r f - iteratedResolventPower R₂ r f) +
      (iteratedResolventPower R₂ r f - iteratedResolventPower R₃ r f) +
      (iteratedResolventPower R₃ r f - iteratedResolventPower R₄ r f) +
      (iteratedResolventPower R₄ r f - iteratedResolventPower R₅ r f) +
      (iteratedResolventPower R₅ r f - iteratedResolventPower R₆ r f) +
      (iteratedResolventPower R₆ r f - iteratedResolventPower R₁ r f) = 0 ∧
    (iteratedIdentityPower R₁ a r f - iteratedIdentityPower R₂ b r f) +
      (iteratedIdentityPower R₂ b r f - iteratedIdentityPower R₃ c r f) +
      (iteratedIdentityPower R₃ c r f - iteratedIdentityPower R₄ d r f) +
      (iteratedIdentityPower R₄ d r f - iteratedIdentityPower R₅ e r f) +
      (iteratedIdentityPower R₅ e r f - iteratedIdentityPower R₆ f_param r f) +
      (iteratedIdentityPower R₆ f_param r f - iteratedIdentityPower R₁ a r f) = 0 ∧
    iteratedResolventPower R₁ r f - iteratedResolventPower R₆ r f =
      (iteratedResolventPower R₁ r f - iteratedResolventPower R₂ r f) +
        (iteratedResolventPower R₂ r f - iteratedResolventPower R₃ r f) +
        (iteratedResolventPower R₃ r f - iteratedResolventPower R₄ r f) +
        (iteratedResolventPower R₄ r f - iteratedResolventPower R₅ r f) +
        (iteratedResolventPower R₅ r f - iteratedResolventPower R₆ r f) ∧
    iteratedIdentityPower R₁ a r f - iteratedIdentityPower R₆ f_param r f =
      (iteratedIdentityPower R₁ a r f - iteratedIdentityPower R₂ b r f) +
        (iteratedIdentityPower R₂ b r f - iteratedIdentityPower R₃ c r f) +
        (iteratedIdentityPower R₃ c r f - iteratedIdentityPower R₄ d r f) +
        (iteratedIdentityPower R₄ d r f - iteratedIdentityPower R₅ e r f) +
        (iteratedIdentityPower R₅ e r f - iteratedIdentityPower R₆ f_param r f) := by
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Six-parameter `(a, b, c, d, e, f_param)` five-hop geometric norm bound and direct bound
for six positive operators `(A₁, A₂, A₃, A₄, A₅, A₆)`. -/
theorem sixParam_iteratedResolventPower_hexagon_norm_bounds
    (A₁ A₂ A₃ A₄ A₅ A₆ : H →ₗ.[ℂ] H) (R₁ R₂ R₃ R₄ R₅ R₆ : H →L[ℂ] H)
    (a b c d e f_param : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param)
    (hr₁ : Resolves A₁ R₁ a) (hr₂ : Resolves A₂ R₂ b)
    (hr₃ : Resolves A₃ R₃ c) (hr₄ : Resolves A₄ R₄ d) (hr₅ : Resolves A₅ R₅ e) (hr₆ : Resolves A₆ R₆ f_param)
    (hp₁ : ∀ z : A₁.domain, 0 ≤ (inner ℂ (A₁ z) (z : H)).re)
    (hp₂ : ∀ z : A₂.domain, 0 ≤ (inner ℂ (A₂ z) (z : H)).re)
    (hp₃ : ∀ z : A₃.domain, 0 ≤ (inner ℂ (A₃ z) (z : H)).re)
    (hp₄ : ∀ z : A₄.domain, 0 ≤ (inner ℂ (A₄ z) (z : H)).re)
    (hp₅ : ∀ z : A₅.domain, 0 ≤ (inner ℂ (A₅ z) (z : H)).re)
    (hp₆ : ∀ z : A₆.domain, 0 ≤ (inner ℂ (A₆ z) (z : H)).re)
    (r : ℕ) (f : H) :
    ‖iteratedResolventPower R₁ r f - iteratedResolventPower R₆ r f‖ ≤
      ‖iteratedResolventPower R₁ r f - iteratedResolventPower R₂ r f‖ +
        ‖iteratedResolventPower R₂ r f - iteratedResolventPower R₃ r f‖ +
        ‖iteratedResolventPower R₃ r f - iteratedResolventPower R₄ r f‖ +
        ‖iteratedResolventPower R₄ r f - iteratedResolventPower R₅ r f‖ +
        ‖iteratedResolventPower R₅ r f - iteratedResolventPower R₆ r f‖ ∧
    ‖iteratedResolventPower R₁ r f - iteratedResolventPower R₂ r f‖ +
        ‖iteratedResolventPower R₂ r f - iteratedResolventPower R₃ r f‖ +
        ‖iteratedResolventPower R₃ r f - iteratedResolventPower R₄ r f‖ +
        ‖iteratedResolventPower R₄ r f - iteratedResolventPower R₅ r f‖ +
        ‖iteratedResolventPower R₅ r f - iteratedResolventPower R₆ r f‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r + (f_param⁻¹) ^ r) * ‖f‖ ∧
    ‖iteratedResolventPower R₁ r f - iteratedResolventPower R₆ r f‖ ≤
      ((a⁻¹) ^ r + (f_param⁻¹) ^ r) * ‖f‖ := by
  have h12345 := fiveParam_iteratedResolventPower_pentagon_norm_bounds
    A₁ A₂ A₃ A₄ A₅ R₁ R₂ R₃ R₄ R₅ a b c d e ha hb hc hd he hr₁ hr₂ hr₃ hr₄ hr₅ hp₁ hp₂ hp₃ hp₄ hp₅ r f
  have h56 := twoParam_iteratedResolventPower_cross_sub_norm_bound
    A₅ A₆ R₅ R₆ e f_param he hf_p hr₅ hr₆ hp₅ hp₆ r f
  have h16 := twoParam_iteratedResolventPower_cross_sub_norm_bound
    A₁ A₆ R₁ R₆ a f_param ha hf_p hr₁ hr₆ hp₁ hp₆ r f
  have h16_decomp :
      iteratedResolventPower R₁ r f - iteratedResolventPower R₆ r f =
        (iteratedResolventPower R₁ r f - iteratedResolventPower R₅ r f) +
        (iteratedResolventPower R₅ r f - iteratedResolventPower R₆ r f) := by abel
  have htri_156 := norm_add_le
    (iteratedResolventPower R₁ r f - iteratedResolventPower R₅ r f)
    (iteratedResolventPower R₅ r f - iteratedResolventPower R₆ r f)
  rw [← h16_decomp] at htri_156
  refine ⟨by linarith [h12345.1, htri_156], by linarith [h12345.2.1, h56], h16⟩

/-- Common-domain 6-parameter `(a, b, c, d, e, f_param)` mediated 5-hop Yosida cross-rate bound
for six positive operators `(A₁, A₂, A₃, A₄, A₅, A₆)`. -/
theorem sixParam_iteratedIdentityPower_hexagon_rate_bounds
    (A₁ A₂ A₃ A₄ A₅ A₆ : H →ₗ.[ℂ] H) (R₁ R₂ R₃ R₄ R₅ R₆ : H →L[ℂ] H)
    (a b c d e f_param : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param)
    (hr₁ : Resolves A₁ R₁ a) (hr₂ : Resolves A₂ R₂ b)
    (hr₃ : Resolves A₃ R₃ c) (hr₄ : Resolves A₄ R₄ d) (hr₅ : Resolves A₅ R₅ e) (hr₆ : Resolves A₆ R₆ f_param)
    (hp₁ : ∀ z : A₁.domain, 0 ≤ (inner ℂ (A₁ z) (z : H)).re)
    (hp₂ : ∀ z : A₂.domain, 0 ≤ (inner ℂ (A₂ z) (z : H)).re)
    (hp₃ : ∀ z : A₃.domain, 0 ≤ (inner ℂ (A₃ z) (z : H)).re)
    (hp₄ : ∀ z : A₄.domain, 0 ≤ (inner ℂ (A₄ z) (z : H)).re)
    (hp₅ : ∀ z : A₅.domain, 0 ≤ (inner ℂ (A₅ z) (z : H)).re)
    (hp₆ : ∀ z : A₆.domain, 0 ≤ (inner ℂ (A₆ z) (z : H)).re)
    (hl₁ : ∀ z : A₁.domain, R₁ (A₁ z + a • (z : H)) = (z : H))
    (hl₂ : ∀ z : A₂.domain, R₂ (A₂ z + b • (z : H)) = (z : H))
    (hl₃ : ∀ z : A₃.domain, R₃ (A₃ z + c • (z : H)) = (z : H))
    (hl₄ : ∀ z : A₄.domain, R₄ (A₄ z + d • (z : H)) = (z : H))
    (hl₅ : ∀ z : A₅.domain, R₅ (A₅ z + e • (z : H)) = (z : H))
    (hl₆ : ∀ z : A₆.domain, R₆ (A₆ z + f_param • (z : H)) = (z : H))
    (r : ℕ) (z : H)
    (hz₁ : z ∈ A₁.domain) (hz₂ : z ∈ A₂.domain) (hz₃ : z ∈ A₃.domain)
    (hz₄ : z ∈ A₄.domain) (hz₅ : z ∈ A₅.domain) (hz₆ : z ∈ A₆.domain) :
    ‖iteratedIdentityPower R₁ a r z - iteratedIdentityPower R₂ b r z‖ +
      ‖iteratedIdentityPower R₂ b r z - iteratedIdentityPower R₃ c r z‖ +
      ‖iteratedIdentityPower R₃ c r z - iteratedIdentityPower R₄ d r z‖ +
      ‖iteratedIdentityPower R₄ d r z - iteratedIdentityPower R₅ e r z‖ +
      ‖iteratedIdentityPower R₅ e r z - iteratedIdentityPower R₆ f_param r z‖ ≤
      (r : ℝ) * a⁻¹ * ‖A₁ ⟨z, hz₁⟩‖ +
        2 * (r : ℝ) * b⁻¹ * ‖A₂ ⟨z, hz₂⟩‖ +
        2 * (r : ℝ) * c⁻¹ * ‖A₃ ⟨z, hz₃⟩‖ +
        2 * (r : ℝ) * d⁻¹ * ‖A₄ ⟨z, hz₄⟩‖ +
        2 * (r : ℝ) * e⁻¹ * ‖A₅ ⟨z, hz₅⟩‖ +
        (r : ℝ) * f_param⁻¹ * ‖A₆ ⟨z, hz₆⟩‖ ∧
    ‖iteratedIdentityPower R₁ a r z - iteratedIdentityPower R₆ f_param r z‖ ≤
      (r : ℝ) * a⁻¹ * ‖A₁ ⟨z, hz₁⟩‖ + (r : ℝ) * f_param⁻¹ * ‖A₆ ⟨z, hz₆⟩‖ := by
  have h12345 := fiveParam_iteratedIdentityPower_pentagon_rate_bounds
    A₁ A₂ A₃ A₄ A₅ R₁ R₂ R₃ R₄ R₅ a b c d e ha hb hc hd he
    hr₁ hr₂ hr₃ hr₄ hr₅ hp₁ hp₂ hp₃ hp₄ hp₅ hl₁ hl₂ hl₃ hl₄ hl₅ r z hz₁ hz₂ hz₃ hz₄ hz₅
  have h56 := twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
    A₅ A₆ R₅ R₆ e f_param he hf_p hr₅ hr₆ hp₅ hp₆ hl₅ hl₆ r z hz₅ hz₆
  have h16 := twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
    A₁ A₆ R₁ R₆ a f_param ha hf_p hr₁ hr₆ hp₁ hp₆ hl₁ hl₆ r z hz₁ hz₆
  refine ⟨by linarith [h12345.1, h56], h16⟩

/-- Six-parameter `(a, b, c, d, e, f_param)` five-operator resolvent system extending
`FiveParameterFiveOperatorSystem H a b c d e` with a sixth spectral parameter `f_param` sharing the
same five operators `(T, P, G, S, H_op, K)`. -/
structure SixParameterFiveOperatorSystem
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (a b c d e f_param : ℝ) where
  pentABCDE : FiveParameterFiveOperatorSystem H a b c d e
  sysF : FiveOperatorResolventSystem H f_param
  same_T_F : sysF.T = pentABCDE.quadABCD.trABC.sysA.T
  same_P_F : sysF.P = pentABCDE.quadABCD.trABC.sysA.P
  same_G_F : sysF.G = pentABCDE.quadABCD.trABC.sysA.G
  same_S_F : sysF.S = pentABCDE.quadABCD.trABC.sysA.S
  same_H_F : sysF.H_op = pentABCDE.quadABCD.trABC.sysA.H_op
  same_K_F : sysF.K = pentABCDE.quadABCD.trABC.sysA.K

/-- Canonical projection from `SixParameterFiveOperatorSystem H a b c d e f_param` to the
`(a, b, c, d, f_param)` `FiveParameterFiveOperatorSystem H a b c d f_param`. -/
def SixParameterFiveOperatorSystem.toFiveABCDF
    {a b c d e f_param : ℝ} (sixsys : SixParameterFiveOperatorSystem H a b c d e f_param) :
    FiveParameterFiveOperatorSystem H a b c d f_param where
  quadABCD := sixsys.pentABCDE.quadABCD
  sysE := sixsys.sysF
  same_T_E := sixsys.same_T_F
  same_P_E := sixsys.same_P_F
  same_G_E := sixsys.same_G_F
  same_S_E := sixsys.same_S_F
  same_H_E := sixsys.same_H_F
  same_K_E := sixsys.same_K_F

/-- Complete six-parameter `(P_a, T_b, G_c, S_d, H_e, H_f)` hexagon cocycle, `sysA.P.domain`
regularity at order `r + 1`, and 5-hop geometric norm bound. -/
theorem sixParam_potential_static_growing_residual_hamiltonian_hexagon_package
    {a b c d e f_param : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param)
    (sixsys : SixParameterFiveOperatorSystem H a b c d e f_param) (r : ℕ) (f : H) :
    (iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysA.RP r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysB.RT r f) +
      (iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysB.RT r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG r f) +
      (iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.sysD.RS r f) +
      (iteratedResolventPower sixsys.pentABCDE.quadABCD.sysD.RS r f -
        iteratedResolventPower sixsys.pentABCDE.sysE.RH r f) +
      (iteratedResolventPower sixsys.pentABCDE.sysE.RH r f -
        iteratedResolventPower sixsys.sysF.RH r f) +
      (iteratedResolventPower sixsys.sysF.RH r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysA.RP r f) = 0 ∧
    iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysA.RP (r + 1) f -
        iteratedResolventPower sixsys.sysF.RH (r + 1) f ∈
      sixsys.pentABCDE.quadABCD.trABC.sysA.P.domain ∧
    ‖iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysA.RP r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysB.RT r f‖ +
      ‖iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysB.RT r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG r f‖ +
      ‖iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.sysD.RS r f‖ +
      ‖iteratedResolventPower sixsys.pentABCDE.quadABCD.sysD.RS r f -
        iteratedResolventPower sixsys.pentABCDE.sysE.RH r f‖ +
      ‖iteratedResolventPower sixsys.pentABCDE.sysE.RH r f -
        iteratedResolventPower sixsys.sysF.RH r f‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r + (f_param⁻¹) ^ r) * ‖f‖ := by
  have hpABCDF := fiveParam_potential_static_growing_residual_hamiltonian_package
    ha hb hc hd hf_p sixsys.toFiveABCDF r f
  have hnorm := (sixParam_iteratedResolventPower_hexagon_norm_bounds
    sixsys.pentABCDE.quadABCD.trABC.sysA.P sixsys.pentABCDE.quadABCD.trABC.sysB.T
    sixsys.pentABCDE.quadABCD.trABC.sysC.G sixsys.pentABCDE.quadABCD.sysD.S
    sixsys.pentABCDE.sysE.H_op sixsys.sysF.H_op
    sixsys.pentABCDE.quadABCD.trABC.sysA.RP sixsys.pentABCDE.quadABCD.trABC.sysB.RT
    sixsys.pentABCDE.quadABCD.trABC.sysC.RG sixsys.pentABCDE.quadABCD.sysD.RS
    sixsys.pentABCDE.sysE.RH sixsys.sysF.RH
    a b c d e f_param ha hb hc hd he hf_p
    sixsys.pentABCDE.quadABCD.trABC.sysA.res_P sixsys.pentABCDE.quadABCD.trABC.sysB.res_T
    sixsys.pentABCDE.quadABCD.trABC.sysC.res_G sixsys.pentABCDE.quadABCD.sysD.res_S
    sixsys.pentABCDE.sysE.res_H sixsys.sysF.res_H
    sixsys.pentABCDE.quadABCD.trABC.sysA.pos_P sixsys.pentABCDE.quadABCD.trABC.sysB.pos_T
    sixsys.pentABCDE.quadABCD.trABC.sysC.pos_G sixsys.pentABCDE.quadABCD.sysD.pos_S
    sixsys.pentABCDE.sysE.pos_H sixsys.sysF.pos_H
    r f).2.1
  exact ⟨by abel, hpABCDF.2.1, hnorm⟩

/-- Complete six-parameter `(T_a, P_b, G_c, S_d, H_e, H_f)` hexagon cocycle, `sysA.T.domain`
regularity at order `r + 1`, and 5-hop geometric norm bound. -/
theorem sixParam_static_potential_growing_residual_hamiltonian_hexagon_package
    {a b c d e f_param : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param)
    (sixsys : SixParameterFiveOperatorSystem H a b c d e f_param) (r : ℕ) (f : H) :
    (iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysA.RT r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysB.RP r f) +
      (iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysB.RP r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG r f) +
      (iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.sysD.RS r f) +
      (iteratedResolventPower sixsys.pentABCDE.quadABCD.sysD.RS r f -
        iteratedResolventPower sixsys.pentABCDE.sysE.RH r f) +
      (iteratedResolventPower sixsys.pentABCDE.sysE.RH r f -
        iteratedResolventPower sixsys.sysF.RH r f) +
      (iteratedResolventPower sixsys.sysF.RH r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysA.RT r f) = 0 ∧
    iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysA.RT (r + 1) f -
        iteratedResolventPower sixsys.sysF.RH (r + 1) f ∈
      sixsys.pentABCDE.quadABCD.trABC.sysA.T.domain ∧
    ‖iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysA.RT r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysB.RP r f‖ +
      ‖iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysB.RP r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG r f‖ +
      ‖iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.sysD.RS r f‖ +
      ‖iteratedResolventPower sixsys.pentABCDE.quadABCD.sysD.RS r f -
        iteratedResolventPower sixsys.pentABCDE.sysE.RH r f‖ +
      ‖iteratedResolventPower sixsys.pentABCDE.sysE.RH r f -
        iteratedResolventPower sixsys.sysF.RH r f‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r + (f_param⁻¹) ^ r) * ‖f‖ := by
  have hpABCDF := fiveParam_static_potential_growing_residual_hamiltonian_package
    ha hb hc hd hf_p sixsys.toFiveABCDF r f
  have hnorm := (sixParam_iteratedResolventPower_hexagon_norm_bounds
    sixsys.pentABCDE.quadABCD.trABC.sysA.T sixsys.pentABCDE.quadABCD.trABC.sysB.P
    sixsys.pentABCDE.quadABCD.trABC.sysC.G sixsys.pentABCDE.quadABCD.sysD.S
    sixsys.pentABCDE.sysE.H_op sixsys.sysF.H_op
    sixsys.pentABCDE.quadABCD.trABC.sysA.RT sixsys.pentABCDE.quadABCD.trABC.sysB.RP
    sixsys.pentABCDE.quadABCD.trABC.sysC.RG sixsys.pentABCDE.quadABCD.sysD.RS
    sixsys.pentABCDE.sysE.RH sixsys.sysF.RH
    a b c d e f_param ha hb hc hd he hf_p
    sixsys.pentABCDE.quadABCD.trABC.sysA.res_T sixsys.pentABCDE.quadABCD.trABC.sysB.res_P
    sixsys.pentABCDE.quadABCD.trABC.sysC.res_G sixsys.pentABCDE.quadABCD.sysD.res_S
    sixsys.pentABCDE.sysE.res_H sixsys.sysF.res_H
    sixsys.pentABCDE.quadABCD.trABC.sysA.pos_T sixsys.pentABCDE.quadABCD.trABC.sysB.pos_P
    sixsys.pentABCDE.quadABCD.trABC.sysC.pos_G sixsys.pentABCDE.quadABCD.sysD.pos_S
    sixsys.pentABCDE.sysE.pos_H sixsys.sysF.pos_H
    r f).2.1
  exact ⟨by abel, hpABCDF.2.1, hnorm⟩

/-- Simultaneous common-domain 6-parameter `(P_a, T_b, G_c, S_d, H_e, H_f)` mediated Yosida
cross-rate bounds across all six legs on `z : sixsys.pentABCDE.quadABCD.trABC.sysA.H_op.domain`. -/
theorem sixParameterFiveOperator_common_domain_yosida_rates
    {a b c d e f_param : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param)
    (sixsys : SixParameterFiveOperatorSystem H a b c d e f_param)
    (r : ℕ) (z : sixsys.pentABCDE.quadABCD.trABC.sysA.H_op.domain) :
    let hGA : (z : H) ∈ sixsys.pentABCDE.quadABCD.trABC.sysA.G.domain :=
      sixsys.pentABCDE.quadABCD.trABC.sysA.dom_HG z.property
    let hPA : (z : H) ∈ sixsys.pentABCDE.quadABCD.trABC.sysA.P.domain :=
      sixsys.pentABCDE.quadABCD.trABC.sysA.dom_GP hGA
    let hHB : (z : H) ∈ sixsys.pentABCDE.quadABCD.trABC.sysB.H_op.domain :=
      sixsys.pentABCDE.quadABCD.trABC.same_H_B.symm ▸ z.property
    let hSB : (z : H) ∈ sixsys.pentABCDE.quadABCD.trABC.sysB.S.domain :=
      sixsys.pentABCDE.quadABCD.trABC.sysB.dom_HS hHB
    let hTB : (z : H) ∈ sixsys.pentABCDE.quadABCD.trABC.sysB.T.domain :=
      sixsys.pentABCDE.quadABCD.trABC.sysB.dom_ST hSB
    let hHC : (z : H) ∈ sixsys.pentABCDE.quadABCD.trABC.sysC.H_op.domain :=
      sixsys.pentABCDE.quadABCD.trABC.same_H_C.symm ▸ z.property
    let hGC : (z : H) ∈ sixsys.pentABCDE.quadABCD.trABC.sysC.G.domain :=
      sixsys.pentABCDE.quadABCD.trABC.sysC.dom_HG hHC
    let hHD : (z : H) ∈ sixsys.pentABCDE.quadABCD.sysD.H_op.domain :=
      sixsys.pentABCDE.quadABCD.same_H_D.symm ▸ z.property
    let hSD : (z : H) ∈ sixsys.pentABCDE.quadABCD.sysD.S.domain :=
      sixsys.pentABCDE.quadABCD.sysD.dom_HS hHD
    let hHE : (z : H) ∈ sixsys.pentABCDE.sysE.H_op.domain :=
      sixsys.pentABCDE.same_H_E.symm ▸ z.property
    let hHF : (z : H) ∈ sixsys.sysF.H_op.domain :=
      sixsys.same_H_F.symm ▸ z.property
    ‖iteratedIdentityPower sixsys.pentABCDE.quadABCD.trABC.sysA.RP a r (z : H) -
        iteratedIdentityPower sixsys.pentABCDE.quadABCD.trABC.sysB.RT b r (z : H)‖ +
      ‖iteratedIdentityPower sixsys.pentABCDE.quadABCD.trABC.sysB.RT b r (z : H) -
        iteratedIdentityPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG c r (z : H)‖ +
      ‖iteratedIdentityPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG c r (z : H) -
        iteratedIdentityPower sixsys.pentABCDE.quadABCD.sysD.RS d r (z : H)‖ +
      ‖iteratedIdentityPower sixsys.pentABCDE.quadABCD.sysD.RS d r (z : H) -
        iteratedIdentityPower sixsys.pentABCDE.sysE.RH e r (z : H)‖ +
      ‖iteratedIdentityPower sixsys.pentABCDE.sysE.RH e r (z : H) -
        iteratedIdentityPower sixsys.sysF.RH f_param r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖sixsys.pentABCDE.quadABCD.trABC.sysA.P ⟨(z : H), hPA⟩‖ +
        2 * (r : ℝ) * b⁻¹ * ‖sixsys.pentABCDE.quadABCD.trABC.sysB.T ⟨(z : H), hTB⟩‖ +
        2 * (r : ℝ) * c⁻¹ * ‖sixsys.pentABCDE.quadABCD.trABC.sysC.G ⟨(z : H), hGC⟩‖ +
        2 * (r : ℝ) * d⁻¹ * ‖sixsys.pentABCDE.quadABCD.sysD.S ⟨(z : H), hSD⟩‖ +
        2 * (r : ℝ) * e⁻¹ * ‖sixsys.pentABCDE.sysE.H_op ⟨(z : H), hHE⟩‖ +
        (r : ℝ) * f_param⁻¹ * ‖sixsys.sysF.H_op ⟨(z : H), hHF⟩‖ ∧
    ‖iteratedIdentityPower sixsys.pentABCDE.quadABCD.trABC.sysA.RP a r (z : H) -
        iteratedIdentityPower sixsys.sysF.RH f_param r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖sixsys.pentABCDE.quadABCD.trABC.sysA.P ⟨(z : H), hPA⟩‖ +
        (r : ℝ) * f_param⁻¹ * ‖sixsys.sysF.H_op ⟨(z : H), hHF⟩‖ := by
  intro hGA hPA hHB hSB hTB hHC hGC hHD hSD hHE hHF
  exact sixParam_iteratedIdentityPower_hexagon_rate_bounds
    sixsys.pentABCDE.quadABCD.trABC.sysA.P sixsys.pentABCDE.quadABCD.trABC.sysB.T
    sixsys.pentABCDE.quadABCD.trABC.sysC.G sixsys.pentABCDE.quadABCD.sysD.S
    sixsys.pentABCDE.sysE.H_op sixsys.sysF.H_op
    sixsys.pentABCDE.quadABCD.trABC.sysA.RP sixsys.pentABCDE.quadABCD.trABC.sysB.RT
    sixsys.pentABCDE.quadABCD.trABC.sysC.RG sixsys.pentABCDE.quadABCD.sysD.RS
    sixsys.pentABCDE.sysE.RH sixsys.sysF.RH
    a b c d e f_param ha hb hc hd he hf_p
    sixsys.pentABCDE.quadABCD.trABC.sysA.res_P sixsys.pentABCDE.quadABCD.trABC.sysB.res_T
    sixsys.pentABCDE.quadABCD.trABC.sysC.res_G sixsys.pentABCDE.quadABCD.sysD.res_S
    sixsys.pentABCDE.sysE.res_H sixsys.sysF.res_H
    sixsys.pentABCDE.quadABCD.trABC.sysA.pos_P sixsys.pentABCDE.quadABCD.trABC.sysB.pos_T
    sixsys.pentABCDE.quadABCD.trABC.sysC.pos_G sixsys.pentABCDE.quadABCD.sysD.pos_S
    sixsys.pentABCDE.sysE.pos_H sixsys.sysF.pos_H
    sixsys.pentABCDE.quadABCD.trABC.sysA.left_P sixsys.pentABCDE.quadABCD.trABC.sysB.left_T
    sixsys.pentABCDE.quadABCD.trABC.sysC.left_G sixsys.pentABCDE.quadABCD.sysD.left_S
    sixsys.pentABCDE.sysE.left_H sixsys.sysF.left_H
    r (z : H) hPA hTB hGC hSD hHE hHF

/-- Master Five-Operator Six-Parameter `(a, b, c, d, e, f_param)` Higher-Power Cross-Resolvent
Hexagon Cocycle and Yosida Rate Synthesis Theorem. -/
theorem fiveOperator_sixParameter_higherPower_hexagon_cocycle_and_yosida_master_synthesis
    {a b c d e f_param : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param)
    (sixsys : SixParameterFiveOperatorSystem H a b c d e f_param)
    (r : ℕ) (f : H) (z : sixsys.pentABCDE.quadABCD.trABC.sysA.H_op.domain) :
    ((iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysA.RP r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysB.RT r f) +
      (iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysB.RT r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG r f) +
      (iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.sysD.RS r f) +
      (iteratedResolventPower sixsys.pentABCDE.quadABCD.sysD.RS r f -
        iteratedResolventPower sixsys.pentABCDE.sysE.RH r f) +
      (iteratedResolventPower sixsys.pentABCDE.sysE.RH r f -
        iteratedResolventPower sixsys.sysF.RH r f) +
      (iteratedResolventPower sixsys.sysF.RH r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysA.RP r f) = 0 ∧
     iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysA.RP (r + 1) f -
        iteratedResolventPower sixsys.sysF.RH (r + 1) f ∈
      sixsys.pentABCDE.quadABCD.trABC.sysA.P.domain ∧
     iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysA.RT (r + 1) f -
        iteratedResolventPower sixsys.sysF.RH (r + 1) f ∈
      sixsys.pentABCDE.quadABCD.trABC.sysA.T.domain ∧
     ‖iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysA.RP r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysB.RT r f‖ +
       ‖iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysB.RT r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG r f‖ +
       ‖iteratedResolventPower sixsys.pentABCDE.quadABCD.trABC.sysC.RG r f -
        iteratedResolventPower sixsys.pentABCDE.quadABCD.sysD.RS r f‖ +
       ‖iteratedResolventPower sixsys.pentABCDE.quadABCD.sysD.RS r f -
        iteratedResolventPower sixsys.pentABCDE.sysE.RH r f‖ +
       ‖iteratedResolventPower sixsys.pentABCDE.sysE.RH r f -
        iteratedResolventPower sixsys.sysF.RH r f‖ ≤
       ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r + (f_param⁻¹) ^ r) * ‖f‖) ∧
    (let hGA : (z : H) ∈ sixsys.pentABCDE.quadABCD.trABC.sysA.G.domain :=
       sixsys.pentABCDE.quadABCD.trABC.sysA.dom_HG z.property
     let hPA : (z : H) ∈ sixsys.pentABCDE.quadABCD.trABC.sysA.P.domain :=
       sixsys.pentABCDE.quadABCD.trABC.sysA.dom_GP hGA
     let hHF : (z : H) ∈ sixsys.sysF.H_op.domain :=
       sixsys.same_H_F.symm ▸ z.property
     ‖iteratedIdentityPower sixsys.pentABCDE.quadABCD.trABC.sysA.RP a r (z : H) -
        iteratedIdentityPower sixsys.sysF.RH f_param r (z : H)‖ ≤
       (r : ℝ) * a⁻¹ * ‖sixsys.pentABCDE.quadABCD.trABC.sysA.P ⟨(z : H), hPA⟩‖ +
         (r : ℝ) * f_param⁻¹ * ‖sixsys.sysF.H_op ⟨(z : H), hHF⟩‖) := by
  have hp1 := sixParam_potential_static_growing_residual_hamiltonian_hexagon_package
    ha hb hc hd he hf_p sixsys r f
  have hp2 := sixParam_static_potential_growing_residual_hamiltonian_hexagon_package
    ha hb hc hd he hf_p sixsys r f
  have hyos := sixParameterFiveOperator_common_domain_yosida_rates
    ha hb hc hd he hf_p sixsys r z
  exact ⟨⟨hp1.1, hp1.2.1, hp2.2.1, hp1.2.2⟩, hyos.2⟩

end AbstractFiveOperatorSixParameterHexagon

#print axioms sixParam_iteratedResolventPower_hexagon_cocycle
#print axioms sixParam_iteratedResolventPower_hexagon_norm_bounds
#print axioms sixParam_iteratedIdentityPower_hexagon_rate_bounds
#print axioms sixParam_potential_static_growing_residual_hamiltonian_hexagon_package
#print axioms sixParam_static_potential_growing_residual_hamiltonian_hexagon_package
#print axioms sixParameterFiveOperator_common_domain_yosida_rates
#print axioms fiveOperator_sixParameter_higherPower_hexagon_cocycle_and_yosida_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorSixParameterHigherPowerHexagonCocycleAndYosida
