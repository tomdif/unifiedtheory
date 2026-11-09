/- Five-Operator Four-Parameter `(a, b, c, d)` Higher-Power Cross-Resolvent Quadrangle Cocycles,
Three-Hop `(P_a, G_b, S_c, H_d)` Chain Decompositions, and Four-Parameter Yosida Cross-Rate Bounds:
1. Establishes the general four-parameter `(a, b, c, d)` cross-operator iterated resolvent and
   Yosida identity quadrangle cocycle calculus for any four positive operators `(A1, A2, A3, A4)`
   resolved at independent spectral shifts `(a, b, c, d)`:
   - Exact 4-step cyclic quadrangle cocycle vanishing
     `(R1a^r f - R2b^r f) + (R2b^r f - R3c^r f) + (R3c^r f - R4d^r f) + (R4d^r f - R1a^r f) = 0`
     and its Yosida-scaled identity counterpart,
   - Mediated three-hop decomposition `R1a^r f - R4d^r f = (R1a^r f - R2b^r f) + (R2b^r f - R3c^r f) + (R3c^r f - R4d^r f)`,
   - Unconditional domain membership at order `r + 1` across `A4.domain ≤ A3.domain ≤ A2.domain ≤ A1.domain`,
   - Four-parameter mediated geometric norm bound `((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + (d⁻¹) ^ r) * ‖f‖`,
   - Four-parameter common-domain Yosida cross-rate bound
     `(r : ℝ) * a⁻¹ * ‖A1 x‖ + 2 * (r : ℝ) * b⁻¹ * ‖A2 x‖ + 2 * (r : ℝ) * c⁻¹ * ‖A3 x‖ + (r : ℝ) * d⁻¹ * ‖A4 x‖`.
2. Defines `FourParameterFiveOperatorSystem H a b c d` extending `ThreeParameterFiveOperatorSystem`
   to four spectral shifts `(a, b, c, d)` and proves the complete 4-parameter `(P_a, G_b, S_c, H_d)`
   and `(P_a, T_b, S_c, H_d)` quadrangle cocycle and Yosida rate synthesis. -/
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorThreeParameterHigherPowerCocycleAndYosida

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorFourParameterHigherPowerCocycleAndYosida

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
  (ThreeParameterFiveOperatorSystem
   threeParam_iteratedResolventPower_cyclic_cocycle
   threeParam_iteratedIdentityPower_cyclic_cocycle
   threeParam_cross_sub_succ_mem_first_domain
   threeParam_iteratedResolventPower_triangle_norm_bounds
   threeParam_iteratedIdentityPower_triangle_rate_bounds
   threeParam_static_residual_hamiltonian_package
   threeParam_potential_growing_hamiltonian_package
   threeParameterFiveOperator_common_domain_yosida_rates)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### 1. Abstract Four-Parameter Cross-Operator Quadrangle Cocycle and Three-Hop Calculus -/

/-- Exact cyclic 4-parameter quadrangle cocycle vanishing and three-hop decomposition for
`iteratedResolventPower` across any four resolvents `(R1a, R2b, R3c, R4d)`. -/
theorem fourParam_iteratedResolventPower_quadrangle_cocycle
    (R1a R2b R3c R4d : H →L[ℂ] H) (r : ℕ) (f : H) :
    (iteratedResolventPower R1a r f - iteratedResolventPower R2b r f) +
      (iteratedResolventPower R2b r f - iteratedResolventPower R3c r f) +
      (iteratedResolventPower R3c r f - iteratedResolventPower R4d r f) +
      (iteratedResolventPower R4d r f - iteratedResolventPower R1a r f) = 0 ∧
    iteratedResolventPower R1a r f - iteratedResolventPower R4d r f =
      (iteratedResolventPower R1a r f - iteratedResolventPower R2b r f) +
        (iteratedResolventPower R2b r f - iteratedResolventPower R3c r f) +
        (iteratedResolventPower R3c r f - iteratedResolventPower R4d r f) := by
  refine ⟨by abel, by abel⟩

/-- Exact cyclic 4-parameter quadrangle cocycle vanishing and three-hop decomposition for
`iteratedIdentityPower` across any four resolvents `(R1a, R2b, R3c, R4d)` at shifts `(a, b, c, d)`. -/
theorem fourParam_iteratedIdentityPower_quadrangle_cocycle
    (R1a R2b R3c R4d : H →L[ℂ] H) (a b c d : ℝ) (r : ℕ) (f : H) :
    (iteratedIdentityPower R1a a r f - iteratedIdentityPower R2b b r f) +
      (iteratedIdentityPower R2b b r f - iteratedIdentityPower R3c c r f) +
      (iteratedIdentityPower R3c c r f - iteratedIdentityPower R4d d r f) +
      (iteratedIdentityPower R4d d r f - iteratedIdentityPower R1a a r f) = 0 ∧
    iteratedIdentityPower R1a a r f - iteratedIdentityPower R4d d r f =
      (iteratedIdentityPower R1a a r f - iteratedIdentityPower R2b b r f) +
        (iteratedIdentityPower R2b b r f - iteratedIdentityPower R3c c r f) +
        (iteratedIdentityPower R3c c r f - iteratedIdentityPower R4d d r f) := by
  refine ⟨by abel, by abel⟩

/-- Unconditional domain membership at order `r + 1` across all three hops `(R1a, R2b)`,
`(R2b, R3c)`, `(R3c, R4d)` and the total span `(R1a, R4d)` whenever
`A4.domain ≤ A3.domain ≤ A2.domain ≤ A1.domain`. -/
theorem fourParam_cross_sub_succ_mem_domains
    (A1 A2 A3 A4 : H →ₗ.[ℂ] H) (R1a R2b R3c R4d : H →L[ℂ] H) (a b c d : ℝ)
    (hr1 : Resolves A1 R1a a) (hr2 : Resolves A2 R2b b)
    (hr3 : Resolves A3 R3c c) (hr4 : Resolves A4 R4d d)
    (hdom21 : A2.domain ≤ A1.domain) (hdom32 : A3.domain ≤ A2.domain)
    (hdom43 : A4.domain ≤ A3.domain)
    (r : ℕ) (f : H) :
    iteratedResolventPower R1a (r + 1) f - iteratedResolventPower R2b (r + 1) f ∈ A1.domain ∧
    iteratedResolventPower R2b (r + 1) f - iteratedResolventPower R3c (r + 1) f ∈ A2.domain ∧
    iteratedResolventPower R3c (r + 1) f - iteratedResolventPower R4d (r + 1) f ∈ A3.domain ∧
    iteratedResolventPower R1a (r + 1) f - iteratedResolventPower R4d (r + 1) f ∈ A1.domain ∧
    iteratedIdentityPower R1a a (r + 1) f - iteratedIdentityPower R4d d (r + 1) f ∈ A1.domain := by
  have h123 := threeParam_cross_sub_succ_mem_first_domain A1 A2 A3 R1a R2b R3c a b c
    hr1 hr2 hr3 hdom21 hdom32 r f
  have h34 := twoParam_cross_sub_succ_mem_first_domain A3 A4 R3c R4d c d hr3 hr4 hdom43 r f
  have h14 := twoParam_cross_sub_succ_mem_first_domain A1 A4 R1a R4d a d hr1 hr4
    (hdom43.trans (hdom32.trans hdom21)) r f
  exact ⟨h123.1, h123.2.1, h34.1, h14.1, h14.2⟩

/-- Mediated three-hop geometric norm bound and direct bound across four positive operators
`(A1, A2, A3, A4)` resolved at `a, b, c, d > 0`. -/
theorem fourParam_iteratedResolventPower_quadrangle_norm_bounds
    (A1 A2 A3 A4 : H →ₗ.[ℂ] H) (R1a R2b R3c R4d : H →L[ℂ] H)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hr1 : Resolves A1 R1a a) (hr2 : Resolves A2 R2b b)
    (hr3 : Resolves A3 R3c c) (hr4 : Resolves A4 R4d d)
    (hp1 : ∀ z : A1.domain, 0 ≤ (inner ℂ (A1 z) (z : H)).re)
    (hp2 : ∀ z : A2.domain, 0 ≤ (inner ℂ (A2 z) (z : H)).re)
    (hp3 : ∀ z : A3.domain, 0 ≤ (inner ℂ (A3 z) (z : H)).re)
    (hp4 : ∀ z : A4.domain, 0 ≤ (inner ℂ (A4 z) (z : H)).re)
    (r : ℕ) (f : H) :
    ‖iteratedResolventPower R1a r f - iteratedResolventPower R4d r f‖ ≤
      ‖iteratedResolventPower R1a r f - iteratedResolventPower R2b r f‖ +
        ‖iteratedResolventPower R2b r f - iteratedResolventPower R3c r f‖ +
        ‖iteratedResolventPower R3c r f - iteratedResolventPower R4d r f‖ ∧
    ‖iteratedResolventPower R1a r f - iteratedResolventPower R2b r f‖ +
        ‖iteratedResolventPower R2b r f - iteratedResolventPower R3c r f‖ +
        ‖iteratedResolventPower R3c r f - iteratedResolventPower R4d r f‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + (d⁻¹) ^ r) * ‖f‖ ∧
    ‖iteratedResolventPower R1a r f - iteratedResolventPower R4d r f‖ ≤
      ((a⁻¹) ^ r + (d⁻¹) ^ r) * ‖f‖ := by
  have h123 := threeParam_iteratedResolventPower_triangle_norm_bounds
    A1 A2 A3 R1a R2b R3c a b c ha hb hc hr1 hr2 hr3 hp1 hp2 hp3 r f
  have h34 := twoParam_iteratedResolventPower_cross_sub_norm_bound
    A3 A4 R3c R4d c d hc hd hr3 hr4 hp3 hp4 r f
  have h14 := twoParam_iteratedResolventPower_cross_sub_norm_bound
    A1 A4 R1a R4d a d ha hd hr1 hr4 hp1 hp4 r f
  have htri :
      ‖iteratedResolventPower R1a r f - iteratedResolventPower R4d r f‖ ≤
        ‖iteratedResolventPower R1a r f - iteratedResolventPower R2b r f‖ +
          ‖iteratedResolventPower R2b r f - iteratedResolventPower R3c r f‖ +
          ‖iteratedResolventPower R3c r f - iteratedResolventPower R4d r f‖ := by
    rw [(fourParam_iteratedResolventPower_quadrangle_cocycle R1a R2b R3c R4d r f).2]
    have ht1 := norm_add_le
      ((iteratedResolventPower R1a r f - iteratedResolventPower R2b r f) +
        (iteratedResolventPower R2b r f - iteratedResolventPower R3c r f))
      (iteratedResolventPower R3c r f - iteratedResolventPower R4d r f)
    have ht2 := norm_add_le
      (iteratedResolventPower R1a r f - iteratedResolventPower R2b r f)
      (iteratedResolventPower R2b r f - iteratedResolventPower R3c r f)
    linarith
  have hring :
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖f‖ + ((c⁻¹) ^ r + (d⁻¹) ^ r) * ‖f‖ =
        ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + (d⁻¹) ^ r) * ‖f‖ := by ring
  exact ⟨htri, by linarith [h123.2.1, h34], h14⟩

/-- Mediated three-hop Yosida cross-rate bound on `A1.domain ∩ A2.domain ∩ A3.domain ∩ A4.domain`
across four positive operators `(A1, A2, A3, A4)` resolved at `a, b, c, d > 0`. -/
theorem fourParam_iteratedIdentityPower_quadrangle_rate_bounds
    (A1 A2 A3 A4 : H →ₗ.[ℂ] H) (R1a R2b R3c R4d : H →L[ℂ] H)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hr1 : Resolves A1 R1a a) (hr2 : Resolves A2 R2b b)
    (hr3 : Resolves A3 R3c c) (hr4 : Resolves A4 R4d d)
    (hp1 : ∀ z : A1.domain, 0 ≤ (inner ℂ (A1 z) (z : H)).re)
    (hp2 : ∀ z : A2.domain, 0 ≤ (inner ℂ (A2 z) (z : H)).re)
    (hp3 : ∀ z : A3.domain, 0 ≤ (inner ℂ (A3 z) (z : H)).re)
    (hp4 : ∀ z : A4.domain, 0 ≤ (inner ℂ (A4 z) (z : H)).re)
    (hl1 : ∀ z : A1.domain, R1a (A1 z + a • (z : H)) = (z : H))
    (hl2 : ∀ z : A2.domain, R2b (A2 z + b • (z : H)) = (z : H))
    (hl3 : ∀ z : A3.domain, R3c (A3 z + c • (z : H)) = (z : H))
    (hl4 : ∀ z : A4.domain, R4d (A4 z + d • (z : H)) = (z : H))
    (r : ℕ) (x : H)
    (hx1 : x ∈ A1.domain) (hx2 : x ∈ A2.domain)
    (hx3 : x ∈ A3.domain) (hx4 : x ∈ A4.domain) :
    ‖iteratedIdentityPower R1a a r x - iteratedIdentityPower R2b b r x‖ +
        ‖iteratedIdentityPower R2b b r x - iteratedIdentityPower R3c c r x‖ +
        ‖iteratedIdentityPower R3c c r x - iteratedIdentityPower R4d d r x‖ ≤
      (r : ℝ) * a⁻¹ * ‖A1 ⟨x, hx1⟩‖ +
        2 * (r : ℝ) * b⁻¹ * ‖A2 ⟨x, hx2⟩‖ +
        2 * (r : ℝ) * c⁻¹ * ‖A3 ⟨x, hx3⟩‖ +
        (r : ℝ) * d⁻¹ * ‖A4 ⟨x, hx4⟩‖ ∧
    ‖iteratedIdentityPower R1a a r x - iteratedIdentityPower R4d d r x‖ ≤
      (r : ℝ) * a⁻¹ * ‖A1 ⟨x, hx1⟩‖ + (r : ℝ) * d⁻¹ * ‖A4 ⟨x, hx4⟩‖ := by
  have h123 := (threeParam_iteratedIdentityPower_triangle_rate_bounds
    A1 A2 A3 R1a R2b R3c a b c ha hb hc hr1 hr2 hr3 hp1 hp2 hp3 hl1 hl2 hl3
    r x hx1 hx2 hx3).2.1
  have h34 := twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
    A3 A4 R3c R4d c d hc hd hr3 hr4 hp3 hp4 hl3 hl4 r x hx3 hx4
  have h14 := twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
    A1 A4 R1a R4d a d ha hd hr1 hr4 hp1 hp4 hl1 hl4 r x hx1 hx4
  exact ⟨by linarith, h14⟩

/-! ### 2. Four-Parameter Five-Operator Clock-Floor System `(T, P, G, S, H_op)` -/

/-- Bundled four-parameter five-operator clock-floor system at spectral shifts `(a, b, c, d)`
sharing the underlying operator hierarchy `(T, P, G, S, H_op, K)`. -/
structure FourParameterFiveOperatorSystem (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (a b c d : ℝ) where
  trABC : ThreeParameterFiveOperatorSystem H a b c
  sysD : FiveOperatorResolventSystem H d
  same_T_D : sysD.T = trABC.sysA.T
  same_P_D : sysD.P = trABC.sysA.P
  same_G_D : sysD.G = trABC.sysA.G
  same_S_D : sysD.S = trABC.sysA.S
  same_H_D : sysD.H_op = trABC.sysA.H_op
  same_K_D : sysD.K = trABC.sysA.K

/-- Canonical projection from `FourParameterFiveOperatorSystem H a b c d` to the `(a, b, d)`
`ThreeParameterFiveOperatorSystem H a b d`. -/
def FourParameterFiveOperatorSystem.toThreeABD
    {a b c d : ℝ} (foursys : FourParameterFiveOperatorSystem H a b c d) :
    ThreeParameterFiveOperatorSystem H a b d where
  sysA := foursys.trABC.sysA
  sysB := foursys.trABC.sysB
  sysC := foursys.sysD
  same_T_B := foursys.trABC.same_T_B
  same_P_B := foursys.trABC.same_P_B
  same_G_B := foursys.trABC.same_G_B
  same_S_B := foursys.trABC.same_S_B
  same_H_B := foursys.trABC.same_H_B
  same_K_B := foursys.trABC.same_K_B
  same_T_C := foursys.same_T_D
  same_P_C := foursys.same_P_D
  same_G_C := foursys.same_G_D
  same_S_C := foursys.same_S_D
  same_H_C := foursys.same_H_D
  same_K_C := foursys.same_K_D

/-- Canonical projection from `FourParameterFiveOperatorSystem H a b c d` to the `(a, c, d)`
`ThreeParameterFiveOperatorSystem H a c d`. -/
def FourParameterFiveOperatorSystem.toThreeACD
    {a b c d : ℝ} (foursys : FourParameterFiveOperatorSystem H a b c d) :
    ThreeParameterFiveOperatorSystem H a c d where
  sysA := foursys.trABC.sysA
  sysB := foursys.trABC.sysC
  sysC := foursys.sysD
  same_T_B := foursys.trABC.same_T_C
  same_P_B := foursys.trABC.same_P_C
  same_G_B := foursys.trABC.same_G_C
  same_S_B := foursys.trABC.same_S_C
  same_H_B := foursys.trABC.same_H_C
  same_K_B := foursys.trABC.same_K_C
  same_T_C := foursys.same_T_D
  same_P_C := foursys.same_P_D
  same_G_C := foursys.same_G_D
  same_S_C := foursys.same_S_D
  same_H_C := foursys.same_H_D
  same_K_C := foursys.same_K_D

/-- Four-parameter `(P_a, G_b, S_c, H_d)` quadrangle cocycle, `sysA.P.domain` regularity at order
`r + 1`, and three-hop geometric norm bound. -/
theorem fourParam_potential_growing_residual_hamiltonian_package
    {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (foursys : FourParameterFiveOperatorSystem H a b c d) (r : ℕ) (f : H) :
    (iteratedResolventPower foursys.trABC.sysA.RP r f -
        iteratedResolventPower foursys.trABC.sysB.RG r f) +
      (iteratedResolventPower foursys.trABC.sysB.RG r f -
        iteratedResolventPower foursys.trABC.sysC.RS r f) +
      (iteratedResolventPower foursys.trABC.sysC.RS r f -
        iteratedResolventPower foursys.sysD.RH r f) +
      (iteratedResolventPower foursys.sysD.RH r f -
        iteratedResolventPower foursys.trABC.sysA.RP r f) = 0 ∧
    iteratedResolventPower foursys.trABC.sysA.RP (r + 1) f -
        iteratedResolventPower foursys.sysD.RH (r + 1) f ∈ foursys.trABC.sysA.P.domain ∧
    ‖iteratedResolventPower foursys.trABC.sysA.RP r f -
        iteratedResolventPower foursys.trABC.sysB.RG r f‖ +
      ‖iteratedResolventPower foursys.trABC.sysB.RG r f -
        iteratedResolventPower foursys.trABC.sysC.RS r f‖ +
      ‖iteratedResolventPower foursys.trABC.sysC.RS r f -
        iteratedResolventPower foursys.sysD.RH r f‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + (d⁻¹) ^ r) * ‖f‖ := by
  have hpABD := threeParam_potential_growing_hamiltonian_package ha hb hd foursys.toThreeABD r f
  have hnorm := (fourParam_iteratedResolventPower_quadrangle_norm_bounds
    foursys.trABC.sysA.P foursys.trABC.sysB.G foursys.trABC.sysC.S foursys.sysD.H_op
    foursys.trABC.sysA.RP foursys.trABC.sysB.RG foursys.trABC.sysC.RS foursys.sysD.RH
    a b c d ha hb hc hd
    foursys.trABC.sysA.res_P foursys.trABC.sysB.res_G foursys.trABC.sysC.res_S foursys.sysD.res_H
    foursys.trABC.sysA.pos_P foursys.trABC.sysB.pos_G foursys.trABC.sysC.pos_S foursys.sysD.pos_H
    r f).2.1
  exact ⟨by abel, hpABD.2.2.1, hnorm⟩

/-- Four-parameter `(P_a, T_b, S_c, H_d)` quadrangle cocycle, `sysA.T.domain` regularity at order
`r + 1`, and three-hop geometric norm bound. -/
theorem fourParam_potential_static_residual_hamiltonian_package
    {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (foursys : FourParameterFiveOperatorSystem H a b c d) (r : ℕ) (f : H) :
    (iteratedResolventPower foursys.trABC.sysA.RP r f -
        iteratedResolventPower foursys.trABC.sysB.RT r f) +
      (iteratedResolventPower foursys.trABC.sysB.RT r f -
        iteratedResolventPower foursys.trABC.sysC.RS r f) +
      (iteratedResolventPower foursys.trABC.sysC.RS r f -
        iteratedResolventPower foursys.sysD.RH r f) +
      (iteratedResolventPower foursys.sysD.RH r f -
        iteratedResolventPower foursys.trABC.sysA.RP r f) = 0 ∧
    iteratedResolventPower foursys.trABC.sysA.RT (r + 1) f -
        iteratedResolventPower foursys.sysD.RH (r + 1) f ∈ foursys.trABC.sysA.T.domain ∧
    ‖iteratedResolventPower foursys.trABC.sysA.RP r f -
        iteratedResolventPower foursys.trABC.sysB.RT r f‖ +
      ‖iteratedResolventPower foursys.trABC.sysB.RT r f -
        iteratedResolventPower foursys.trABC.sysC.RS r f‖ +
      ‖iteratedResolventPower foursys.trABC.sysC.RS r f -
        iteratedResolventPower foursys.sysD.RH r f‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + (d⁻¹) ^ r) * ‖f‖ := by
  have hpACD := threeParam_static_residual_hamiltonian_package ha hc hd foursys.toThreeACD r f
  have hnorm := (fourParam_iteratedResolventPower_quadrangle_norm_bounds
    foursys.trABC.sysA.P foursys.trABC.sysB.T foursys.trABC.sysC.S foursys.sysD.H_op
    foursys.trABC.sysA.RP foursys.trABC.sysB.RT foursys.trABC.sysC.RS foursys.sysD.RH
    a b c d ha hb hc hd
    foursys.trABC.sysA.res_P foursys.trABC.sysB.res_T foursys.trABC.sysC.res_S foursys.sysD.res_H
    foursys.trABC.sysA.pos_P foursys.trABC.sysB.pos_T foursys.trABC.sysC.pos_S foursys.sysD.pos_H
    r f).2.1
  exact ⟨by abel, hpACD.2.2.2.1, hnorm⟩

/-- Simultaneous common-domain 4-parameter mediated Yosida cross-rate bounds across
`(P_a, G_b, S_c, H_d)` on `z : foursys.trABC.sysA.H_op.domain`. -/
theorem fourParameterFiveOperator_common_domain_yosida_rates
    {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (foursys : FourParameterFiveOperatorSystem H a b c d)
    (r : ℕ) (z : foursys.trABC.sysA.H_op.domain) :
    let hGA : (z : H) ∈ foursys.trABC.sysA.G.domain := foursys.trABC.sysA.dom_HG z.property
    let hPA : (z : H) ∈ foursys.trABC.sysA.P.domain := foursys.trABC.sysA.dom_GP hGA
    let hHB : (z : H) ∈ foursys.trABC.sysB.H_op.domain := foursys.trABC.same_H_B.symm ▸ z.property
    let hGB : (z : H) ∈ foursys.trABC.sysB.G.domain := foursys.trABC.sysB.dom_HG hHB
    let hHC : (z : H) ∈ foursys.trABC.sysC.H_op.domain := foursys.trABC.same_H_C.symm ▸ z.property
    let hSC : (z : H) ∈ foursys.trABC.sysC.S.domain := foursys.trABC.sysC.dom_HS hHC
    let hHD : (z : H) ∈ foursys.sysD.H_op.domain := foursys.same_H_D.symm ▸ z.property
    ‖iteratedIdentityPower foursys.trABC.sysA.RP a r (z : H) -
        iteratedIdentityPower foursys.trABC.sysB.RG b r (z : H)‖ +
      ‖iteratedIdentityPower foursys.trABC.sysB.RG b r (z : H) -
        iteratedIdentityPower foursys.trABC.sysC.RS c r (z : H)‖ +
      ‖iteratedIdentityPower foursys.trABC.sysC.RS c r (z : H) -
        iteratedIdentityPower foursys.sysD.RH d r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖foursys.trABC.sysA.P ⟨(z : H), hPA⟩‖ +
        2 * (r : ℝ) * b⁻¹ * ‖foursys.trABC.sysB.G ⟨(z : H), hGB⟩‖ +
        2 * (r : ℝ) * c⁻¹ * ‖foursys.trABC.sysC.S ⟨(z : H), hSC⟩‖ +
        (r : ℝ) * d⁻¹ * ‖foursys.sysD.H_op ⟨(z : H), hHD⟩‖ ∧
    ‖iteratedIdentityPower foursys.trABC.sysA.RP a r (z : H) -
        iteratedIdentityPower foursys.sysD.RH d r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖foursys.trABC.sysA.P ⟨(z : H), hPA⟩‖ +
        (r : ℝ) * d⁻¹ * ‖foursys.sysD.H_op ⟨(z : H), hHD⟩‖ := by
  intro hGA hPA hHB hGB hHC hSC hHD
  exact fourParam_iteratedIdentityPower_quadrangle_rate_bounds
    foursys.trABC.sysA.P foursys.trABC.sysB.G foursys.trABC.sysC.S foursys.sysD.H_op
    foursys.trABC.sysA.RP foursys.trABC.sysB.RG foursys.trABC.sysC.RS foursys.sysD.RH
    a b c d ha hb hc hd
    foursys.trABC.sysA.res_P foursys.trABC.sysB.res_G foursys.trABC.sysC.res_S foursys.sysD.res_H
    foursys.trABC.sysA.pos_P foursys.trABC.sysB.pos_G foursys.trABC.sysC.pos_S foursys.sysD.pos_H
    foursys.trABC.sysA.left_P foursys.trABC.sysB.left_G foursys.trABC.sysC.left_S foursys.sysD.left_H
    r (z : H) hPA hGB hSC hHD

/-- Master Five-Operator Four-Parameter `(a, b, c, d)` Higher-Power Cross-Resolvent Quadrangle
Cocycle and Yosida Rate Synthesis Theorem. -/
theorem fiveOperator_fourParameter_higherPower_cocycle_and_yosida_master_synthesis
    {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (foursys : FourParameterFiveOperatorSystem H a b c d)
    (r : ℕ) (f : H) (z : foursys.trABC.sysA.H_op.domain) :
    ((iteratedResolventPower foursys.trABC.sysA.RP r f -
        iteratedResolventPower foursys.trABC.sysB.RG r f) +
      (iteratedResolventPower foursys.trABC.sysB.RG r f -
        iteratedResolventPower foursys.trABC.sysC.RS r f) +
      (iteratedResolventPower foursys.trABC.sysC.RS r f -
        iteratedResolventPower foursys.sysD.RH r f) +
      (iteratedResolventPower foursys.sysD.RH r f -
        iteratedResolventPower foursys.trABC.sysA.RP r f) = 0 ∧
     (iteratedIdentityPower foursys.trABC.sysA.RP a r f -
        iteratedIdentityPower foursys.trABC.sysB.RG b r f) +
      (iteratedIdentityPower foursys.trABC.sysB.RG b r f -
        iteratedIdentityPower foursys.trABC.sysC.RS c r f) +
      (iteratedIdentityPower foursys.trABC.sysC.RS c r f -
        iteratedIdentityPower foursys.sysD.RH d r f) +
      (iteratedIdentityPower foursys.sysD.RH d r f -
        iteratedIdentityPower foursys.trABC.sysA.RP a r f) = 0) ∧
    (iteratedResolventPower foursys.trABC.sysA.RP (r + 1) f -
        iteratedResolventPower foursys.sysD.RH (r + 1) f ∈ foursys.trABC.sysA.P.domain ∧
     iteratedResolventPower foursys.trABC.sysA.RT (r + 1) f -
        iteratedResolventPower foursys.sysD.RH (r + 1) f ∈ foursys.trABC.sysA.T.domain) ∧
    ‖iteratedResolventPower foursys.trABC.sysA.RP r f -
        iteratedResolventPower foursys.trABC.sysB.RG r f‖ +
      ‖iteratedResolventPower foursys.trABC.sysB.RG r f -
        iteratedResolventPower foursys.trABC.sysC.RS r f‖ +
      ‖iteratedResolventPower foursys.trABC.sysC.RS r f -
        iteratedResolventPower foursys.sysD.RH r f‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + (d⁻¹) ^ r) * ‖f‖ ∧
    ‖iteratedIdentityPower foursys.trABC.sysA.RP a r (z : H) -
        iteratedIdentityPower foursys.sysD.RH d r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ *
          ‖foursys.trABC.sysA.P ⟨(z : H), foursys.trABC.sysA.dom_GP (foursys.trABC.sysA.dom_HG z.property)⟩‖ +
        (r : ℝ) * d⁻¹ *
          ‖foursys.sysD.H_op ⟨(z : H), foursys.same_H_D.symm ▸ z.property⟩‖ := by
  have hpPGSH := fourParam_potential_growing_residual_hamiltonian_package ha hb hc hd foursys r f
  have hpPTSH := fourParam_potential_static_residual_hamiltonian_package ha hb hc hd foursys r f
  have hy := fourParameterFiveOperator_common_domain_yosida_rates ha hb hc hd foursys r z
  exact ⟨⟨hpPGSH.1, (fourParam_iteratedIdentityPower_quadrangle_cocycle
      foursys.trABC.sysA.RP foursys.trABC.sysB.RG foursys.trABC.sysC.RS foursys.sysD.RH
      a b c d r f).1⟩,
    ⟨hpPGSH.2.1, hpPTSH.2.1⟩,
    hpPGSH.2.2,
    hy.2⟩

#print axioms fourParam_iteratedResolventPower_quadrangle_cocycle
#print axioms fourParam_iteratedIdentityPower_quadrangle_cocycle
#print axioms fourParam_cross_sub_succ_mem_domains
#print axioms fourParam_iteratedResolventPower_quadrangle_norm_bounds
#print axioms fourParam_iteratedIdentityPower_quadrangle_rate_bounds
#print axioms fourParam_potential_growing_residual_hamiltonian_package
#print axioms fourParam_potential_static_residual_hamiltonian_package
#print axioms fourParameterFiveOperator_common_domain_yosida_rates
#print axioms fiveOperator_fourParameter_higherPower_cocycle_and_yosida_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorFourParameterHigherPowerCocycleAndYosida
