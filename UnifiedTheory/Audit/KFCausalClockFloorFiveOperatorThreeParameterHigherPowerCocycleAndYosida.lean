/- Five-Operator Three-Parameter `(a, b, c)` Higher-Power Cross-Resolvent Cocycles,
Mediated `(T, S, H)` and `(P, G, H)` Triangle Decompositions, and Three-Parameter Yosida
Cross-Rate Bounds:
1. Establishes the general three-parameter cross-operator iterated resolvent and Yosida
   identity cocycle calculus for any three positive operators `(A1, A2, A3)` resolved at
   independent spectral shifts `(a, b, c)`:
   - Exact cyclic cocycle vanishing `(R1a^r f - R2b^r f) + (R2b^r f - R3c^r f) + (R3c^r f - R1a^r f) = 0`
     and `((a R1a)^r f - (b R2b)^r f) + ((b R2b)^r f - (c R3c)^r f) + ((c R3c)^r f - (a R1a)^r f) = 0`,
   - Mediated two-hop decomposition `R1a^r f - R3c^r f = (R1a^r f - R2b^r f) + (R2b^r f - R3c^r f)`,
   - Unconditional `A1.domain` membership at order `r + 1` of both hops and their sum whenever
     `A3.domain ≤ A2.domain ≤ A1.domain`,
   - Three-parameter mediated geometric norm bound `((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖f‖`
     and direct `((a⁻¹) ^ r + (c⁻¹) ^ r) * ‖f‖` bound,
   - Three-parameter common-domain Yosida cross-rate bound
     `(r : ℝ) * a⁻¹ * ‖A1 x‖ + 2 * (r : ℝ) * b⁻¹ * ‖A2 x‖ + (r : ℝ) * c⁻¹ * ‖A3 x‖`.
2. Defines `ThreeParameterFiveOperatorSystem H a b c` bundling three `FiveOperatorResolventSystem`
   instances at spectral shifts `(a, b, c)` with canonical projections `toTwoAB`, `toTwoBC`,
   and `toTwoAC`, and proves:
   - Exact 3-parameter `(T_a, S_b, H_c)` and `(P_a, G_b, H_c)` cyclic cocycles, `sysA.T.domain`
     and `sysA.P.domain` regularity at order `r + 1`, and geometric/Yosida norm bounds,
   - Exact 5-operator 3-parameter chain telescope connecting `RP_a`, `RG_b`, `RS_b`, and `RH_c`,
   - Simultaneous common-domain 3-parameter Yosida cross-rate bounds on `sysA.H_op.domain`,
   - Master 3-parameter higher-power cross-resolvent and Yosida synthesis theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorTwoParameterHigherPowerCrossResolvent

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorThreeParameterHigherPowerCocycleAndYosida

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
   twoParam_iteratedIdentityPower_cross_sub_norm_le_two
   twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
   twoParam_cross_sub_succ_mem_first_domain
   pair1_twoParam_potential_sub_growing_package
   pair2_twoParam_residual_sub_hamiltonian_package
   pair3_twoParam_static_sub_residual_package
   pair4_twoParam_static_sub_hamiltonian_package
   pair5_twoParam_potential_sub_hamiltonian_package
   twoParameterFiveOperator_common_domain_yosida_cross_rate_bounds)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### 1. Abstract Three-Parameter Cross-Operator Cocycle and Mediated Triangle Calculus -/

/-- Exact cyclic 3-parameter cocycle vanishing and two-hop triangle decomposition for
`iteratedResolventPower` across any three resolvents `(R1a, R2b, R3c)`. -/
theorem threeParam_iteratedResolventPower_cyclic_cocycle
    (R1a R2b R3c : H →L[ℂ] H) (r : ℕ) (f : H) :
    (iteratedResolventPower R1a r f - iteratedResolventPower R2b r f) +
      (iteratedResolventPower R2b r f - iteratedResolventPower R3c r f) +
      (iteratedResolventPower R3c r f - iteratedResolventPower R1a r f) = 0 ∧
    iteratedResolventPower R1a r f - iteratedResolventPower R3c r f =
      (iteratedResolventPower R1a r f - iteratedResolventPower R2b r f) +
        (iteratedResolventPower R2b r f - iteratedResolventPower R3c r f) := by
  refine ⟨by abel, by abel⟩

/-- Exact cyclic 3-parameter cocycle vanishing and two-hop triangle decomposition for
`iteratedIdentityPower` across any three resolvents `(R1a, R2b, R3c)` at shifts `(a, b, c)`. -/
theorem threeParam_iteratedIdentityPower_cyclic_cocycle
    (R1a R2b R3c : H →L[ℂ] H) (a b c : ℝ) (r : ℕ) (f : H) :
    (iteratedIdentityPower R1a a r f - iteratedIdentityPower R2b b r f) +
      (iteratedIdentityPower R2b b r f - iteratedIdentityPower R3c c r f) +
      (iteratedIdentityPower R3c c r f - iteratedIdentityPower R1a a r f) = 0 ∧
    iteratedIdentityPower R1a a r f - iteratedIdentityPower R3c c r f =
      (iteratedIdentityPower R1a a r f - iteratedIdentityPower R2b b r f) +
        (iteratedIdentityPower R2b b r f - iteratedIdentityPower R3c c r f) := by
  refine ⟨by abel, by abel⟩

/-- Unconditional `A1.domain` membership at order `r + 1` for both hops `(R1a, R2b)` and
`(R2b, R3c)` and their sum `(R1a, R3c)` whenever `A3.domain ≤ A2.domain ≤ A1.domain`. -/
theorem threeParam_cross_sub_succ_mem_first_domain
    (A1 A2 A3 : H →ₗ.[ℂ] H) (R1a R2b R3c : H →L[ℂ] H) (a b c : ℝ)
    (hr1 : Resolves A1 R1a a) (hr2 : Resolves A2 R2b b) (hr3 : Resolves A3 R3c c)
    (hdom21 : A2.domain ≤ A1.domain) (hdom32 : A3.domain ≤ A2.domain)
    (r : ℕ) (f : H) :
    iteratedResolventPower R1a (r + 1) f - iteratedResolventPower R2b (r + 1) f ∈ A1.domain ∧
    iteratedResolventPower R2b (r + 1) f - iteratedResolventPower R3c (r + 1) f ∈ A2.domain ∧
    iteratedResolventPower R1a (r + 1) f - iteratedResolventPower R3c (r + 1) f ∈ A1.domain ∧
    iteratedIdentityPower R1a a (r + 1) f - iteratedIdentityPower R3c c (r + 1) f ∈ A1.domain := by
  have h12 := twoParam_cross_sub_succ_mem_first_domain A1 A2 R1a R2b a b hr1 hr2 hdom21 r f
  have h23 := twoParam_cross_sub_succ_mem_first_domain A2 A3 R2b R3c b c hr2 hr3 hdom32 r f
  have h13 := twoParam_cross_sub_succ_mem_first_domain A1 A3 R1a R3c a c hr1 hr3
    (hdom32.trans hdom21) r f
  exact ⟨h12.1, h23.1, h13.1, h13.2⟩

/-- Mediated two-hop triangle norm bound and geometric bound across three positive operators
`(A1, A2, A3)` resolved at `a, b, c > 0`. -/
theorem threeParam_iteratedResolventPower_triangle_norm_bounds
    (A1 A2 A3 : H →ₗ.[ℂ] H) (R1a R2b R3c : H →L[ℂ] H)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr1 : Resolves A1 R1a a) (hr2 : Resolves A2 R2b b) (hr3 : Resolves A3 R3c c)
    (hp1 : ∀ z : A1.domain, 0 ≤ (inner ℂ (A1 z) (z : H)).re)
    (hp2 : ∀ z : A2.domain, 0 ≤ (inner ℂ (A2 z) (z : H)).re)
    (hp3 : ∀ z : A3.domain, 0 ≤ (inner ℂ (A3 z) (z : H)).re)
    (r : ℕ) (f : H) :
    ‖iteratedResolventPower R1a r f - iteratedResolventPower R3c r f‖ ≤
      ‖iteratedResolventPower R1a r f - iteratedResolventPower R2b r f‖ +
        ‖iteratedResolventPower R2b r f - iteratedResolventPower R3c r f‖ ∧
    ‖iteratedResolventPower R1a r f - iteratedResolventPower R2b r f‖ +
        ‖iteratedResolventPower R2b r f - iteratedResolventPower R3c r f‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖f‖ ∧
    ‖iteratedResolventPower R1a r f - iteratedResolventPower R3c r f‖ ≤
      ((a⁻¹) ^ r + (c⁻¹) ^ r) * ‖f‖ := by
  have htri :
      ‖iteratedResolventPower R1a r f - iteratedResolventPower R3c r f‖ ≤
        ‖iteratedResolventPower R1a r f - iteratedResolventPower R2b r f‖ +
          ‖iteratedResolventPower R2b r f - iteratedResolventPower R3c r f‖ := by
    rw [(threeParam_iteratedResolventPower_cyclic_cocycle R1a R2b R3c r f).2]
    exact norm_add_le _ _
  have h12 := twoParam_iteratedResolventPower_cross_sub_norm_bound
    A1 A2 R1a R2b a b ha hb hr1 hr2 hp1 hp2 r f
  have h23 := twoParam_iteratedResolventPower_cross_sub_norm_bound
    A2 A3 R2b R3c b c hb hc hr2 hr3 hp2 hp3 r f
  have h13 := twoParam_iteratedResolventPower_cross_sub_norm_bound
    A1 A3 R1a R3c a c ha hc hr1 hr3 hp1 hp3 r f
  have hring :
      ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ + ((b⁻¹) ^ r + (c⁻¹) ^ r) * ‖f‖ =
        ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖f‖ := by ring
  exact ⟨htri, by linarith, h13⟩

/-- Mediated two-hop Yosida cross-rate bound on `A1.domain ∩ A2.domain ∩ A3.domain` across
three positive operators `(A1, A2, A3)` resolved at `a, b, c > 0`. -/
theorem threeParam_iteratedIdentityPower_triangle_rate_bounds
    (A1 A2 A3 : H →ₗ.[ℂ] H) (R1a R2b R3c : H →L[ℂ] H)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr1 : Resolves A1 R1a a) (hr2 : Resolves A2 R2b b) (hr3 : Resolves A3 R3c c)
    (hp1 : ∀ z : A1.domain, 0 ≤ (inner ℂ (A1 z) (z : H)).re)
    (hp2 : ∀ z : A2.domain, 0 ≤ (inner ℂ (A2 z) (z : H)).re)
    (hp3 : ∀ z : A3.domain, 0 ≤ (inner ℂ (A3 z) (z : H)).re)
    (hl1 : ∀ z : A1.domain, R1a (A1 z + a • (z : H)) = (z : H))
    (hl2 : ∀ z : A2.domain, R2b (A2 z + b • (z : H)) = (z : H))
    (hl3 : ∀ z : A3.domain, R3c (A3 z + c • (z : H)) = (z : H))
    (r : ℕ) (x : H) (hx1 : x ∈ A1.domain) (hx2 : x ∈ A2.domain) (hx3 : x ∈ A3.domain) :
    ‖iteratedIdentityPower R1a a r x - iteratedIdentityPower R3c c r x‖ ≤
      ‖iteratedIdentityPower R1a a r x - iteratedIdentityPower R2b b r x‖ +
        ‖iteratedIdentityPower R2b b r x - iteratedIdentityPower R3c c r x‖ ∧
    ‖iteratedIdentityPower R1a a r x - iteratedIdentityPower R2b b r x‖ +
        ‖iteratedIdentityPower R2b b r x - iteratedIdentityPower R3c c r x‖ ≤
      (r : ℝ) * a⁻¹ * ‖A1 ⟨x, hx1⟩‖ +
        2 * (r : ℝ) * b⁻¹ * ‖A2 ⟨x, hx2⟩‖ +
        (r : ℝ) * c⁻¹ * ‖A3 ⟨x, hx3⟩‖ ∧
    ‖iteratedIdentityPower R1a a r x - iteratedIdentityPower R3c c r x‖ ≤
      (r : ℝ) * a⁻¹ * ‖A1 ⟨x, hx1⟩‖ + (r : ℝ) * c⁻¹ * ‖A3 ⟨x, hx3⟩‖ := by
  have htri :
      ‖iteratedIdentityPower R1a a r x - iteratedIdentityPower R3c c r x‖ ≤
        ‖iteratedIdentityPower R1a a r x - iteratedIdentityPower R2b b r x‖ +
          ‖iteratedIdentityPower R2b b r x - iteratedIdentityPower R3c c r x‖ := by
    rw [(threeParam_iteratedIdentityPower_cyclic_cocycle R1a R2b R3c a b c r x).2]
    exact norm_add_le _ _
  have h12 := twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
    A1 A2 R1a R2b a b ha hb hr1 hr2 hp1 hp2 hl1 hl2 r x hx1 hx2
  have h23 := twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
    A2 A3 R2b R3c b c hb hc hr2 hr3 hp2 hp3 hl2 hl3 r x hx2 hx3
  have h13 := twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
    A1 A3 R1a R3c a c ha hc hr1 hr3 hp1 hp3 hl1 hl3 r x hx1 hx3
  exact ⟨htri, by linarith, h13⟩

/-! ### 2. Three-Parameter Five-Operator Clock-Floor System `(T, P, G, S, H_op)` -/

/-- Bundled three-parameter five-operator clock-floor system at spectral shifts `(a, b, c)`
sharing the underlying operator hierarchy `(T, P, G, S, H_op, K)`. -/
structure ThreeParameterFiveOperatorSystem (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (a b c : ℝ) where
  sysA : FiveOperatorResolventSystem H a
  sysB : FiveOperatorResolventSystem H b
  sysC : FiveOperatorResolventSystem H c
  same_T_B : sysB.T = sysA.T
  same_P_B : sysB.P = sysA.P
  same_G_B : sysB.G = sysA.G
  same_S_B : sysB.S = sysA.S
  same_H_B : sysB.H_op = sysA.H_op
  same_K_B : sysB.K = sysA.K
  same_T_C : sysC.T = sysA.T
  same_P_C : sysC.P = sysA.P
  same_G_C : sysC.G = sysA.G
  same_S_C : sysC.S = sysA.S
  same_H_C : sysC.H_op = sysA.H_op
  same_K_C : sysC.K = sysA.K

/-- Canonical projection from `ThreeParameterFiveOperatorSystem H a b c` to the `(a, b)`
`TwoParameterFiveOperatorSystem H a b`. -/
def ThreeParameterFiveOperatorSystem.toTwoAB
    {a b c : ℝ} (trsys : ThreeParameterFiveOperatorSystem H a b c) :
    TwoParameterFiveOperatorSystem H a b where
  sysA := trsys.sysA
  sysB := trsys.sysB
  same_T := trsys.same_T_B
  same_P := trsys.same_P_B
  same_G := trsys.same_G_B
  same_S := trsys.same_S_B
  same_H := trsys.same_H_B
  same_K := trsys.same_K_B

/-- Canonical projection from `ThreeParameterFiveOperatorSystem H a b c` to the `(b, c)`
`TwoParameterFiveOperatorSystem H b c`. -/
def ThreeParameterFiveOperatorSystem.toTwoBC
    {a b c : ℝ} (trsys : ThreeParameterFiveOperatorSystem H a b c) :
    TwoParameterFiveOperatorSystem H b c where
  sysA := trsys.sysB
  sysB := trsys.sysC
  same_T := trsys.same_T_C.trans trsys.same_T_B.symm
  same_P := trsys.same_P_C.trans trsys.same_P_B.symm
  same_G := trsys.same_G_C.trans trsys.same_G_B.symm
  same_S := trsys.same_S_C.trans trsys.same_S_B.symm
  same_H := trsys.same_H_C.trans trsys.same_H_B.symm
  same_K := trsys.same_K_C.trans trsys.same_K_B.symm

/-- Canonical projection from `ThreeParameterFiveOperatorSystem H a b c` to the `(a, c)`
`TwoParameterFiveOperatorSystem H a c`. -/
def ThreeParameterFiveOperatorSystem.toTwoAC
    {a b c : ℝ} (trsys : ThreeParameterFiveOperatorSystem H a b c) :
    TwoParameterFiveOperatorSystem H a c where
  sysA := trsys.sysA
  sysB := trsys.sysC
  same_T := trsys.same_T_C
  same_P := trsys.same_P_C
  same_G := trsys.same_G_C
  same_S := trsys.same_S_C
  same_H := trsys.same_H_C
  same_K := trsys.same_K_C

/-- Three-parameter `(T_a, S_b, H_c)` cyclic cocycle, `sysA.T.domain` and `sysA.S.domain`
regularity at order `r + 1`, and two-hop geometric/Yosida norm bounds. -/
theorem threeParam_static_residual_hamiltonian_package
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (trsys : ThreeParameterFiveOperatorSystem H a b c) (r : ℕ) (f : H) :
    (iteratedResolventPower trsys.sysA.RT r f - iteratedResolventPower trsys.sysB.RS r f) +
        (iteratedResolventPower trsys.sysB.RS r f - iteratedResolventPower trsys.sysC.RH r f) +
        (iteratedResolventPower trsys.sysC.RH r f - iteratedResolventPower trsys.sysA.RT r f) = 0 ∧
    iteratedResolventPower trsys.sysA.RT (r + 1) f -
        iteratedResolventPower trsys.sysB.RS (r + 1) f ∈ trsys.sysA.T.domain ∧
    iteratedResolventPower trsys.sysB.RS (r + 1) f -
        iteratedResolventPower trsys.sysC.RH (r + 1) f ∈ trsys.sysA.S.domain ∧
    iteratedResolventPower trsys.sysA.RT (r + 1) f -
        iteratedResolventPower trsys.sysC.RH (r + 1) f ∈ trsys.sysA.T.domain ∧
    ‖iteratedResolventPower trsys.sysA.RT r f - iteratedResolventPower trsys.sysB.RS r f‖ +
        ‖iteratedResolventPower trsys.sysB.RS r f - iteratedResolventPower trsys.sysC.RH r f‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖f‖ := by
  have hpTS := pair3_twoParam_static_sub_residual_package ha hb trsys.toTwoAB r f
  have hpSH := pair2_twoParam_residual_sub_hamiltonian_package hb hc trsys.toTwoBC r f
  have hpTH := pair4_twoParam_static_sub_hamiltonian_package ha hc trsys.toTwoAC r f
  have hmemS :
      iteratedResolventPower trsys.sysB.RS (r + 1) f -
          iteratedResolventPower trsys.sysC.RH (r + 1) f ∈ trsys.sysA.S.domain := by
    rw [← trsys.same_S_B]
    exact hpSH.2.1
  have hsum :
      ‖iteratedResolventPower trsys.sysA.RT r f - iteratedResolventPower trsys.sysB.RS r f‖ +
          ‖iteratedResolventPower trsys.sysB.RS r f - iteratedResolventPower trsys.sysC.RH r f‖ ≤
        ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖f‖ :=
    (threeParam_iteratedResolventPower_triangle_norm_bounds
      trsys.sysA.T trsys.sysB.S trsys.sysC.H_op
      trsys.sysA.RT trsys.sysB.RS trsys.sysC.RH a b c ha hb hc
      trsys.sysA.res_T trsys.sysB.res_S trsys.sysC.res_H
      trsys.sysA.pos_T trsys.sysB.pos_S trsys.sysC.pos_H r f).2.1
  exact ⟨by abel, hpTS.2.1, hmemS, hpTH.2.1, hsum⟩

/-- Three-parameter `(P_a, G_b, H_c)` cyclic cocycle, `sysA.P.domain` regularity at order
`r + 1`, and two-hop geometric/Yosida norm bounds. -/
theorem threeParam_potential_growing_hamiltonian_package
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (trsys : ThreeParameterFiveOperatorSystem H a b c) (r : ℕ) (f : H) :
    (iteratedResolventPower trsys.sysA.RP r f - iteratedResolventPower trsys.sysB.RG r f) +
        (iteratedResolventPower trsys.sysB.RG r f - iteratedResolventPower trsys.sysC.RH r f) +
        (iteratedResolventPower trsys.sysC.RH r f - iteratedResolventPower trsys.sysA.RP r f) = 0 ∧
    iteratedResolventPower trsys.sysA.RP (r + 1) f -
        iteratedResolventPower trsys.sysB.RG (r + 1) f ∈ trsys.sysA.P.domain ∧
    iteratedResolventPower trsys.sysA.RP (r + 1) f -
        iteratedResolventPower trsys.sysC.RH (r + 1) f ∈ trsys.sysA.P.domain ∧
    ‖iteratedResolventPower trsys.sysA.RP r f - iteratedResolventPower trsys.sysB.RG r f‖ +
        ‖iteratedResolventPower trsys.sysB.RG r f - iteratedResolventPower trsys.sysC.RH r f‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖f‖ := by
  have hpPG := pair1_twoParam_potential_sub_growing_package ha hb trsys.toTwoAB r f
  have hpPH := pair5_twoParam_potential_sub_hamiltonian_package ha hc trsys.toTwoAC r f
  have hsum :
      ‖iteratedResolventPower trsys.sysA.RP r f - iteratedResolventPower trsys.sysB.RG r f‖ +
          ‖iteratedResolventPower trsys.sysB.RG r f - iteratedResolventPower trsys.sysC.RH r f‖ ≤
        ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖f‖ :=
    (threeParam_iteratedResolventPower_triangle_norm_bounds
      trsys.sysA.P trsys.sysB.G trsys.sysC.H_op
      trsys.sysA.RP trsys.sysB.RG trsys.sysC.RH a b c ha hb hc
      trsys.sysA.res_P trsys.sysB.res_G trsys.sysC.res_H
      trsys.sysA.pos_P trsys.sysB.pos_G trsys.sysC.pos_H r f).2.1
  exact ⟨by abel, hpPG.2.1, hpPH.2.1, hsum⟩

/-- Exact 4-hop 3-parameter 5-operator telescope connecting `RP_a`, `RG_b`, `RT_b`, `RS_b`,
and `RH_c` for both `iteratedResolventPower` and `iteratedIdentityPower`. -/
theorem threeParameterFiveOperator_full_five_chain_telescope
    {a b c : ℝ} (trsys : ThreeParameterFiveOperatorSystem H a b c) (r : ℕ) (f : H) :
    iteratedResolventPower trsys.sysA.RP r f - iteratedResolventPower trsys.sysC.RH r f =
      (iteratedResolventPower trsys.sysA.RP r f - iteratedResolventPower trsys.sysB.RG r f) +
      (iteratedResolventPower trsys.sysB.RG r f - iteratedResolventPower trsys.sysB.RS r f) +
      (iteratedResolventPower trsys.sysB.RS r f - iteratedResolventPower trsys.sysC.RH r f) ∧
    iteratedIdentityPower trsys.sysA.RP a r f - iteratedIdentityPower trsys.sysC.RH c r f =
      (iteratedIdentityPower trsys.sysA.RP a r f - iteratedIdentityPower trsys.sysB.RG b r f) +
      (iteratedIdentityPower trsys.sysB.RG b r f - iteratedIdentityPower trsys.sysB.RS b r f) +
      (iteratedIdentityPower trsys.sysB.RS b r f - iteratedIdentityPower trsys.sysC.RH c r f) := by
  refine ⟨by abel, by abel⟩

/-- Simultaneous common-domain 3-parameter mediated Yosida cross-rate bounds across
`(T_a, S_b, H_c)` and `(P_a, G_b, H_c)` on `z : trsys.sysA.H_op.domain`. -/
theorem threeParameterFiveOperator_common_domain_yosida_rates
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (trsys : ThreeParameterFiveOperatorSystem H a b c)
    (r : ℕ) (z : trsys.sysA.H_op.domain) :
    let hTA : (z : H) ∈ trsys.sysA.T.domain := trsys.sysA.dom_HT z.property
    let hHB : (z : H) ∈ trsys.sysB.H_op.domain := trsys.same_H_B.symm ▸ z.property
    let hSB : (z : H) ∈ trsys.sysB.S.domain := trsys.sysB.dom_HS hHB
    let hGA : (z : H) ∈ trsys.sysA.G.domain := trsys.sysA.dom_HG z.property
    let hPA : (z : H) ∈ trsys.sysA.P.domain := trsys.sysA.dom_GP hGA
    let hHC : (z : H) ∈ trsys.sysC.H_op.domain := trsys.same_H_C.symm ▸ z.property
    ‖iteratedIdentityPower trsys.sysA.RT a r (z : H) -
      iteratedIdentityPower trsys.sysB.RS b r (z : H)‖ +
    ‖iteratedIdentityPower trsys.sysB.RS b r (z : H) -
      iteratedIdentityPower trsys.sysC.RH c r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖trsys.sysA.T ⟨(z : H), hTA⟩‖ +
        2 * (r : ℝ) * b⁻¹ * ‖trsys.sysB.S ⟨(z : H), hSB⟩‖ +
        (r : ℝ) * c⁻¹ * ‖trsys.sysC.H_op ⟨(z : H), hHC⟩‖ ∧
    ‖iteratedIdentityPower trsys.sysA.RP a r (z : H) -
      iteratedIdentityPower trsys.sysC.RH c r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖trsys.sysA.P ⟨(z : H), hPA⟩‖ +
        (r : ℝ) * c⁻¹ * ‖trsys.sysC.H_op ⟨(z : H), hHC⟩‖ := by
  intro hTA hHB hSB hGA hPA hHC
  have h1 := (threeParam_iteratedIdentityPower_triangle_rate_bounds
    trsys.sysA.T trsys.sysB.S trsys.sysC.H_op
    trsys.sysA.RT trsys.sysB.RS trsys.sysC.RH a b c ha hb hc
    trsys.sysA.res_T trsys.sysB.res_S trsys.sysC.res_H
    trsys.sysA.pos_T trsys.sysB.pos_S trsys.sysC.pos_H
    trsys.sysA.left_T trsys.sysB.left_S trsys.sysC.left_H
    r (z : H) hTA hSB hHC).2.1
  have h2 := (twoParameterFiveOperator_common_domain_yosida_cross_rate_bounds
    ha hc trsys.toTwoAC r z).2.2.2.2
  exact ⟨h1, h2⟩

/-- Master Five-Operator Three-Parameter `(a, b, c)` Higher-Power Cross-Resolvent Cocycle
and Yosida Rate Synthesis Theorem. -/
theorem fiveOperator_threeParameter_higherPower_cocycle_and_yosida_master_synthesis
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (trsys : ThreeParameterFiveOperatorSystem H a b c)
    (r : ℕ) (f : H) (z : trsys.sysA.H_op.domain) :
    ((iteratedResolventPower trsys.sysA.RT r f - iteratedResolventPower trsys.sysB.RS r f) +
       (iteratedResolventPower trsys.sysB.RS r f - iteratedResolventPower trsys.sysC.RH r f) +
       (iteratedResolventPower trsys.sysC.RH r f - iteratedResolventPower trsys.sysA.RT r f) = 0 ∧
     (iteratedResolventPower trsys.sysA.RP r f - iteratedResolventPower trsys.sysB.RG r f) +
       (iteratedResolventPower trsys.sysB.RG r f - iteratedResolventPower trsys.sysC.RH r f) +
       (iteratedResolventPower trsys.sysC.RH r f - iteratedResolventPower trsys.sysA.RP r f) = 0) ∧
    (iteratedResolventPower trsys.sysA.RT (r + 1) f -
       iteratedResolventPower trsys.sysC.RH (r + 1) f ∈ trsys.sysA.T.domain ∧
     iteratedResolventPower trsys.sysA.RP (r + 1) f -
       iteratedResolventPower trsys.sysC.RH (r + 1) f ∈ trsys.sysA.P.domain) ∧
    (‖iteratedResolventPower trsys.sysA.RT r f - iteratedResolventPower trsys.sysB.RS r f‖ +
       ‖iteratedResolventPower trsys.sysB.RS r f - iteratedResolventPower trsys.sysC.RH r f‖ ≤
       ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖f‖ ∧
     ‖iteratedResolventPower trsys.sysA.RP r f - iteratedResolventPower trsys.sysB.RG r f‖ +
       ‖iteratedResolventPower trsys.sysB.RG r f - iteratedResolventPower trsys.sysC.RH r f‖ ≤
       ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖f‖) ∧
    ‖iteratedIdentityPower trsys.sysA.RP a r (z : H) -
      iteratedIdentityPower trsys.sysC.RH c r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ *
        ‖trsys.sysA.P ⟨(z : H), trsys.sysA.dom_GP (trsys.sysA.dom_HG z.property)⟩‖ +
        (r : ℝ) * c⁻¹ * ‖trsys.sysC.H_op ⟨(z : H), trsys.same_H_C.symm ▸ z.property⟩‖ := by
  have hTSH := threeParam_static_residual_hamiltonian_package ha hb hc trsys r f
  have hPGH := threeParam_potential_growing_hamiltonian_package ha hb hc trsys r f
  have hrate := threeParameterFiveOperator_common_domain_yosida_rates ha hb hc trsys r z
  exact ⟨⟨hTSH.1, hPGH.1⟩, ⟨hTSH.2.2.2.1, hPGH.2.2.1⟩, ⟨hTSH.2.2.2.2, hPGH.2.2.2⟩, hrate.2⟩

#print axioms threeParam_iteratedResolventPower_cyclic_cocycle
#print axioms threeParam_iteratedIdentityPower_cyclic_cocycle
#print axioms threeParam_cross_sub_succ_mem_first_domain
#print axioms threeParam_iteratedResolventPower_triangle_norm_bounds
#print axioms threeParam_iteratedIdentityPower_triangle_rate_bounds
#print axioms threeParam_static_residual_hamiltonian_package
#print axioms threeParam_potential_growing_hamiltonian_package
#print axioms threeParameterFiveOperator_full_five_chain_telescope
#print axioms threeParameterFiveOperator_common_domain_yosida_rates
#print axioms fiveOperator_threeParameter_higherPower_cocycle_and_yosida_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorThreeParameterHigherPowerCocycleAndYosida
