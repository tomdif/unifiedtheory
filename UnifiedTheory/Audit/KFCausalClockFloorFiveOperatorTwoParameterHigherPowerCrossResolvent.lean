/- Five-Operator Two-Parameter Higher-Power Cross-Resolvent Calculus, Combined First-and-Second
Resolvent Decompositions, and Two-Parameter Yosida Cross-Rate Bounds:
1. Establishes the general two-parameter cross-operator iterated resolvent difference calculus
   `iteratedResolventPower R1a r f - iteratedResolventPower R2b r f` and two-parameter
   Yosida-scaled identity cross-difference calculus
   `iteratedIdentityPower R1a a r f - iteratedIdentityPower R2b b r f` for any two positive
   operators `A1, A2 : H →ₗ.[ℂ] H` resolved at spectral shifts `a > 0` and `b > 0`:
   - Left-bridge and right-bridge decompositions through intermediate single-operator or
     single-parameter steps,
   - Two-parameter geometric cross-resolvent norm bound `((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖`,
   - Two-parameter uniform Yosida stability bound `≤ 2 * ‖f‖`,
   - Two-parameter common-domain Yosida cross-rate bound
     `(r : ℝ) * a⁻¹ * ‖A1 ⟨x, hx1⟩‖ + (r : ℝ) * b⁻¹ * ‖A2 ⟨x, hx2⟩‖`,
   - Unconditional `A1.domain` regularity at order `r + 1` whenever `A2.domain ≤ A1.domain`.
2. Combines the higher-power first resolvent identity (across shifts `a, b` on `A1`) with the
   higher-power second resolvent identity (between `A1` and `A2 = A1 + K` at shift `b`):
   - Exact combined first-and-second resolvent decomposition at order `r + 1`,
   - `secondPowerDomain A1` regularity of the two-parameter cross-resolvent difference at order
     `r + 1` whenever `K` maps `A2.domain` into `A1.domain` and `R2 b` preserves `secondPowerDomain A1`,
   - Combined two-parameter + bounded-perturbation (`‖K z‖ ≤ M * ‖z‖`) Yosida Cauchy-perturbation
     bound `(r : ℝ) * (a⁻¹ + b⁻¹) * ‖A1 x‖ + (r : ℝ) * b⁻¹ * M * ‖(x : H)‖`.
3. Instantiates two-parameter higher-power cross-resolvent decompositions, domain regularity,
   geometric norm bounds, and common-domain Yosida cross-rate bounds across all five coupled
   clock-floor operator pairs `(P, G)`, `(S, H)`, `(T, S)`, `(T, H)`, and `(P, H)` as well as
   coupled closed-graph-form self-adjoint positive Hamiltonians `KFCausalClosedGraphForm.hamiltonian D`. -/
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorHigherPowerSecondResolventCrossIdentity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorTwoParameterHigherPowerCrossResolvent

noncomputable section

open scoped Topology InnerProduct
open KFCausalPositiveResolventBounds
  (Resolves point point_value resolvent_apply_norm_bound)
open KFCausalClosedGraphForm
  (Data hamiltonian hamiltonian_selfAdjoint hamiltonian_positive)
open KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence
  (secondPowerDomain
   operatorPowerDomain operatorPowerDomain_zero_one_two_eq
   operatorPowerDomain_le_and_low_order_inclusions
   resolvent_mem_operatorPowerDomain_succ
   iteratedResolventPower iteratedIdentityPower
   iteratedResolvent_and_identity_recurrences
   iteratedResolvent_and_identity_mem_operatorPowerDomain
   iteratedResolvent_and_identity_norm_bounds
   iteratedIdentityPower_domain_rate_bound)
open KFCausalClockFloorFiveOperatorHigherPowerSecondResolventCrossIdentity
  (iteratedResolventPower_cross_sub_zero
   iteratedResolventPower_cross_sub_succ_left
   iteratedIdentityPower_cross_sub_zero
   general_second_resolvent_identity
   cross_sub_succ_mem_first_domain
   cross_sub_succ_mem_secondPowerDomain
   higherPower_second_resolvent_cross_identities_left_and_right
   higherPower_second_resolvent_bounded_perturbation_rates
   FiveOperatorResolventSystem
   fiveOperator_HP_domain_and_decomposition
   fiveOperator_first_order_second_resolvent_identities
   singleOperator_first_resolvent_identity
   singleOperator_higherPower_sub_succ_eq_and_regularity
   singleOperator_two_parameter_yosida_cauchy_bound)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### 1. Abstract Two-Parameter Cross-Operator Resolvent and Yosida Difference Calculus -/

/-- At `r = 0`, the two-parameter cross-operator iterated resolvent difference vanishes. -/
theorem twoParam_iteratedResolventPower_cross_sub_zero
    (R1a R2b : H →L[ℂ] H) (f : H) :
    iteratedResolventPower R1a 0 f - iteratedResolventPower R2b 0 f = 0 :=
  sub_self f

/-- Left-bridge and right-bridge decompositions of the two-parameter cross-operator iterated
resolvent difference `iteratedResolventPower (R1 a) r f - iteratedResolventPower (R2 b) r f`
through `iteratedResolventPower (R1 b) r f` and `iteratedResolventPower (R2 a) r f`. -/
theorem twoParam_iteratedResolventPower_bridge_decompositions
    (R1 R2 : ℝ → H →L[ℂ] H) (a b : ℝ) (r : ℕ) (f : H) :
    iteratedResolventPower (R1 a) r f - iteratedResolventPower (R2 b) r f =
      (iteratedResolventPower (R1 a) r f - iteratedResolventPower (R1 b) r f) +
        (iteratedResolventPower (R1 b) r f - iteratedResolventPower (R2 b) r f) ∧
    iteratedResolventPower (R1 a) r f - iteratedResolventPower (R2 b) r f =
      (iteratedResolventPower (R1 a) r f - iteratedResolventPower (R2 a) r f) +
        (iteratedResolventPower (R2 a) r f - iteratedResolventPower (R2 b) r f) := by
  refine ⟨by abel, by abel⟩

/-- Left-bridge and right-bridge decompositions of the two-parameter cross-operator Yosida
identity difference `iteratedIdentityPower (R1 a) a r f - iteratedIdentityPower (R2 b) b r f`
through `iteratedIdentityPower (R1 b) b r f` and `iteratedIdentityPower (R2 a) a r f`. -/
theorem twoParam_iteratedIdentityPower_bridge_decompositions
    (R1 R2 : ℝ → H →L[ℂ] H) (a b : ℝ) (r : ℕ) (f : H) :
    iteratedIdentityPower (R1 a) a r f - iteratedIdentityPower (R2 b) b r f =
      (iteratedIdentityPower (R1 a) a r f - iteratedIdentityPower (R1 b) b r f) +
        (iteratedIdentityPower (R1 b) b r f - iteratedIdentityPower (R2 b) b r f) ∧
    iteratedIdentityPower (R1 a) a r f - iteratedIdentityPower (R2 b) b r f =
      (iteratedIdentityPower (R1 a) a r f - iteratedIdentityPower (R2 a) a r f) +
        (iteratedIdentityPower (R2 a) a r f - iteratedIdentityPower (R2 b) b r f) := by
  refine ⟨by abel, by abel⟩

/-- Decomposition of the two-parameter cross-operator Yosida identity difference through `f`:
`iteratedIdentityPower R1a a r f - iteratedIdentityPower R2b b r f = (iteratedIdentityPower R1a a r f - f) - (iteratedIdentityPower R2b b r f - f)`. -/
theorem twoParam_iteratedIdentityPower_split_via_self
    (R1a R2b : H →L[ℂ] H) (a b : ℝ) (r : ℕ) (f : H) :
    iteratedIdentityPower R1a a r f - iteratedIdentityPower R2b b r f =
      (iteratedIdentityPower R1a a r f - f) - (iteratedIdentityPower R2b b r f - f) := by
  abel

/-- At `r = 0`, `iteratedIdentityPower R1a a 0 f - iteratedIdentityPower R2b b 0 f = 0`. -/
theorem twoParam_iteratedIdentityPower_cross_sub_zero
    (R1a R2b : H →L[ℂ] H) (a b : ℝ) (f : H) :
    iteratedIdentityPower R1a a 0 f - iteratedIdentityPower R2b b 0 f = 0 := by
  rw [(iteratedResolvent_and_identity_recurrences R1a a 0 f).2.2.2.1,
    (iteratedResolvent_and_identity_recurrences R2b b 0 f).2.2.2.1, sub_self]

/-- At `r = 1`, `iteratedIdentityPower R1a a 1 f - iteratedIdentityPower R2b b 1 f = (a : ℂ) • R1a f - (b : ℂ) • R2b f`. -/
theorem twoParam_iteratedIdentityPower_cross_sub_one
    (R1a R2b : H →L[ℂ] H) (a b : ℝ) (f : H) :
    iteratedIdentityPower R1a a 1 f - iteratedIdentityPower R2b b 1 f =
      (a : ℂ) • R1a f - (b : ℂ) • R2b f := by
  rw [(iteratedResolvent_and_identity_recurrences R1a a 0 f).2.2.2.2.1,
    (iteratedResolvent_and_identity_recurrences R2b b 0 f).2.2.2.2.1]

/-- Left and right step recurrences for the two-parameter cross-operator Yosida-scaled identity
difference at order `r + 1`. -/
theorem twoParam_iteratedIdentityPower_cross_sub_succ_left_and_right
    (R1a R2b : H →L[ℂ] H) (a b : ℝ) (r : ℕ) (f : H) :
    iteratedIdentityPower R1a a (r + 1) f - iteratedIdentityPower R2b b (r + 1) f =
      ((a : ℂ) • R1a (iteratedIdentityPower R1a a r f) -
        (b : ℂ) • R2b (iteratedIdentityPower R1a a r f)) +
        (b : ℂ) • R2b (iteratedIdentityPower R1a a r f - iteratedIdentityPower R2b b r f) ∧
    iteratedIdentityPower R1a a (r + 1) f - iteratedIdentityPower R2b b (r + 1) f =
      (a : ℂ) • R1a (iteratedIdentityPower R1a a r f - iteratedIdentityPower R2b b r f) +
        ((a : ℂ) • R1a (iteratedIdentityPower R2b b r f) -
          (b : ℂ) • R2b (iteratedIdentityPower R2b b r f)) := by
  rw [(iteratedResolvent_and_identity_recurrences R1a a r f).2.2.2.2.2,
    (iteratedResolvent_and_identity_recurrences R2b b r f).2.2.2.2.2]
  constructor
  · rw [map_sub, smul_sub]
    abel
  · rw [map_sub, smul_sub]
    abel

/-- Geometric norm bound on the two-parameter cross-operator iterated resolvent difference for
any two positive operators `A1, A2` resolved by `R1a, R2b` at `a > 0` and `b > 0`:
`‖iteratedResolventPower R1a r f - iteratedResolventPower R2b r f‖ ≤ ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖`. -/
theorem twoParam_iteratedResolventPower_cross_sub_norm_bound
    (A1 A2 : H →ₗ.[ℂ] H) (R1a R2b : H →L[ℂ] H) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr1 : Resolves A1 R1a a) (hr2 : Resolves A2 R2b b)
    (hp1 : ∀ z : A1.domain, 0 ≤ (inner ℂ (A1 z) (z : H)).re)
    (hp2 : ∀ z : A2.domain, 0 ≤ (inner ℂ (A2 z) (z : H)).re)
    (r : ℕ) (f : H) :
    ‖iteratedResolventPower R1a r f - iteratedResolventPower R2b r f‖ ≤
      ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ := by
  have htri := norm_sub_le (iteratedResolventPower R1a r f) (iteratedResolventPower R2b r f)
  have h1 := (iteratedResolvent_and_identity_norm_bounds A1 R1a a ha hr1 hp1 r f).1
  have h2 := (iteratedResolvent_and_identity_norm_bounds A2 R2b b hb hr2 hp2 r f).1
  have hring : (a⁻¹) ^ r * ‖f‖ + (b⁻¹) ^ r * ‖f‖ = ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ := by ring
  linarith

/-- Uniform stability bound `≤ 2 * ‖f‖` on the two-parameter cross-operator Yosida-scaled
identity difference for any `a > 0`, `b > 0`, and `r : ℕ`. -/
theorem twoParam_iteratedIdentityPower_cross_sub_norm_le_two
    (A1 A2 : H →ₗ.[ℂ] H) (R1a R2b : H →L[ℂ] H) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr1 : Resolves A1 R1a a) (hr2 : Resolves A2 R2b b)
    (hp1 : ∀ z : A1.domain, 0 ≤ (inner ℂ (A1 z) (z : H)).re)
    (hp2 : ∀ z : A2.domain, 0 ≤ (inner ℂ (A2 z) (z : H)).re)
    (r : ℕ) (f : H) :
    ‖iteratedIdentityPower R1a a r f - iteratedIdentityPower R2b b r f‖ ≤ 2 * ‖f‖ := by
  have htri := norm_sub_le (iteratedIdentityPower R1a a r f) (iteratedIdentityPower R2b b r f)
  have h1 := (iteratedResolvent_and_identity_norm_bounds A1 R1a a ha hr1 hp1 r f).2
  have h2 := (iteratedResolvent_and_identity_norm_bounds A2 R2b b hb hr2 hp2 r f).2
  linarith

/-- Quantitative two-parameter cross-operator Yosida rate bound on `A1.domain ∩ A2.domain`:
`‖iteratedIdentityPower R1a a r x - iteratedIdentityPower R2b b r x‖ ≤ (r : ℝ) * a⁻¹ * ‖A1 ⟨x, hx1⟩‖ + (r : ℝ) * b⁻¹ * ‖A2 ⟨x, hx2⟩‖`. -/
theorem twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
    (A1 A2 : H →ₗ.[ℂ] H) (R1a R2b : H →L[ℂ] H) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr1 : Resolves A1 R1a a) (hr2 : Resolves A2 R2b b)
    (hp1 : ∀ z : A1.domain, 0 ≤ (inner ℂ (A1 z) (z : H)).re)
    (hp2 : ∀ z : A2.domain, 0 ≤ (inner ℂ (A2 z) (z : H)).re)
    (hl1 : ∀ z : A1.domain, R1a (A1 z + a • (z : H)) = (z : H))
    (hl2 : ∀ z : A2.domain, R2b (A2 z + b • (z : H)) = (z : H))
    (r : ℕ) (x : H) (hx1 : x ∈ A1.domain) (hx2 : x ∈ A2.domain) :
    ‖iteratedIdentityPower R1a a r x - iteratedIdentityPower R2b b r x‖ ≤
      (r : ℝ) * a⁻¹ * ‖A1 ⟨x, hx1⟩‖ + (r : ℝ) * b⁻¹ * ‖A2 ⟨x, hx2⟩‖ := by
  rw [twoParam_iteratedIdentityPower_split_via_self R1a R2b a b r x]
  have htri := norm_sub_le
    (iteratedIdentityPower R1a a r x - x)
    (iteratedIdentityPower R2b b r x - x)
  have h1 := iteratedIdentityPower_domain_rate_bound A1 R1a a ha hr1 hp1 hl1 r ⟨x, hx1⟩
  have h2 := iteratedIdentityPower_domain_rate_bound A2 R2b b hb hr2 hp2 hl2 r ⟨x, hx2⟩
  linarith

/-- Unconditional `A1.domain` membership for the `(r + 1)`-th power two-parameter cross-operator
resolvent difference and Yosida identity cross-difference whenever `A2.domain ≤ A1.domain`. -/
theorem twoParam_cross_sub_succ_mem_first_domain
    (A1 A2 : H →ₗ.[ℂ] H) (R1a R2b : H →L[ℂ] H) (a b : ℝ)
    (hr1 : Resolves A1 R1a a) (hr2 : Resolves A2 R2b b)
    (hdom : A2.domain ≤ A1.domain) (r : ℕ) (f : H) :
    iteratedResolventPower R1a (r + 1) f - iteratedResolventPower R2b (r + 1) f ∈ A1.domain ∧
    iteratedIdentityPower R1a a (r + 1) f - iteratedIdentityPower R2b b (r + 1) f ∈ A1.domain := by
  have h1 := iteratedResolvent_and_identity_mem_operatorPowerDomain A1 R1a a hr1 (r + 1) f
  have h2 := iteratedResolvent_and_identity_mem_operatorPowerDomain A2 R2b b hr2 (r + 1) f
  have hdom1 : operatorPowerDomain A1 (r + 1) ≤ A1.domain :=
    (operatorPowerDomain_le_and_low_order_inclusions A1 r).2.1
  have hdom2 : operatorPowerDomain A2 (r + 1) ≤ A2.domain :=
    (operatorPowerDomain_le_and_low_order_inclusions A2 r).2.1
  exact ⟨A1.domain.sub_mem (hdom1 h1.1) (hdom (hdom2 h2.1)),
    A1.domain.sub_mem (hdom1 h1.2) (hdom (hdom2 h2.2))⟩

/-! ### 2. Combined First-and-Second Resolvent Identity and `secondPowerDomain` Regularity -/

/-- First-order (`r = 1`) combined first-and-second resolvent identity across two operators
`A1, A2` (`A2 = A1 + K`) and two spectral shifts `a, b`:
`R1 a f - R2 b f = ((b - a : ℝ) : ℂ) • R1 a (R1 b f) + R1 b (K ⟨R2 b f, hK ...⟩)`. -/
theorem combined_first_and_second_resolvent_identity
    (A1 A2 K : H →ₗ.[ℂ] H) (R1 R2 : ℝ → H →L[ℂ] H) (a b : ℝ)
    (hr1b : Resolves A1 (R1 b) b) (hr2b : Resolves A2 (R2 b) b)
    (hl1a : ∀ z : A1.domain, R1 a (A1 z + a • (z : H)) = (z : H))
    (hl1b : ∀ z : A1.domain, R1 b (A1 z + b • (z : H)) = (z : H))
    (hdom : A2.domain ≤ A1.domain) (hK : A2.domain ≤ K.domain)
    (hadd : ∀ z : A2.domain, A2 z = A1 ⟨(z : H), hdom z.property⟩ + K ⟨(z : H), hK z.property⟩)
    (f : H) :
    R1 a f - R2 b f =
      ((b - a : ℝ) : ℂ) • R1 a (R1 b f) +
        R1 b (K ⟨R2 b f, hK (point A2 (R2 b) b hr2b f).property⟩) := by
  have hbridge : R1 a f - R2 b f = (R1 a f - R1 b f) + (R1 b f - R2 b f) := by abel
  rw [hbridge,
    singleOperator_first_resolvent_identity A1 R1 a b hr1b hl1a f,
    general_second_resolvent_identity A1 A2 K (R1 b) (R2 b) b hr2b hl1b hdom hK hadd f]

/-- Higher-power (`r + 1`) combined first-and-second resolvent decomposition for
`iteratedResolventPower (R1 a) (r + 1) f - iteratedResolventPower (R2 b) (r + 1) f`. -/
theorem higherPower_combined_first_and_second_resolvent_identity
    (A1 A2 K : H →ₗ.[ℂ] H) (R1 R2 : ℝ → H →L[ℂ] H) (a b : ℝ)
    (hr1a : Resolves A1 (R1 a) a) (hr1b : Resolves A1 (R1 b) b)
    (hr2b : Resolves A2 (R2 b) b)
    (hl1a : ∀ z : A1.domain, R1 a (A1 z + a • (z : H)) = (z : H))
    (hl1b : ∀ z : A1.domain, R1 b (A1 z + b • (z : H)) = (z : H))
    (hdom : A2.domain ≤ A1.domain) (hK : A2.domain ≤ K.domain)
    (hadd : ∀ z : A2.domain, A2 z = A1 ⟨(z : H), hdom z.property⟩ + K ⟨(z : H), hK z.property⟩)
    (r : ℕ) (f : H) :
    iteratedResolventPower (R1 a) (r + 1) f - iteratedResolventPower (R2 b) (r + 1) f =
      (((b - a : ℝ) : ℂ) • R1 a (R1 b (iteratedResolventPower (R1 a) r f)) +
        R1 b (iteratedResolventPower (R1 a) r f - iteratedResolventPower (R1 b) r f)) +
      (R1 b (K ⟨R2 b (iteratedResolventPower (R1 b) r f),
          hK (point A2 (R2 b) b hr2b (iteratedResolventPower (R1 b) r f)).property⟩) +
        R2 b (iteratedResolventPower (R1 b) r f - iteratedResolventPower (R2 b) r f)) := by
  rw [(twoParam_iteratedResolventPower_bridge_decompositions R1 R2 a b (r + 1) f).1,
    (singleOperator_higherPower_sub_succ_eq_and_regularity A1 R1 a b hr1a hr1b hl1a r f).1,
    (higherPower_second_resolvent_cross_identities_left_and_right
      A1 A2 K (R1 b) (R2 b) b hr2b hl1b hdom hK hadd r f).1]

/-- Unconditional `secondPowerDomain A1` regularity of the two-parameter cross-operator
resolvent difference `iteratedResolventPower (R1 a) (r + 1) f - iteratedResolventPower (R2 b) (r + 1) f`
whenever `K` maps `A2.domain` into `A1.domain` and `R2 b` preserves `secondPowerDomain A1`. -/
theorem twoParam_cross_sub_succ_mem_secondPowerDomain
    (A1 A2 K : H →ₗ.[ℂ] H) (R1 R2 : ℝ → H →L[ℂ] H) (a b : ℝ)
    (hr1a : Resolves A1 (R1 a) a) (hr1b : Resolves A1 (R1 b) b)
    (hr2b : Resolves A2 (R2 b) b)
    (hl1a : ∀ z : A1.domain, R1 a (A1 z + a • (z : H)) = (z : H))
    (hl1b : ∀ z : A1.domain, R1 b (A1 z + b • (z : H)) = (z : H))
    (hdom : A2.domain ≤ A1.domain) (hK : A2.domain ≤ K.domain)
    (hadd : ∀ z : A2.domain, A2 z = A1 ⟨(z : H), hdom z.property⟩ + K ⟨(z : H), hK z.property⟩)
    (hK_dom : ∀ z : A2.domain, K ⟨(z : H), hK z.property⟩ ∈ A1.domain)
    (hR2_pres : ∀ g : H, g ∈ secondPowerDomain A1 → R2 b g ∈ secondPowerDomain A1)
    (r : ℕ) (f : H) :
    iteratedResolventPower (R1 a) (r + 1) f - iteratedResolventPower (R2 b) (r + 1) f ∈
      secondPowerDomain A1 := by
  rw [(twoParam_iteratedResolventPower_bridge_decompositions R1 R2 a b (r + 1) f).1]
  have h1_pow :
      iteratedResolventPower (R1 a) (r + 1) f - iteratedResolventPower (R1 b) (r + 1) f ∈
        operatorPowerDomain A1 (r + 2) :=
    (singleOperator_higherPower_sub_succ_eq_and_regularity A1 R1 a b hr1a hr1b hl1a r f).2
  have h1_sec :
      iteratedResolventPower (R1 a) (r + 1) f - iteratedResolventPower (R1 b) (r + 1) f ∈
        secondPowerDomain A1 :=
    (operatorPowerDomain_le_and_low_order_inclusions A1 r).2.2 h1_pow
  have h2_sec :
      iteratedResolventPower (R1 b) (r + 1) f - iteratedResolventPower (R2 b) (r + 1) f ∈
        secondPowerDomain A1 :=
    (cross_sub_succ_mem_secondPowerDomain A1 A2 K (R1 b) (R2 b) b hr1b hr2b hl1b
      hdom hK hadd hK_dom hR2_pres r f).1
  exact (secondPowerDomain A1).add_mem h1_sec h2_sec

/-- Combined two-parameter + bounded-perturbation (`‖K z‖ ≤ M * ‖z‖`) norm bounds for
`iteratedResolventPower (R1 a) r f - iteratedResolventPower (R2 b) r f` on `H` and
`iteratedIdentityPower (R1 a) a r (x : H) - iteratedIdentityPower (R2 b) b r (x : H)` on `A1.domain`. -/
theorem twoParam_bounded_perturbation_resolvent_and_yosida_bounds
    (A1 A2 K : H →ₗ.[ℂ] H) (R1 R2 : ℝ → H →L[ℂ] H) (a b M : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hM : 0 ≤ M)
    (hr1a : Resolves A1 (R1 a) a) (hr1b : Resolves A1 (R1 b) b)
    (hr2b : Resolves A2 (R2 b) b)
    (hp1 : ∀ z : A1.domain, 0 ≤ (inner ℂ (A1 z) (z : H)).re)
    (hp2 : ∀ z : A2.domain, 0 ≤ (inner ℂ (A2 z) (z : H)).re)
    (hl1a : ∀ z : A1.domain, R1 a (A1 z + a • (z : H)) = (z : H))
    (hl1b : ∀ z : A1.domain, R1 b (A1 z + b • (z : H)) = (z : H))
    (hdom : A2.domain ≤ A1.domain) (hK : A2.domain ≤ K.domain)
    (hadd : ∀ z : A2.domain, A2 z = A1 ⟨(z : H), hdom z.property⟩ + K ⟨(z : H), hK z.property⟩)
    (hK_bound : ∀ z : K.domain, ‖K z‖ ≤ M * ‖(z : H)‖)
    (r : ℕ) (f : H) (x : A1.domain) :
    ‖iteratedResolventPower (R1 a) r f - iteratedResolventPower (R2 b) r f‖ ≤
      ‖iteratedResolventPower (R1 a) r f - iteratedResolventPower (R1 b) r f‖ +
        (r : ℝ) * M * (b⁻¹) ^ (r + 1) * ‖f‖ ∧
    ‖iteratedIdentityPower (R1 a) a r (x : H) - iteratedIdentityPower (R2 b) b r (x : H)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖A1 x‖ + (r : ℝ) * b⁻¹ * M * ‖(x : H)‖ := by
  have hpert_f := higherPower_second_resolvent_bounded_perturbation_rates
    A1 A2 K (R1 b) (R2 b) b M hb hM hr1b hr2b hp1 hp2 hl1b hdom hK hadd hK_bound r f
  have hpert_x := higherPower_second_resolvent_bounded_perturbation_rates
    A1 A2 K (R1 b) (R2 b) b M hb hM hr1b hr2b hp1 hp2 hl1b hdom hK hadd hK_bound r (x : H)
  have hcauchy := singleOperator_two_parameter_yosida_cauchy_bound
    A1 R1 a b ha hb hr1a hr1b hp1 hl1a hl1b r x
  constructor
  · rw [(twoParam_iteratedResolventPower_bridge_decompositions R1 R2 a b r f).1]
    have htri := norm_add_le
      (iteratedResolventPower (R1 a) r f - iteratedResolventPower (R1 b) r f)
      (iteratedResolventPower (R1 b) r f - iteratedResolventPower (R2 b) r f)
    linarith [hpert_f.1]
  · rw [(twoParam_iteratedIdentityPower_bridge_decompositions R1 R2 a b r (x : H)).1]
    have htri := norm_add_le
      (iteratedIdentityPower (R1 a) a r (x : H) - iteratedIdentityPower (R1 b) b r (x : H))
      (iteratedIdentityPower (R1 b) b r (x : H) - iteratedIdentityPower (R2 b) b r (x : H))
    linarith [hpert_x.2]

/-! ### 3. Two-Parameter Five-Operator Clock-Floor System `(T, P, G, S, H_op)` -/

/-- Bundled two-parameter five-operator clock-floor system at spectral shifts `a` and `b`
sharing the underlying operator hierarchy `(T, P, G, S, H_op, K)`. -/
structure TwoParameterFiveOperatorSystem (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b : ℝ) where
  sysA : FiveOperatorResolventSystem H a
  sysB : FiveOperatorResolventSystem H b
  same_T : sysB.T = sysA.T
  same_P : sysB.P = sysA.P
  same_G : sysB.G = sysA.G
  same_S : sysB.S = sysA.S
  same_H : sysB.H_op = sysA.H_op
  same_K : sysB.K = sysA.K

/-- Canonical diagonal constructor `ofSingle` embedding any `FiveOperatorResolventSystem H a`
into `TwoParameterFiveOperatorSystem H a a`. -/
def TwoParameterFiveOperatorSystem.ofSingle {a : ℝ} (sys : FiveOperatorResolventSystem H a) :
    TwoParameterFiveOperatorSystem H a a where
  sysA := sys
  sysB := sys
  same_T := rfl
  same_P := rfl
  same_G := rfl
  same_S := rfl
  same_H := rfl
  same_K := rfl

/-- Domain compatibility lemmas for `TwoParameterFiveOperatorSystem`: `sysB`'s operators have
domains included in the corresponding first-operator domains of `sysA`. -/
theorem twoParameterFiveOperator_domain_inclusions
    {a b : ℝ} (tsys : TwoParameterFiveOperatorSystem H a b) :
    tsys.sysB.G.domain ≤ tsys.sysA.P.domain ∧
    tsys.sysB.H_op.domain ≤ tsys.sysA.S.domain ∧
    tsys.sysB.S.domain ≤ tsys.sysA.T.domain ∧
    tsys.sysB.H_op.domain ≤ tsys.sysA.T.domain ∧
    tsys.sysB.H_op.domain ≤ tsys.sysA.P.domain := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [tsys.same_G]
    exact tsys.sysA.dom_GP
  · rw [tsys.same_H]
    exact tsys.sysA.dom_HS
  · rw [tsys.same_S]
    exact tsys.sysA.dom_ST
  · rw [tsys.same_H]
    exact tsys.sysA.dom_HT
  · rw [tsys.same_H]
    exact tsys.sysA.dom_HG.trans tsys.sysA.dom_GP

/-- Pair 1 `(P, G)`: Two-parameter left and right bridge decompositions, `sysA.P.domain`
regularity at order `r + 1`, and geometric/Yosida norm bounds. -/
theorem pair1_twoParam_potential_sub_growing_package
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (tsys : TwoParameterFiveOperatorSystem H a b) (r : ℕ) (f : H) :
    iteratedResolventPower tsys.sysA.RP r f - iteratedResolventPower tsys.sysB.RG r f =
      (iteratedResolventPower tsys.sysA.RP r f - iteratedResolventPower tsys.sysB.RP r f) +
        (iteratedResolventPower tsys.sysB.RP r f - iteratedResolventPower tsys.sysB.RG r f) ∧
    iteratedResolventPower tsys.sysA.RP (r + 1) f - iteratedResolventPower tsys.sysB.RG (r + 1) f ∈
      tsys.sysA.P.domain ∧
    iteratedIdentityPower tsys.sysA.RP a (r + 1) f - iteratedIdentityPower tsys.sysB.RG b (r + 1) f ∈
      tsys.sysA.P.domain ∧
    ‖iteratedResolventPower tsys.sysA.RP r f - iteratedResolventPower tsys.sysB.RG r f‖ ≤
      ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ ∧
    ‖iteratedIdentityPower tsys.sysA.RP a r f - iteratedIdentityPower tsys.sysB.RG b r f‖ ≤
      2 * ‖f‖ := by
  have hdom := (twoParameterFiveOperator_domain_inclusions tsys).1
  have hmem := twoParam_cross_sub_succ_mem_first_domain
    tsys.sysA.P tsys.sysB.G tsys.sysA.RP tsys.sysB.RG a b
    tsys.sysA.res_P tsys.sysB.res_G hdom r f
  refine ⟨by abel, hmem.1, hmem.2,
    twoParam_iteratedResolventPower_cross_sub_norm_bound
      tsys.sysA.P tsys.sysB.G tsys.sysA.RP tsys.sysB.RG a b ha hb
      tsys.sysA.res_P tsys.sysB.res_G tsys.sysA.pos_P tsys.sysB.pos_G r f,
    twoParam_iteratedIdentityPower_cross_sub_norm_le_two
      tsys.sysA.P tsys.sysB.G tsys.sysA.RP tsys.sysB.RG a b ha hb
      tsys.sysA.res_P tsys.sysB.res_G tsys.sysA.pos_P tsys.sysB.pos_G r f⟩

/-- Pair 2 `(S, H_op)`: Two-parameter bridge decomposition, `sysA.S.domain` regularity at order
`r + 1`, and geometric/Yosida norm bounds. -/
theorem pair2_twoParam_residual_sub_hamiltonian_package
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (tsys : TwoParameterFiveOperatorSystem H a b) (r : ℕ) (f : H) :
    iteratedResolventPower tsys.sysA.RS r f - iteratedResolventPower tsys.sysB.RH r f =
      (iteratedResolventPower tsys.sysA.RS r f - iteratedResolventPower tsys.sysB.RS r f) +
        (iteratedResolventPower tsys.sysB.RS r f - iteratedResolventPower tsys.sysB.RH r f) ∧
    iteratedResolventPower tsys.sysA.RS (r + 1) f - iteratedResolventPower tsys.sysB.RH (r + 1) f ∈
      tsys.sysA.S.domain ∧
    iteratedIdentityPower tsys.sysA.RS a (r + 1) f - iteratedIdentityPower tsys.sysB.RH b (r + 1) f ∈
      tsys.sysA.S.domain ∧
    ‖iteratedResolventPower tsys.sysA.RS r f - iteratedResolventPower tsys.sysB.RH r f‖ ≤
      ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ ∧
    ‖iteratedIdentityPower tsys.sysA.RS a r f - iteratedIdentityPower tsys.sysB.RH b r f‖ ≤
      2 * ‖f‖ := by
  have hdom := (twoParameterFiveOperator_domain_inclusions tsys).2.1
  have hmem := twoParam_cross_sub_succ_mem_first_domain
    tsys.sysA.S tsys.sysB.H_op tsys.sysA.RS tsys.sysB.RH a b
    tsys.sysA.res_S tsys.sysB.res_H hdom r f
  refine ⟨by abel, hmem.1, hmem.2,
    twoParam_iteratedResolventPower_cross_sub_norm_bound
      tsys.sysA.S tsys.sysB.H_op tsys.sysA.RS tsys.sysB.RH a b ha hb
      tsys.sysA.res_S tsys.sysB.res_H tsys.sysA.pos_S tsys.sysB.pos_H r f,
    twoParam_iteratedIdentityPower_cross_sub_norm_le_two
      tsys.sysA.S tsys.sysB.H_op tsys.sysA.RS tsys.sysB.RH a b ha hb
      tsys.sysA.res_S tsys.sysB.res_H tsys.sysA.pos_S tsys.sysB.pos_H r f⟩

/-- Pair 3 `(T, S)`: Two-parameter bridge decomposition, `sysA.T.domain` regularity at order
`r + 1`, and geometric/Yosida norm bounds. -/
theorem pair3_twoParam_static_sub_residual_package
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (tsys : TwoParameterFiveOperatorSystem H a b) (r : ℕ) (f : H) :
    iteratedResolventPower tsys.sysA.RT r f - iteratedResolventPower tsys.sysB.RS r f =
      (iteratedResolventPower tsys.sysA.RT r f - iteratedResolventPower tsys.sysB.RT r f) +
        (iteratedResolventPower tsys.sysB.RT r f - iteratedResolventPower tsys.sysB.RS r f) ∧
    iteratedResolventPower tsys.sysA.RT (r + 1) f - iteratedResolventPower tsys.sysB.RS (r + 1) f ∈
      tsys.sysA.T.domain ∧
    iteratedIdentityPower tsys.sysA.RT a (r + 1) f - iteratedIdentityPower tsys.sysB.RS b (r + 1) f ∈
      tsys.sysA.T.domain ∧
    ‖iteratedResolventPower tsys.sysA.RT r f - iteratedResolventPower tsys.sysB.RS r f‖ ≤
      ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ ∧
    ‖iteratedIdentityPower tsys.sysA.RT a r f - iteratedIdentityPower tsys.sysB.RS b r f‖ ≤
      2 * ‖f‖ := by
  have hdom := (twoParameterFiveOperator_domain_inclusions tsys).2.2.1
  have hmem := twoParam_cross_sub_succ_mem_first_domain
    tsys.sysA.T tsys.sysB.S tsys.sysA.RT tsys.sysB.RS a b
    tsys.sysA.res_T tsys.sysB.res_S hdom r f
  refine ⟨by abel, hmem.1, hmem.2,
    twoParam_iteratedResolventPower_cross_sub_norm_bound
      tsys.sysA.T tsys.sysB.S tsys.sysA.RT tsys.sysB.RS a b ha hb
      tsys.sysA.res_T tsys.sysB.res_S tsys.sysA.pos_T tsys.sysB.pos_S r f,
    twoParam_iteratedIdentityPower_cross_sub_norm_le_two
      tsys.sysA.T tsys.sysB.S tsys.sysA.RT tsys.sysB.RS a b ha hb
      tsys.sysA.res_T tsys.sysB.res_S tsys.sysA.pos_T tsys.sysB.pos_S r f⟩

/-- Pair 4 `(T, H_op)`: Two-parameter bridge decomposition, `sysA.T.domain` regularity at order
`r + 1`, and geometric/Yosida norm bounds. -/
theorem pair4_twoParam_static_sub_hamiltonian_package
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (tsys : TwoParameterFiveOperatorSystem H a b) (r : ℕ) (f : H) :
    iteratedResolventPower tsys.sysA.RT r f - iteratedResolventPower tsys.sysB.RH r f =
      (iteratedResolventPower tsys.sysA.RT r f - iteratedResolventPower tsys.sysB.RT r f) +
        (iteratedResolventPower tsys.sysB.RT r f - iteratedResolventPower tsys.sysB.RH r f) ∧
    iteratedResolventPower tsys.sysA.RT (r + 1) f - iteratedResolventPower tsys.sysB.RH (r + 1) f ∈
      tsys.sysA.T.domain ∧
    iteratedIdentityPower tsys.sysA.RT a (r + 1) f - iteratedIdentityPower tsys.sysB.RH b (r + 1) f ∈
      tsys.sysA.T.domain ∧
    ‖iteratedResolventPower tsys.sysA.RT r f - iteratedResolventPower tsys.sysB.RH r f‖ ≤
      ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ ∧
    ‖iteratedIdentityPower tsys.sysA.RT a r f - iteratedIdentityPower tsys.sysB.RH b r f‖ ≤
      2 * ‖f‖ := by
  have hdom := (twoParameterFiveOperator_domain_inclusions tsys).2.2.2.1
  have hmem := twoParam_cross_sub_succ_mem_first_domain
    tsys.sysA.T tsys.sysB.H_op tsys.sysA.RT tsys.sysB.RH a b
    tsys.sysA.res_T tsys.sysB.res_H hdom r f
  refine ⟨by abel, hmem.1, hmem.2,
    twoParam_iteratedResolventPower_cross_sub_norm_bound
      tsys.sysA.T tsys.sysB.H_op tsys.sysA.RT tsys.sysB.RH a b ha hb
      tsys.sysA.res_T tsys.sysB.res_H tsys.sysA.pos_T tsys.sysB.pos_H r f,
    twoParam_iteratedIdentityPower_cross_sub_norm_le_two
      tsys.sysA.T tsys.sysB.H_op tsys.sysA.RT tsys.sysB.RH a b ha hb
      tsys.sysA.res_T tsys.sysB.res_H tsys.sysA.pos_T tsys.sysB.pos_H r f⟩

/-- Pair 5 `(P, H_op)`: Two-parameter bridge decomposition, `sysA.P.domain` regularity at order
`r + 1`, and geometric/Yosida norm bounds. -/
theorem pair5_twoParam_potential_sub_hamiltonian_package
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (tsys : TwoParameterFiveOperatorSystem H a b) (r : ℕ) (f : H) :
    iteratedResolventPower tsys.sysA.RP r f - iteratedResolventPower tsys.sysB.RH r f =
      (iteratedResolventPower tsys.sysA.RP r f - iteratedResolventPower tsys.sysB.RP r f) +
        (iteratedResolventPower tsys.sysB.RP r f - iteratedResolventPower tsys.sysB.RH r f) ∧
    iteratedResolventPower tsys.sysA.RP (r + 1) f - iteratedResolventPower tsys.sysB.RH (r + 1) f ∈
      tsys.sysA.P.domain ∧
    iteratedIdentityPower tsys.sysA.RP a (r + 1) f - iteratedIdentityPower tsys.sysB.RH b (r + 1) f ∈
      tsys.sysA.P.domain ∧
    ‖iteratedResolventPower tsys.sysA.RP r f - iteratedResolventPower tsys.sysB.RH r f‖ ≤
      ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ ∧
    ‖iteratedIdentityPower tsys.sysA.RP a r f - iteratedIdentityPower tsys.sysB.RH b r f‖ ≤
      2 * ‖f‖ := by
  have hdom := (twoParameterFiveOperator_domain_inclusions tsys).2.2.2.2
  have hmem := twoParam_cross_sub_succ_mem_first_domain
    tsys.sysA.P tsys.sysB.H_op tsys.sysA.RP tsys.sysB.RH a b
    tsys.sysA.res_P tsys.sysB.res_H hdom r f
  refine ⟨by abel, hmem.1, hmem.2,
    twoParam_iteratedResolventPower_cross_sub_norm_bound
      tsys.sysA.P tsys.sysB.H_op tsys.sysA.RP tsys.sysB.RH a b ha hb
      tsys.sysA.res_P tsys.sysB.res_H tsys.sysA.pos_P tsys.sysB.pos_H r f,
    twoParam_iteratedIdentityPower_cross_sub_norm_le_two
      tsys.sysA.P tsys.sysB.H_op tsys.sysA.RP tsys.sysB.RH a b ha hb
      tsys.sysA.res_P tsys.sysB.res_H tsys.sysA.pos_P tsys.sysB.pos_H r f⟩

/-- Simultaneous common-domain two-parameter Yosida cross-rate bounds across all five coupled
operator pairs `(P, G)`, `(S, H_op)`, `(T, S)`, `(T, H_op)`, and `(P, H_op)` on `z : tsys.sysA.H_op.domain`. -/
theorem twoParameterFiveOperator_common_domain_yosida_cross_rate_bounds
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (tsys : TwoParameterFiveOperatorSystem H a b)
    (r : ℕ) (z : tsys.sysA.H_op.domain) :
    let hHB : (z : H) ∈ tsys.sysB.H_op.domain := tsys.same_H.symm ▸ z.property
    let hGB : (z : H) ∈ tsys.sysB.G.domain := tsys.sysB.dom_HG hHB
    let hSB : (z : H) ∈ tsys.sysB.S.domain := tsys.sysB.dom_HS hHB
    let hGA : (z : H) ∈ tsys.sysA.G.domain := tsys.sysA.dom_HG z.property
    let hPA : (z : H) ∈ tsys.sysA.P.domain := tsys.sysA.dom_GP hGA
    let hSA : (z : H) ∈ tsys.sysA.S.domain := tsys.sysA.dom_HS z.property
    let hTA : (z : H) ∈ tsys.sysA.T.domain := tsys.sysA.dom_HT z.property
    ‖iteratedIdentityPower tsys.sysA.RP a r (z : H) -
      iteratedIdentityPower tsys.sysB.RG b r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖tsys.sysA.P ⟨(z : H), hPA⟩‖ +
        (r : ℝ) * b⁻¹ * ‖tsys.sysB.G ⟨(z : H), hGB⟩‖ ∧
    ‖iteratedIdentityPower tsys.sysA.RS a r (z : H) -
      iteratedIdentityPower tsys.sysB.RH b r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖tsys.sysA.S ⟨(z : H), hSA⟩‖ +
        (r : ℝ) * b⁻¹ * ‖tsys.sysB.H_op ⟨(z : H), hHB⟩‖ ∧
    ‖iteratedIdentityPower tsys.sysA.RT a r (z : H) -
      iteratedIdentityPower tsys.sysB.RS b r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖tsys.sysA.T ⟨(z : H), hTA⟩‖ +
        (r : ℝ) * b⁻¹ * ‖tsys.sysB.S ⟨(z : H), hSB⟩‖ ∧
    ‖iteratedIdentityPower tsys.sysA.RT a r (z : H) -
      iteratedIdentityPower tsys.sysB.RH b r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖tsys.sysA.T ⟨(z : H), hTA⟩‖ +
        (r : ℝ) * b⁻¹ * ‖tsys.sysB.H_op ⟨(z : H), hHB⟩‖ ∧
    ‖iteratedIdentityPower tsys.sysA.RP a r (z : H) -
      iteratedIdentityPower tsys.sysB.RH b r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖tsys.sysA.P ⟨(z : H), hPA⟩‖ +
        (r : ℝ) * b⁻¹ * ‖tsys.sysB.H_op ⟨(z : H), hHB⟩‖ := by
  intro hHB hGB hSB hGA hPA hSA hTA
  exact ⟨
    twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
      tsys.sysA.P tsys.sysB.G tsys.sysA.RP tsys.sysB.RG a b ha hb
      tsys.sysA.res_P tsys.sysB.res_G tsys.sysA.pos_P tsys.sysB.pos_G
      tsys.sysA.left_P tsys.sysB.left_G r (z : H) hPA hGB,
    twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
      tsys.sysA.S tsys.sysB.H_op tsys.sysA.RS tsys.sysB.RH a b ha hb
      tsys.sysA.res_S tsys.sysB.res_H tsys.sysA.pos_S tsys.sysB.pos_H
      tsys.sysA.left_S tsys.sysB.left_H r (z : H) hSA hHB,
    twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
      tsys.sysA.T tsys.sysB.S tsys.sysA.RT tsys.sysB.RS a b ha hb
      tsys.sysA.res_T tsys.sysB.res_S tsys.sysA.pos_T tsys.sysB.pos_S
      tsys.sysA.left_T tsys.sysB.left_S r (z : H) hTA hSB,
    twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
      tsys.sysA.T tsys.sysB.H_op tsys.sysA.RT tsys.sysB.RH a b ha hb
      tsys.sysA.res_T tsys.sysB.res_H tsys.sysA.pos_T tsys.sysB.pos_H
      tsys.sysA.left_T tsys.sysB.left_H r (z : H) hTA hHB,
    twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
      tsys.sysA.P tsys.sysB.H_op tsys.sysA.RP tsys.sysB.RH a b ha hb
      tsys.sysA.res_P tsys.sysB.res_H tsys.sysA.pos_P tsys.sysB.pos_H
      tsys.sysA.left_P tsys.sysB.left_H r (z : H) hPA hHB⟩

/-- Closed-loop two-parameter triangle identities across `(RT_a, RS_c, RH_b)` and
`(RP_a, RG_c, RH_b)` for both `iteratedResolventPower` and `iteratedIdentityPower`. -/
theorem twoParameterFiveOperator_triangle_identities
    {a b c : ℝ} (sysA : FiveOperatorResolventSystem H a)
    (sysB : FiveOperatorResolventSystem H b)
    (sysC : FiveOperatorResolventSystem H c) (r : ℕ) (f : H) :
    iteratedResolventPower sysA.RT r f - iteratedResolventPower sysB.RH r f =
      (iteratedResolventPower sysA.RT r f - iteratedResolventPower sysC.RS r f) +
        (iteratedResolventPower sysC.RS r f - iteratedResolventPower sysB.RH r f) ∧
    iteratedResolventPower sysA.RP r f - iteratedResolventPower sysB.RH r f =
      (iteratedResolventPower sysA.RP r f - iteratedResolventPower sysC.RG r f) +
        (iteratedResolventPower sysC.RG r f - iteratedResolventPower sysB.RH r f) ∧
    iteratedIdentityPower sysA.RT a r f - iteratedIdentityPower sysB.RH b r f =
      (iteratedIdentityPower sysA.RT a r f - iteratedIdentityPower sysC.RS c r f) +
        (iteratedIdentityPower sysC.RS c r f - iteratedIdentityPower sysB.RH b r f) ∧
    iteratedIdentityPower sysA.RP a r f - iteratedIdentityPower sysB.RH b r f =
      (iteratedIdentityPower sysA.RP a r f - iteratedIdentityPower sysC.RG c r f) +
        (iteratedIdentityPower sysC.RG c r f - iteratedIdentityPower sysB.RH b r f) := by
  refine ⟨by abel, by abel, by abel, by abel⟩

/-! ### 4. Coupled Closed-Graph-Form Hamiltonians Two-Parameter Cross-Resolvent Package -/

section CoupledClosedGraphFormsTwoParameter

variable {K1 K2 : Type*}
  [NormedAddCommGroup K1] [InnerProductSpace ℂ K1]
  [NormedAddCommGroup K2] [InnerProductSpace ℂ K2]
  [CompleteSpace H] [CompleteSpace K1] [CompleteSpace K2]

/-- Two-parameter higher-power cross-resolvent and Yosida difference package for any two
closed-graph-form Hamiltonians `hamiltonian D1` and `hamiltonian D2` at shifts `a > 0` and `b > 0`. -/
theorem coupled_closedGraphForm_twoParam_cross_resolvent_package
    (D1 : Data H K1) (D2 : Data H K2)
    (R1a R2b : H →L[ℂ] H) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr1 : Resolves (hamiltonian D1) R1a a)
    (hr2 : Resolves (hamiltonian D2) R2b b)
    (hl1 : ∀ z : (hamiltonian D1).domain, R1a (hamiltonian D1 z + a • (z : H)) = (z : H))
    (hl2 : ∀ z : (hamiltonian D2).domain, R2b (hamiltonian D2 z + b • (z : H)) = (z : H))
    (hdom : (hamiltonian D2).domain ≤ (hamiltonian D1).domain)
    (r : ℕ) (f : H) (z : (hamiltonian D2).domain) :
    IsSelfAdjoint (hamiltonian D1) ∧
    IsSelfAdjoint (hamiltonian D2) ∧
    iteratedResolventPower R1a (r + 1) f - iteratedResolventPower R2b (r + 1) f ∈
      (hamiltonian D1).domain ∧
    iteratedIdentityPower R1a a (r + 1) f - iteratedIdentityPower R2b b (r + 1) f ∈
      (hamiltonian D1).domain ∧
    ‖iteratedResolventPower R1a r f - iteratedResolventPower R2b r f‖ ≤
      ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ ∧
    ‖iteratedIdentityPower R1a a r f - iteratedIdentityPower R2b b r f‖ ≤ 2 * ‖f‖ ∧
    ‖iteratedIdentityPower R1a a r (z : H) - iteratedIdentityPower R2b b r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖hamiltonian D1 ⟨(z : H), hdom z.property⟩‖ +
        (r : ℝ) * b⁻¹ * ‖hamiltonian D2 z‖ := by
  have hmem := twoParam_cross_sub_succ_mem_first_domain
    (hamiltonian D1) (hamiltonian D2) R1a R2b a b hr1 hr2 hdom r f
  exact ⟨hamiltonian_selfAdjoint D1,
    hamiltonian_selfAdjoint D2,
    hmem.1, hmem.2,
    twoParam_iteratedResolventPower_cross_sub_norm_bound
      (hamiltonian D1) (hamiltonian D2) R1a R2b a b ha hb hr1 hr2
      (hamiltonian_positive D1) (hamiltonian_positive D2) r f,
    twoParam_iteratedIdentityPower_cross_sub_norm_le_two
      (hamiltonian D1) (hamiltonian D2) R1a R2b a b ha hb hr1 hr2
      (hamiltonian_positive D1) (hamiltonian_positive D2) r f,
    twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
      (hamiltonian D1) (hamiltonian D2) R1a R2b a b ha hb hr1 hr2
      (hamiltonian_positive D1) (hamiltonian_positive D2) hl1 hl2 r (z : H)
      (hdom z.property) z.property⟩

/-- Combined two-parameter + bounded-perturbation rate specialization for two coupled
closed-graph-form Hamiltonians `hamiltonian D1` and `hamiltonian D2`. -/
theorem coupled_closedGraphForm_twoParam_bounded_perturbation_rates
    (D1 : Data H K1) (D2 : Data H K2) (K : H →ₗ.[ℂ] H)
    (R1 R2 : ℝ → H →L[ℂ] H) (a b M : ℝ) (ha : 0 < a) (hb : 0 < b) (hM : 0 ≤ M)
    (hr1a : Resolves (hamiltonian D1) (R1 a) a)
    (hr1b : Resolves (hamiltonian D1) (R1 b) b)
    (hr2b : Resolves (hamiltonian D2) (R2 b) b)
    (hl1a : ∀ z : (hamiltonian D1).domain, R1 a (hamiltonian D1 z + a • (z : H)) = (z : H))
    (hl1b : ∀ z : (hamiltonian D1).domain, R1 b (hamiltonian D1 z + b • (z : H)) = (z : H))
    (hdom : (hamiltonian D2).domain ≤ (hamiltonian D1).domain)
    (hK : (hamiltonian D2).domain ≤ K.domain)
    (hadd : ∀ z : (hamiltonian D2).domain,
      hamiltonian D2 z = hamiltonian D1 ⟨(z : H), hdom z.property⟩ + K ⟨(z : H), hK z.property⟩)
    (hK_bound : ∀ z : K.domain, ‖K z‖ ≤ M * ‖(z : H)‖)
    (r : ℕ) (f : H) (x : (hamiltonian D1).domain) :
    ‖iteratedResolventPower (R1 a) r f - iteratedResolventPower (R2 b) r f‖ ≤
      ‖iteratedResolventPower (R1 a) r f - iteratedResolventPower (R1 b) r f‖ +
        (r : ℝ) * M * (b⁻¹) ^ (r + 1) * ‖f‖ ∧
    ‖iteratedIdentityPower (R1 a) a r (x : H) - iteratedIdentityPower (R2 b) b r (x : H)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖hamiltonian D1 x‖ + (r : ℝ) * b⁻¹ * M * ‖(x : H)‖ :=
  twoParam_bounded_perturbation_resolvent_and_yosida_bounds
    (hamiltonian D1) (hamiltonian D2) K R1 R2 a b M ha hb hM
    hr1a hr1b hr2b (hamiltonian_positive D1) (hamiltonian_positive D2)
    hl1a hl1b hdom hK hadd hK_bound r f x

end CoupledClosedGraphFormsTwoParameter

/-- Master 5-Pair Two-Parameter Higher-Power Cross-Resolvent Synthesis Theorem. -/
theorem fiveOperator_twoParameter_higherPower_cross_resolvent_master_synthesis
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (tsys : TwoParameterFiveOperatorSystem H a b)
    (r : ℕ) (f : H) (z : tsys.sysA.H_op.domain) :
    (iteratedResolventPower tsys.sysA.RP (r + 1) f -
       iteratedResolventPower tsys.sysB.RG (r + 1) f ∈ tsys.sysA.P.domain ∧
     iteratedResolventPower tsys.sysA.RS (r + 1) f -
       iteratedResolventPower tsys.sysB.RH (r + 1) f ∈ tsys.sysA.S.domain ∧
     iteratedResolventPower tsys.sysA.RT (r + 1) f -
       iteratedResolventPower tsys.sysB.RS (r + 1) f ∈ tsys.sysA.T.domain ∧
     iteratedResolventPower tsys.sysA.RT (r + 1) f -
       iteratedResolventPower tsys.sysB.RH (r + 1) f ∈ tsys.sysA.T.domain ∧
     iteratedResolventPower tsys.sysA.RP (r + 1) f -
       iteratedResolventPower tsys.sysB.RH (r + 1) f ∈ tsys.sysA.P.domain) ∧
    (‖iteratedResolventPower tsys.sysA.RP r f - iteratedResolventPower tsys.sysB.RG r f‖ ≤
       ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ ∧
     ‖iteratedResolventPower tsys.sysA.RS r f - iteratedResolventPower tsys.sysB.RH r f‖ ≤
       ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ ∧
     ‖iteratedResolventPower tsys.sysA.RT r f - iteratedResolventPower tsys.sysB.RS r f‖ ≤
       ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ ∧
     ‖iteratedResolventPower tsys.sysA.RT r f - iteratedResolventPower tsys.sysB.RH r f‖ ≤
       ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ ∧
     ‖iteratedResolventPower tsys.sysA.RP r f - iteratedResolventPower tsys.sysB.RH r f‖ ≤
       ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖) ∧
    (‖iteratedIdentityPower tsys.sysA.RP a r f - iteratedIdentityPower tsys.sysB.RG b r f‖ ≤
       2 * ‖f‖ ∧
     ‖iteratedIdentityPower tsys.sysA.RS a r f - iteratedIdentityPower tsys.sysB.RH b r f‖ ≤
       2 * ‖f‖ ∧
     ‖iteratedIdentityPower tsys.sysA.RT a r f - iteratedIdentityPower tsys.sysB.RS b r f‖ ≤
       2 * ‖f‖ ∧
     ‖iteratedIdentityPower tsys.sysA.RT a r f - iteratedIdentityPower tsys.sysB.RH b r f‖ ≤
       2 * ‖f‖ ∧
     ‖iteratedIdentityPower tsys.sysA.RP a r f - iteratedIdentityPower tsys.sysB.RH b r f‖ ≤
       2 * ‖f‖) ∧
    ‖iteratedIdentityPower tsys.sysA.RT a r (z : H) -
      iteratedIdentityPower tsys.sysB.RH b r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖tsys.sysA.T ⟨(z : H), tsys.sysA.dom_HT z.property⟩‖ +
        (r : ℝ) * b⁻¹ * ‖tsys.sysB.H_op ⟨(z : H), tsys.same_H.symm ▸ z.property⟩‖ := by
  have hp1 := pair1_twoParam_potential_sub_growing_package ha hb tsys r f
  have hp2 := pair2_twoParam_residual_sub_hamiltonian_package ha hb tsys r f
  have hp3 := pair3_twoParam_static_sub_residual_package ha hb tsys r f
  have hp4 := pair4_twoParam_static_sub_hamiltonian_package ha hb tsys r f
  have hp5 := pair5_twoParam_potential_sub_hamiltonian_package ha hb tsys r f
  have hrate := (twoParameterFiveOperator_common_domain_yosida_cross_rate_bounds ha hb tsys r z).2.2.2.1
  exact ⟨⟨hp1.2.1, hp2.2.1, hp3.2.1, hp4.2.1, hp5.2.1⟩,
    ⟨hp1.2.2.2.1, hp2.2.2.2.1, hp3.2.2.2.1, hp4.2.2.2.1, hp5.2.2.2.1⟩,
    ⟨hp1.2.2.2.2, hp2.2.2.2.2, hp3.2.2.2.2, hp4.2.2.2.2, hp5.2.2.2.2⟩,
    hrate⟩

end

#print axioms twoParam_iteratedResolventPower_cross_sub_zero
#print axioms twoParam_iteratedResolventPower_bridge_decompositions
#print axioms twoParam_iteratedIdentityPower_bridge_decompositions
#print axioms twoParam_iteratedIdentityPower_split_via_self
#print axioms twoParam_iteratedIdentityPower_cross_sub_zero
#print axioms twoParam_iteratedIdentityPower_cross_sub_one
#print axioms twoParam_iteratedIdentityPower_cross_sub_succ_left_and_right
#print axioms twoParam_iteratedResolventPower_cross_sub_norm_bound
#print axioms twoParam_iteratedIdentityPower_cross_sub_norm_le_two
#print axioms twoParam_iteratedIdentityPower_cross_sub_domain_rate_bound
#print axioms twoParam_cross_sub_succ_mem_first_domain
#print axioms combined_first_and_second_resolvent_identity
#print axioms higherPower_combined_first_and_second_resolvent_identity
#print axioms twoParam_cross_sub_succ_mem_secondPowerDomain
#print axioms twoParam_bounded_perturbation_resolvent_and_yosida_bounds
#print axioms twoParameterFiveOperator_domain_inclusions
#print axioms pair1_twoParam_potential_sub_growing_package
#print axioms pair2_twoParam_residual_sub_hamiltonian_package
#print axioms pair3_twoParam_static_sub_residual_package
#print axioms pair4_twoParam_static_sub_hamiltonian_package
#print axioms pair5_twoParam_potential_sub_hamiltonian_package
#print axioms twoParameterFiveOperator_common_domain_yosida_cross_rate_bounds
#print axioms twoParameterFiveOperator_triangle_identities
#print axioms coupled_closedGraphForm_twoParam_cross_resolvent_package
#print axioms coupled_closedGraphForm_twoParam_bounded_perturbation_rates
#print axioms fiveOperator_twoParameter_higherPower_cross_resolvent_master_synthesis

end UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorTwoParameterHigherPowerCrossResolvent
