/-
  LayerA/AnomalyFromOrder.lean — Anomaly cancellation is algebraic, not QFT-imported

  Critique #4: "Anomaly cancellation is imported from QFT, not derived."

  RESPONSE: The anomaly cancellation condition is a POLYNOMIAL IDENTITY
  constraining rational charges. The physical content (why anomalies must
  cancel) derives from gauge invariance. But the algebraic content (the
  polynomial equation and its solutions) is pure number theory.

  We prove:
  1. The anomaly polynomial for SU(N_c) with N_c colors is a specific
     cubic expression in the charges
  2. For N_c = 3, the cubic factors as 18·yQ·(4·yQ + yu)·(2·yQ - yu)
  3. For yQ ≠ 0, there are exactly two branches: SM and exotic
  4. The SM branch gives the correct electric charges

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.AnomalyFromOrder

/-! ## 1. The anomaly polynomial as pure algebra -/

/-- A charge assignment for a single generation of fermions
    in SU(N_c) x SU(2) x U(1). All charges are rational. -/
structure RationalChargeAssignment where
  /-- Quark doublet hypercharge -/
  yQ : ℚ
  /-- Up-type singlet hypercharge (left-handed conjugate) -/
  yu : ℚ
  /-- Down-type singlet hypercharge (left-handed conjugate) -/
  yd : ℚ
  /-- Lepton doublet hypercharge -/
  yL : ℚ
  /-- Charged lepton singlet hypercharge (left-handed conjugate) -/
  ye : ℚ

/-- The cubic anomaly polynomial for N_c colors.
    Tr[Y^3] = 2*N_c*yQ^3 + N_c*yu^3 + N_c*yd^3 + 2*yL^3 + ye^3. -/
def cubicAnomalyPoly (Nc : ℚ) (ca : RationalChargeAssignment) : ℚ :=
  2 * Nc * ca.yQ ^ 3 + Nc * ca.yu ^ 3 + Nc * ca.yd ^ 3 +
  2 * ca.yL ^ 3 + ca.ye ^ 3

/-- The linear anomaly polynomial (gravitational). -/
def linearAnomalyPoly (Nc : ℚ) (ca : RationalChargeAssignment) : ℚ :=
  2 * Nc * ca.yQ + Nc * ca.yu + Nc * ca.yd + 2 * ca.yL + ca.ye

/-- The SU(2)^2 x U(1) mixed anomaly polynomial. -/
def su2MixedPoly (Nc : ℚ) (ca : RationalChargeAssignment) : ℚ :=
  Nc * ca.yQ + ca.yL

/-- The SU(3)^2 x U(1) mixed anomaly polynomial. -/
def su3MixedPoly (ca : RationalChargeAssignment) : ℚ :=
  2 * ca.yQ + ca.yu + ca.yd

/-! ## 2. The anomaly conditions are purely algebraic -/

/-- The anomaly conditions are polynomial equations on rationals.
    No quantum field theory, no path integrals, no Feynman diagrams. -/
def IsAnomalyFreeRational (Nc : ℚ) (ca : RationalChargeAssignment) : Prop :=
  cubicAnomalyPoly Nc ca = 0 ∧
  linearAnomalyPoly Nc ca = 0 ∧
  su2MixedPoly Nc ca = 0 ∧
  su3MixedPoly ca = 0

/-- The anomaly conditions are ALGEBRAIC: they can be written as a system
    of polynomial equations with rational coefficients. -/
theorem anomaly_is_algebraic (Nc : ℚ) (ca : RationalChargeAssignment) :
    IsAnomalyFreeRational Nc ca ↔
    (2 * Nc * ca.yQ ^ 3 + Nc * ca.yu ^ 3 + Nc * ca.yd ^ 3 +
      2 * ca.yL ^ 3 + ca.ye ^ 3 = 0 ∧
     2 * Nc * ca.yQ + Nc * ca.yu + Nc * ca.yd + 2 * ca.yL + ca.ye = 0 ∧
     Nc * ca.yQ + ca.yL = 0 ∧
     2 * ca.yQ + ca.yu + ca.yd = 0) := by
  unfold IsAnomalyFreeRational cubicAnomalyPoly linearAnomalyPoly
    su2MixedPoly su3MixedPoly
  rfl

/-! ## 3. Solving the system: mixed conditions determine charges -/

/-- From SU(2)^2 mixed: yL = -N_c * yQ. -/
theorem mixed_determines_yL (Nc : ℚ) (ca : RationalChargeAssignment)
    (h : su2MixedPoly Nc ca = 0) :
    ca.yL = -Nc * ca.yQ := by
  unfold su2MixedPoly at h; linarith

/-- From SU(3)^2 mixed: yd = -2*yQ - yu. -/
theorem mixed_determines_yd (ca : RationalChargeAssignment)
    (h : su3MixedPoly ca = 0) :
    ca.yd = -2 * ca.yQ - ca.yu := by
  unfold su3MixedPoly at h; linarith

/-- From the linear condition, substituting yL and yd:
    ye = -(2*Nc*yQ + Nc*yu + Nc*yd + 2*yL).
    With yL = -Nc*yQ and yd = -2*yQ - yu, we get ye = 2*Nc*yQ.
    Since this involves products of unknowns, we prove it via nlinarith. -/
theorem linear_determines_ye (Nc : ℚ) (ca : RationalChargeAssignment)
    (hlin : linearAnomalyPoly Nc ca = 0)
    (hsu2 : su2MixedPoly Nc ca = 0)
    (hsu3 : su3MixedPoly ca = 0) :
    ca.ye = 2 * Nc * ca.yQ := by
  have h1 : ca.yL = -Nc * ca.yQ := mixed_determines_yL Nc ca hsu2
  have h2 : ca.yd = -2 * ca.yQ - ca.yu := mixed_determines_yd ca hsu3
  unfold linearAnomalyPoly at hlin
  -- Substitute h1 and h2 into hlin:
  -- hlin: 2*Nc*yQ + Nc*yu + Nc*yd + 2*yL + ye = 0
  -- With yL = -Nc*yQ and yd = -2*yQ - yu:
  -- 2*Nc*yQ + Nc*yu + Nc*(-2*yQ - yu) + 2*(-Nc*yQ) + ye = 0
  -- = 2*Nc*yQ + Nc*yu - 2*Nc*yQ - Nc*yu - 2*Nc*yQ + ye = 0
  -- = -2*Nc*yQ + ye = 0
  -- So ye = 2*Nc*yQ
  rw [h1, h2] at hlin; linarith

/-! ## 4. The cubic factorization -/

/-- For N_c = 3, after substituting the mixed + linear conditions,
    the cubic anomaly reduces to 18*yQ*(4*yQ + yu)*(2*yQ - yu). -/
theorem cubic_factorization (yQ yu : ℚ) :
    let yL := -(3 : ℚ) * yQ
    let yd := -2 * yQ - yu
    let ye := 2 * 3 * yQ
    2 * 3 * yQ ^ 3 + 3 * yu ^ 3 + 3 * yd ^ 3 + 2 * yL ^ 3 + ye ^ 3 =
    18 * yQ * (4 * yQ + yu) * (2 * yQ - yu) := by
  ring

/-! ## 5. The SM charge assignment -/

/-- The SM charge assignment (rational). -/
def smChargesQ : RationalChargeAssignment where
  yQ := 1/6
  yu := -2/3
  yd := 1/3
  yL := -1/2
  ye := 1

/-- The SM is anomaly-free for N_c = 3. Pure computation. -/
theorem sm_anomaly_free_Nc3 : IsAnomalyFreeRational 3 smChargesQ := by
  unfold IsAnomalyFreeRational cubicAnomalyPoly linearAnomalyPoly
    su2MixedPoly su3MixedPoly smChargesQ
  constructor <;> [norm_num; constructor <;> [norm_num; constructor <;> norm_num]]

/-- The SM has yu = -4*yQ, which is one root of the factored cubic. -/
theorem sm_is_factored_root : smChargesQ.yu = -4 * smChargesQ.yQ := by
  unfold smChargesQ; norm_num

/-! ## 6. Uniqueness: two branches from the factorization -/

/-- Any anomaly-free assignment with N_c = 3 and yQ != 0 satisfies
    either yu = -4*yQ or yu = 2*yQ.

    Proof: from the factorization 18*yQ*(4*yQ + yu)*(2*yQ - yu) = 0
    with yQ != 0, either (4*yQ + yu) = 0 or (2*yQ - yu) = 0. -/
theorem anomaly_two_branches (yQ yu : ℚ) (hQ : yQ ≠ 0)
    (hcubic : 18 * yQ * (4 * yQ + yu) * (2 * yQ - yu) = 0) :
    yu = -4 * yQ ∨ yu = 2 * yQ := by
  have h18 : (18 : ℚ) ≠ 0 := by norm_num
  -- Rewrite as (18 * yQ) * ((4 * yQ + yu) * (2 * yQ - yu)) = 0
  have hprod : (4 * yQ + yu) * (2 * yQ - yu) = 0 := by
    have h1 : 18 * yQ ≠ 0 := mul_ne_zero h18 hQ
    -- 18 * yQ * (4 * yQ + yu) * (2 * yQ - yu) = (18 * yQ) * ((4 * yQ + yu) * (2 * yQ - yu))
    have heq : 18 * yQ * (4 * yQ + yu) * (2 * yQ - yu) =
               (18 * yQ) * ((4 * yQ + yu) * (2 * yQ - yu)) := by ring
    rw [heq] at hcubic
    exact (mul_eq_zero.mp hcubic).resolve_left h1
  rcases mul_eq_zero.mp hprod with h | h
  · left; linarith
  · right; linarith

/-- The exotic branch yu = 2*yQ gives yd = -4*yQ. -/
theorem exotic_branch_charges (yQ : ℚ) :
    let yu := 2 * yQ
    let yd := -2 * yQ - yu
    yd = -4 * yQ := by
  ring

/-! ## 7. The SM branch gives the correct electric charges -/

/-- With normalization yQ = 1/6, the SM branch reproduces
    the known electric charges: Q = T3 + Y. -/
theorem sm_branch_gives_correct_charges :
    let yQ : ℚ := 1/6
    let yu := -4 * yQ
    let yd := -2 * yQ - yu
    let yL := -3 * yQ
    let ye := 6 * yQ
    -- u_L: T3 = 1/2, Y = yQ -> Q = 2/3
    (1/2 + yQ = 2/3) ∧
    -- d_L: T3 = -1/2, Y = yQ -> Q = -1/3
    (-1/2 + yQ = -1/3) ∧
    -- nu_L: T3 = 1/2, Y = yL -> Q = 0
    (1/2 + yL = 0) ∧
    -- e_L: T3 = -1/2, Y = yL -> Q = -1
    (-1/2 + yL = -1) ∧
    -- u_R has Y = -yu (un-conjugate): Q = 2/3
    (-yu = 2/3) ∧
    -- d_R has Y = -yd (un-conjugate): Q = -1/3
    (-yd = -1/3) ∧
    -- e_R has Y = -ye (un-conjugate): Q = -1
    (-ye = -1) := by
  norm_num

/-! ## 8. The anomaly polynomial is a number-theoretic object -/

/-- If all charges are integer multiples of yQ, the cubic anomaly
    becomes a polynomial in the integer ratio n = yu/yQ.
    With yu = n * yQ, the factored cubic is
    18 * yQ^3 * (4 + n) * (2 - n). -/
theorem cubic_in_integer_ratio (yQ : ℚ) (n : ℤ) :
    let yu := (n : ℚ) * yQ
    18 * yQ * (4 * yQ + yu) * (2 * yQ - yu) =
    18 * yQ ^ 3 * ((4 : ℚ) + n) * (2 - n) := by
  ring

/-- For nonzero yQ, the integer equation (4 + n)(2 - n) = 0 has
    exactly two solutions: n = -4 (SM) and n = 2 (exotic). -/
theorem integer_solutions (n : ℤ) :
    ((4 : ℤ) + n) * (2 - n) = 0 ↔ n = -4 ∨ n = 2 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · left; omega
    · right; omega
  · rintro (rfl | rfl) <;> norm_num

/-! ## 9. Summary theorem -/

/-- MASTER THEOREM: Anomaly cancellation is purely algebraic.

    (1) SM satisfies all anomaly conditions
    (2) The cubic factors as 18*yQ*(4*yQ + yu)*(2*yQ - yu)
    (3) Non-trivial solutions: yu = -4*yQ or yu = 2*yQ
    (4) The SM branch gives the correct electric charges

    The physical input is gauge invariance (why anomalies must cancel).
    The mathematical content (which charges work) is pure algebra. -/
theorem anomaly_purely_algebraic :
    -- (1) SM satisfies all anomaly conditions
    IsAnomalyFreeRational 3 smChargesQ
    -- (2) The cubic factors
    ∧ (∀ yQ yu : ℚ,
        let yL := -(3 : ℚ) * yQ
        let yd := -2 * yQ - yu
        let ye := 2 * 3 * yQ
        2 * 3 * yQ ^ 3 + 3 * yu ^ 3 + 3 * yd ^ 3 + 2 * yL ^ 3 + ye ^ 3 =
        18 * yQ * (4 * yQ + yu) * (2 * yQ - yu))
    -- (3) Non-trivial solutions
    ∧ (∀ yQ yu : ℚ, yQ ≠ 0 →
        18 * yQ * (4 * yQ + yu) * (2 * yQ - yu) = 0 →
        yu = -4 * yQ ∨ yu = 2 * yQ) := by
  exact ⟨sm_anomaly_free_Nc3, cubic_factorization, anomaly_two_branches⟩

end UnifiedTheory.LayerA.AnomalyFromOrder
