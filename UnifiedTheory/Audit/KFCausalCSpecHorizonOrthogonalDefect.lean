/-
  Audit/KFCausalCSpecHorizonOrthogonalDefect.lean

  Horizon-orthogonal least-defect growth, finite algebraic core.

  The entropy bridge identifies the horizon-hit source `J` as the exact finite
  focusing channel: tilting a finite birth law by `J` changes one-birth horizon
  area by `-Var(J)` at first order.

  This file proves the complementary finite statement: any defect source can be
  projected orthogonally to `J` in covariance geometry, and its residual has no
  first-order effect on horizon focusing.  Therefore geometry/defect repair can
  be added in the covariance-orthogonal directions without renormalizing the
  horizon entropy channel to first order.

  Context/citation: this is the finite causal-growth control layer built around
  the Dorau--Much relative-entropy route formalized in
  `KFCausalCSpecArakiHorizonRelativeEntropy.lean`:

    Philipp Dorau and Albert Much,
    "From Quantum Relative Entropy to the Semiclassical Einstein Equations,"
    arXiv:2510.24491v3 [hep-th], 3 Mar 2026.
    Phys. Rev. Lett. 136, 091602 (2026).
    DOI: 10.1103/lmq8-nsty; arXiv DOI: 10.48550/arXiv.2510.24491.

  Zero sorry.  Zero custom axioms.
-/

import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHorizonOrthogonalDefect

open Filter
open scoped BigOperators

/-! ## 1. Finite covariance geometry -/

/-- Finite weighted expectation. -/
noncomputable def expectation {ι : Type*} [Fintype ι]
    (w X : ι → ℝ) : ℝ :=
  ∑ i, w i * X i

/-- Finite weighted covariance. -/
noncomputable def covariance {ι : Type*} [Fintype ι]
    (w X Y : ι → ℝ) : ℝ :=
  expectation w (fun i => X i * Y i) - expectation w X * expectation w Y

/-- Finite weighted variance. -/
noncomputable def variance {ι : Type*} [Fintype ι]
    (w X : ι → ℝ) : ℝ :=
  covariance w X X

/-- One-birth horizon-area change: `c` is the new maximal contribution and
`J` is the number of old horizon/frontier elements hit. -/
def finiteAreaChange {ι : Type*} (c : ℝ) (J : ι → ℝ) : ι → ℝ :=
  fun i => c - J i

/-- A source centered against the finite weighted expectation. -/
noncomputable def centeredSource {ι : Type*} [Fintype ι]
    (w S : ι → ℝ) : ι → ℝ :=
  fun i => S i - expectation w S

/-- First-order response of observable `X` to source tilt `S`. -/
noncomputable def linearResponse {ι : Type*} [Fintype ι]
    (w S X : ι → ℝ) : ℝ :=
  expectation w (fun i => X i * centeredSource w S i)

/-- The finite second central response numerator for observable `X` under
source `S`.  In an exponential-tilt Taylor expansion at the current parent
state, this is the algebraic second-order obstruction term. -/
noncomputable def quadraticResponse {ι : Type*} [Fintype ι]
    (w S X : ι → ℝ) : ℝ :=
  covariance w X (fun i => centeredSource w S i ^ 2)

/-- The second-order horizon leakage of source `S`: even when `S` is
covariance-orthogonal to `J`, its squared centered amplitude may still correlate
with the horizon channel. -/
noncomputable def horizonSecondOrderLeakage {ι : Type*} [Fintype ι]
    (w J S : ι → ℝ) : ℝ :=
  covariance w J (fun i => centeredSource w S i ^ 2)

/-- The polarized second-order leakage form.  Its diagonal is
`horizonSecondOrderLeakage`. -/
noncomputable def horizonSecondOrderCrossLeakage {ι : Type*} [Fintype ι]
    (w J A B : ι → ℝ) : ℝ :=
  covariance w J (fun i => centeredSource w A i * centeredSource w B i)

theorem expectation_add {ι : Type*} [Fintype ι]
    (w X Y : ι → ℝ) :
    expectation w (fun i => X i + Y i) =
      expectation w X + expectation w Y := by
  unfold expectation
  calc
    (∑ i, w i * (X i + Y i))
        = ∑ i, (w i * X i + w i * Y i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = (∑ i, w i * X i) + ∑ i, w i * Y i := by
            rw [Finset.sum_add_distrib]

theorem expectation_sub {ι : Type*} [Fintype ι]
    (w X Y : ι → ℝ) :
    expectation w (fun i => X i - Y i) =
      expectation w X - expectation w Y := by
  unfold expectation
  calc
    (∑ i, w i * (X i - Y i))
        = ∑ i, (w i * X i - w i * Y i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = (∑ i, w i * X i) - ∑ i, w i * Y i := by
            rw [Finset.sum_sub_distrib]

theorem expectation_const_mul {ι : Type*} [Fintype ι]
    (w X : ι → ℝ) (a : ℝ) :
    expectation w (fun i => a * X i) =
      a * expectation w X := by
  unfold expectation
  calc
    (∑ i, w i * (a * X i))
        = ∑ i, a * (w i * X i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = a * ∑ i, w i * X i := by
            rw [Finset.mul_sum]

theorem expectation_linear_combination {ι : Type*} [Fintype ι]
    (w A B : ι → ℝ) (a b : ℝ) :
    expectation w (fun i => a * A i + b * B i) =
      a * expectation w A + b * expectation w B := by
  rw [expectation_add]
  rw [expectation_const_mul, expectation_const_mul]

theorem centeredSource_linear_combination {ι : Type*} [Fintype ι]
    (w A B : ι → ℝ) (a b : ℝ) :
    centeredSource w (fun i => a * A i + b * B i) =
      fun i => a * centeredSource w A i + b * centeredSource w B i := by
  funext i
  unfold centeredSource
  rw [expectation_linear_combination]
  ring

/-- Covariance is symmetric over real-valued observables. -/
theorem covariance_comm {ι : Type*} [Fintype ι]
    (w X Y : ι → ℝ) :
    covariance w X Y = covariance w Y X := by
  unfold covariance expectation
  have hprod :
      (∑ i, w i * (X i * Y i)) =
        ∑ i, w i * (Y i * X i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hprod]
  ring

theorem covariance_add_left {ι : Type*} [Fintype ι]
    (w X Y Z : ι → ℝ) :
    covariance w (fun i => X i + Y i) Z =
      covariance w X Z + covariance w Y Z := by
  unfold covariance
  have hprod :
      expectation w (fun i => (X i + Y i) * Z i) =
        expectation w (fun i => X i * Z i) +
          expectation w (fun i => Y i * Z i) := by
    calc
      expectation w (fun i => (X i + Y i) * Z i)
          = expectation w (fun i => X i * Z i + Y i * Z i) := by
              congr
              funext i
              ring
      _ = expectation w (fun i => X i * Z i) +
            expectation w (fun i => Y i * Z i) :=
              expectation_add w (fun i => X i * Z i) (fun i => Y i * Z i)
  rw [hprod, expectation_add]
  ring

theorem covariance_sub_left {ι : Type*} [Fintype ι]
    (w X Y Z : ι → ℝ) :
    covariance w (fun i => X i - Y i) Z =
      covariance w X Z - covariance w Y Z := by
  unfold covariance
  have hprod :
      expectation w (fun i => (X i - Y i) * Z i) =
        expectation w (fun i => X i * Z i) -
          expectation w (fun i => Y i * Z i) := by
    calc
      expectation w (fun i => (X i - Y i) * Z i)
          = expectation w (fun i => X i * Z i - Y i * Z i) := by
              congr
              funext i
              ring
      _ = expectation w (fun i => X i * Z i) -
            expectation w (fun i => Y i * Z i) :=
              expectation_sub w (fun i => X i * Z i) (fun i => Y i * Z i)
  rw [hprod, expectation_sub]
  ring

theorem covariance_const_mul_left {ι : Type*} [Fintype ι]
    (w X Y : ι → ℝ) (a : ℝ) :
    covariance w (fun i => a * X i) Y =
      a * covariance w X Y := by
  unfold covariance
  have hprod :
      expectation w (fun i => (a * X i) * Y i) =
        a * expectation w (fun i => X i * Y i) := by
    calc
      expectation w (fun i => (a * X i) * Y i)
          = expectation w (fun i => a * (X i * Y i)) := by
              congr
              funext i
              ring
      _ = a * expectation w (fun i => X i * Y i) :=
              expectation_const_mul w (fun i => X i * Y i) a
  rw [hprod, expectation_const_mul]
  ring

theorem covariance_add_right {ι : Type*} [Fintype ι]
    (w X Y Z : ι → ℝ) :
    covariance w X (fun i => Y i + Z i) =
      covariance w X Y + covariance w X Z := by
  rw [covariance_comm w X (fun i => Y i + Z i)]
  rw [covariance_add_left]
  rw [covariance_comm w Y X, covariance_comm w Z X]

theorem covariance_const_mul_right {ι : Type*} [Fintype ι]
    (w X Y : ι → ℝ) (a : ℝ) :
    covariance w X (fun i => a * Y i) =
      a * covariance w X Y := by
  rw [covariance_comm w X (fun i => a * Y i)]
  rw [covariance_const_mul_left]
  rw [covariance_comm w Y X]

theorem covariance_const_mul_add_right {ι : Type*} [Fintype ι]
    (w X Y Z : ι → ℝ) (a b : ℝ) :
    covariance w X (fun i => a * Y i + b * Z i) =
      a * covariance w X Y + b * covariance w X Z := by
  rw [covariance_comm w X (fun i => a * Y i + b * Z i)]
  rw [covariance_add_left]
  rw [covariance_const_mul_left, covariance_const_mul_left]
  rw [covariance_comm w Y X, covariance_comm w Z X]

/-! ## 2. Horizon focusing and orthogonal residuals -/

/-- The first-order tilt response is covariance with the source. -/
theorem linearResponse_eq_covariance {ι : Type*} [Fintype ι]
    (w S X : ι → ℝ) :
    linearResponse w S X = covariance w X S := by
  unfold linearResponse centeredSource covariance expectation
  calc
    (∑ i, w i * (X i * (S i - ∑ j, w j * S j)))
        = ∑ i, (w i * (X i * S i) -
            (∑ j, w j * S j) * (w i * X i)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = ∑ i, w i * (X i * S i) -
          (∑ j, w j * S j) * (∑ i, w i * X i) := by
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [Finset.mul_sum]
    _ = (∑ i, w i * (X i * S i)) -
          (∑ i, w i * X i) * (∑ i, w i * S i) := by
            ring

/-- Covariance of area change `c-J` against any source is the negative
covariance of `J` against that source. -/
theorem covariance_finiteAreaChange_eq_neg_covariance
    {ι : Type*} [Fintype ι]
    (w J S : ι → ℝ) (c : ℝ)
    (hw : (∑ i, w i) = 1) :
    covariance w (finiteAreaChange c J) S = -covariance w J S := by
  unfold covariance finiteAreaChange
  have harea :
      expectation w (fun i => c - J i) = c - expectation w J := by
    unfold expectation
    calc
      (∑ i, w i * (c - J i))
          = ∑ i, (c * w i - w i * J i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = c * (∑ i, w i) - ∑ i, w i * J i := by
              rw [Finset.sum_sub_distrib]
              congr 1
              rw [Finset.mul_sum]
      _ = c - ∑ i, w i * J i := by
              rw [hw]
              ring
  have hprod :
      expectation w (fun i => (c - J i) * S i) =
        c * expectation w S - expectation w (fun i => J i * S i) := by
    unfold expectation
    calc
      (∑ i, w i * ((c - J i) * S i))
          = ∑ i, (c * (w i * S i) - w i * (J i * S i)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = c * (∑ i, w i * S i) - ∑ i, w i * (J i * S i) := by
              rw [Finset.sum_sub_distrib]
              congr 1
              rw [Finset.mul_sum]
  rw [harea, hprod]
  ring

/-- Pure horizon-source tilt focuses area with slope `-Var(J)`. -/
theorem linearResponse_finiteAreaChange_self
    {ι : Type*} [Fintype ι]
    (w J : ι → ℝ) (c : ℝ)
    (hw : (∑ i, w i) = 1) :
    linearResponse w J (finiteAreaChange c J) = -variance w J := by
  rw [linearResponse_eq_covariance]
  exact covariance_finiteAreaChange_eq_neg_covariance w J J c hw

/-! ## 3. Second-order obstruction -/

/-- The second central area-response numerator is exactly the negative
horizon leakage of the squared centered source. -/
theorem quadraticResponse_finiteAreaChange_eq_neg_leakage
    {ι : Type*} [Fintype ι]
    (w J S : ι → ℝ) (c : ℝ)
    (hw : (∑ i, w i) = 1) :
    quadraticResponse w S (finiteAreaChange c J) =
      -horizonSecondOrderLeakage w J S := by
  unfold quadraticResponse horizonSecondOrderLeakage
  exact covariance_finiteAreaChange_eq_neg_covariance w J
    (fun i => centeredSource w S i ^ 2) c hw

/-- First-order horizon orthogonality does not hide the next obstruction:
the remaining second central area response is the displayed leakage. -/
theorem orthogonal_source_secondOrder_area_obstruction
    {ι : Type*} [Fintype ι]
    (w J S : ι → ℝ) (c : ℝ)
    (hw : (∑ i, w i) = 1)
    (horth : covariance w S J = 0) :
    linearResponse w S (finiteAreaChange c J) = 0 ∧
      quadraticResponse w S (finiteAreaChange c J) =
        -horizonSecondOrderLeakage w J S := by
  constructor
  · rw [linearResponse_eq_covariance]
    rw [covariance_finiteAreaChange_eq_neg_covariance w J S c hw]
    rw [covariance_comm w J S]
    rw [horth]
    ring
  · exact quadraticResponse_finiteAreaChange_eq_neg_leakage w J S c hw

/-- A source whose first covariance and second leakage both vanish is protected
through the finite second central response. -/
theorem orthogonal_source_firstAndSecondOrder_area_zero
    {ι : Type*} [Fintype ι]
    (w J S : ι → ℝ) (c : ℝ)
    (hw : (∑ i, w i) = 1)
    (horth : covariance w S J = 0)
    (hleak : horizonSecondOrderLeakage w J S = 0) :
    linearResponse w S (finiteAreaChange c J) = 0 ∧
      quadraticResponse w S (finiteAreaChange c J) = 0 := by
  constructor
  · rw [linearResponse_eq_covariance]
    rw [covariance_finiteAreaChange_eq_neg_covariance w J S c hw]
    rw [covariance_comm w J S]
    rw [horth]
    ring
  · rw [quadraticResponse_finiteAreaChange_eq_neg_leakage w J S c hw]
    rw [hleak]
    ring

/-- Second-order leakage is a quadratic form in two source directions.  This is
the algebraic "null cone" used for second-order protected defect mixtures. -/
theorem horizonSecondOrderLeakage_linear_combination
    {ι : Type*} [Fintype ι]
    (w J A B : ι → ℝ) (a b : ℝ) :
    horizonSecondOrderLeakage w J (fun i => a * A i + b * B i) =
      a ^ 2 * horizonSecondOrderCrossLeakage w J A A +
        2 * a * b * horizonSecondOrderCrossLeakage w J A B +
          b ^ 2 * horizonSecondOrderCrossLeakage w J B B := by
  unfold horizonSecondOrderLeakage horizonSecondOrderCrossLeakage
  rw [centeredSource_linear_combination]
  have hsq :
      (fun i =>
          (a * centeredSource w A i + b * centeredSource w B i) ^ 2)
        =
        fun i =>
          a ^ 2 * (centeredSource w A i * centeredSource w A i) +
            ((2 * a * b) *
              (centeredSource w A i * centeredSource w B i) +
                b ^ 2 *
                  (centeredSource w B i * centeredSource w B i)) := by
    funext i
    ring
  rw [hsq]
  rw [covariance_add_right]
  rw [covariance_add_right]
  rw [covariance_const_mul_right, covariance_const_mul_right,
    covariance_const_mul_right]
  ring

/-- If two sources are first-order horizon-orthogonal, then any linear
combination is first-order horizon-orthogonal. -/
theorem covariance_linear_combination_left_zero
    {ι : Type*} [Fintype ι]
    (w J A B : ι → ℝ) (a b : ℝ)
    (hA : covariance w A J = 0)
    (hB : covariance w B J = 0) :
    covariance w (fun i => a * A i + b * B i) J = 0 := by
  rw [covariance_add_left]
  rw [covariance_const_mul_left, covariance_const_mul_left]
  rw [hA, hB]
  ring

/-- A two-channel defect mixture is protected through the finite second central
area response when it lies on the quadratic leakage null cone. -/
theorem twoChannel_firstAndSecondOrder_area_zero
    {ι : Type*} [Fintype ι]
    (w J A B : ι → ℝ) (c a b : ℝ)
    (hw : (∑ i, w i) = 1)
    (hA : covariance w A J = 0)
    (hB : covariance w B J = 0)
    (hcone :
      a ^ 2 * horizonSecondOrderCrossLeakage w J A A +
        2 * a * b * horizonSecondOrderCrossLeakage w J A B +
          b ^ 2 * horizonSecondOrderCrossLeakage w J B B = 0) :
    linearResponse w (fun i => a * A i + b * B i)
        (finiteAreaChange c J) = 0 ∧
      quadraticResponse w (fun i => a * A i + b * B i)
        (finiteAreaChange c J) = 0 := by
  refine orthogonal_source_firstAndSecondOrder_area_zero w J
    (fun i => a * A i + b * B i) c hw ?_ ?_
  · exact covariance_linear_combination_left_zero w J A B a b hA hB
  · rw [horizonSecondOrderLeakage_linear_combination]
    exact hcone

/-- Null-cone certificate bridge for two explicit defect channels: if the
mixture is first-order horizon-orthogonal, lies on the second-order leakage
null cone, and descends a named certificate-error observable, then horizon
protection and certificate descent hold simultaneously. -/
theorem twoChannel_protected_certificate_error_source_bridge
    {ι : Type*} [Fintype ι]
    (w J A B certificateError : ι → ℝ) (c a b descentRate : ℝ)
    (hw : (∑ i, w i) = 1)
    (hA : covariance w A J = 0)
    (hB : covariance w B J = 0)
    (hcone :
      a ^ 2 * horizonSecondOrderCrossLeakage w J A A +
        2 * a * b * horizonSecondOrderCrossLeakage w J A B +
          b ^ 2 * horizonSecondOrderCrossLeakage w J B B = 0)
    (hdesc :
      linearResponse w (fun i => a * A i + b * B i)
        certificateError ≤ -descentRate) :
    (linearResponse w (fun i => a * A i + b * B i)
        (finiteAreaChange c J) = 0 ∧
      quadraticResponse w (fun i => a * A i + b * B i)
        (finiteAreaChange c J) = 0) ∧
      linearResponse w (fun i => a * A i + b * B i)
        certificateError ≤ -descentRate := by
  constructor
  · exact twoChannel_firstAndSecondOrder_area_zero w J A B c a b hw hA hB
      hcone
  · exact hdesc

/-- If the two-channel descent rate is positive, the certificate-error response
is strictly negative. -/
theorem twoChannel_certificate_error_response_negative
    {ι : Type*} [Fintype ι]
    (w A B certificateError : ι → ℝ) (a b descentRate : ℝ)
    (hdesc :
      linearResponse w (fun i => a * A i + b * B i)
        certificateError ≤ -descentRate)
    (hpos : 0 < descentRate) :
    linearResponse w (fun i => a * A i + b * B i)
      certificateError < 0 := by
  exact lt_of_le_of_lt hdesc (by linarith)

/-- Projection coefficient of a defect observable `G` onto the horizon source
`J`, in the finite covariance geometry of the current parent state. -/
noncomputable def horizonProjectionCoeff {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ) : ℝ :=
  covariance w G J / variance w J

/-- The component of `G` covariance-orthogonal to the horizon source `J`. -/
noncomputable def horizonOrthogonalResidual {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ) : ι → ℝ :=
  fun i => G i - horizonProjectionCoeff w J G * J i

/-- The raw defect splits exactly into its horizon-parallel component plus the
horizon-orthogonal residual. -/
theorem rawDefect_eq_projection_plus_residual
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ) :
    (fun i => horizonProjectionCoeff w J G * J i +
      horizonOrthogonalResidual w J G i) = G := by
  funext i
  unfold horizonOrthogonalResidual
  ring

/-- The residual really is covariance-orthogonal to `J`, provided `J` has
nonzero variance. -/
theorem covariance_horizonOrthogonalResidual_self
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ)
    (hvar : variance w J ≠ 0) :
    covariance w (horizonOrthogonalResidual w J G) J = 0 := by
  unfold horizonOrthogonalResidual horizonProjectionCoeff
  rw [covariance_sub_left]
  rw [covariance_const_mul_left]
  unfold variance at hvar ⊢
  field_simp [hvar]
  ring_nf

/-- The displayed projection coefficient is the unique coefficient whose
residual is covariance-orthogonal to the horizon source. -/
theorem horizonProjectionCoeff_unique
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ)
    (hvar : variance w J ≠ 0)
    (a : ℝ)
    (horth : covariance w (fun i => G i - a * J i) J = 0) :
    a = horizonProjectionCoeff w J G := by
  have hcalc :
      covariance w (fun i => G i - a * J i) J =
        covariance w G J - a * variance w J := by
    rw [covariance_sub_left]
    rw [covariance_const_mul_left]
    unfold variance
    ring
  rw [hcalc] at horth
  have hmul : a * variance w J = covariance w G J := by
    linarith
  unfold horizonProjectionCoeff
  calc
    a = (a * variance w J) / variance w J := by
          field_simp [hvar]
    _ = covariance w G J / variance w J := by
          rw [hmul]

/-- Any source covariance-orthogonal to the horizon source has no first-order
horizon-area response. -/
theorem orthogonal_source_area_response_zero
    {ι : Type*} [Fintype ι]
    (w J S : ι → ℝ) (c : ℝ)
    (hw : (∑ i, w i) = 1)
    (horth : covariance w S J = 0) :
    linearResponse w S (finiteAreaChange c J) = 0 := by
  rw [linearResponse_eq_covariance]
  rw [covariance_finiteAreaChange_eq_neg_covariance w J S c hw]
  rw [covariance_comm w J S]
  rw [horth]
  ring

/-- A horizon-orthogonal residual source has no first-order horizon-area
response. -/
theorem horizonOrthogonalResidual_area_response_zero
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ) (c : ℝ)
    (hw : (∑ i, w i) = 1)
    (hvar : variance w J ≠ 0) :
    linearResponse w (horizonOrthogonalResidual w J G)
      (finiteAreaChange c J) = 0 := by
  exact orthogonal_source_area_response_zero w J
    (horizonOrthogonalResidual w J G) c hw
    (covariance_horizonOrthogonalResidual_self w J G hvar)

/-- The projected residual's second central area response is precisely its
second-order horizon leakage.  This is the next term that must be controlled
after the first-order projection theorem. -/
theorem horizonOrthogonalResidual_secondOrder_area_obstruction
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ) (c : ℝ)
    (hw : (∑ i, w i) = 1)
    (hvar : variance w J ≠ 0) :
    linearResponse w (horizonOrthogonalResidual w J G)
        (finiteAreaChange c J) = 0 ∧
      quadraticResponse w (horizonOrthogonalResidual w J G)
        (finiteAreaChange c J) =
          -horizonSecondOrderLeakage w J
            (horizonOrthogonalResidual w J G) := by
  exact orthogonal_source_secondOrder_area_obstruction w J
    (horizonOrthogonalResidual w J G) c hw
    (covariance_horizonOrthogonalResidual_self w J G hvar)

/-- If the projected residual also has zero second-order leakage, it preserves
horizon focusing through the finite second central response. -/
theorem horizonOrthogonalResidual_firstAndSecondOrder_area_zero
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ) (c : ℝ)
    (hw : (∑ i, w i) = 1)
    (hvar : variance w J ≠ 0)
    (hleak :
      horizonSecondOrderLeakage w J
        (horizonOrthogonalResidual w J G) = 0) :
    linearResponse w (horizonOrthogonalResidual w J G)
        (finiteAreaChange c J) = 0 ∧
      quadraticResponse w (horizonOrthogonalResidual w J G)
        (finiteAreaChange c J) = 0 := by
  exact orthogonal_source_firstAndSecondOrder_area_zero w J
    (horizonOrthogonalResidual w J G) c hw
    (covariance_horizonOrthogonalResidual_self w J G hvar) hleak

/-- A source made from a horizon part plus any horizon-orthogonal part has the
same first-order area response as the horizon component alone. -/
theorem combined_orthogonal_area_response
    {ι : Type*} [Fintype ι]
    (w J S : ι → ℝ) (c thetaJ thetaS : ℝ)
    (hw : (∑ i, w i) = 1)
    (horth : covariance w S J = 0) :
    linearResponse w
        (fun i => thetaJ * J i + thetaS * S i)
        (finiteAreaChange c J)
      = -thetaJ * variance w J := by
  rw [linearResponse_eq_covariance]
  rw [covariance_const_mul_add_right]
  rw [covariance_finiteAreaChange_eq_neg_covariance w J J c hw]
  have hzero := orthogonal_source_area_response_zero w J S c hw horth
  rw [linearResponse_eq_covariance] at hzero
  rw [hzero]
  unfold variance
  ring

/-- A combined source made from horizon focusing plus a horizon-orthogonal
defect residual has the same first-order area response as the horizon component
alone. -/
theorem combined_horizonOrthogonal_area_response
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ) (c thetaJ thetaG : ℝ)
    (hw : (∑ i, w i) = 1)
    (hvar : variance w J ≠ 0) :
    linearResponse w
        (fun i => thetaJ * J i +
          thetaG * horizonOrthogonalResidual w J G i)
        (finiteAreaChange c J)
      = -thetaJ * variance w J := by
  exact combined_orthogonal_area_response w J
    (horizonOrthogonalResidual w J G) c thetaJ thetaG hw
    (covariance_horizonOrthogonalResidual_self w J G hvar)

/-- Null-cone certificate bridge specialized to two raw defect observables
after projecting both off the horizon source.  This is the formal counterpart
of the residualized two-channel scans. -/
theorem twoResidualChannel_protected_certificate_error_source_bridge
    {ι : Type*} [Fintype ι]
    (w J GA GB certificateError : ι → ℝ) (c a b descentRate : ℝ)
    (hw : (∑ i, w i) = 1)
    (hvar : variance w J ≠ 0)
    (hcone :
      a ^ 2 *
          horizonSecondOrderCrossLeakage w J
            (horizonOrthogonalResidual w J GA)
            (horizonOrthogonalResidual w J GA) +
        2 * a * b *
          horizonSecondOrderCrossLeakage w J
            (horizonOrthogonalResidual w J GA)
            (horizonOrthogonalResidual w J GB) +
          b ^ 2 *
            horizonSecondOrderCrossLeakage w J
              (horizonOrthogonalResidual w J GB)
              (horizonOrthogonalResidual w J GB) = 0)
    (hdesc :
      linearResponse w
        (fun i =>
          a * horizonOrthogonalResidual w J GA i +
            b * horizonOrthogonalResidual w J GB i)
        certificateError ≤ -descentRate) :
    (linearResponse w
        (fun i =>
          a * horizonOrthogonalResidual w J GA i +
            b * horizonOrthogonalResidual w J GB i)
        (finiteAreaChange c J) = 0 ∧
      quadraticResponse w
        (fun i =>
          a * horizonOrthogonalResidual w J GA i +
            b * horizonOrthogonalResidual w J GB i)
        (finiteAreaChange c J) = 0) ∧
      linearResponse w
        (fun i =>
          a * horizonOrthogonalResidual w J GA i +
            b * horizonOrthogonalResidual w J GB i)
        certificateError ≤ -descentRate := by
  exact twoChannel_protected_certificate_error_source_bridge w J
    (horizonOrthogonalResidual w J GA)
    (horizonOrthogonalResidual w J GB) certificateError c a b descentRate hw
    (covariance_horizonOrthogonalResidual_self w J GA hvar)
    (covariance_horizonOrthogonalResidual_self w J GB hvar) hcone hdesc

/-! ## 4. Least-defect source package -/

/-- A single finite least-defect certificate at a parent state.

The raw defect `G` is allowed to be correlated with the horizon source.  The
field `horizonResidual` removes precisely the covariance component parallel to
`J`, leaving a repair direction that does not perturb horizon focusing at first
order. -/
structure HorizonOrthogonalDefectCertificate
    (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  horizonSource : ι → ℝ
  rawDefect : ι → ℝ
  newMaximalContribution : ℝ
  weight_sum : (∑ i, weight i) = 1
  horizon_variance_ne_zero : variance weight horizonSource ≠ 0

namespace HorizonOrthogonalDefectCertificate

noncomputable def horizonResidual {ι : Type*} [Fintype ι]
    (C : HorizonOrthogonalDefectCertificate ι) : ι → ℝ :=
  horizonOrthogonalResidual C.weight C.horizonSource C.rawDefect

noncomputable def leastDefectSource {ι : Type*} [Fintype ι]
    (C : HorizonOrthogonalDefectCertificate ι)
    (thetaH thetaD : ℝ) : ι → ℝ :=
  fun i => thetaH * C.horizonSource i + thetaD * C.horizonResidual i

/-- The certificate's residual repair source is exactly horizon-orthogonal. -/
theorem residual_orthogonal {ι : Type*} [Fintype ι]
    (C : HorizonOrthogonalDefectCertificate ι) :
    covariance C.weight C.horizonResidual C.horizonSource = 0 :=
  covariance_horizonOrthogonalResidual_self
    C.weight C.horizonSource C.rawDefect C.horizon_variance_ne_zero

/-- The certificate residual has zero first-order area response, and its
remaining finite second central response is exactly its second-order leakage. -/
theorem residual_secondOrder_area_obstruction
    {ι : Type*} [Fintype ι]
    (C : HorizonOrthogonalDefectCertificate ι) :
    linearResponse C.weight C.horizonResidual
        (finiteAreaChange C.newMaximalContribution C.horizonSource) = 0 ∧
      quadraticResponse C.weight C.horizonResidual
        (finiteAreaChange C.newMaximalContribution C.horizonSource) =
          -horizonSecondOrderLeakage C.weight C.horizonSource
            C.horizonResidual :=
  horizonOrthogonalResidual_secondOrder_area_obstruction
    C.weight C.horizonSource C.rawDefect C.newMaximalContribution
    C.weight_sum C.horizon_variance_ne_zero

/-- If the certificate residual's squared centered amplitude is also
horizon-balanced, then the residual is protected through the second central
response. -/
theorem residual_firstAndSecondOrder_area_zero
    {ι : Type*} [Fintype ι]
    (C : HorizonOrthogonalDefectCertificate ι)
    (hleak :
      horizonSecondOrderLeakage C.weight C.horizonSource
        C.horizonResidual = 0) :
    linearResponse C.weight C.horizonResidual
        (finiteAreaChange C.newMaximalContribution C.horizonSource) = 0 ∧
      quadraticResponse C.weight C.horizonResidual
        (finiteAreaChange C.newMaximalContribution C.horizonSource) = 0 :=
  horizonOrthogonalResidual_firstAndSecondOrder_area_zero
    C.weight C.horizonSource C.rawDefect C.newMaximalContribution
    C.weight_sum C.horizon_variance_ne_zero hleak

/-- Least-defect source theorem: the defect-repair coefficient `thetaD` does
not change the first-order horizon-focusing law. -/
theorem leastDefectSource_preserves_horizon_focusing
    {ι : Type*} [Fintype ι]
    (C : HorizonOrthogonalDefectCertificate ι)
    (thetaH thetaD : ℝ) :
    linearResponse C.weight (C.leastDefectSource thetaH thetaD)
        (finiteAreaChange C.newMaximalContribution C.horizonSource)
      = -thetaH * variance C.weight C.horizonSource := by
  exact combined_horizonOrthogonal_area_response
    C.weight C.horizonSource C.rawDefect C.newMaximalContribution
    thetaH thetaD C.weight_sum C.horizon_variance_ne_zero

/-- For the full least-defect source, the finite second central area response
is always the negative horizon leakage of that same source. -/
theorem leastDefectSource_secondOrder_area_obstruction
    {ι : Type*} [Fintype ι]
    (C : HorizonOrthogonalDefectCertificate ι)
    (thetaH thetaD : ℝ) :
    quadraticResponse C.weight (C.leastDefectSource thetaH thetaD)
        (finiteAreaChange C.newMaximalContribution C.horizonSource)
      =
        -horizonSecondOrderLeakage C.weight C.horizonSource
          (C.leastDefectSource thetaH thetaD) :=
  quadraticResponse_finiteAreaChange_eq_neg_leakage
    C.weight C.horizonSource (C.leastDefectSource thetaH thetaD)
    C.newMaximalContribution C.weight_sum

end HorizonOrthogonalDefectCertificate

/-! ## 5. Protected certificate-error source interface -/

/-- A finite source that simultaneously protects the horizon channel through
the second central response and descends a named certificate-error observable.

This is the formal interface suggested by the certificate-basis scans: a
physical defect source must be horizon-orthogonal, second-order
horizon-balanced, and negatively correlated with the certificate error that it
is meant to repair. -/
structure ProtectedCertificateErrorSource
    (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  horizonSource : ι → ℝ
  defectSource : ι → ℝ
  certificateError : ι → ℝ
  newMaximalContribution : ℝ
  descentRate : ℝ
  weight_sum : (∑ i, weight i) = 1
  source_horizon_orthogonal :
    covariance weight defectSource horizonSource = 0
  source_second_leakage_zero :
    horizonSecondOrderLeakage weight horizonSource defectSource = 0
  certificate_error_descent :
    linearResponse weight defectSource certificateError ≤ -descentRate

namespace ProtectedCertificateErrorSource

/-- The protected certificate source has no first-order horizon-area response. -/
theorem first_area_response_zero
    {ι : Type*} [Fintype ι]
    (C : ProtectedCertificateErrorSource ι) :
    linearResponse C.weight C.defectSource
        (finiteAreaChange C.newMaximalContribution C.horizonSource) = 0 := by
  exact orthogonal_source_area_response_zero C.weight C.horizonSource
    C.defectSource C.newMaximalContribution C.weight_sum
    C.source_horizon_orthogonal

/-- The protected certificate source has no finite second central horizon-area
response. -/
theorem second_area_response_zero
    {ι : Type*} [Fintype ι]
    (C : ProtectedCertificateErrorSource ι) :
    quadraticResponse C.weight C.defectSource
        (finiteAreaChange C.newMaximalContribution C.horizonSource) = 0 := by
  rw [quadraticResponse_finiteAreaChange_eq_neg_leakage C.weight
    C.horizonSource C.defectSource C.newMaximalContribution C.weight_sum]
  rw [C.source_second_leakage_zero]
  ring

/-- The protected certificate source preserves the horizon channel through the
finite second central response. -/
theorem preserves_horizon_through_secondOrder
    {ι : Type*} [Fintype ι]
    (C : ProtectedCertificateErrorSource ι) :
    linearResponse C.weight C.defectSource
        (finiteAreaChange C.newMaximalContribution C.horizonSource) = 0 ∧
      quadraticResponse C.weight C.defectSource
        (finiteAreaChange C.newMaximalContribution C.horizonSource) = 0 := by
  exact orthogonal_source_firstAndSecondOrder_area_zero C.weight
    C.horizonSource C.defectSource C.newMaximalContribution C.weight_sum
    C.source_horizon_orthogonal C.source_second_leakage_zero

/-- The same source descends the named certificate-error observable by the
recorded rate. -/
theorem descends_certificate_error
    {ι : Type*} [Fintype ι]
    (C : ProtectedCertificateErrorSource ι) :
    linearResponse C.weight C.defectSource C.certificateError ≤
      -C.descentRate :=
  C.certificate_error_descent

/-- If the descent rate is positive, the certificate-error response is strictly
negative. -/
theorem certificate_error_response_negative
    {ι : Type*} [Fintype ι]
    (C : ProtectedCertificateErrorSource ι)
    (hpos : 0 < C.descentRate) :
    linearResponse C.weight C.defectSource C.certificateError < 0 := by
  exact lt_of_le_of_lt C.certificate_error_descent (by linarith)

/-- Compact bridge statement: finite second-order horizon protection and
certificate-error descent hold at the same parent state. -/
theorem protected_certificate_error_source_bridge
    {ι : Type*} [Fintype ι]
    (C : ProtectedCertificateErrorSource ι) :
    (linearResponse C.weight C.defectSource
        (finiteAreaChange C.newMaximalContribution C.horizonSource) = 0 ∧
      quadraticResponse C.weight C.defectSource
        (finiteAreaChange C.newMaximalContribution C.horizonSource) = 0) ∧
      linearResponse C.weight C.defectSource C.certificateError ≤
        -C.descentRate := by
  constructor
  · exact C.preserves_horizon_through_secondOrder
  · exact C.descends_certificate_error

end ProtectedCertificateErrorSource

/-! ## 6. Refinement-limit certificate interface -/

/-- A refinement sequence of finite protected certificate-error sources on a
fixed finite birth-option type.  First-order horizon contamination is zero at
every stage, while second-order leakage only has to vanish in the refinement
limit. -/
structure ProtectedCertificateErrorRefinement
    (ι : Type*) [Fintype ι] where
  weight : ℕ → ι → ℝ
  horizonSource : ℕ → ι → ℝ
  defectSource : ℕ → ι → ℝ
  certificateError : ℕ → ι → ℝ
  newMaximalContribution : ℕ → ℝ
  descentRate : ℝ
  weight_sum : ∀ n, (∑ i, weight n i) = 1
  source_horizon_orthogonal :
    ∀ n, covariance (weight n) (defectSource n) (horizonSource n) = 0
  leakage_tendsto_zero :
    Tendsto
      (fun n =>
        horizonSecondOrderLeakage (weight n) (horizonSource n)
          (defectSource n))
      atTop (nhds 0)
  certificate_error_descent :
    ∀ n,
      linearResponse (weight n) (defectSource n) (certificateError n) ≤
        -descentRate

namespace ProtectedCertificateErrorRefinement

/-- First-order horizon-area response vanishes at each finite refinement
stage. -/
theorem first_area_response_zero
    {ι : Type*} [Fintype ι]
    (R : ProtectedCertificateErrorRefinement ι) (n : ℕ) :
    linearResponse (R.weight n) (R.defectSource n)
        (finiteAreaChange (R.newMaximalContribution n)
          (R.horizonSource n)) = 0 := by
  exact orthogonal_source_area_response_zero (R.weight n) (R.horizonSource n)
    (R.defectSource n) (R.newMaximalContribution n) (R.weight_sum n)
    (R.source_horizon_orthogonal n)

/-- If leakage vanishes along refinement, then the finite second central
horizon-area response also vanishes along refinement. -/
theorem quadratic_area_response_tendsto_zero
    {ι : Type*} [Fintype ι]
    (R : ProtectedCertificateErrorRefinement ι) :
    Tendsto
      (fun n =>
        quadraticResponse (R.weight n) (R.defectSource n)
          (finiteAreaChange (R.newMaximalContribution n)
            (R.horizonSource n)))
      atTop (nhds 0) := by
  have hquad :
      (fun n =>
        quadraticResponse (R.weight n) (R.defectSource n)
          (finiteAreaChange (R.newMaximalContribution n)
            (R.horizonSource n))) =
        fun n =>
          -horizonSecondOrderLeakage (R.weight n) (R.horizonSource n)
            (R.defectSource n) := by
    funext n
    exact quadraticResponse_finiteAreaChange_eq_neg_leakage (R.weight n)
      (R.horizonSource n) (R.defectSource n)
      (R.newMaximalContribution n) (R.weight_sum n)
  rw [hquad]
  simpa using R.leakage_tendsto_zero.neg

/-- The certificate-error observable descends at every finite refinement
stage. -/
theorem descends_certificate_error
    {ι : Type*} [Fintype ι]
    (R : ProtectedCertificateErrorRefinement ι) (n : ℕ) :
    linearResponse (R.weight n) (R.defectSource n)
        (R.certificateError n) ≤ -R.descentRate :=
  R.certificate_error_descent n

/-- A positive uniform descent rate gives a strictly negative certificate-error
response at every refinement stage. -/
theorem certificate_error_response_negative
    {ι : Type*} [Fintype ι]
    (R : ProtectedCertificateErrorRefinement ι)
    (hpos : 0 < R.descentRate) (n : ℕ) :
    linearResponse (R.weight n) (R.defectSource n)
        (R.certificateError n) < 0 := by
  exact lt_of_le_of_lt (R.certificate_error_descent n) (by linarith)

end ProtectedCertificateErrorRefinement

#print axioms covariance_comm
#print axioms centeredSource_linear_combination
#print axioms covariance_add_right
#print axioms covariance_const_mul_right
#print axioms rawDefect_eq_projection_plus_residual
#print axioms covariance_horizonOrthogonalResidual_self
#print axioms horizonProjectionCoeff_unique
#print axioms orthogonal_source_area_response_zero
#print axioms quadraticResponse_finiteAreaChange_eq_neg_leakage
#print axioms orthogonal_source_secondOrder_area_obstruction
#print axioms orthogonal_source_firstAndSecondOrder_area_zero
#print axioms horizonSecondOrderLeakage_linear_combination
#print axioms covariance_linear_combination_left_zero
#print axioms twoChannel_firstAndSecondOrder_area_zero
#print axioms twoChannel_protected_certificate_error_source_bridge
#print axioms twoChannel_certificate_error_response_negative
#print axioms horizonOrthogonalResidual_area_response_zero
#print axioms horizonOrthogonalResidual_secondOrder_area_obstruction
#print axioms horizonOrthogonalResidual_firstAndSecondOrder_area_zero
#print axioms combined_orthogonal_area_response
#print axioms combined_horizonOrthogonal_area_response
#print axioms twoResidualChannel_protected_certificate_error_source_bridge
#print axioms HorizonOrthogonalDefectCertificate.residual_orthogonal
#print axioms HorizonOrthogonalDefectCertificate.residual_secondOrder_area_obstruction
#print axioms HorizonOrthogonalDefectCertificate.residual_firstAndSecondOrder_area_zero
#print axioms HorizonOrthogonalDefectCertificate.leastDefectSource_preserves_horizon_focusing
#print axioms HorizonOrthogonalDefectCertificate.leastDefectSource_secondOrder_area_obstruction
#print axioms ProtectedCertificateErrorSource.preserves_horizon_through_secondOrder
#print axioms ProtectedCertificateErrorSource.certificate_error_response_negative
#print axioms ProtectedCertificateErrorSource.protected_certificate_error_source_bridge
#print axioms ProtectedCertificateErrorRefinement.first_area_response_zero
#print axioms ProtectedCertificateErrorRefinement.quadratic_area_response_tendsto_zero
#print axioms ProtectedCertificateErrorRefinement.certificate_error_response_negative

end UnifiedTheory.Audit.KFCausalCSpecHorizonOrthogonalDefect
