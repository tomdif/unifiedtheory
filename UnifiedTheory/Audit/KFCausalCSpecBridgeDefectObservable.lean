/-
  Audit/KFCausalCSpecBridgeDefectObservable.lean

  CSpec bridge-census defect as a horizon-orthogonal repair target.

  The private-marker bridge poset makes edge transport recoverable from the
  global causal order: the shifted bridge census is not an imported label.  This
  file turns the resulting census mismatch into a finite real observable, then
  proves the horizon-orthogonal descent and protected-correction bridge for that
  observable.

  Scope: finite order/conformal control.  This defines a concrete defect target
  for the protected-source interface; it does not derive continuum dynamics.

  Citation context: Philipp Dorau and Albert Much, "From Quantum Relative
  Entropy to the Semiclassical Einstein Equations," arXiv:2510.24491v3
  [hep-th], Phys. Rev. Lett. 136, 091602 (2026).

  Zero sorry. Zero custom axioms.
-/

import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecCensusRecovery

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecBridgePoset
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecOverlapScore
open UnifiedTheory.Audit.KFCausalCSpecCensusRecovery
open UnifiedTheory.Audit.KFCausalCSpecGlobalization

/-! ## 1. Minimal finite covariance control layer -/

noncomputable def expectation {ι : Type*} [Fintype ι]
    (w X : ι → ℝ) : ℝ :=
  ∑ i, w i * X i

noncomputable def covariance {ι : Type*} [Fintype ι]
    (w X Y : ι → ℝ) : ℝ :=
  expectation w (fun i => X i * Y i) - expectation w X * expectation w Y

noncomputable def variance {ι : Type*} [Fintype ι]
    (w X : ι → ℝ) : ℝ :=
  covariance w X X

noncomputable def centeredSource {ι : Type*} [Fintype ι]
    (w S : ι → ℝ) : ι → ℝ :=
  fun i => S i - expectation w S

noncomputable def linearResponse {ι : Type*} [Fintype ι]
    (w S X : ι → ℝ) : ℝ :=
  expectation w (fun i => X i * centeredSource w S i)

noncomputable def quadraticResponse {ι : Type*} [Fintype ι]
    (w S X : ι → ℝ) : ℝ :=
  covariance w X (fun i => centeredSource w S i ^ 2)

def finiteAreaChange {ι : Type*} (c : ℝ) (J : ι → ℝ) : ι → ℝ :=
  fun i => c - J i

noncomputable def horizonSecondOrderCrossLeakage {ι : Type*} [Fintype ι]
    (w J A B : ι → ℝ) : ℝ :=
  covariance w J (fun i => centeredSource w A i * centeredSource w B i)

noncomputable def horizonSecondOrderLeakageQuadratic
    {ι : Type*} [Fintype ι]
    (w J A B : ι → ℝ) (a b : ℝ) : ℝ :=
  a ^ 2 * horizonSecondOrderCrossLeakage w J A A +
    2 * a * b * horizonSecondOrderCrossLeakage w J A B +
      b ^ 2 * horizonSecondOrderCrossLeakage w J B B

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

theorem covariance_const_mul_right {ι : Type*} [Fintype ι]
    (w X Y : ι → ℝ) (a : ℝ) :
    covariance w X (fun i => a * Y i) =
      a * covariance w X Y := by
  rw [covariance_comm w X (fun i => a * Y i)]
  rw [covariance_const_mul_left]
  rw [covariance_comm w Y X]

theorem covariance_add_right {ι : Type*} [Fintype ι]
    (w X Y Z : ι → ℝ) :
    covariance w X (fun i => Y i + Z i) =
      covariance w X Y + covariance w X Z := by
  rw [covariance_comm w X (fun i => Y i + Z i)]
  rw [covariance_add_left]
  rw [covariance_comm w Y X, covariance_comm w Z X]

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

theorem quadraticResponse_finiteAreaChange_eq_neg_leakageQuadratic
    {ι : Type*} [Fintype ι]
    (w J A B : ι → ℝ) (c a b : ℝ)
    (hw : (∑ i, w i) = 1) :
    quadraticResponse w (fun i => a * A i + b * B i)
        (finiteAreaChange c J) =
      -horizonSecondOrderLeakageQuadratic w J A B a b := by
  unfold quadraticResponse horizonSecondOrderLeakageQuadratic
    horizonSecondOrderCrossLeakage
  rw [covariance_finiteAreaChange_eq_neg_covariance w J
    (fun i => centeredSource w (fun j => a * A j + b * B j) i ^ 2) c hw]
  have hcenter :
      centeredSource w (fun i => a * A i + b * B i) =
        fun i => a * centeredSource w A i + b * centeredSource w B i := by
    funext i
    unfold centeredSource
    rw [expectation_add]
    rw [expectation_const_mul, expectation_const_mul]
    ring
  rw [hcenter]
  have hsq :
      (fun i => (a * centeredSource w A i + b * centeredSource w B i) ^ 2) =
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

noncomputable def horizonProjectionCoeff {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ) : ℝ :=
  covariance w G J / variance w J

noncomputable def horizonOrthogonalResidual {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ) : ι → ℝ :=
  fun i => G i - horizonProjectionCoeff w J G * J i

theorem rawDefect_eq_projection_plus_residual
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ) :
    (fun i => horizonProjectionCoeff w J G * J i +
      horizonOrthogonalResidual w J G i) = G := by
  funext i
  unfold horizonOrthogonalResidual
  ring

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

noncomputable def canonicalHorizonInvisibleDescentSource
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ) : ι → ℝ :=
  fun i => -horizonOrthogonalResidual w J G i

noncomputable def correctedCanonicalHorizonInvisibleDescentSource
    {ι : Type*} [Fintype ι]
    (w J G H : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i => -horizonOrthogonalResidual w J G i +
    t * horizonOrthogonalResidual w J H i

theorem covariance_neg_left
    {ι : Type*} [Fintype ι]
    (w S X : ι → ℝ) :
    covariance w (fun i => -S i) X = -covariance w S X := by
  have hfun : (fun i => -S i) = fun i => (-1 : ℝ) * S i := by
    funext i
    ring
  rw [hfun, covariance_const_mul_left]
  ring

theorem linearResponse_neg_source
    {ι : Type*} [Fintype ι]
    (w S X : ι → ℝ) :
    linearResponse w (fun i => -S i) X =
      -linearResponse w S X := by
  rw [linearResponse_eq_covariance, linearResponse_eq_covariance]
  have hneg : (fun i => -S i) = fun i => (-1 : ℝ) * S i := by
    funext i
    ring
  rw [hneg, covariance_const_mul_right]
  ring

theorem horizonOrthogonalResidual_linearResponse_rawDefect
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ)
    (hvar : variance w J ≠ 0) :
    linearResponse w (horizonOrthogonalResidual w J G) G =
      variance w (horizonOrthogonalResidual w J G) := by
  let R : ι → ℝ := horizonOrthogonalResidual w J G
  have horth : covariance w R J = 0 := by
    simpa [R] using covariance_horizonOrthogonalResidual_self w J G hvar
  have hsplit :
      G = fun i => horizonProjectionCoeff w J G * J i + R i := by
    symm
    simpa [R] using rawDefect_eq_projection_plus_residual w J G
  rw [linearResponse_eq_covariance]
  change covariance w G R = variance w R
  rw [hsplit]
  calc
    covariance w (fun i => horizonProjectionCoeff w J G * J i + R i) R
        =
          horizonProjectionCoeff w J G * covariance w J R +
            covariance w R R := by
          rw [covariance_add_left]
          rw [covariance_const_mul_left]
    _ = variance w R := by
          have horth' : covariance w J R = 0 := by
            rw [covariance_comm]
            exact horth
          rw [horth']
          unfold variance
          ring

theorem canonicalHorizonInvisibleDescentSource_response_rawDefect
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ)
    (hvar : variance w J ≠ 0) :
    linearResponse w (canonicalHorizonInvisibleDescentSource w J G) G =
      -variance w (horizonOrthogonalResidual w J G) := by
  unfold canonicalHorizonInvisibleDescentSource
  rw [linearResponse_neg_source]
  rw [horizonOrthogonalResidual_linearResponse_rawDefect w J G hvar]

theorem canonicalHorizonInvisibleDescentSource_area_response_zero
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ) (c : ℝ)
    (hw : (∑ i, w i) = 1)
    (hvar : variance w J ≠ 0) :
    linearResponse w (canonicalHorizonInvisibleDescentSource w J G)
        (finiteAreaChange c J) = 0 := by
  rw [linearResponse_eq_covariance]
  unfold canonicalHorizonInvisibleDescentSource
  have hneg :
      (fun i => -horizonOrthogonalResidual w J G i) =
        fun i => (-1 : ℝ) * horizonOrthogonalResidual w J G i := by
    funext i
    ring
  rw [hneg, covariance_const_mul_right]
  rw [covariance_finiteAreaChange_eq_neg_covariance w J
    (horizonOrthogonalResidual w J G) c hw]
  rw [covariance_comm w J (horizonOrthogonalResidual w J G)]
  rw [covariance_horizonOrthogonalResidual_self w J G hvar]
  ring

theorem correctedCanonicalHorizonInvisibleDescentSource_protected_bridge
    {ι : Type*} [Fintype ι]
    (w J G H : ι → ℝ) (c t descentRate : ℝ)
    (hw : (∑ i, w i) = 1)
    (hvar : variance w J ≠ 0)
    (hcone :
      horizonSecondOrderLeakageQuadratic w J
        (horizonOrthogonalResidual w J G)
        (horizonOrthogonalResidual w J H) (-1) t = 0)
    (hmargin :
      t * linearResponse w (horizonOrthogonalResidual w J H) G ≤
        variance w (horizonOrthogonalResidual w J G) - descentRate) :
    (linearResponse w
        (correctedCanonicalHorizonInvisibleDescentSource w J G H t)
        (finiteAreaChange c J) = 0 ∧
      quadraticResponse w
        (correctedCanonicalHorizonInvisibleDescentSource w J G H t)
        (finiteAreaChange c J) = 0) ∧
      linearResponse w
        (correctedCanonicalHorizonInvisibleDescentSource w J G H t)
        G ≤ -descentRate := by
  let A : ι → ℝ := horizonOrthogonalResidual w J G
  let B : ι → ℝ := horizonOrthogonalResidual w J H
  have hsource :
      correctedCanonicalHorizonInvisibleDescentSource w J G H t =
        fun i => (-1 : ℝ) * A i + t * B i := by
    funext i
    unfold correctedCanonicalHorizonInvisibleDescentSource A B
    ring
  have hA : covariance w A J = 0 := by
    simpa [A] using covariance_horizonOrthogonalResidual_self w J G hvar
  have hB : covariance w B J = 0 := by
    simpa [B] using covariance_horizonOrthogonalResidual_self w J H hvar
  have harea :
      linearResponse w (fun i => (-1 : ℝ) * A i + t * B i)
          (finiteAreaChange c J) = 0 := by
    rw [linearResponse_eq_covariance]
    rw [covariance_finiteAreaChange_eq_neg_covariance w J
      (fun i => (-1 : ℝ) * A i + t * B i) c hw]
    rw [covariance_add_right]
    rw [covariance_const_mul_right, covariance_const_mul_right]
    rw [covariance_comm w J A, covariance_comm w J B]
    rw [hA, hB]
    ring
  have hquad :
      quadraticResponse w (fun i => (-1 : ℝ) * A i + t * B i)
          (finiteAreaChange c J) = 0 := by
    rw [quadraticResponse_finiteAreaChange_eq_neg_leakageQuadratic
      w J A B c (-1) t hw]
    simpa [A, B] using hcone
  have hdesc :
      linearResponse w (fun i => (-1 : ℝ) * A i + t * B i) G ≤
        -descentRate := by
    have hresp :
        linearResponse w (fun i => (-1 : ℝ) * A i + t * B i) G =
          -variance w A + t * linearResponse w B G := by
      rw [linearResponse_eq_covariance, linearResponse_eq_covariance]
      rw [covariance_add_right]
      rw [covariance_const_mul_right, covariance_const_mul_right]
      have hvarA :
          covariance w G A = variance w A := by
        have hlin := horizonOrthogonalResidual_linearResponse_rawDefect w J G hvar
        rw [linearResponse_eq_covariance] at hlin
        simpa [A] using hlin
      rw [hvarA]
      ring
    rw [hresp]
    have hmargin' :
        t * linearResponse w B G ≤ variance w A - descentRate := by
      simpa [A, B] using hmargin
    linarith
  rw [hsource]
  exact ⟨⟨harea, hquad⟩, hdesc⟩

/-! ## 2. Bridge-census defect -/

noncomputable def bridgeCensusDefect
    (e : E4) (τ : Equiv.Perm Direction) : ℝ :=
  18 - permScore bprof (fun b => bprof ((fourState.perm e)⁻¹ b)) τ

theorem fourState_src_ne_dst (e : E4) :
    fourState.src e ≠ fourState.dst e := by
  cases e <;> decide

theorem bridgeCensusDefect_canonical_zero (e : E4) :
    bridgeCensusDefect e (fourState.perm e) = 0 := by
  unfold bridgeCensusDefect
  rw [permScore_shift bprof (fourState.perm e) (fourState.perm e)]
  rw [inv_mul_cancel]
  rw [gram_permScore_one bprof bgram]
  ring

theorem bridgeCensusDefect_pos_of_ne
    (e : E4) (τ : Equiv.Perm Direction)
    (hτ : τ ≠ fourState.perm e) :
    0 < bridgeCensusDefect e τ := by
  unfold bridgeCensusDefect
  have hcanon := census_recovers_global_transport e τ hτ
  have hbest :
      permScore bprof (fun b => bprof ((fourState.perm e)⁻¹ b))
          (fourState.perm e) = 18 := by
    rw [permScore_shift bprof (fourState.perm e) (fourState.perm e)]
    rw [inv_mul_cancel]
    rw [gram_permScore_one bprof bgram]
  linarith

theorem bridgeCensusDefect_nonneg
    (e : E4) (τ : Equiv.Perm Direction) :
    0 ≤ bridgeCensusDefect e τ := by
  by_cases hτ : τ = fourState.perm e
  · rw [hτ, bridgeCensusDefect_canonical_zero]
  · exact le_of_lt (bridgeCensusDefect_pos_of_ne e τ hτ)

theorem bridgeCensusDefect_eq_zero_iff
    (e : E4) (τ : Equiv.Perm Direction) :
    bridgeCensusDefect e τ = 0 ↔ τ = fourState.perm e := by
  constructor
  · intro hzero
    by_contra hτ
    have hpos := bridgeCensusDefect_pos_of_ne e τ hτ
    linarith
  · intro hτ
    rw [hτ]
    exact bridgeCensusDefect_canonical_zero e

theorem bridgeCensusDefect_canonical_min
    (e : E4) (τ : Equiv.Perm Direction) :
    bridgeCensusDefect e (fourState.perm e) ≤ bridgeCensusDefect e τ := by
  rw [bridgeCensusDefect_canonical_zero]
  exact bridgeCensusDefect_nonneg e τ

theorem bridgeCensusDefect_zero_and_orderRecovered (e : E4) :
    bridgeCensusDefect e (fourState.perm e) = 0 ∧
      ∀ a b : Fin 3,
        Cov fourState (GPoint.atom (fourState.dst e) b)
            (GPoint.bridge e a) →
          b = fourState.perm e a := by
  constructor
  · exact bridgeCensusDefect_canonical_zero e
  · intro a b h
    exact bridge_incidence_recovers_transport fourState e a b h
      (fourState_src_ne_dst e)

/-! ## 3. Finite candidate-population observable -/

noncomputable def cSpecBridgeDefectObservable
    {ι : Type*} (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) :
    ι → ℝ :=
  fun i => bridgeCensusDefect (edge i) (candidate i)

noncomputable def canonicalCSpecBridgeCandidate
    {ι : Type*} (edge : ι → E4) : ι → Equiv.Perm Direction :=
  fun i => fourState.perm (edge i)

noncomputable def cSpecBridgePairConsistencyObservable
    {ι : Type*} (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) :
    ι → ℝ :=
  fun i => 2 * cSpecBridgeDefectObservable edge candidate i

noncomputable def cSpecBridgeHauptvermutungDistortion
    {ι : Type*} (_scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) : ι → ℝ :=
  fun i => cSpecBridgePairConsistencyObservable edge candidate i / 2

theorem cSpecBridgeHauptvermutungDistortion_eq_defect
    {ι : Type*} (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) :
    cSpecBridgeHauptvermutungDistortion scale edge candidate =
      cSpecBridgeDefectObservable edge candidate := by
  funext i
  unfold cSpecBridgeHauptvermutungDistortion
    cSpecBridgePairConsistencyObservable
  ring

theorem cSpecBridgeHauptvermutungDistortion_apply
    {ι : Type*} (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) (i : ι) :
    cSpecBridgeHauptvermutungDistortion scale edge candidate i =
      bridgeCensusDefect (edge i) (candidate i) := by
  have h :=
    congrFun (cSpecBridgeHauptvermutungDistortion_eq_defect scale edge candidate) i
  simpa [cSpecBridgeDefectObservable] using h

theorem cSpecBridgeHauptvermutungDistortion_nonneg
    {ι : Type*} (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) (i : ι) :
    0 ≤ cSpecBridgeHauptvermutungDistortion scale edge candidate i := by
  rw [cSpecBridgeHauptvermutungDistortion_apply]
  exact bridgeCensusDefect_nonneg (edge i) (candidate i)

theorem cSpecBridgeHauptvermutungDistortion_zero_iff
    {ι : Type*} (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) (i : ι) :
    cSpecBridgeHauptvermutungDistortion scale edge candidate i = 0 ↔
      candidate i = fourState.perm (edge i) := by
  rw [cSpecBridgeHauptvermutungDistortion_apply]
  exact bridgeCensusDefect_eq_zero_iff (edge i) (candidate i)

theorem cSpecBridgeHauptvermutungDistortion_pos_iff
    {ι : Type*} (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) (i : ι) :
    0 < cSpecBridgeHauptvermutungDistortion scale edge candidate i ↔
      candidate i ≠ fourState.perm (edge i) := by
  constructor
  · intro hpos hcandidate
    have hzero :
        cSpecBridgeHauptvermutungDistortion scale edge candidate i = 0 :=
      (cSpecBridgeHauptvermutungDistortion_zero_iff scale edge candidate i).2
        hcandidate
    rw [hzero] at hpos
    linarith
  · intro hcandidate
    by_contra hnot
    have hle :
        cSpecBridgeHauptvermutungDistortion scale edge candidate i ≤ 0 :=
      le_of_not_gt hnot
    have hnonneg :=
      cSpecBridgeHauptvermutungDistortion_nonneg scale edge candidate i
    have hzero :
        cSpecBridgeHauptvermutungDistortion scale edge candidate i = 0 :=
      le_antisymm hle hnonneg
    exact hcandidate
      ((cSpecBridgeHauptvermutungDistortion_zero_iff scale edge candidate i).1
        hzero)

noncomputable def cSpecBridgeTotalDistortion
    {ι : Type*} [Fintype ι] (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) : ℝ :=
  ∑ i, cSpecBridgeHauptvermutungDistortion scale edge candidate i

theorem cSpecBridgeTotalDistortion_nonneg
    {ι : Type*} [Fintype ι] (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) :
    0 ≤ cSpecBridgeTotalDistortion scale edge candidate := by
  unfold cSpecBridgeTotalDistortion
  exact Finset.sum_nonneg
    (fun i _ => cSpecBridgeHauptvermutungDistortion_nonneg scale edge candidate i)

theorem cSpecBridgeTotalDistortion_eq_zero_iff
    {ι : Type*} [Fintype ι] (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) :
    cSpecBridgeTotalDistortion scale edge candidate = 0 ↔
      ∀ i, candidate i = fourState.perm (edge i) := by
  unfold cSpecBridgeTotalDistortion
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => cSpecBridgeHauptvermutungDistortion_nonneg scale edge candidate i)]
  simp [cSpecBridgeHauptvermutungDistortion_zero_iff]

theorem cSpecBridgeTotalDistortion_eq_zero_iff_candidate_eq_canonical
    {ι : Type*} [Fintype ι] (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) :
    cSpecBridgeTotalDistortion scale edge candidate = 0 ↔
      candidate = canonicalCSpecBridgeCandidate edge := by
  constructor
  · intro hzero
    funext i
    exact (cSpecBridgeTotalDistortion_eq_zero_iff scale edge candidate).1
      hzero i
  · intro hcandidate
    rw [hcandidate]
    rw [cSpecBridgeTotalDistortion_eq_zero_iff]
    intro i
    rfl

theorem cSpecBridgeTotalDistortion_canonical_zero
    {ι : Type*} [Fintype ι] (scale : ℝ) (edge : ι → E4) :
    cSpecBridgeTotalDistortion scale edge
      (canonicalCSpecBridgeCandidate edge) = 0 := by
  rw [cSpecBridgeTotalDistortion_eq_zero_iff]
  intro i
  rfl

theorem cSpecBridgeTotalDistortion_canonical_min
    {ι : Type*} [Fintype ι] (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) :
    cSpecBridgeTotalDistortion scale edge
      (canonicalCSpecBridgeCandidate edge) ≤
        cSpecBridgeTotalDistortion scale edge candidate := by
  rw [cSpecBridgeTotalDistortion_canonical_zero]
  exact cSpecBridgeTotalDistortion_nonneg scale edge candidate

theorem cSpecBridgeCandidate_ne_canonical_iff_exists_wrong
    {ι : Type*} (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction) :
    candidate ≠ canonicalCSpecBridgeCandidate edge ↔
      ∃ i, candidate i ≠ fourState.perm (edge i) := by
  constructor
  · intro hcandidate
    by_contra hnone
    apply hcandidate
    funext i
    by_contra hwrong
    exact hnone ⟨i, hwrong⟩
  · intro hwrong hcandidate
    rcases hwrong with ⟨i, hi⟩
    exact hi (congrFun hcandidate i)

theorem cSpecBridgeTotalDistortion_pos_of_exists_wrong
    {ι : Type*} [Fintype ι] (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction)
    (hwrong : ∃ i, candidate i ≠ fourState.perm (edge i)) :
    0 < cSpecBridgeTotalDistortion scale edge candidate := by
  by_contra hnot
  have hle :
      cSpecBridgeTotalDistortion scale edge candidate ≤ 0 :=
    le_of_not_gt hnot
  have hnonneg := cSpecBridgeTotalDistortion_nonneg scale edge candidate
  have hzero : cSpecBridgeTotalDistortion scale edge candidate = 0 :=
    le_antisymm hle hnonneg
  rcases hwrong with ⟨i, hi⟩
  exact hi ((cSpecBridgeTotalDistortion_eq_zero_iff scale edge candidate).1
    hzero i)

theorem cSpecBridgeTotalDistortion_pos_iff_candidate_ne_canonical
    {ι : Type*} [Fintype ι] (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction) :
    0 < cSpecBridgeTotalDistortion scale edge candidate ↔
      candidate ≠ canonicalCSpecBridgeCandidate edge := by
  constructor
  · intro hpos hcandidate
    rw [hcandidate, cSpecBridgeTotalDistortion_canonical_zero] at hpos
    linarith
  · intro hcandidate
    exact cSpecBridgeTotalDistortion_pos_of_exists_wrong scale edge candidate
      ((cSpecBridgeCandidate_ne_canonical_iff_exists_wrong edge candidate).1
        hcandidate)

theorem cSpecBridgeTotalDistortion_strict_min_of_ne
    {ι : Type*} [Fintype ι] (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction)
    (hcandidate : candidate ≠ canonicalCSpecBridgeCandidate edge) :
    cSpecBridgeTotalDistortion scale edge
      (canonicalCSpecBridgeCandidate edge) <
        cSpecBridgeTotalDistortion scale edge candidate := by
  rw [cSpecBridgeTotalDistortion_canonical_zero]
  exact (cSpecBridgeTotalDistortion_pos_iff_candidate_ne_canonical
    scale edge candidate).2 hcandidate

theorem cSpecBridgeTotalDistortion_zero_orderRecovered
    {ι : Type*} [Fintype ι] (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction)
    (hzero : cSpecBridgeTotalDistortion scale edge candidate = 0) :
    ∀ i a b,
      Cov fourState (GPoint.atom (fourState.dst (edge i)) b)
          (GPoint.bridge (edge i) a) →
        b = candidate i a := by
  have hcandidate :
      ∀ i, candidate i = fourState.perm (edge i) :=
    (cSpecBridgeTotalDistortion_eq_zero_iff scale edge candidate).1 hzero
  intro i a b h
  rw [hcandidate i]
  exact bridge_incidence_recovers_transport fourState (edge i) a b h
    (fourState_src_ne_dst (edge i))

/-! ## 4. Horizon-orthogonal descent specialization -/

theorem cSpecBridge_canonicalSource_descends_distortion
    {ι : Type*} [Fintype ι]
    (w J : ι → ℝ) (scale : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction)
    (hvar : variance w J ≠ 0) :
    linearResponse w
        (canonicalHorizonInvisibleDescentSource w J
          (cSpecBridgeHauptvermutungDistortion scale edge candidate))
        (cSpecBridgeHauptvermutungDistortion scale edge candidate) =
      -variance w
        (horizonOrthogonalResidual w J
          (cSpecBridgeHauptvermutungDistortion scale edge candidate)) := by
  exact canonicalHorizonInvisibleDescentSource_response_rawDefect
    w J (cSpecBridgeHauptvermutungDistortion scale edge candidate) hvar

theorem cSpecBridge_canonicalSource_area_response_zero
    {ι : Type*} [Fintype ι]
    (w J : ι → ℝ) (scale c : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction)
    (hw : (∑ i, w i) = 1)
    (hvar : variance w J ≠ 0) :
    linearResponse w
        (canonicalHorizonInvisibleDescentSource w J
          (cSpecBridgeHauptvermutungDistortion scale edge candidate))
        (finiteAreaChange c J) = 0 := by
  exact canonicalHorizonInvisibleDescentSource_area_response_zero
    w J (cSpecBridgeHauptvermutungDistortion scale edge candidate) c hw hvar

theorem cSpecBridge_correctedSource_protected_bridge
    {ι : Type*} [Fintype ι]
    (w J H : ι → ℝ) (scale c t descentRate : ℝ)
    (edge : ι → E4) (candidate : ι → Equiv.Perm Direction)
    (hw : (∑ i, w i) = 1)
    (hvar : variance w J ≠ 0)
    (hcone :
      horizonSecondOrderLeakageQuadratic w J
        (horizonOrthogonalResidual w J
          (cSpecBridgeHauptvermutungDistortion scale edge candidate))
        (horizonOrthogonalResidual w J H) (-1) t = 0)
    (hmargin :
      t * linearResponse w (horizonOrthogonalResidual w J H)
          (cSpecBridgeHauptvermutungDistortion scale edge candidate) ≤
        variance w
          (horizonOrthogonalResidual w J
            (cSpecBridgeHauptvermutungDistortion scale edge candidate)) -
          descentRate) :
    (linearResponse w
        (correctedCanonicalHorizonInvisibleDescentSource w J
          (cSpecBridgeHauptvermutungDistortion scale edge candidate) H t)
        (finiteAreaChange c J) = 0 ∧
      quadraticResponse w
        (correctedCanonicalHorizonInvisibleDescentSource w J
          (cSpecBridgeHauptvermutungDistortion scale edge candidate) H t)
        (finiteAreaChange c J) = 0) ∧
      linearResponse w
        (correctedCanonicalHorizonInvisibleDescentSource w J
          (cSpecBridgeHauptvermutungDistortion scale edge candidate) H t)
        (cSpecBridgeHauptvermutungDistortion scale edge candidate) ≤
          -descentRate := by
  exact correctedCanonicalHorizonInvisibleDescentSource_protected_bridge
    w J (cSpecBridgeHauptvermutungDistortion scale edge candidate) H
    c t descentRate hw hvar hcone hmargin

/-! ## 5. Aggregate physical-Hauptvermutung distortion interface -/

noncomputable def physicalHauptvermutungDistortion
    {ι : Type*}
    (countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale : ℝ) (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction) : ι → ℝ :=
  fun i => (countWindow i + curvatureBias i + spectralLocality i) +
    cSpecBridgeHauptvermutungDistortion scale edge candidate i

noncomputable def physicalHauptvermutungBaseDistortion
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ι → ℝ) : ℝ :=
  ∑ i, (countWindow i + curvatureBias i + spectralLocality i)

noncomputable def physicalHauptvermutungTotalDistortion
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale : ℝ) (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction) : ℝ :=
  ∑ i, physicalHauptvermutungDistortion
    countWindow curvatureBias spectralLocality scale edge candidate i

theorem physicalHauptvermutungDistortion_nonneg
    {ι : Type*}
    (countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale : ℝ) (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction) (i : ι)
    (hcount : 0 ≤ countWindow i)
    (hcurv : 0 ≤ curvatureBias i)
    (hlocal : 0 ≤ spectralLocality i) :
    0 ≤ physicalHauptvermutungDistortion
      countWindow curvatureBias spectralLocality scale edge candidate i := by
  have hbridge :=
    cSpecBridgeHauptvermutungDistortion_nonneg scale edge candidate i
  unfold physicalHauptvermutungDistortion
  linarith

theorem physicalHauptvermutungDistortion_zero_iff
    {ι : Type*}
    (countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale : ℝ) (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction) (i : ι)
    (hcount : 0 ≤ countWindow i)
    (hcurv : 0 ≤ curvatureBias i)
    (hlocal : 0 ≤ spectralLocality i) :
    physicalHauptvermutungDistortion
      countWindow curvatureBias spectralLocality scale edge candidate i = 0 ↔
      countWindow i = 0 ∧ curvatureBias i = 0 ∧
        spectralLocality i = 0 ∧
          candidate i = fourState.perm (edge i) := by
  constructor
  · intro hzero
    have hbridgeNonneg :=
      cSpecBridgeHauptvermutungDistortion_nonneg scale edge candidate i
    have hcountZero : countWindow i = 0 := by
      unfold physicalHauptvermutungDistortion at hzero
      linarith
    have hcurvZero : curvatureBias i = 0 := by
      unfold physicalHauptvermutungDistortion at hzero
      linarith
    have hlocalZero : spectralLocality i = 0 := by
      unfold physicalHauptvermutungDistortion at hzero
      linarith
    have hbridgeZero :
        cSpecBridgeHauptvermutungDistortion scale edge candidate i = 0 := by
      unfold physicalHauptvermutungDistortion at hzero
      linarith
    exact ⟨hcountZero, hcurvZero, hlocalZero,
      (cSpecBridgeHauptvermutungDistortion_zero_iff
        scale edge candidate i).1 hbridgeZero⟩
  · rintro ⟨hcountZero, hcurvZero, hlocalZero, hcandidate⟩
    have hbridgeZero :
        cSpecBridgeHauptvermutungDistortion scale edge candidate i = 0 :=
      (cSpecBridgeHauptvermutungDistortion_zero_iff
        scale edge candidate i).2 hcandidate
    unfold physicalHauptvermutungDistortion
    rw [hcountZero, hcurvZero, hlocalZero, hbridgeZero]
    ring

theorem physicalHauptvermutungTotalDistortion_eq_base_plus_bridge
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale : ℝ) (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction) :
    physicalHauptvermutungTotalDistortion
      countWindow curvatureBias spectralLocality scale edge candidate =
      physicalHauptvermutungBaseDistortion
        countWindow curvatureBias spectralLocality +
        cSpecBridgeTotalDistortion scale edge candidate := by
  unfold physicalHauptvermutungTotalDistortion
    physicalHauptvermutungDistortion
    physicalHauptvermutungBaseDistortion
    cSpecBridgeTotalDistortion
  rw [Finset.sum_add_distrib]

theorem physicalHauptvermutungTotalDistortion_nonneg
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale : ℝ) (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction)
    (hcount : ∀ i, 0 ≤ countWindow i)
    (hcurv : ∀ i, 0 ≤ curvatureBias i)
    (hlocal : ∀ i, 0 ≤ spectralLocality i) :
    0 ≤ physicalHauptvermutungTotalDistortion
      countWindow curvatureBias spectralLocality scale edge candidate := by
  unfold physicalHauptvermutungTotalDistortion
  exact Finset.sum_nonneg
    (fun i _ => physicalHauptvermutungDistortion_nonneg
      countWindow curvatureBias spectralLocality scale edge candidate i
        (hcount i) (hcurv i) (hlocal i))

theorem physicalHauptvermutungTotalDistortion_eq_zero_iff
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale : ℝ) (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction)
    (hcount : ∀ i, 0 ≤ countWindow i)
    (hcurv : ∀ i, 0 ≤ curvatureBias i)
    (hlocal : ∀ i, 0 ≤ spectralLocality i) :
    physicalHauptvermutungTotalDistortion
      countWindow curvatureBias spectralLocality scale edge candidate = 0 ↔
      (∀ i, countWindow i = 0) ∧
        (∀ i, curvatureBias i = 0) ∧
          (∀ i, spectralLocality i = 0) ∧
            candidate = canonicalCSpecBridgeCandidate edge := by
  constructor
  · intro hzero
    have hpoint :
        ∀ i,
          physicalHauptvermutungDistortion
            countWindow curvatureBias spectralLocality
            scale edge candidate i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => physicalHauptvermutungDistortion_nonneg
          countWindow curvatureBias spectralLocality scale edge candidate j
            (hcount j) (hcurv j) (hlocal j))).1 hzero i (Finset.mem_univ i)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      exact ((physicalHauptvermutungDistortion_zero_iff
        countWindow curvatureBias spectralLocality scale edge candidate i
          (hcount i) (hcurv i) (hlocal i)).1 (hpoint i)).1
    · intro i
      exact ((physicalHauptvermutungDistortion_zero_iff
        countWindow curvatureBias spectralLocality scale edge candidate i
          (hcount i) (hcurv i) (hlocal i)).1 (hpoint i)).2.1
    · intro i
      exact ((physicalHauptvermutungDistortion_zero_iff
        countWindow curvatureBias spectralLocality scale edge candidate i
          (hcount i) (hcurv i) (hlocal i)).1 (hpoint i)).2.2.1
    · funext i
      exact ((physicalHauptvermutungDistortion_zero_iff
        countWindow curvatureBias spectralLocality scale edge candidate i
          (hcount i) (hcurv i) (hlocal i)).1 (hpoint i)).2.2.2
  · rintro ⟨hcountZero, hcurvZero, hlocalZero, hcandidate⟩
    unfold physicalHauptvermutungTotalDistortion
    apply Finset.sum_eq_zero
    intro i _
    exact (physicalHauptvermutungDistortion_zero_iff
      countWindow curvatureBias spectralLocality scale edge candidate i
        (hcount i) (hcurv i) (hlocal i)).2
      ⟨hcountZero i, hcurvZero i, hlocalZero i, by
        rw [hcandidate]
        rfl⟩

theorem physicalHauptvermutungTotalDistortion_strict_transport_min_of_ne
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale : ℝ) (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction)
    (hcandidate : candidate ≠ canonicalCSpecBridgeCandidate edge) :
    physicalHauptvermutungTotalDistortion countWindow curvatureBias
      spectralLocality scale edge (canonicalCSpecBridgeCandidate edge) <
        physicalHauptvermutungTotalDistortion countWindow curvatureBias
          spectralLocality scale edge candidate := by
  rw [physicalHauptvermutungTotalDistortion_eq_base_plus_bridge
    countWindow curvatureBias spectralLocality scale edge
      (canonicalCSpecBridgeCandidate edge)]
  rw [physicalHauptvermutungTotalDistortion_eq_base_plus_bridge
    countWindow curvatureBias spectralLocality scale edge candidate]
  have hbridge :=
    cSpecBridgeTotalDistortion_strict_min_of_ne scale edge candidate hcandidate
  linarith

theorem physicalHauptvermutungTotalDistortion_pos_of_transport_ne_canonical
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale : ℝ) (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction)
    (hcount : ∀ i, 0 ≤ countWindow i)
    (hcurv : ∀ i, 0 ≤ curvatureBias i)
    (hlocal : ∀ i, 0 ≤ spectralLocality i)
    (hcandidate : candidate ≠ canonicalCSpecBridgeCandidate edge) :
    0 < physicalHauptvermutungTotalDistortion
      countWindow curvatureBias spectralLocality scale edge candidate := by
  by_contra hnot
  have hle :
      physicalHauptvermutungTotalDistortion
        countWindow curvatureBias spectralLocality scale edge candidate ≤ 0 :=
    le_of_not_gt hnot
  have hnonneg := physicalHauptvermutungTotalDistortion_nonneg
    countWindow curvatureBias spectralLocality scale edge candidate
      hcount hcurv hlocal
  have hzero :
      physicalHauptvermutungTotalDistortion
        countWindow curvatureBias spectralLocality scale edge candidate = 0 :=
    le_antisymm hle hnonneg
  exact hcandidate
    ((physicalHauptvermutungTotalDistortion_eq_zero_iff
      countWindow curvatureBias spectralLocality scale edge candidate
        hcount hcurv hlocal).1 hzero).2.2.2

/-! ## 6. Physical growth repair-source contraction interface -/

structure PhysicalGrowthSuppliesRepairSource
    {ι : Type*} [Fintype ι]
    (w J source countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale c step descentRate remainder currentTotal nextTotal : ℝ)
    (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction) : Prop where
  first_horizon_area_zero :
    linearResponse w source (finiteAreaChange c J) = 0
  second_horizon_area_zero :
    quadraticResponse w source (finiteAreaChange c J) = 0
  descends_aggregate :
    linearResponse w source
      (physicalHauptvermutungDistortion
        countWindow curvatureBias spectralLocality scale edge candidate) ≤
      -descentRate
  update_bound :
    nextTotal ≤ currentTotal +
      step * linearResponse w source
        (physicalHauptvermutungDistortion
          countWindow curvatureBias spectralLocality scale edge candidate) +
        remainder
  remainder_bound :
    remainder ≤ step * descentRate / 2

theorem physicalGrowthSuppliesRepairSource_contracts
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ι → ℝ}
    {scale c step descentRate remainder currentTotal nextTotal : ℝ}
    {edge : ι → E4}
    {candidate : ι → Equiv.Perm Direction}
    (C : PhysicalGrowthSuppliesRepairSource w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder currentTotal nextTotal
      edge candidate)
    (hstep : 0 ≤ step) :
    nextTotal ≤ currentTotal - step * descentRate / 2 := by
  have hmul :
      step * linearResponse w source
        (physicalHauptvermutungDistortion
          countWindow curvatureBias spectralLocality scale edge candidate) ≤
        step * (-descentRate) := by
    exact mul_le_mul_of_nonneg_left C.descends_aggregate hstep
  linarith [C.update_bound, C.remainder_bound, hmul]

theorem physicalGrowthSuppliesRepairSource_strictly_contracts
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ι → ℝ}
    {scale c step descentRate remainder currentTotal nextTotal : ℝ}
    {edge : ι → E4}
    {candidate : ι → Equiv.Perm Direction}
    (C : PhysicalGrowthSuppliesRepairSource w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder currentTotal nextTotal
      edge candidate)
    (hstep : 0 < step)
    (hdescent : 0 < descentRate) :
    nextTotal < currentTotal := by
  have hcontract :=
    physicalGrowthSuppliesRepairSource_contracts C (le_of_lt hstep)
  have hgap : 0 < step * descentRate / 2 := by
    nlinarith [mul_pos hstep hdescent]
  linarith

theorem physicalGrowthSuppliesRepairSource_protected_and_contracts
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ι → ℝ}
    {scale c step descentRate remainder currentTotal nextTotal : ℝ}
    {edge : ι → E4}
    {candidate : ι → Equiv.Perm Direction}
    (C : PhysicalGrowthSuppliesRepairSource w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder currentTotal nextTotal
      edge candidate)
    (hstep : 0 < step)
    (hdescent : 0 < descentRate) :
    (linearResponse w source (finiteAreaChange c J) = 0 ∧
      quadraticResponse w source (finiteAreaChange c J) = 0) ∧
      nextTotal < currentTotal := by
  exact ⟨⟨C.first_horizon_area_zero, C.second_horizon_area_zero⟩,
    physicalGrowthSuppliesRepairSource_strictly_contracts C hstep hdescent⟩

#print axioms bridgeCensusDefect_canonical_zero
#print axioms bridgeCensusDefect_pos_of_ne
#print axioms bridgeCensusDefect_eq_zero_iff
#print axioms bridgeCensusDefect_zero_and_orderRecovered
#print axioms cSpecBridgeHauptvermutungDistortion_eq_defect
#print axioms cSpecBridgeHauptvermutungDistortion_pos_iff
#print axioms cSpecBridgeTotalDistortion_eq_zero_iff
#print axioms cSpecBridgeTotalDistortion_pos_iff_candidate_ne_canonical
#print axioms cSpecBridgeTotalDistortion_strict_min_of_ne
#print axioms cSpecBridgeTotalDistortion_zero_orderRecovered
#print axioms cSpecBridge_canonicalSource_descends_distortion
#print axioms cSpecBridge_canonicalSource_area_response_zero
#print axioms cSpecBridge_correctedSource_protected_bridge
#print axioms physicalHauptvermutungTotalDistortion_eq_zero_iff
#print axioms physicalHauptvermutungTotalDistortion_strict_transport_min_of_ne
#print axioms physicalHauptvermutungTotalDistortion_pos_of_transport_ne_canonical
#print axioms physicalGrowthSuppliesRepairSource_protected_and_contracts

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
