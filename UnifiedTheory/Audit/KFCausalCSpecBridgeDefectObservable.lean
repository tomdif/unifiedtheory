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

#print axioms bridgeCensusDefect_canonical_zero
#print axioms bridgeCensusDefect_pos_of_ne
#print axioms bridgeCensusDefect_zero_and_orderRecovered
#print axioms cSpecBridgeHauptvermutungDistortion_eq_defect
#print axioms cSpecBridge_canonicalSource_descends_distortion
#print axioms cSpecBridge_canonicalSource_area_response_zero
#print axioms cSpecBridge_correctedSource_protected_bridge

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
