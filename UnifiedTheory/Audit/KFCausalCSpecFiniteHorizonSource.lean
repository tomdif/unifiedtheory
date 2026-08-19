/-
  Audit/KFCausalCSpecFiniteHorizonSource.lean

  Finite two-channel horizon source: algebraic core of the numerical
  `horizon_mix_pareto.py` result.

  The finite source is

      S_a = std( std(J) + a * B )

  where `J` is the exact horizon-hit/focusing source and `B` is the
  parentwise component of the action channel orthogonal to `J`.

  Because the two channels are standardized and orthogonal, the normalized
  mixture has horizon projection

      1 / sqrt(1 + a^2).

  Therefore the focusing-retention coefficient is exact and depends only on
  the chosen mixing coefficient `a`, not on depth or the parent ensemble.
  This explains the observed stability:

      a = 0.20 = 1/5  gives  retention^2 = 25/26.

  The bulk/action response is correspondingly

      (gap_J + a * gap_B) / sqrt(1 + a^2).

  This file proves both:

    * the scalar two-channel source geometry, and
    * the exact finite exponential-tilt identity

          d/dlambda KL_lambda = -lambda * d/dlambda E_lambda[c - J]

      for any normalized nonnegative finite birth law.

  The concrete probabilistic construction of `J`, the orthogonal residual `B`,
  and the path-level tests live in `horizon_entropy_probe.py`,
  `horizon_source_scan.py`, `horizon_mix_pareto.py`, and
  `horizon_tilt_paths.py`.

  Zero sorry.  Zero custom axioms.
-/

import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecFiniteHorizonSource

open scoped BigOperators

/-- Normalization of two orthogonal standardized channels. -/
noncomputable def sourceNorm (a : ℝ) : ℝ :=
  Real.sqrt (1 + a ^ 2)

/-- Horizon focusing retained by the normalized two-channel source. -/
noncomputable def focusRetention (a : ℝ) : ℝ :=
  1 / sourceNorm a

/-- Linear response of any observable with pure-horizon slope `x` and
orthogonal-bulk/action slope `y` under the normalized source. -/
noncomputable def mixedSlope (x y a : ℝ) : ℝ :=
  (x + a * y) / sourceNorm a

theorem sourceNorm_pos (a : ℝ) : 0 < sourceNorm a := by
  unfold sourceNorm
  exact Real.sqrt_pos_of_pos (by nlinarith [sq_nonneg a])

theorem focusRetention_pos (a : ℝ) : 0 < focusRetention a := by
  unfold focusRetention
  exact one_div_pos.mpr (sourceNorm_pos a)

/-- The area/focusing channel has no orthogonal-bulk contribution, so its
normalized slope is exactly the pure slope times the retention coefficient. -/
theorem mixed_area_slope_eq_retained (areaJ a : ℝ) :
    mixedSlope areaJ 0 a = focusRetention a * areaJ := by
  unfold mixedSlope focusRetention
  ring

/-- The action/gap response is the normalized sum of horizon and orthogonal
bulk/action responses. -/
theorem mixed_gap_slope_formula (gapJ gapBulk a : ℝ) :
    mixedSlope gapJ gapBulk a =
      focusRetention a * (gapJ + a * gapBulk) := by
  unfold mixedSlope focusRetention
  ring

/-- Squared focusing retention is `1/(1+a^2)`. -/
theorem focusRetention_sq (a : ℝ) :
    focusRetention a ^ 2 = 1 / (1 + a ^ 2) := by
  unfold focusRetention sourceNorm
  rw [div_pow]
  rw [Real.sq_sqrt (by nlinarith [sq_nonneg a])]
  norm_num

/-- Registered strict source coefficient: `a = 0.20 = 1/5` retains
`25/26` of the squared focusing response. -/
theorem focusRetention_one_fifth_sq :
    focusRetention ((1 : ℝ) / 5) ^ 2 = 25 / 26 := by
  rw [focusRetention_sq]
  norm_num

/-- At `a = 1/5`, the mixed gap/action response is exactly
`focusRetention (1/5) * (gapJ + gapBulk/5)`. -/
theorem mixed_gap_slope_one_fifth (gapJ gapBulk : ℝ) :
    mixedSlope gapJ gapBulk ((1 : ℝ) / 5) =
      focusRetention ((1 : ℝ) / 5) * (gapJ + gapBulk / 5) := by
  rw [mixed_gap_slope_formula]
  ring

/-! ## Finite focusing covariance -/

/-- Finite weighted expectation.  The weights are allowed to be any real
function; normalization is supplied only to the theorems that need it. -/
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

/-- One-birth horizon-area change in the finite probe:
`c` is the new maximal element contribution and `J` is the number of old
frontier elements hit by the precursor. -/
def finiteAreaChange {ι : Type*} (c : ℝ) (J : ι → ℝ) : ι → ℝ :=
  fun i => c - J i

/-- The expectation of `c - J` under normalized weights is
`c - E[J]`. -/
theorem expectation_finiteAreaChange {ι : Type*} [Fintype ι]
    (w J : ι → ℝ) (c : ℝ)
    (hw : (∑ i, w i) = 1) :
    expectation w (finiteAreaChange c J) = c - expectation w J := by
  unfold expectation finiteAreaChange
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

/-- The mixed second moment of `(c-J)` with `J`. -/
theorem expectation_finiteAreaChange_mul_self {ι : Type*} [Fintype ι]
    (w J : ι → ℝ) (c : ℝ) :
    expectation w (fun i => finiteAreaChange c J i * J i) =
      c * expectation w J - expectation w (fun i => J i * J i) := by
  unfold expectation finiteAreaChange
  calc
    (∑ i, w i * ((c - J i) * J i))
        = ∑ i, (c * (w i * J i) - w i * (J i * J i)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = c * (∑ i, w i * J i) - ∑ i, w i * (J i * J i) := by
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [Finset.mul_sum]

/-- Exact finite focusing covariance:
for normalized weights, the covariance of the one-birth horizon-area change
`c-J` with the horizon-hit source `J` is the negative variance of `J`. -/
theorem covariance_finiteAreaChange_self_eq_neg_variance
    {ι : Type*} [Fintype ι]
    (w J : ι → ℝ) (c : ℝ)
    (hw : (∑ i, w i) = 1) :
    covariance w (finiteAreaChange c J) J = -variance w J := by
  unfold covariance variance
  rw [expectation_finiteAreaChange (w := w) (J := J) (c := c) hw]
  rw [expectation_finiteAreaChange_mul_self (w := w) (J := J) (c := c)]
  unfold covariance
  ring

/-- A source centered against the finite weighted expectation. -/
noncomputable def centeredSource {ι : Type*} [Fintype ι]
    (w S : ι → ℝ) : ι → ℝ :=
  fun i => S i - expectation w S

/-- First-order response to an infinitesimal centered source tilt. -/
noncomputable def linearTiltResponse {ι : Type*} [Fintype ι]
    (w S X : ι → ℝ) : ℝ :=
  expectation w (fun i => X i * centeredSource w S i)

/-- A centered source has zero weighted expectation when the weights are
normalized. -/
theorem expectation_centeredSource_eq_zero {ι : Type*} [Fintype ι]
    (w S : ι → ℝ)
    (hw : (∑ i, w i) = 1) :
    expectation w (centeredSource w S) = 0 := by
  unfold expectation centeredSource
  calc
    (∑ i, w i * (S i - ∑ j, w j * S j))
        = ∑ i, (w i * S i - (∑ j, w j * S j) * w i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = ∑ i, w i * S i - (∑ j, w j * S j) * (∑ i, w i) := by
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [Finset.mul_sum]
    _ = 0 := by
            rw [hw]
            ring

/-- Finite linear response identity:
the first-order response of an observable to a centered source tilt is its
weighted covariance with that source. -/
theorem linearTiltResponse_eq_covariance {ι : Type*} [Fintype ι]
    (w S X : ι → ℝ) :
    linearTiltResponse w S X = covariance w X S := by
  unfold linearTiltResponse centeredSource covariance expectation
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

/-- Specializing finite linear response to the horizon-hit source proves that
the infinitesimal area response is exactly negative source variance. -/
theorem linearTiltResponse_finiteAreaChange_self_eq_neg_variance
    {ι : Type*} [Fintype ι]
    (w J : ι → ℝ) (c : ℝ)
    (hw : (∑ i, w i) = 1) :
    linearTiltResponse w J (finiteAreaChange c J) = -variance w J := by
  rw [linearTiltResponse_eq_covariance]
  exact covariance_finiteAreaChange_self_eq_neg_variance
    (w := w) (J := J) (c := c) hw

/-- Moment-only form of the same identity.  If `m1 = E[J]` and
`m2 = E[J^2]`, then `Cov(c-J,J) = -Var(J)`. -/
def varianceMoment (m1 m2 : ℝ) : ℝ :=
  m2 - m1 ^ 2

/-- Moment-only covariance of `c-J` with `J`. -/
def covarianceConstSubSelfMoment (c m1 m2 : ℝ) : ℝ :=
  (c * m1 - m2) - (c - m1) * m1

theorem covarianceConstSubSelfMoment_eq_neg_varianceMoment
    (c m1 m2 : ℝ) :
    covarianceConstSubSelfMoment c m1 m2 = -varianceMoment m1 m2 := by
  unfold covarianceConstSubSelfMoment varianceMoment
  ring

/-- Quadratic small-source relative-entropy coefficient for an exponential
tilt, expressed only in terms of the source variance. -/
noncomputable def quadraticKLApprox (lambda sourceVariance : ℝ) : ℝ :=
  lambda ^ 2 / 2 * sourceVariance

/-- Linear focusing response coefficient for the same source. -/
def linearAreaResponse (lambda sourceVariance : ℝ) : ℝ :=
  -lambda * sourceVariance

/-- The finite small-source relation used in the numerical probe:
`area_shift = -2 KL_quad / lambda` for nonzero source parameter. -/
theorem linearAreaResponse_eq_neg_two_quadraticKLApprox_div
    {lambda sourceVariance : ℝ} (hlambda : lambda ≠ 0) :
  linearAreaResponse lambda sourceVariance =
      -(2 * quadraticKLApprox lambda sourceVariance) / lambda := by
  unfold linearAreaResponse quadraticKLApprox
  field_simp [hlambda]

/-! ## Exact finite exponential-tilt breakthrough -/

/-- Partition function for a finite exponential source tilt. -/
noncomputable def expTiltPartition {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (lambda : ℝ) : ℝ :=
  ∑ i, p i * Real.exp (lambda * J i)

/-- Unnormalized tilted moment. -/
noncomputable def expTiltMoment {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (lambda : ℝ) (X : ι → ℝ) : ℝ :=
  ∑ i, p i * Real.exp (lambda * J i) * X i

/-- Tilted finite expectation. -/
noncomputable def expTiltExpectation {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (lambda : ℝ) (X : ι → ℝ) : ℝ :=
  expTiltMoment p J lambda X / expTiltPartition p J lambda

/-- Tilted finite covariance. -/
noncomputable def expTiltCovariance {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (lambda : ℝ) (X Y : ι → ℝ) : ℝ :=
  expTiltExpectation p J lambda (fun i => X i * Y i) -
    expTiltExpectation p J lambda X * expTiltExpectation p J lambda Y

/-- Tilted finite variance of the source. -/
noncomputable def expTiltVariance {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (lambda : ℝ) : ℝ :=
  expTiltCovariance p J lambda J J

/-- Exponential-family relative entropy formula:
`KL(q_lambda || p) = lambda * E_lambda[J] - log Z(lambda)`. -/
noncomputable def expTiltKL {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (lambda : ℝ) : ℝ :=
  lambda * expTiltExpectation p J lambda J -
    Real.log (expTiltPartition p J lambda)

/-- Derivative of one tilted kernel term. -/
theorem hasDerivAt_expTiltKernel {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (i : ι) (lambda : ℝ) :
    HasDerivAt
      (fun t : ℝ => p i * Real.exp (t * J i))
      (p i * Real.exp (lambda * J i) * J i)
      lambda := by
  have hlin : HasDerivAt (fun t : ℝ => t * J i) (1 * J i) lambda :=
    (hasDerivAt_id lambda).mul_const (J i)
  have hexp : HasDerivAt
      (fun t : ℝ => Real.exp (t * J i))
      (Real.exp (lambda * J i) * (1 * J i))
      lambda :=
    hlin.exp
  have hterm := hexp.const_mul (p i)
  convert hterm using 1
  ring

/-- Derivative of one tilted moment term. -/
theorem hasDerivAt_expTiltMomentKernel {ι : Type*} [Fintype ι]
    (p J X : ι → ℝ) (i : ι) (lambda : ℝ) :
    HasDerivAt
      (fun t : ℝ => p i * Real.exp (t * J i) * X i)
      (p i * Real.exp (lambda * J i) * (J i * X i))
      lambda := by
  have h := (hasDerivAt_expTiltKernel p J i lambda).mul_const (X i)
  convert h using 1
  ring

/-- Derivative of the finite partition function. -/
theorem hasDerivAt_expTiltPartition {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (lambda : ℝ) :
    HasDerivAt
      (fun t : ℝ => expTiltPartition p J t)
      (expTiltMoment p J lambda J)
      lambda := by
  simpa [expTiltPartition, expTiltMoment] using
    (HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun i t => p i * Real.exp (t * J i))
      (A' := fun i => p i * Real.exp (lambda * J i) * J i)
      (x := lambda)
      (fun i _ => hasDerivAt_expTiltKernel p J i lambda))

/-- Derivative of a finite tilted unnormalized moment. -/
theorem hasDerivAt_expTiltMoment {ι : Type*} [Fintype ι]
    (p J X : ι → ℝ) (lambda : ℝ) :
    HasDerivAt
      (fun t : ℝ => expTiltMoment p J t X)
      (expTiltMoment p J lambda (fun i => J i * X i))
      lambda := by
  simpa [expTiltMoment] using
    (HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun i t => p i * Real.exp (t * J i) * X i)
      (A' := fun i => p i * Real.exp (lambda * J i) * (J i * X i))
      (x := lambda)
      (fun i _ => hasDerivAt_expTiltMomentKernel p J X i lambda))

/-- Derivative of a finite tilted expectation is covariance with the source. -/
theorem hasDerivAt_expTiltExpectation {ι : Type*} [Fintype ι]
    (p J X : ι → ℝ) (lambda : ℝ)
    (hZ : expTiltPartition p J lambda ≠ 0) :
    HasDerivAt
      (fun t : ℝ => expTiltExpectation p J t X)
      (expTiltCovariance p J lambda X J)
      lambda := by
  have hM := hasDerivAt_expTiltMoment p J X lambda
  have hZderiv := hasDerivAt_expTiltPartition p J lambda
  have hdiv := hM.div hZderiv hZ
  have hJX :
      expTiltMoment p J lambda (fun i => J i * X i) =
        expTiltMoment p J lambda (fun i => X i * J i) := by
    unfold expTiltMoment
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdrv :
      (expTiltMoment p J lambda (fun i => J i * X i) *
            expTiltPartition p J lambda -
          expTiltMoment p J lambda X * expTiltMoment p J lambda J) /
          expTiltPartition p J lambda ^ 2 =
        expTiltCovariance p J lambda X J := by
    rw [hJX]
    unfold expTiltCovariance expTiltExpectation
    field_simp [hZ]
  rw [← hdrv]
  exact hdiv

/-- The source expectation differentiates to the tilted source variance. -/
theorem hasDerivAt_expTiltSourceExpectation {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (lambda : ℝ)
    (hZ : expTiltPartition p J lambda ≠ 0) :
    HasDerivAt
      (fun t : ℝ => expTiltExpectation p J t J)
      (expTiltVariance p J lambda)
      lambda := by
  simpa [expTiltVariance] using
    hasDerivAt_expTiltExpectation p J J lambda hZ

/-- Unnormalized finite moment of the one-birth horizon-area change. -/
theorem expTiltMoment_finiteAreaChange {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (c lambda : ℝ) :
    expTiltMoment p J lambda (finiteAreaChange c J) =
      c * expTiltPartition p J lambda - expTiltMoment p J lambda J := by
  unfold expTiltMoment expTiltPartition finiteAreaChange
  calc
    (∑ i, p i * Real.exp (lambda * J i) * (c - J i))
        = ∑ i,
            (c * (p i * Real.exp (lambda * J i)) -
              p i * Real.exp (lambda * J i) * J i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = c * (∑ i, p i * Real.exp (lambda * J i)) -
          ∑ i, p i * Real.exp (lambda * J i) * J i := by
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [Finset.mul_sum]

/-- Normalized tilted expectation of the one-birth horizon-area change. -/
theorem expTiltExpectation_finiteAreaChange {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (c lambda : ℝ)
    (hZ : expTiltPartition p J lambda ≠ 0) :
    expTiltExpectation p J lambda (finiteAreaChange c J) =
      c - expTiltExpectation p J lambda J := by
  unfold expTiltExpectation
  rw [expTiltMoment_finiteAreaChange]
  field_simp [hZ]

/-- Exact focusing under the finite exponential tilt:
the tilted horizon-area expectation differentiates to negative source
variance. -/
theorem hasDerivAt_expTiltAreaExpectation {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (c lambda : ℝ)
    (hZall : ∀ t : ℝ, expTiltPartition p J t ≠ 0) :
    HasDerivAt
      (fun t : ℝ => expTiltExpectation p J t (finiteAreaChange c J))
      (-expTiltVariance p J lambda)
      lambda := by
  have hfun :
      (fun t : ℝ => expTiltExpectation p J t (finiteAreaChange c J)) =
        fun t : ℝ => c - expTiltExpectation p J t J := by
    funext t
    exact expTiltExpectation_finiteAreaChange p J c t (hZall t)
  rw [hfun]
  have hE := hasDerivAt_expTiltSourceExpectation p J lambda (hZall lambda)
  simpa using (hasDerivAt_const lambda c).sub hE

/-- Exact derivative of the exponential-family KL formula. -/
theorem hasDerivAt_expTiltKL {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (lambda : ℝ)
    (hZ : expTiltPartition p J lambda ≠ 0) :
    HasDerivAt
      (fun t : ℝ => expTiltKL p J t)
      (lambda * expTiltVariance p J lambda)
      lambda := by
  have hE := hasDerivAt_expTiltSourceExpectation p J lambda hZ
  have hprod := (hasDerivAt_id lambda).mul hE
  have hlog := (hasDerivAt_expTiltPartition p J lambda).log hZ
  have h := hprod.sub hlog
  have hdrv :
      1 * expTiltExpectation p J lambda J +
            lambda * expTiltVariance p J lambda -
          expTiltMoment p J lambda J / expTiltPartition p J lambda =
        lambda * expTiltVariance p J lambda := by
    unfold expTiltExpectation
    field_simp [hZ]
    ring
  rw [← hdrv]
  exact h

/-- Breakthrough theorem, derivative form:
finite exponential relative entropy controls finite horizon focusing exactly.

For every finite birth law with nonzero partition function along the source
line, the derivative of the KL formula is `-lambda` times the derivative of
the expected one-birth horizon-area change. -/
theorem finiteEntropyFocusing_deriv_identity {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (c lambda : ℝ)
    (hZall : ∀ t : ℝ, expTiltPartition p J t ≠ 0) :
    deriv (fun t : ℝ => expTiltKL p J t) lambda =
      -lambda *
        deriv
          (fun t : ℝ => expTiltExpectation p J t (finiteAreaChange c J))
          lambda := by
  have hKL := hasDerivAt_expTiltKL p J lambda (hZall lambda)
  have hArea := hasDerivAt_expTiltAreaExpectation p J c lambda hZall
  rw [hKL.deriv, hArea.deriv]
  ring

/-- Existential version recording the two derivatives and their balance. -/
theorem finiteEntropyFocusing_breakthrough {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (c lambda : ℝ)
    (hZall : ∀ t : ℝ, expTiltPartition p J t ≠ 0) :
    ∃ areaDeriv klDeriv : ℝ,
      HasDerivAt
          (fun t : ℝ => expTiltExpectation p J t (finiteAreaChange c J))
          areaDeriv lambda ∧
        HasDerivAt (fun t : ℝ => expTiltKL p J t) klDeriv lambda ∧
        klDeriv = -lambda * areaDeriv := by
  refine ⟨-expTiltVariance p J lambda,
    lambda * expTiltVariance p J lambda, ?_, ?_, ?_⟩
  · exact hasDerivAt_expTiltAreaExpectation p J c lambda hZall
  · exact hasDerivAt_expTiltKL p J lambda (hZall lambda)
  · ring

/-- A normalized nonnegative finite birth law has strictly positive tilted
partition function for every source strength. -/
theorem expTiltPartition_pos_of_birthLaw {ι : Type*} [Fintype ι]
    (p J : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp_sum : (∑ i, p i) = 1)
    (lambda : ℝ) :
    0 < expTiltPartition p J lambda := by
  have h_exists : ∃ i, 0 < p i := by
    by_contra h
    push_neg at h
    have hzero : ∀ i, p i = 0 := by
      intro i
      exact le_antisymm (h i) (hp_nonneg i)
    have hsum0 : (∑ i, p i) = 0 := by
      simp [hzero]
    linarith
  rcases h_exists with ⟨i0, hi0⟩
  unfold expTiltPartition
  refine Finset.sum_pos' ?_ ⟨i0, Finset.mem_univ i0, ?_⟩
  · intro i _
    exact mul_nonneg (hp_nonneg i) (le_of_lt (Real.exp_pos _))
  · exact mul_pos hi0 (Real.exp_pos _)

/-- Birth-law version of the breakthrough theorem: the nonzero partition
hypothesis follows from ordinary finite probability weights. -/
theorem finiteEntropyFocusing_birthLaw_deriv_identity
    {ι : Type*} [Fintype ι]
    (p J : ι → ℝ) (c lambda : ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp_sum : (∑ i, p i) = 1) :
    deriv (fun t : ℝ => expTiltKL p J t) lambda =
      -lambda *
        deriv
          (fun t : ℝ => expTiltExpectation p J t (finiteAreaChange c J))
          lambda := by
  exact finiteEntropyFocusing_deriv_identity p J c lambda
    (fun t => ne_of_gt (expTiltPartition_pos_of_birthLaw p J hp_nonneg hp_sum t))

/-! ## Finite causal-growth birth kernels -/

/-- A finite one-step causal-growth kernel before normalization.

The index type `ι` represents the finite set of admissible next-birth
precursors from a fixed parent state.  The only assumptions needed for the
entropy-focusing theorem are nonnegative raw weights and positive total raw
weight. -/
structure FiniteCausalGrowthKernel (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_partition_pos : 0 < ∑ i, weight i

namespace FiniteCausalGrowthKernel

/-- Total raw transition weight. -/
noncomputable def partition {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) : ℝ :=
  ∑ i, K.weight i

/-- Normalized one-step birth law generated by the raw growth kernel. -/
noncomputable def birthLaw {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) : ι → ℝ :=
  fun i => K.weight i / K.partition

theorem partition_pos {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) :
    0 < K.partition := by
  simpa [partition] using K.weight_partition_pos

theorem partition_ne_zero {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) :
    K.partition ≠ 0 :=
  ne_of_gt K.partition_pos

/-- The normalized kernel is nonnegative on every finite precursor. -/
theorem birthLaw_nonneg {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) :
    ∀ i, 0 ≤ K.birthLaw i := by
  intro i
  unfold birthLaw
  exact div_nonneg (K.weight_nonneg i) (le_of_lt K.partition_pos)

/-- The normalized kernel has total probability one. -/
theorem birthLaw_sum {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) :
    (∑ i, K.birthLaw i) = 1 := by
  unfold birthLaw
  calc
    (∑ i, K.weight i / K.partition)
        = (∑ i, K.weight i) / K.partition := by
            rw [Finset.sum_div]
    _ = K.partition / K.partition := by
            simp [partition]
    _ = 1 := by
            field_simp [K.partition_ne_zero]

/-- The normalized kernel is exactly a finite birth law in the sense required
by the entropy-focusing theorem. -/
theorem produces_birthLaw {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) :
    (∀ i, 0 ≤ K.birthLaw i) ∧ (∑ i, K.birthLaw i) = 1 :=
  ⟨K.birthLaw_nonneg, K.birthLaw_sum⟩

/-- Exponentially source-tilted one-step birth law. -/
noncomputable def tiltedBirthLaw {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) (J : ι → ℝ) (lambda : ℝ) : ι → ℝ :=
  fun i =>
    K.birthLaw i * Real.exp (lambda * J i) /
      expTiltPartition K.birthLaw J lambda

theorem tilted_partition_pos {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) (J : ι → ℝ) (lambda : ℝ) :
    0 < expTiltPartition K.birthLaw J lambda :=
  expTiltPartition_pos_of_birthLaw
    K.birthLaw J K.birthLaw_nonneg K.birthLaw_sum lambda

theorem tilted_partition_ne_zero {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) (J : ι → ℝ) (lambda : ℝ) :
    expTiltPartition K.birthLaw J lambda ≠ 0 :=
  ne_of_gt (K.tilted_partition_pos J lambda)

/-- Source tilting preserves nonnegativity of the one-step birth law. -/
theorem tiltedBirthLaw_nonneg {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) (J : ι → ℝ) (lambda : ℝ) :
    ∀ i, 0 ≤ K.tiltedBirthLaw J lambda i := by
  intro i
  unfold tiltedBirthLaw
  exact div_nonneg
    (mul_nonneg (K.birthLaw_nonneg i) (le_of_lt (Real.exp_pos _)))
    (le_of_lt (K.tilted_partition_pos J lambda))

/-- Source tilting preserves total probability one. -/
theorem tiltedBirthLaw_sum {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) (J : ι → ℝ) (lambda : ℝ) :
    (∑ i, K.tiltedBirthLaw J lambda i) = 1 := by
  unfold tiltedBirthLaw expTiltPartition
  calc
    (∑ i,
        K.birthLaw i * Real.exp (lambda * J i) /
          ∑ j, K.birthLaw j * Real.exp (lambda * J j))
        =
        (∑ i, K.birthLaw i * Real.exp (lambda * J i)) /
          ∑ j, K.birthLaw j * Real.exp (lambda * J j) := by
            rw [Finset.sum_div]
    _ = 1 := by
            have hZ :
                (∑ x, K.birthLaw x * Real.exp (lambda * J x)) ≠ 0 := by
              simpa [expTiltPartition] using K.tilted_partition_ne_zero J lambda
            exact div_self hZ

/-- The tilted kernel is again a normalized nonnegative finite birth law. -/
theorem source_tilt_produces_birthLaw {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) (J : ι → ℝ) (lambda : ℝ) :
    (∀ i, 0 ≤ K.tiltedBirthLaw J lambda i) ∧
      (∑ i, K.tiltedBirthLaw J lambda i) = 1 :=
  ⟨K.tiltedBirthLaw_nonneg J lambda, K.tiltedBirthLaw_sum J lambda⟩

/-- Causal-growth kernel version of the entropy-focusing identity.  Once a
parent state supplies finite nonnegative transition weights, no extra
normalization hypothesis is needed. -/
theorem kernel_entropyFocusing_deriv_identity
    {ι : Type*} [Fintype ι]
    (K : FiniteCausalGrowthKernel ι) (J : ι → ℝ) (c lambda : ℝ) :
    deriv (fun t : ℝ => expTiltKL K.birthLaw J t) lambda =
      -lambda *
        deriv
          (fun t : ℝ =>
            expTiltExpectation K.birthLaw J t (finiteAreaChange c J))
          lambda :=
  finiteEntropyFocusing_birthLaw_deriv_identity
    K.birthLaw J c lambda K.birthLaw_nonneg K.birthLaw_sum

end FiniteCausalGrowthKernel

/-! ## Parent-indexed finite growth systems -/

/-- A finite causal-growth system: each parent state has a finite type of
admissible next-birth moves and a positive nonnegative raw kernel on those
moves. -/
structure FiniteCausalGrowthSystem (σ : Type*) where
  Move : σ → Type*
  moveFintype : ∀ s, Fintype (Move s)
  kernel : ∀ s, @FiniteCausalGrowthKernel (Move s) (moveFintype s)

namespace FiniteCausalGrowthSystem

/-- Parentwise normalized birth law. -/
noncomputable def birthLaw {σ : Type*}
    (G : FiniteCausalGrowthSystem σ) (s : σ) : G.Move s → ℝ :=
  letI := G.moveFintype s
  (G.kernel s).birthLaw

/-- Parentwise source-tilted birth law. -/
noncomputable def tiltedBirthLaw {σ : Type*}
    (G : FiniteCausalGrowthSystem σ)
    (J : ∀ s, G.Move s → ℝ) (lambda : ℝ) (s : σ) : G.Move s → ℝ :=
  letI := G.moveFintype s
  (G.kernel s).tiltedBirthLaw (J s) lambda

/-- The finite system supplies normalized nonnegative birth laws at every
parent state. -/
def ProducesRequiredBirthLaws {σ : Type*}
    (G : FiniteCausalGrowthSystem σ) : Prop :=
  ∀ s,
    letI := G.moveFintype s
    (∀ i, 0 ≤ G.birthLaw s i) ∧ (∑ i, G.birthLaw s i) = 1

/-- The finite system supplies the birth-law hypotheses required by the
entropy-focusing theorem at every parent state. -/
theorem producesRequiredBirthLaws {σ : Type*}
    (G : FiniteCausalGrowthSystem σ) :
    G.ProducesRequiredBirthLaws := by
  intro s
  letI := G.moveFintype s
  exact (G.kernel s).produces_birthLaw

/-- A source tilt of a finite growth system again supplies normalized
nonnegative birth laws at every parent state. -/
theorem sourceTiltProducesRequiredBirthLaws {σ : Type*}
    (G : FiniteCausalGrowthSystem σ)
    (J : ∀ s, G.Move s → ℝ) (lambda : ℝ) :
    ∀ s,
      letI := G.moveFintype s
      (∀ i, 0 ≤ G.tiltedBirthLaw J lambda s i) ∧
        (∑ i, G.tiltedBirthLaw J lambda s i) = 1 := by
  intro s
  letI := G.moveFintype s
  exact (G.kernel s).source_tilt_produces_birthLaw (J s) lambda

/-- Parentwise causal-growth version of the finite entropy-focusing identity. -/
theorem entropyFocusing_at_parent {σ : Type*}
    (G : FiniteCausalGrowthSystem σ)
    (J : ∀ s, G.Move s → ℝ) (c lambda : ℝ) (s : σ) :
    letI := G.moveFintype s
    deriv (fun t : ℝ => expTiltKL (G.birthLaw s) (J s) t) lambda =
      -lambda *
        deriv
          (fun t : ℝ =>
            expTiltExpectation (G.birthLaw s) (J s) t
              (finiteAreaChange c (J s)))
          lambda := by
  letI := G.moveFintype s
  exact (G.kernel s).kernel_entropyFocusing_deriv_identity (J s) c lambda

end FiniteCausalGrowthSystem

#print axioms sourceNorm_pos
#print axioms focusRetention_sq
#print axioms focusRetention_one_fifth_sq
#print axioms mixed_area_slope_eq_retained
#print axioms mixed_gap_slope_one_fifth
#print axioms covariance_finiteAreaChange_self_eq_neg_variance
#print axioms linearTiltResponse_eq_covariance
#print axioms linearTiltResponse_finiteAreaChange_self_eq_neg_variance
#print axioms covarianceConstSubSelfMoment_eq_neg_varianceMoment
#print axioms linearAreaResponse_eq_neg_two_quadraticKLApprox_div
#print axioms hasDerivAt_expTiltExpectation
#print axioms hasDerivAt_expTiltAreaExpectation
#print axioms hasDerivAt_expTiltKL
#print axioms finiteEntropyFocusing_deriv_identity
#print axioms finiteEntropyFocusing_breakthrough
#print axioms finiteEntropyFocusing_birthLaw_deriv_identity
#print axioms FiniteCausalGrowthKernel.produces_birthLaw
#print axioms FiniteCausalGrowthKernel.source_tilt_produces_birthLaw
#print axioms FiniteCausalGrowthKernel.kernel_entropyFocusing_deriv_identity
#print axioms FiniteCausalGrowthSystem.producesRequiredBirthLaws
#print axioms FiniteCausalGrowthSystem.sourceTiltProducesRequiredBirthLaws
#print axioms FiniteCausalGrowthSystem.entropyFocusing_at_parent

end UnifiedTheory.Audit.KFCausalCSpecFiniteHorizonSource
