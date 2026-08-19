/-
  Audit/KFCausalCSpecEntropyFluxLimit.lean

  First bridge toward the remaining continuum quantum-gravity fields.

  The already-proved finite theorem says that exponential relative entropy
  controls finite horizon focusing exactly.  The next missing bridge is:

      finite horizon source  --->  continuum null-energy / Araki flux.

  This file formalizes the first usable version of that bridge:

    * scaled horizon-hit source:      J_rho / rho^p;
    * flat Rindler exact scaling:     J_rho = rho^p (W + residual_rho);
    * RSS/Poisson-style error budget: (epsilon + b + epsilon*b) S;
    * convergence criterion:          if the error goes to zero, the finite
                                      source converges to the continuum flux;
    * finite birth-law positivity:    normalized nonnegative finite birth laws
                                      have strictly positive tilt partition;
    * derivative bridge:              exact finite focusing derivative laws
                                      pass to the limit when area derivatives
                                      converge.

  This is not the full AQFT/Rindler proof.  It is the checked formal slot that
  the analytic/geometric estimates must fill.

  Zero sorry.  Zero custom axioms.
-/

import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit

open Filter Topology
open scoped BigOperators

/-! ## 1. Scaled finite horizon source -/

/-- Scaling used for a finite horizon-hit source at density `rho`.
The natural exponent is left explicit because it depends on the horizon
codimension and the chosen small-diamond normalization. -/
noncomputable def horizonSourceScale (rho : ℝ) (power : ℕ) : ℝ :=
  1 / rho ^ power

/-- Scaled finite horizon source `J_rho / rho^power`. -/
noncomputable def scaledHorizonSource (rho : ℝ) (power : ℕ) (J : ℝ) : ℝ :=
  J / rho ^ power

/-- If the finite source has the exact flat-patch form
`J = rho^power * W`, the scaled source is exactly the continuum flux `W`. -/
theorem scaledHorizonSource_exact_of_hits_eq
    {rho J W : ℝ} {power : ℕ}
    (hrho : rho ≠ 0)
    (hJ : J = rho ^ power * W) :
    scaledHorizonSource rho power J = W := by
  unfold scaledHorizonSource
  rw [hJ]
  field_simp [pow_ne_zero power hrho]

/-- If the finite source has a residual
`J = rho^power * (W + residual)`, then the scaled source is `W + residual`. -/
theorem scaledHorizonSource_eq_flux_add_residual
    {rho J W residual : ℝ} {power : ℕ}
    (hrho : rho ≠ 0)
    (hJ : J = rho ^ power * (W + residual)) :
    scaledHorizonSource rho power J = W + residual := by
  unfold scaledHorizonSource
  rw [hJ]
  field_simp [pow_ne_zero power hrho]

/-- A flat local Rindler source family with an explicit residual. -/
structure FlatRindlerScaledSource where
  density : ℕ → ℝ
  power : ℕ
  hitSource : ℕ → ℝ
  nullFlux : ℝ
  residual : ℕ → ℝ
  density_ne_zero : ∀ n, density n ≠ 0
  hit_decomposition :
    ∀ n, hitSource n = density n ^ power * (nullFlux + residual n)
  residual_tendsto_zero : Tendsto residual atTop (𝓝 0)

/-- The scaled flux estimator associated to a flat Rindler source family. -/
noncomputable def FlatRindlerScaledSource.scaledFlux
    (S : FlatRindlerScaledSource) : ℕ → ℝ :=
  fun n => scaledHorizonSource (S.density n) S.power (S.hitSource n)

/-- Flat Rindler source scaling: if the residual tends to zero, the scaled
finite source converges to the continuum null flux. -/
theorem flat_rindler_scaledFlux_converges
    (S : FlatRindlerScaledSource) :
    Tendsto S.scaledFlux atTop (𝓝 S.nullFlux) := by
  have hfun : S.scaledFlux = fun n => S.nullFlux + S.residual n := by
    funext n
    exact scaledHorizonSource_eq_flux_add_residual
      (S.density_ne_zero n) (S.hit_decomposition n)
  rw [hfun]
  simpa using (tendsto_const_nhds.add S.residual_tendsto_zero)

/-! ## 2. Error-control convergence criterion -/

/-- Deterministic convergence criterion used by the bridge:
if `|f_n - L|` is eventually bounded by a nonnegative error `e_n` and
`e_n -> 0`, then `f_n -> L`. -/
theorem tendsto_of_abs_sub_le_error
    {f error : ℕ → ℝ} {L : ℝ}
    (herror_nonneg : ∀ᶠ n in atTop, 0 ≤ error n)
    (herror_zero : Tendsto error atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, |f n - L| ≤ error n) :
    Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at herror_zero
  obtain ⟨Nerr, hNerr⟩ := herror_zero ε hε
  rw [eventually_atTop] at herror_nonneg
  rw [eventually_atTop] at hbound
  obtain ⟨Nnonneg, hNnonneg⟩ := herror_nonneg
  obtain ⟨Nbound, hNbound⟩ := hbound
  refine ⟨max Nerr (max Nnonneg Nbound), fun n hn => ?_⟩
  have hnerr : Nerr ≤ n := le_of_max_le_left hn
  have hnn : Nnonneg ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hnb : Nbound ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  have herrlt := hNerr n hnerr
  have herrnn := hNnonneg n hnn
  have hb := hNbound n hnb
  rw [Real.dist_eq]
  have herrlt' : error n < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg herrnn] at herrlt
    exact herrlt
  exact lt_of_le_of_lt hb herrlt'

/-- Error-controlled finite entropy source.  The field `continuumNullFlux`
is the target continuum flux.  In a Dorau--Much application it is identified
with the Araki weighted null-energy flux. -/
structure EntropyFluxErrorControl where
  finiteScaledFlux : ℕ → ℝ
  continuumNullFlux : ℝ
  error : ℕ → ℝ
  error_nonneg_eventually : ∀ᶠ n in atTop, 0 ≤ error n
  error_tendsto_zero : Tendsto error atTop (𝓝 0)
  source_error_bound :
    ∀ᶠ n in atTop, |finiteScaledFlux n - continuumNullFlux| ≤ error n

/-- The source convergence obtained from deterministic error control. -/
theorem finiteEntropySource_converges_to_nullFlux
    (B : EntropyFluxErrorControl) :
    Tendsto B.finiteScaledFlux atTop (𝓝 B.continuumNullFlux) :=
  tendsto_of_abs_sub_le_error
    B.error_nonneg_eventually B.error_tendsto_zero B.source_error_bound

/-- The named first bridge field: finite entropy source converges to an
Araki/null-energy flux target. -/
def FiniteEntropySourceConvergesToArakiFlux
    (finiteScaledFlux : ℕ → ℝ) (arakiFlux : ℝ) : Prop :=
  Tendsto finiteScaledFlux atTop (𝓝 arakiFlux)

/-- If the continuum null-flux target is the Araki flux, error control closes
the first bridge field. -/
theorem finiteEntropySource_converges_to_ArakiFlux_of_errorControl
    (B : EntropyFluxErrorControl) (arakiFlux : ℝ)
    (hAraki : arakiFlux = B.continuumNullFlux) :
    FiniteEntropySourceConvergesToArakiFlux B.finiteScaledFlux arakiFlux := by
  unfold FiniteEntropySourceConvergesToArakiFlux
  rw [hAraki]
  exact finiteEntropySource_converges_to_nullFlux B

/-! ## 3. RSS/Poisson-style error budget -/

/-- The standard multiplicative error budget from counting window `epsilon`
and curvature bias `b`, applied to interval scale `S`. -/
def rssPoissonError (epsilon b S : ℝ) : ℝ :=
  (epsilon + b + epsilon * b) * S

/-- The RSS/Poisson error budget is nonnegative when its components are. -/
theorem rssPoissonError_nonneg
    {epsilon b S : ℝ} (heps : 0 ≤ epsilon) (hb : 0 ≤ b) (hS : 0 ≤ S) :
    0 ≤ rssPoissonError epsilon b S := by
  unfold rssPoissonError
  positivity

/-- If the counting window and curvature bias both vanish at high density,
then the fixed-scale RSS/Poisson error budget vanishes. -/
theorem rssPoissonError_tendsto_zero
    (epsilon b : ℕ → ℝ) (S : ℝ)
    (heps : Tendsto epsilon atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n => rssPoissonError (epsilon n) (b n) S) atTop (𝓝 0) := by
  unfold rssPoissonError
  have hsum : Tendsto
      (fun n => epsilon n + b n + epsilon n * b n) atTop (𝓝 0) := by
    simpa using (heps.add hb).add (heps.mul hb)
  simpa using hsum.mul_const S

/-- Eventually nonnegative RSS/Poisson error budget. -/
theorem rssPoissonError_eventually_nonneg
    (epsilon b : ℕ → ℝ) {S : ℝ}
    (heps : ∀ᶠ n in atTop, 0 ≤ epsilon n)
    (hb : ∀ᶠ n in atTop, 0 ≤ b n)
    (hS : 0 ≤ S) :
    ∀ᶠ n in atTop, 0 ≤ rssPoissonError (epsilon n) (b n) S := by
  filter_upwards [heps, hb] with n he hb'
  exact rssPoissonError_nonneg he hb' hS

/-- RSS/Poisson error control implies flux convergence. -/
theorem finiteEntropySource_converges_of_rssPoissonError
    (finiteScaledFlux : ℕ → ℝ) (continuumNullFlux : ℝ)
    (epsilon b : ℕ → ℝ) (S : ℝ)
    (heps_nonneg : ∀ᶠ n in atTop, 0 ≤ epsilon n)
    (hb_nonneg : ∀ᶠ n in atTop, 0 ≤ b n)
    (hS : 0 ≤ S)
    (heps_zero : Tendsto epsilon atTop (𝓝 0))
    (hb_zero : Tendsto b atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      |finiteScaledFlux n - continuumNullFlux| ≤
        rssPoissonError (epsilon n) (b n) S) :
    Tendsto finiteScaledFlux atTop (𝓝 continuumNullFlux) :=
  tendsto_of_abs_sub_le_error
    (rssPoissonError_eventually_nonneg epsilon b heps_nonneg hb_nonneg hS)
    (rssPoissonError_tendsto_zero epsilon b S heps_zero hb_zero)
    hbound

/-! ## 3b. Physical horizon-hit cell estimator -/

/-- A concrete finite horizon-hit estimator, decomposed into finitely many
horizon cells.

For cell `i` at refinement level `n`, `hitCount n i` is the finite horizon-hit
count, `density n` is the sprinkling density, and `power` is the scaling
exponent.  The finite cell flux is therefore

```text
scaledHorizonSource (density n) power (hitCount n i).
```

The fields `cellError_*` encode the analytic/geometric estimates that still
need to be instantiated for a physical causal-growth law. -/
structure HorizonHitSourceEstimator (ι : Type*) [Fintype ι] where
  density : ℕ → ℝ
  power : ℕ
  hitCount : ℕ → ι → ℝ
  cellWeight : ι → ℝ
  continuumCellFlux : ι → ℝ
  cellWeight_nonneg : ∀ i, 0 ≤ cellWeight i
  cellError : ℕ → ι → ℝ
  cellError_nonneg_eventually : ∀ i, ∀ᶠ n in atTop, 0 ≤ cellError n i
  cellError_tendsto_zero : ∀ i, Tendsto (fun n => cellError n i) atTop (𝓝 0)
  cell_error_bound : ∀ᶠ n in atTop, ∀ i,
    |scaledHorizonSource (density n) power (hitCount n i) -
      continuumCellFlux i| ≤ cellError n i

namespace HorizonHitSourceEstimator

/-- Weighted finite flux from horizon-hit counts. -/
noncomputable def finiteScaledFlux {ι : Type*} [Fintype ι]
    (H : HorizonHitSourceEstimator ι) : ℕ → ℝ :=
  fun n => ∑ i,
    H.cellWeight i *
      scaledHorizonSource (H.density n) H.power (H.hitCount n i)

/-- Weighted continuum null-flux target. -/
noncomputable def continuumFlux {ι : Type*} [Fintype ι]
    (H : HorizonHitSourceEstimator ι) : ℝ :=
  ∑ i, H.cellWeight i * H.continuumCellFlux i

/-- Weighted total cell-error budget. -/
noncomputable def totalError {ι : Type*} [Fintype ι]
    (H : HorizonHitSourceEstimator ι) : ℕ → ℝ :=
  fun n => ∑ i, H.cellWeight i * H.cellError n i

/-- Pointwise cell-error bounds imply a bound on the weighted horizon flux. -/
theorem abs_finiteScaledFlux_sub_continuumFlux_le_totalError
    {ι : Type*} [Fintype ι]
    (H : HorizonHitSourceEstimator ι) (n : ℕ)
    (hcell : ∀ i,
      |scaledHorizonSource (H.density n) H.power (H.hitCount n i) -
        H.continuumCellFlux i| ≤ H.cellError n i) :
    |H.finiteScaledFlux n - H.continuumFlux| ≤ H.totalError n := by
  unfold finiteScaledFlux continuumFlux totalError
  have hsumdiff :
      (∑ i, H.cellWeight i *
          scaledHorizonSource (H.density n) H.power (H.hitCount n i)) -
        (∑ i, H.cellWeight i * H.continuumCellFlux i)
        =
        ∑ i,
          (H.cellWeight i *
              scaledHorizonSource (H.density n) H.power (H.hitCount n i) -
            H.cellWeight i * H.continuumCellFlux i) := by
    rw [Finset.sum_sub_distrib]
  rw [hsumdiff]
  calc
    |∑ i,
        (H.cellWeight i *
            scaledHorizonSource (H.density n) H.power (H.hitCount n i) -
          H.cellWeight i * H.continuumCellFlux i)|
        ≤ ∑ i,
            |H.cellWeight i *
                scaledHorizonSource (H.density n) H.power (H.hitCount n i) -
              H.cellWeight i * H.continuumCellFlux i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, H.cellWeight i * H.cellError n i := by
          apply Finset.sum_le_sum
          intro i _
          have hterm :
              H.cellWeight i *
                  scaledHorizonSource (H.density n) H.power (H.hitCount n i) -
                H.cellWeight i * H.continuumCellFlux i
              =
                H.cellWeight i *
                  (scaledHorizonSource (H.density n) H.power (H.hitCount n i) -
                    H.continuumCellFlux i) := by
            ring
          rw [hterm, abs_mul, abs_of_nonneg (H.cellWeight_nonneg i)]
          exact mul_le_mul_of_nonneg_left (hcell i) (H.cellWeight_nonneg i)

/-- The weighted total cell-error budget is eventually nonnegative. -/
theorem totalError_eventually_nonneg
    {ι : Type*} [Fintype ι]
    (H : HorizonHitSourceEstimator ι) :
    ∀ᶠ n in atTop, 0 ≤ H.totalError n := by
  have hcell : ∀ᶠ n in atTop, ∀ i, 0 ≤ H.cellError n i :=
    eventually_all.mpr H.cellError_nonneg_eventually
  filter_upwards [hcell] with n hn
  unfold totalError
  exact Finset.sum_nonneg
    (fun i _ => mul_nonneg (H.cellWeight_nonneg i) (hn i))

/-- The weighted total cell-error budget tends to zero when each cell error
tends to zero. -/
theorem totalError_tendsto_zero
    {ι : Type*} [Fintype ι]
    (H : HorizonHitSourceEstimator ι) :
    Tendsto H.totalError atTop (𝓝 0) := by
  unfold totalError
  simpa using tendsto_finset_sum Finset.univ
    (fun i _ => (H.cellError_tendsto_zero i).const_mul (H.cellWeight i))

/-- The source-error bound required by `EntropyFluxErrorControl`. -/
theorem source_error_bound
    {ι : Type*} [Fintype ι]
    (H : HorizonHitSourceEstimator ι) :
    ∀ᶠ n in atTop,
      |H.finiteScaledFlux n - H.continuumFlux| ≤ H.totalError n := by
  filter_upwards [H.cell_error_bound] with n hn
  exact H.abs_finiteScaledFlux_sub_continuumFlux_le_totalError n hn

/-- The finite physical horizon-hit source converges to the weighted
continuum null flux under per-cell vanishing error control. -/
theorem finiteScaledFlux_converges_to_continuumFlux
    {ι : Type*} [Fintype ι]
    (H : HorizonHitSourceEstimator ι) :
    Tendsto H.finiteScaledFlux atTop (𝓝 H.continuumFlux) :=
  tendsto_of_abs_sub_le_error
    H.totalError_eventually_nonneg
    H.totalError_tendsto_zero
    H.source_error_bound

/-- The physical horizon-hit estimator instantiates the abstract
`EntropyFluxErrorControl` bridge. -/
noncomputable def toEntropyFluxErrorControl
    {ι : Type*} [Fintype ι]
    (H : HorizonHitSourceEstimator ι) : EntropyFluxErrorControl where
  finiteScaledFlux := H.finiteScaledFlux
  continuumNullFlux := H.continuumFlux
  error := H.totalError
  error_nonneg_eventually := H.totalError_eventually_nonneg
  error_tendsto_zero := H.totalError_tendsto_zero
  source_error_bound := H.source_error_bound

/-- If the weighted continuum null-flux target is identified with the Araki
flux, the physical horizon-hit estimator closes the first continuum bridge
field. -/
theorem closes_ArakiFlux_bridge
    {ι : Type*} [Fintype ι]
    (H : HorizonHitSourceEstimator ι) (arakiFlux : ℝ)
    (hAraki : arakiFlux = H.continuumFlux) :
    FiniteEntropySourceConvergesToArakiFlux H.finiteScaledFlux arakiFlux :=
  finiteEntropySource_converges_to_ArakiFlux_of_errorControl
    H.toEntropyFluxErrorControl arakiFlux hAraki

end HorizonHitSourceEstimator

/-! ## 4. Finite birth-law positivity -/

/-- A finite normalized nonnegative birth law over possible next-birth
precursors. -/
structure FiniteBirthLaw (ι : Type*) [Fintype ι] where
  p : ι → ℝ
  nonneg : ∀ i, 0 ≤ p i
  sum_one : (∑ i, p i) = 1

/-- Exponential-tilt partition for a finite birth law. -/
noncomputable def FiniteBirthLaw.partition
    {ι : Type*} [Fintype ι] (P : FiniteBirthLaw ι)
    (J : ι → ℝ) (lambda : ℝ) : ℝ :=
  ∑ i, P.p i * Real.exp (lambda * J i)

/-- Normalized nonnegative finite birth laws have strictly positive
exponential-tilt partition for every source strength. -/
theorem FiniteBirthLaw.partition_pos
    {ι : Type*} [Fintype ι] (P : FiniteBirthLaw ι)
    (J : ι → ℝ) (lambda : ℝ) :
    0 < P.partition J lambda := by
  have h_exists : ∃ i, 0 < P.p i := by
    by_contra h
    push_neg at h
    have hzero : ∀ i, P.p i = 0 := by
      intro i
      exact le_antisymm (h i) (P.nonneg i)
    have hsum0 : (∑ i, P.p i) = 0 := by
      simp [hzero]
    linarith [P.sum_one, hsum0]
  rcases h_exists with ⟨i0, hi0⟩
  unfold FiniteBirthLaw.partition
  refine Finset.sum_pos' ?_ ⟨i0, Finset.mem_univ i0, ?_⟩
  · intro i _
    exact mul_nonneg (P.nonneg i) (le_of_lt (Real.exp_pos _))
  · exact mul_pos hi0 (Real.exp_pos _)

/-! ## 5. Passing exact finite focusing derivatives to the limit -/

/-- A sequence of finite exact entropy-focusing derivative identities. -/
structure FiniteEntropyFocusingDerivativeFamily where
  lambda : ℝ
  areaDeriv : ℕ → ℝ
  klDeriv : ℕ → ℝ
  exact_law : ∀ n, klDeriv n = -lambda * areaDeriv n

/-- If the finite area-focusing derivative has a continuum limit, the KL
derivative has the corresponding `-lambda`-scaled limit. -/
theorem kl_deriv_converges_of_area_deriv_converges
    (F : FiniteEntropyFocusingDerivativeFamily) (areaLimit : ℝ)
    (hArea : Tendsto F.areaDeriv atTop (𝓝 areaLimit)) :
    Tendsto F.klDeriv atTop (𝓝 (-F.lambda * areaLimit)) := by
  have hfun : F.klDeriv = fun n => -F.lambda * F.areaDeriv n := by
    funext n
    exact F.exact_law n
  rw [hfun]
  simpa using hArea.const_mul (-F.lambda)

/-- A combined bridge object for the first remaining continuum field:
finite source convergence plus finite exact entropy-focusing derivatives. -/
structure EntropyFluxLimitBridge where
  source : EntropyFluxErrorControl
  focusing : FiniteEntropyFocusingDerivativeFamily
  continuumAreaDeriv : ℝ
  area_deriv_tendsto :
    Tendsto focusing.areaDeriv atTop (𝓝 continuumAreaDeriv)
  arakiFlux : ℝ
  arakiFlux_eq_nullFlux : arakiFlux = source.continuumNullFlux

/-- The bridge closes the first field and transports the exact finite
entropy-focusing derivative law to the continuum derivative target. -/
theorem entropyFluxLimitBridge_closes_first_field
    (B : EntropyFluxLimitBridge) :
    FiniteEntropySourceConvergesToArakiFlux
        B.source.finiteScaledFlux B.arakiFlux
      ∧ Tendsto B.focusing.klDeriv atTop
        (𝓝 (-B.focusing.lambda * B.continuumAreaDeriv)) := by
  constructor
  · exact finiteEntropySource_converges_to_ArakiFlux_of_errorControl
      B.source B.arakiFlux B.arakiFlux_eq_nullFlux
  · exact kl_deriv_converges_of_area_deriv_converges
      B.focusing B.continuumAreaDeriv B.area_deriv_tendsto

#print axioms scaledHorizonSource_exact_of_hits_eq
#print axioms flat_rindler_scaledFlux_converges
#print axioms tendsto_of_abs_sub_le_error
#print axioms finiteEntropySource_converges_to_ArakiFlux_of_errorControl
#print axioms finiteEntropySource_converges_of_rssPoissonError
#print axioms HorizonHitSourceEstimator.finiteScaledFlux_converges_to_continuumFlux
#print axioms HorizonHitSourceEstimator.closes_ArakiFlux_bridge
#print axioms FiniteBirthLaw.partition_pos
#print axioms kl_deriv_converges_of_area_deriv_converges
#print axioms entropyFluxLimitBridge_closes_first_field

end UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
