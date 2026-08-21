# Gate2 HVDistortion Swarm Notes

Scope: Agent Gate2-HVDistortion. No Lean source edits, no `.lake` writes, no
commits, no pushes.

## Current State

The bridge component is already strong in
`UnifiedTheory/Audit/KFCausalCSpecBridgeDefectObservable.lean`:

```lean
cSpecBridgeTotalDistortion_eq_zero_iff_candidate_eq_canonical
physicalHauptvermutungConvergenceCertificate_eventually_bridge_total_zero
physicalHauptvermutungConvergenceCertificate_eventually_orderRecovered
```

The remaining Gate 2 issue is the non-bridge base residual. The aggregate
currently treats

```text
countWindow, curvatureBias, spectralLocality
```

as nonnegative real channels. Lean proves that the aggregate zero set forces
these scalars to be zero, but the repo still needs named component zero-set
theorems saying what those zeros mean in finite order/geometric data.

## Missing Theorems

### 1. Algebraic Base Zero Set

Target file:
`UnifiedTheory/Audit/KFCausalCSpecBridgeDefectObservable.lean`, near
`physicalHauptvermutungBaseDistortion`.

Small theorem statement:

```lean
theorem physicalHauptvermutungBaseDistortion_eq_zero_iff
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ι -> ℝ)
    (hcount : ∀ i, 0 ≤ countWindow i)
    (hcurv : ∀ i, 0 ≤ curvatureBias i)
    (hspectral : ∀ i, 0 ≤ spectralLocality i) :
    physicalHauptvermutungBaseDistortion
      countWindow curvatureBias spectralLocality = 0 ↔
      (∀ i, countWindow i = 0) ∧
        (∀ i, curvatureBias i = 0) ∧
          (∀ i, spectralLocality i = 0)
```

This is the smallest formal next step. It packages the arithmetic part now
spread through `physicalHauptvermutungTotalDistortion_eq_zero_iff` and
`PhysicalHauptvermutungRecoveredStage.residuals_zero`.

### 2. Count-Window Semantic Zero Set

Target file:
`UnifiedTheory/Audit/KFCausalCSpecHauptvermutungPhysicalBridge.lean`, or a new
finite-zero-set file imported by it.

Needed finite residual definition, because the current certificate field
`countWindow` is only an upper bound and need not be minimal:

```lean
noncomputable def finiteCountWindowResidual
    {X ι : Type*} [Fintype X] [Fintype ι]
    (density : ℝ) (count volume : ι -> X -> X -> ℝ) : ℝ :=
  ∑ i, ∑ x, ∑ x',
    |count i x x' / (density * volume i x x') - 1|
```

Zero-set theorem:

```lean
theorem finiteCountWindowResidual_eq_zero_iff
    {X ι : Type*} [Fintype X] [Fintype ι]
    {density : ℝ} {count volume : ι -> X -> X -> ℝ}
    (hdensity : 0 < density)
    (hvolume : ∀ i x x', 0 < volume i x x') :
    finiteCountWindowResidual density count volume = 0 ↔
      ∀ i x x',
        count i x x' = density * volume i x x'
```

### 3. Curvature-Bias Semantic Zero Set

Target file:
`UnifiedTheory/Audit/KFCausalCSpecHauptvermutungPhysicalBridge.lean` or the same
new finite-zero-set file.

Needed finite residual definition:

```lean
noncomputable def finiteCurvatureBiasResidual
    {X ι : Type*} [Fintype X] [Fintype ι]
    (G : X -> X -> ℝ) (volume : ι -> X -> X -> ℝ) : ℝ :=
  ∑ i, ∑ x, ∑ x',
    |volume i x x' / ((Real.pi / 24) * (G x x') ^ 2) - 1|
```

Zero-set theorem:

```lean
theorem finiteCurvatureBiasResidual_eq_zero_iff
    {X ι : Type*} [Fintype X] [Fintype ι]
    {G : X -> X -> ℝ} {volume : ι -> X -> X -> ℝ}
    (hG : ∀ x x', 0 < G x x') :
    finiteCurvatureBiasResidual G volume = 0 ↔
      ∀ i x x',
        volume i x x' = (Real.pi / 24) * (G x x') ^ 2
```

### 4. Spectral-Locality / Pair-Consistency Semantic Zero Set

This is the most important naming gap. In
`KFCausalCSpecHorizonOrthogonalDefect.lean` and
`KFCausalCSpecHauptvermutungPhysicalBridge.lean`, the third quantitative
Hauptvermutung channel is `pairConsistency`; in
`KFCausalCSpecBridgeDefectObservable.lean`, the aggregate calls the third
channel `spectralLocality`.

Target theorem should either rename the channel downstream or explicitly bridge:

```lean
def spectralLocalityOfPairConsistency
    {ι : Type*} (pairConsistency : ι -> ℝ) : ι -> ℝ :=
  fun i => pairConsistency i / 2

theorem spectralLocalityOfPairConsistency_eq_zero_iff
    {ι : Type*} (pairConsistency : ι -> ℝ) :
    (∀ i, spectralLocalityOfPairConsistency pairConsistency i = 0) ↔
      ∀ i, pairConsistency i = 0
```

Then define the finite semantic residual:

```lean
noncomputable def finitePairConsistencyResidual
    {X Y ι : Type*} [AddCommGroup Y] [Module ℝ Y]
    [Fintype X] [Fintype ι]
    (B : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (chart : ι -> X -> Y) : ℝ :=
  ∑ i, ∑ j, ∑ x, ∑ x',
    |B ((chart i x - chart i x') - (chart j x - chart j x'))
       ((chart i x - chart i x') - (chart j x - chart j x'))|
```

Zero-set theorem:

```lean
theorem finitePairConsistencyResidual_eq_zero_iff
    {X Y ι : Type*} [AddCommGroup Y] [Module ℝ Y]
    [Fintype X] [Fintype ι]
    (B : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (chart : ι -> X -> Y) :
    finitePairConsistencyResidual B chart = 0 ↔
      ∀ i j x x',
        B ((chart i x - chart i x') - (chart j x - chart j x'))
          ((chart i x - chart i x') - (chart j x - chart j x')) = 0
```

This makes the third channel's zero set equal exact overlap consistency of the
finite chart family.

## Smallest Next Step

Add only theorem 1 first:
`physicalHauptvermutungBaseDistortion_eq_zero_iff`.

It should be a short proof by `Finset.sum_eq_zero_iff_of_nonneg`,
`Finset.sum_eq_zero`, and `linarith`. After that, the semantic component work
can proceed one channel at a time, starting with `finitePairConsistencyResidual`
because it has no division or curvature-expansion side conditions.
