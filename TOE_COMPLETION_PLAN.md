# TOE Completion Plan

Status: working plan for closing the repo's remaining theory-of-everything
gaps.  This is not a claim that the gaps are closed.

Date: 2026-08-20

## Scope Rule

Every claim should live in one of five buckets:

```text
proved finite theorem
conditional bridge
numerical evidence
physical conjecture
falsifiable prediction
```

The repo is strongest when each public claim points to a theorem, script,
dataset, or explicitly named assumption.

## Gates

### Gate 1: Physical Causal-Growth Law

Goal: select the actual microscopic dynamics.

Definition of done:

```text
one label-invariant, normalized, quantum-consistent causal-growth law
whose source terms are computed from parent order data
```

Open work:

- prove normalization/projective consistency for the physical law;
- prove strong positivity or the intended quantum-measure replacement;
- remove external geometric or embedding oracles from source selection.

### Gate 2: Physical Hauptvermutung Distortion

Goal: make manifold-likeness a finite certificate target.

Implemented start:

```text
physicalHauptvermutungDistortion
physicalHauptvermutungTotalDistortion
physicalHauptvermutungTotalDistortion_eq_zero_iff
```

The current aggregate has four finite components:

```text
countWindow
curvatureBias
spectralLocality
bridge-census transport defect
```

The bridge-census component is exact:

```text
cSpecBridgeTotalDistortion_pos_iff_candidate_ne_canonical
cSpecBridgeTotalDistortion_strict_min_of_ne
physicalHauptvermutungTotalDistortion_strict_transport_min_of_ne
```

Definition of done:

```text
the aggregate zero set is equivalent to the intended finite
order-to-geometry certificate, component by component
```

### Gate 3: Dynamical Contraction

Goal: prove physical growth drives the aggregate distortion down.

Implemented start:

```text
PhysicalGrowthSuppliesRepairSource
physicalGrowthSuppliesRepairSource_contracts
physicalGrowthSuppliesRepairSource_strictly_contracts
physicalGrowthSuppliesRepairSource_protected_and_contracts
PhysicalGrowthRepairRefinement
physicalGrowthRepairRefinement_protected_and_contracts
```

This interface says: if physical growth supplies a source that protects the
horizon channel, descends the aggregate distortion, and has a controlled
finite update remainder, then the next aggregate distortion is strictly
smaller.

The refinement wrapper records this certificate at every finite stage and
proves each step preserves the horizon channel while strictly contracting the
tracked aggregate total:

```text
linearResponse(S_n, c_n - J_n) = 0
quadraticResponse(S_n, c_n - J_n) = 0
D_{n+1} < D_n
```

Definition of done:

```text
D_{n+1} <= q_n D_n, eventually with q_n <= q < 1
```

while first-order and second central horizon-area responses remain protected.

### Gate 4: Horizon-To-Einstein Limit

Goal: remove the remaining analytic caveats behind GR recovery.

Open work:

- prove finite horizon-hit estimators converge to Araki/null flux;
- prove per-cell errors vanish under the physical refinement;
- derive the null-balance hypotheses from the physical law;
- recover the semiclassical Einstein equation in the continuum limit.

### Gate 5: QFT And Standard Model IR Limit

Goal: recover known low-energy physics from the same dynamics.

Open work:

- construct the effective Hilbert space and local QFT limit;
- recover propagators, spin/statistics, gauge fields, and renormalization;
- connect finite Standard Model algebra to the same infrared limit;
- derive the parameter-identification chain instead of assuming it.

### Gate 6: Cosmology And Black Holes

Goal: cover sectors a complete theory cannot skip.

Open work:

- initial condition or cosmological measure;
- cosmological constant/dark-energy mechanism;
- dark matter prediction or exclusion;
- black-hole entropy, evaporation, and information recovery;
- compatibility with CMB, structure formation, and gravitational waves.

### Gate 7: External Tests

Goal: make the theory scientifically sharp.

Open work:

- freeze predictions before comparison;
- attach uncertainty estimates;
- record decisive future tests;
- keep a failure ledger.

## Immediate Next Theorem Targets

1. Derive each non-bridge aggregate component from order data.
2. Prove each component is quotient-invariant.
3. Prove each component has a strict zero-set theorem like the bridge-census
   component.
4. Instantiate `PhysicalGrowthSuppliesRepairSource` from the actual
   causal-growth law instead of assuming it.
5. Upgrade stepwise strict contraction to a geometric or summable-rate
   convergence theorem.
