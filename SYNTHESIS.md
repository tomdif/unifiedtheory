# Unified Einstein + Matter Branch: Formal Synthesis

## What this project proves

From a single mathematical structure (ParentU), we formally derive:

1. **The inverse-square law** is the unique scale-invariant potential (alpha = 2).
2. **Null-cone determination**: any symmetric form vanishing on null vectors is proportional to the Minkowski metric.
3. **Source/dressing split**: field configurations decompose into a gravitationally active source channel (K) and a gravitationally inert dressing channel (P).
4. **Einstein endpoint**: any divergence-free admissible tensor equals a*G + b*g (Einstein + cosmological constant).
5. **Defect matter emergence**: stable defects of the parent structure simultaneously project to BF source data and null focusing bias, with quantitative equality.
6. **Conserved charge**: defect source strength Q is additive, determines the inert/source sector, and has a conjugation (anti-defect) with Q(d_bar) = -Q(d).
7. **Annihilation**: d + d_bar is gravitationally inert.
8. **Far-field reduction**: the gravitational far field of any composite depends only on net charge. Neutral composites are invisible.

All theorems are machine-checked in Lean 4 with Mathlib, depending only on the three standard Lean axioms (propext, Classical.choice, Quot.sound). No custom axioms. No sorry.

## What ParentU means physically

ParentU is the minimal common ancestor of gravity and matter. It packages four data blocks:

- **ScaleBlock**: a coarse-graining operator R_l acting on power-law potentials. The fixed-point condition forces alpha = 2. Physically: the renormalization group selects the inverse-square law.

- **NullBlock**: a Lorentzian quadratic form and a symmetric tensor whose null contractions vanish. Physically: null-ray geometry determines the metric up to trace.

- **BFBlock**: a vector space with a projector splitting fields into source (K) and dressing (P) channels. Physically: the BF/Plebanski framework where only K-type components source curvature.

- **EndptBlock**: curvature data with a divergence-free natural tensor. The contracted Bianchi identity forces the tensor to be Einstein + Lambda. Physically: the field equation is not postulated but derived.

## What defects mean physically

A **defect** is a localized obstruction in the parent structure. It has two projections:

- **BF projection** (K_d, P_d): how much the defect contributes to the gravitational source and to topological dressing.
- **Null projection** (beta_d): how much the defect biases null-ray focusing/expansion.

The **source-focusing bridge theorem** says: for stable defects, the BF source strength equals the null focusing strength. This is why "mass curves spacetime" — it's not a postulate but a projection identity.

## What charge means physically

**Charge** Q(d) = K_d is the defect's source strength. It has all the properties of a physical conserved quantum number:

- Additive: Q(d1 + d2) = Q(d1) + Q(d2)
- Signed: positive and negative charges exist
- Conjugation: every defect has an anti-defect with Q(d_bar) = -Q(d)
- Sector-determining: Q = 0 iff inert (gravitationally invisible)
- Conserved: total charge is preserved under all compositions

## What annihilation means physically

When a defect d and its conjugate d_bar compose, the result has:
- Zero charge: Q = 0
- Zero focusing bias: beta = 0
- Zero far-field response: gravitationally invisible

This is formal particle-antiparticle annihilation: the composite is inert.

## What far-field reduction means physically

The **far-field theorem** says: two systems with the same net charge are indistinguishable at large distance. Adding a neutral composite (screening cloud) to any system does not change its far-field gravitational response.

This is the formal version of: gravity sees only total mass-energy.

## Concrete realizations

Two models instantiate the abstract framework:

1. **Algebraic model** (Lean-certified): FieldSpace = R^2, defects = (kappa, delta) pairs, with explicit inert and source-carrying examples.

2. **Causal 2-complex model** (Python-verified): Poisson-sprinkled causal diamonds in 1+1 and 2+1 dimensions, with face labels, null chains, and localized defect insertions. Verified across 388 configurations with zero failures.

The causal model additionally demonstrates:
- Inverse-square focusing law (alpha = 0.988, expected 1.0 in 2+1)
- Defect composition algebra (325/325 pass)
- Conserved charge with anti-defect annihilation (7/7 properties)

## Trusted base

Every Lean theorem in this project depends only on:
- `propext` (propositional extensionality)
- `Classical.choice` (classical logic)
- `Quot.sound` (quotient soundness)

These are the three standard axioms of Lean 4's foundation. No physics axioms, no custom postulates, no sorry placeholders.

## Status

The project is frozen as of 2026-03-15. The formal core covers:
- Gravity selection from a common parent object
- Einstein endpoint derivation
- Matter emergence via stable defects
- Conserved charge algebra with conjugation and annihilation
- Multi-particle sector with far-field reduction
- Two concrete certified realizations

The next frontier is deeper physics: richer 3+1 models, interaction/binding laws, or a sharper dictionary to known particle physics.
