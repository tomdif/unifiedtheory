# The Fused Arc — Terminus

The continuum matter-measure thread and the discrete growth-arrow arc met at one
object: the chirality Z2. This is the consolidated, grade-tagged terminus. It is
not a proof of the framework; it is a map of exactly where the road ends.

## The fused claim

> **The weak interaction is left-handed because time runs forward.** The causal
> growth arrow selects −i (Ξ=+1, P_L) at every linked birth; a connection defect
> carries a chiral adjoint fermion zero mode whose handedness is that same sign;
> and the discrete chirality Z2 and the continuum Chern–Simons sign(γ) are one
> Z2, locked by the arrow. Handedness, time-arrow, and CS sign are a single
> choice — not three.

The absolute *name* of "left" is a convention, provably underivable (reflection
covariance admits both branches). What is derived is that there is **one** such
choice, shared across both arcs.

## In front of the wall — built and checked

**Unconditional** (Lean-grade / axiom-grade / theorem):

| Result | Grade | Artifact |
|---|---|---|
| Adjoint fermion: anomaly-free, massless, Cl(3) Weyl spinor | Lean | `ConnectionDefect{Adjoint,Massless}`, `AdjointCarrierSpinor` |
| Per-defect chirality arrow-LOCKED (one Z2) | axiom | `ArrowChiralityLock` + `ContinuumChiralityFlip` (bridge = order-faithfulness axiom) |
| Discrete selection: arrow → −i → Ξ=+1 → P_L | Lean | `KFCausalSetGrowthArrowChirality` (repo) |
| Census identities: Σ orientationSource = 0; arrow-oddness | Lean | `CensusIdentities` |
| Census imprint: N_left = L at birth (N_right = 0 identically) | theorem | selection theorem + definition |
| Continuum flip: time reversal ⇒ S_III → −S_III | Lean+axiom | `ContinuumChiralityFlip` |

**Conditional on one named ansatz:**

| Result | Condition |
|---|---|
| Census EXISTENCE (net cosmic handedness) | record PERSISTENCE = the **tensor-factorization ansatz** — the birth-imprinted chirality surviving as the defect acquires future structure (goes static-neutral per `bulk_cancellation`). The imprint is a theorem; only its persistence is conditional. |

Attribution note: the census asymmetry is sourced by the **growth process** (histories
are intrinsically oriented), NOT by any special measure — even symmetric
percolation returns ⟨record⟩ = L. The phase-weighted measure did no work here.

Architecture note: totality is a feature. The record is 100%-left, not
slightly-biased; static compensation is handled by `bulk_cancellation`
(Σ orientationSource = 0). This is the discrete form of "anomaly cancels
globally, chirality is what the records carry," and it matches the fully-left
weak current better than a small-excess picture.

## Behind the wall — R3 (the Lorentzian continuum bridge)

One wall, the field-wide open problem the main ledger already names. Four riders,
each named, none invented to park a problem:

1. **Existence of an order-faithful Φ** — conditionalizes even the chirality lock
   ("for every order-faithful continuum, the arrow fixes sign(γ)"). No metric
   data is needed for the lock's *logic* (order-faithfulness suffices); that a Φ
   exists at all is R3's.
2. **Census continuum assembly** — a defect-specific, director-valued winding
   density. Probed and found behind the wall: a scalar source cannot be both
   local and defect-specific (achiral crowns carry generic nonzero flux); a
   genuine winding needs a director (angle) field = continuum structure. Only the
   density's closed-sum-zero property came forward (= `bulk_cancellation`, Lean).
3. **Magnitude** of γ (and α, β) from the discrete precursor.
4. **Multiplet count** — 2-dim Cartan carrier → octet + triplet via the index.

## The single highest-leverage move in front of the wall

Deriving the **tensor-factorization ansatz** discharges the census persistence
condition AND the entire evidence layer at once — it is the one named gate
everything conditional waits behind. That, and the R3 program itself, are the
remaining moves. They are papers, not sessions.

## Artifacts

Seven axiom-clean Lean files (`ConnectionDefectAdjoint`, `ConnectionDefectMassless`,
`AdjointCarrierSpinor`, `ArrowChiralityLock`, `ContinuumChiralityFlip`,
`CensusIdentities`, + the repo's discrete-chirality files); eight analysis scripts
(`rg_falsification`, `unify_search`, `unify_combos`, `zero_mode`,
`zero_mode_derive`, `census`, `winding_probe`, `phase_census`, `winding_density`);
this doc and `MATTER_MEASURE_SCOPE.md §0–7k` carrying the full dependency trail.

## Terminus

One wall the whole field shares; one named condition in front of it (the
factorization ansatz); one underivable convention (the absolute name of "left");
everything else machine-checked or theorem. The bracketing pattern of the final
stretch — overclaim, withdrawal, partial reversal, each landing on a sharper
observable — was the process working. The right response to reaching a wall the
whole field shares is to pin it, grade it, and stop.
