# Horizon-Invisible Geometric Relaxation

Status: finite machine-checked mechanism and research lead, not an
experimental discovery and not a completed proof of continuum quantum gravity.

## Citation Anchor

This note builds on the horizon-entropy bridge used throughout the audit:

Philipp Dorau and Albert Much, "From Quantum Relative Entropy to the
Semiclassical Einstein Equations," arXiv:2510.24491v3 [hep-th], last revised
3 Mar 2026, Phys. Rev. Lett. 136, 091602 (2026), DOI:
10.1103/lmq8-nsty; arXiv DOI: 10.48550/arXiv.2510.24491.

Dorau--Much give the continuum-side target: quantum relative entropy on a
horizon supplies the energy-flux/area-variation relation that reproduces the
semiclassical Einstein equations.  The finite repo work asks a sharper causal
set question: can a growth law also repair order-to-geometry defects without
renormalizing that same local horizon channel?

## New Physics Lead

The candidate principle is:

```text
causal growth has two locally distinct response sectors

J       = horizon entropy/focusing source
S_perp  = geometric defect-relaxation source
```

The horizon source `J` carries the Dorau--Much/Jacobson focusing response.
The defect source `S_perp` is projected away from `J` and then oriented toward
descent of the displayed Hauptvermutung distortion observable.  If it also has
zero second-order horizon leakage, Lean proves that it can improve the
geometry certificate while remaining invisible to the local horizon area
response through the finite second central order.

This is the new finite mechanism: a causal-set analogue of a
Lyapunov/Ricci-flow-like geometry relaxation, but one that is thermodynamically
silent at local horizons.  In physical terms, it says that the microscopic
growth law may contain a state-dependent "repair" drive for manifold-likeness
that does not appear as extra stress-energy in the horizon entropy balance.

## Formal Content

The key finite conditions are:

```text
Cov(S_perp, J) = 0
Cov(J, centered(S_perp)^2) = 0
linearResponse(S_perp, Distortion) != 0
```

The first condition removes first-order horizon contamination.  The second
removes the finite second central horizon leakage.  The third gives a genuine
geometric descent direction after local sign orientation.

The latest Lean corollary packages the bridge:

```text
orientedProtectedHauptvermutungDistortionSource_bridge
```

It combines these previously checked facts:

```text
linearResponse_orientTowardObservable_eq_neg_abs
covariance_orientTowardObservable_horizon
horizonSecondOrderLeakage_orientTowardObservable
orientedProtectedHauptvermutungDistortionSource_descentRate_positive
ProtectedHauptvermutungDistortionSource.preserves_horizon_and_descends_distortion
ProtectedHauptvermutungDistortionDescent.horizon_protection_and_distortion_tendsto_zero
```

Read literally, the theorem says: once a raw defect source is horizon-clean and
leakage-clean, the parent-local sign choice makes it descend the named
Hauptvermutung distortion observable, while the finite horizon-area response
still vanishes through second order.

## Numerical Evidence

The current gate probe uses the certificate-basis direction

```text
residual(cert_pairConsistency) + 3.5035 residual(-gap)
```

against the displayed distortion target `cert_scaledDistortionBound`.

On the `n=18`, `paths=4`, seed-53 sample, a global fixed orientation descends
the target on 28/35 parents.  With parent-local orientation, descent is
positive on 35/35 parents, and the half-remainder gate passes on all parents
at steps `0.005` and `0.010`.

That is not a uniform refinement proof.  It is evidence that the finite theorem
is pointing at the correct physical shape: the source should be allowed to
depend on the parent state.

## Physical Interpretation

The usual danger is that a proposed microscopic repair of geometry changes the
same horizon flux that is supposed to give the Einstein equation.  The new
mechanism separates the two effects algebraically.

In lay terms:

```text
the horizon channel tells spacetime how to curve in response to energy;
the hidden relaxation channel nudges the discrete order toward a smoother
manifold-like geometry without adding new apparent energy at the horizon.
```

If this survives refinement and is derived from the actual causal-growth
dynamics, it would make the Hauptvermutung less like an external assumption and
more like a dynamical attractor: manifold-likeness would be selected by a
local finite relaxation law that leaves the semiclassical horizon balance
intact.

## Testable Next Predictions

The research program now has concrete internal predictions:

1. Parent-local sign or coefficient selection should keep the half-remainder
   gate valid under increasing depth, path count, and independent seeds.
2. Replacing proxy errors by invariant physical certificate errors should
   preserve descent of the displayed distortion observable.
3. The oriented source should leave first-order horizon response zero and drive
   second central horizon leakage toward zero along refinement.
4. The final physical growth law should compute or approximate the oriented
   source from parent-local order data, not from external embedding data.
5. In the continuum limit, this relaxation should disappear from the local
   stress-energy/horizon-flux balance while remaining visible in convergence
   of the order-to-geometry certificate.

## What Remains

To turn this into physics rather than a finite mechanism, the repo still has to
derive the certificate source from the actual causal-growth dynamics, prove a
uniform half-remainder or equivalent contraction bound, replace the current
proxy observables with invariant physical certificate errors, and connect the
resulting refinement flow to infrared GR/QFT recovery.

The breakthrough target is therefore precise:

```text
prove that physical causal growth contains a horizon-invisible,
state-dependent geometric relaxation channel whose attractor is the
quantitative Hauptvermutung certificate.
```
