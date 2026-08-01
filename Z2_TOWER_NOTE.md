# The ℤ₂ tower theorem (statement, reduction, and what remains)

**2026-08-01.**  Referee's formulation adopted: the three fan knobs are
Cauchy sequences in ℤ₂, and the unbounded-height statement is the
existence of three 2-adic integers whose truncations realize every
height.

## Statement (conjecture, h ≤ 16 verified)

There exist w₂*, w₃*, w₄* ∈ ℤ₂ such that for every h ≥ 6, the fan
causet with chain z₁ < … < z_h and widths given by (sufficiently deep
truncations of) w₂*, w₃*, w₄* at attachment depths 2, 3, 4 — all
deeper fans empty — is hereditarily real at ε = 1/4, φ = 8π.  Data:
w₄* = 27 exactly (constant across six modulus doublings), w₃* ≡ 175
(mod 2⁸), w₂* ≡ 63 (mod 2¹²), residues stable from h = 9 through 16
(fan_tower_2adic.log).

## The compactness reduction (proved)

Let S_h ⊆ ℤ₂³ be the solution set of the level conditions 4..h (each
condition is a congruence, hence S_h is closed; S_h ⊇ S_{h+1}).  ℤ₂³
is compact, so IF every S_h is nonempty, the nested intersection
∩S_h is nonempty and any element is the required triple: **"solvable
at every finite height" already implies "witnessed by three 2-adic
integers."**  The theorem therefore reduces entirely to: S_h ≠ ∅ for
all h — verified through h = 16 by exact elimination + jump
verification.

## The remaining lemma and its case structure

Level h+1 adds one congruence whose deepest term is c_{h-1}·w₂ with
coefficient 2-content governed by P(h-1), P(k) = (k² − 13k + 18)/2:
P(k) is odd iff k ≡ 0, 1 (mod 4).  In the odd case the new condition
has a unit on w₂'s fresh bits and is solvable outright; in the even
case (k ≡ 2, 3 mod 4) solvability must be routed through w₃/w₄'s
shallower terms — this alternation is visible in the data (the pin
depth of w₂ advances unevenly: 6, 8, 8, 10, 14, 16, 17, 19, 22, 24
bits at h = 6..15).  Proving the even-case step closes the theorem
and retires the height question permanently.

## The scaling law, stated from the mechanism

w₂'s pinned residue deepens ~2 bits per level asymptotically, so the
minimal fan witness has n(h) ~ w₂ ~ 2^{2h−O(1)}: **h ≤ ½·log₂ n + O(1)
in the achieved direction.**  DATASET CAVEAT (referee): the minimal
representatives 22, 53, 177, 274, 4371, 53268, 98325, … have noisy
consecutive ratios (2.4, 3.3, 1.5, 16, 12, 1.8, …) because the pin
depth advances unevenly (see above) and because "minimal
representative" at h = 8 is the true lattice minimum (residue sweep)
while h ≥ 9 minima are smallest-representative choices — the law
rests on the bit-deepening mechanism, not on fitting these points.
The h = 9 entry resolves the apparent anomaly: n = 274 = 9 + (63 +
175 + 27 + 9·0) is the smallest-representative total, consistent with
the pinned residues, not a cheaper construction.

The LOWER direction — no height-h causet below some n(h), i.e. that
escapes are necessarily wide in every family, not just fans — is
open; the single-fan incompatibility (referee) is the template, and
without it "logarithmic time at resonance" remains half a claim.

## Scope

All of this is at ε = 1/4, φ = 8π; the tower and its moduli are
resonance-dependent, and none of it touches the physical-band
in-window story (the seam sentence of Paper 1 applies).
