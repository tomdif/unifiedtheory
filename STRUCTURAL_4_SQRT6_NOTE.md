# The 4/sqrt6 identity: structural investigation (2026-08-11)

The 4D Benincasa-Dowker prefactor and the pure-gravity Liouville
coupling are the same number in the same written form:

    beta_4 = 4/sqrt6 = 1.632993...          (Dowker-Glaser, CQG 2013)
    gamma(c=0) = (sqrt25 - sqrt1)/sqrt6     (KPZ/DDK)
               = 4/sqrt6 = sqrt(8/3)        (Brownian map; SLE_{8/3})

No cross-reference exists in either literature (searched 2026-08-11).
This note records the structural investigation: where each sqrt6 comes
from, which extendable bridges fail, and the one embedding that works —
with an exact anchor and a falsifiable target.  Arithmetic:
structural_4sqrt6.py / .log.

## 1. Origins decomposition (no common derivation found)

BD side: beta_4 arises from the 4D causal-interval volume in null
coordinates, V_4 = (pi/6)(uv)^2 — the 6 is S_2 * 2^{-1} / (d(d-1)) at
d = 4 (i.e. 4pi/24, the pi cancelling against the 2-sphere).  KPZ
side: the sqrt6 is the background-charge anomaly c_L = 1 + 6Q^2 (the 6
descending from the Schwarzian normalization 12), balanced against the
ghost 26.  The two 6's descend from different 12's — d(d-1)|_{d=4}
versus the universal central-term normalization.  No shared mechanism
at the level of the derivations.

## 2. Point identities (exact, and all about dimension four)

  gamma(c=0) = 4/sqrt6 = beta_4;   gamma^2 = 8/3 = kappa_SAW;
  d_H(sqrt(8/3)-LQG) = d_H(Brownian map) = 4   (Le Gall; also
  Watabiki(c=0) = 2(7+5)/(5+1) = 4 exactly);
  Starobinsky/f(R) scalaron exponent sqrt(2/3) = (4/sqrt6)/2
  (4D conformal-mode normalization, (d-1)(d-2) = 6).

The defensible reading: on BOTH sides 4/sqrt6 is the pure-geometry
constant attached to FOUR-dimensionality — by construction in causal
sets, by the d_H = 4 theorem in LQG.

## 3. Family-map tests — all FAIL (the identity is a point, not a curve)

  (a) prefactor -> central charge: beta_3 = (pi/(3 sqrt2))^{2/3}
      / Gamma(5/3) = 0.9067 maps to c = -17.4: nothing distinguished.
  (b) d_H bridge: gamma with Watabiki d_H = 3 is 1.0954, vs beta_3 =
      0.9067 — 21% mismatch.
  (c) beta_d = sqrt(2d/3)?  d=2 gives 1.155 vs the actual 2D constants
      (2 and 4): fails (and the 2D operator has two UNEQUAL constants,
      so no single 2D prefactor exists to match gamma(c=1) = 2).

Any structural content is specific to (d = 4, c = 0).

## 4. THE EMBEDDING THAT WORKS: mating of trees at c = -2

Mating-of-trees (Duplantier-Miller-Sheffield): a gamma-LQG surface
decorated by space-filling SLE is equivalent to a pair of Brownian
motions with correlation rho = -cos(pi gamma^2/4).  Pure gravity:
rho = +1/2.  Spanning trees (gamma = sqrt2, c = -2): rho = 0
(independent walks).  A 2D ORDER IS LITERALLY A MATED PAIR of linear
orders — two coordinate walks.  Dictionary: point-pair concordance =
ordering fraction, r = 1/2 + arcsin(rho)/pi.

EXACT ANCHOR (validated on our data): classical 2D sprinkling has
independent coordinates, so it must sit at rho = 0, i.e. r = 1/2 and
c = -2.  Measured: sprinkling r = 0.4997 -> c_eff = -2.01; uniform
growth r = 0.5080 -> c_eff = -1.86.  The classical causal-set ensemble
IS the c = -2 (uniform-spanning-tree) point of the mating family, on
the nose.  This is the structural connection between causal sets and
Liouville quantum gravity: not at pure gravity, but at c = -2.

Under the same dictionary, the QUANTIZED measure deviates BELOW:

    pi/4 law   r(7) = 0.3942 -> c_eff = -4.6;  r(8) = 0.4136 -> -4.0
    4/sqrt6 4D law r(7) = 0.3905 -> c_eff = -4.7

The quantum dynamics ANTI-correlates the two orders (rho_eff = -0.27
at n = 8), i.e. moves the geometry to smaller gamma (more tree-like /
branchy), drifting back toward c = -2 with depth.  Pure gravity would
require POSITIVE correlation, r -> 2/3.  So at accessible depth the
quantized causal measure is NOT in the Brownian-map class, and the
4/sqrt6 coincidence does NOT close through this embedding.

Caveat, stated plainly: the concordance <-> mating-correlation
identification is exact only at the independent point (where it is
forced); away from it the Gaussian-copula reading is a heuristic chart
— the DMS walks are boundary-length processes of a space-filling
exploration, not coordinate ranks.  The exact anchor at c = -2 and the
SIGN/direction of the quantum deviation are the defensible content;
the c_eff values away from -2 are exploratory coordinates.

## 5. Verdict and the falsifiable target

1. No curve-level structural connection exists between the BD
   dimension family and the Liouville central-charge family (Section 3).
2. A genuine structural embedding DOES exist at one point: classical
   2D-order causal sets = the c = -2 mating class (exact anchor,
   verified to 1% on two independent baselines).
3. The 4/sqrt6 identity itself remains a point coincidence whose two
   sides both say "pure quantum geometry <-> dimension four"; it would
   BECOME structural if the quantized causal growth measure flowed to
   the Brownian-map class in the deep limit.  That is now a sharp,
   registered, falsifiable target:

       r(n) -> 2/3  <=>  quantized causal growth is pure 2D quantum
                         gravity (Brownian map), and 4/sqrt6 governs
                         both its 4D action normalization and its
                         emergent 2D coupling;
       r(n) -> 1/2  <=>  the quantum measure returns to the classical
                         c = -2 point and the identity stays a
                         coincidence.

   Current trend (r: 0.30 -> 0.41, rising, increments shrinking)
   points at ~1/2, i.e. coincidence — but the limit is not yet
   determined by the data.

4. Registered follow-up beyond r: a causal-set KPZ test.  If the
   quantized measure defines a random geometry in some gamma-class,
   classical vs quantum scaling dimensions of stem observables should
   satisfy the KPZ quadratic relation x = (gamma^2/4) Delta^2 +
   (1 - gamma^2/4) Delta, giving a second, independent measurement of
   gamma_eff to confront with the mating value.  Agreement of the two
   would promote the embedding from a chart to a class assignment.

## Sources

Dowker-Glaser arXiv:1305.2588; Glaser arXiv:1311.1701; Benincasa-
Dowker via arXiv:1903.11544; Duplantier-Sheffield arXiv:0808.1560;
Miller-Sheffield arXiv:1507.00719, 1605.03563, 1608.05391;
Gwynne-Holden-Sun survey arXiv:1910.04713 (rho = -cos(pi gamma^2/4));
SAW -> SLE_{8/3} on sqrt(8/3)-LQG arXiv:1608.00956; Le Gall d_H = 4;
Starobinsky exponent e.g. arXiv:2111.09058.
