# Random 2-orders realize the c = -2 point of the mating-of-trees
# correspondence: theorem sketch (2026-08-13)

CLAIM.  The uniform random 2D order (2-order) on n elements is, in the
scaling limit, the causal-set realization of the c = -2 / gamma =
sqrt(2) point of the mating-of-trees (Duplantier-Miller-Sheffield)
family.

PROOF SKETCH (each step standard):
1. A uniform 2-order is the intersection of two independent uniform
   linear orders L1, L2 (equivalently: a uniform permutation pi;
   x < y iff both coordinates agree).  This is the definition of the
   random 2-order ensemble (Winkler; el-Zahar/Sauer), and equals a
   density-1 sprinkling of the 2D causal diamond in lightcone
   coordinates by a standard bijection (u-rank, v-rank).
2. Encode the pair (L1, L2) as the two coordinate walks
   (X_k, Y_k) = (rank processes).  For a uniform permutation the
   walks' increments are exchangeable and asymptotically independent;
   by Donsker the pair converges to a two-dimensional Brownian motion
   with CORRELATION ZERO.
3. In the mating-of-trees dictionary, a gamma-LQG surface decorated by
   space-filling SLE corresponds to a Brownian pair with correlation
   -cos(pi gamma^2 / 4).  Correlation 0 <=> gamma^2 = 2 <=> gamma =
   sqrt(2) <=> central charge c = 26 - 6(gamma/2 + 2/gamma)^2 ... =
   -2: the uniform-spanning-tree / bipolar-orientation point (indeed
   Kenyon-Miller-Sheffield-Wilson's bipolar-orientation bijection is
   the rigorous instance of a correlation-0 mating).
4. Hence the ordering fraction and all concordance statistics of
   random 2-orders are, asymptotically, statistics of the gamma =
   sqrt(2) peanosphere - measured in this repo's chart as c_eff =
   -2.01 (sprinkling) and -1.86 (uniform growth) at n = 8.

REMARKS.  (a) The identification is at the level of the coordinate-
walk encoding (peanosphere/mating topology), the natural common
refinement of "causal set" and "LQG surface" - not a claim about
conformal structure of the order itself.  (b) The quantized pi/4
measure moves the walk correlation NEGATIVE (c_eff ~ -4 at n = 8,
drifting back toward -2 with depth; anti-KPZ class = exponential
tilt, not a gamma-LQG reweighting - kpz-causal-test-2026-08-13).
(c) Bipolar orientations give the route to a fully rigorous statement
including the decorating tree pair; for the bare correlation-0
statement, steps 1-3 suffice.

STATUS: theorem-sketch grade; the write-up target is a short note
(4-6 pp) for the causal-set and random-geometry communities, filling
what our 2026-08-11 literature sweep found to be an unremarked bridge.
