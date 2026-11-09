# Birth-order balance of the pi/4 Born chain vs the 1/3-2/3 bounds (2026-09-25)

Script: `birth_order_balance.py` (log `birth_order_balance.log`). Exact, no sampling.

Birth orders of a final causet C are its linear extensions. Rideout-Sorkin covariance
makes them uniform given C, which is the setting of the 1/3-2/3 conjecture
(Kahn-Saks; Brightwell-Felsner-Trotter 0.2764; Aires-Chan-Pak-Panova 2026 +eps;
exact 1/3 verified for n <= 11). `AUDIT_COVARIANCE.md` proves pi/4 is not strictly
covariant, so its conditional birth-order law P(x before y | C) was computed by a DP
over the downset lattice of every n = 8 class.

| law | supported non-chain C | min delta | max abs(P_law - P_unif) | mean dev per C | C with a forced spacelike order (Born mass) |
|---|---|---|---|---|---|
| percolation p=1/2 (control) | 16998 | 0.3333 | 0 (exact) | 0 | 0 |
| uniform labeled growth | 16998 | 0.3600 | 0.41 | 0.16 | 0 |
| pi/4 max-entropy | 13958 | 0.3333 | 0.96 | 0.31 | 6039 (0.10) |
| pi/4 random 0 | 11931 | 0.3404 | 0.95 | 0.31 | 7445 (0.28) |
| pi/4 random 1 | 10942 | 0.3924 | 0.97 | 0.34 | 6312 (0.33) |

delta(C) = max over incomparable pairs of min(P(x<y), P(y<x)).

Registered readings: (C) holds for the balance bound only. No supported C has
delta < 1/3 under any law, so pi/4 never produces a causet without a balanced pair.
Per-pair covariance, though, is badly broken. Under every pi/4 selection, 10-33% of
Born mass sits on causets where some spacelike pair has a strictly forced birth
order (P = 0 or 1), which no covariant law can produce. Mechanism: zero-weight
child classes (the law's support is 64-82% of classes) delete whole families of
linear extensions. The existence is robust across selections; the magnitude is
selection-dominated.

Reading: this quantifies `covariance_no_go`. Under pi/4, birth order is physical, not
gauge, yet the dynamics still leaves every causet with a coin-flip-like pair. Whether
delta >= 1/3 is a theorem for this law class or an n = 8 accident is open; n = 9 would test it.
