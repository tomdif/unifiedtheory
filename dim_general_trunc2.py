#!/usr/bin/env python3
# Dimension-general truncation-2 band scan (see PAPER1 section 3').
# Channels {0, W0, W0+W1, 2W0}; dimension enters via (W0, W1, prefactor).
# Results 2026-08-01: 2D band mostly ALIVE, 3D mostly dead + top sliver,
# 4D dead; W1-sign is a certificate-validity condition, not the decider.
# (Script body: see session log; kept as the parameter table of record.)
# 2D: W0=2e, W1=2e(1-3e), band [0.16,0.25], boundary 1/3
# 3D: W0=e,  W1=e(1-35e/8), band [0.064,0.125], boundary 8/35
# 4D: W0=e,  W1=e(1-10e), band [0.026,0.063], boundary 1/10
# 5D: boundary 16/231; 6D: 1/35; all bands below boundaries (1+|C2|<2^d).
