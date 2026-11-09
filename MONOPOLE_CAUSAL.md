# Dirac monopole on a causal set: b₂ window and lattice Chern numbers

Date: 2026-11-03. Follow-up to `AHARONOV_BOHM_CAUSAL.md`. It goes from b₁ and AB holonomy to b₂ and the Chern class.
Script: `scripts/ab_monopole_nerve.py`, run with python3.11, niced, single-threaded BLAS. Logs: `ab_monopole_nerve_seed{1,2,3}.log`.
Nothing is committed and no Lean files were touched.

## Setup
* Sprinklings into 2+1 ℝ×S² (sphere radius r_s = 0.25, T = 1.2, ρ = 2000 and 4000) and the control ℝ×D² (disc radius 0.5, same area).
* The antichain A is the set of minimal elements of {t ≥ 0.25}.
* Thickened antichain T_n(A) → maximal elements → shadows on A → nerve (the same construction as `ab_thickened_antichain.py`), extended to 3-simplices.
* b₀, b₁, b₂ are computed over GF(2). **This part is order-only.**
* Chern part, which depends on the embedding: the vertex position is the normalized centroid of its shadow. The link phase is θ_uv = (g/2)·Ω(N,u,v), which is the Dirac-string gauge A = (g/2)(1−cosθ)dφ integrated exactly along geodesics. The plaquette F is the principal value of the oriented edge sum, with m = (F−raw)/2π. The real 2-cycle z is the solid-angle cochain projected onto ker ∂₂ (residual ≤ 1e-9), normalized so that ⟨Ω,z⟩ = 4π. The Chern number is c = ⟨F,z⟩/2π.

## (a) b₂ window. The grid is n ∈ {1,2,3,5,8,12,18,25,35,50,70,…}; ">" means the window was still open at the 400k-tetrahedron cap.

| run | seed 1 | seed 2 | seed 3 |
|---|---|---|---|
| S², ρ=2000 | (1,0,1) at n = 25–50 > | 25–50 > | 12–35 > |
| S², ρ=4000 | 18–35 > | 18–35 > | 12–35 > |
| D², ρ=2000 | (1,0,1) **only at n=12** (isolated); else (1,0,0) for 18–140 | (1,0,0) for 18–70 | (1,0,0) for 18–140 |
| D², ρ=4000 | (1,0,0) for 12–50 | (1,0,0) for 18–50 | (1,0,0) for 18–50 |

* The sphere has a stable b₀=1, b₁=0, b₂=1 window in 6/6 runs, spanning 3–4 grid points to the cap.
* The disc shows b₂=0 throughout its connected range in 6/6 runs, apart from one isolated (1,0,1) at the lower edge (D², seed 1, n=12). For that point the projection of Ω onto ker ∂₂ is exactly 0, so the class has degree 0 and does not wrap anything. It looks like lower-edge noise, like the b₁ noise at small n.
* The sphere's lower edge is ragged: for seed 1 at ρ=2000, n=12 and 18 give b₂=0.
* **The upper edge was not measured.** The tetrahedron count passes 4×10⁵ at n≈50–70, and the pure-Python GF(2) rank becomes the bottleneck. The window should close once shadows reach hemisphere size; this is untested.

## (b) Chern recovery. 20 window points over 6 runs; delta-m counts 3-simplices with δm ≠ 0.

| g | c | δm = 0? | string plaquettes |
|---|---|---|---|
| 1, −1, 2 | **exactly 1, −1, 2** (to 1e-6) at every window point, except g=2 at n=50, ρ=2000, seeds 1 and 2 (1.95, 1.96) | yes, except those two points | 0 |
| 3 | exactly 3 at 13/20 points (all 10 at ρ=4000) | fails where max\|F\|→π | 0 |
| 0.5 | **0** (an integer) | yes | 65–1823 |
| 1.3 | **1** (an integer) | yes | 65–1823 |

* For integer g the string is invisible: F = (g/2)Ω on every plaquette, and c = g.
* For non-integer g the gauge-invariant plaquette field is integer-quantized anyway. c = round-ish(g), and the leftover 2π·frac(g) sits on a visible string of plaquettes around the south pole. This is Dirac quantization on the order-built nerve.
* The failures, for g=3 and for g=2 at large n, are the usual lattice-admissibility limit: |g|·Ω_τ/2 approaches π on the largest triangles, so δm ≠ 0 on some tetrahedra. They happen at coarse n with large g and go away at higher ρ (all of ρ=4000 is clean).

## Verdict and scope
* **Order-only:** b₂=1 with b₁=0 in a stable window on ℝ×S², and not on ℝ×D². ℝ×S² is globally hyperbolic and compact, so Major–Rideout–Surya (0902.0434) already cover the existence of this window. As with the cylinder, this is a reproduction or extension (to b₂), not a new theorem.
* **Embedding-dependent:** the connection and the normalization ⟨Ω,z⟩=4π. The latter assumes the centroid map has degree ±1. As in the b₁ case, "c = g" is then a degree computation. The integer-quantization statement (c ∈ ℤ, with the string visible iff g ∉ ℤ) is a lattice-gauge identity once the 2-cycle exists.
* **Not done:**
  - an order-only integral generator of H₂ (or H²) analogous to ω in `ab_chain_pair_holonomy.py`, so that c can be read without Ω;
  - the upper window edge, which needs a faster rank, for example sparse GF(2) elimination or collapses;
  - window scaling with ρ;
  - a Lean statement (a `hol_homologous` analogue for 2-cochains).
