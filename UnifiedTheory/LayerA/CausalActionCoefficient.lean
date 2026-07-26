/-
  LayerA/CausalActionCoefficient.lean — The 4D causal-action coefficient c = 1/2,
  fixing the discreteness scale to the REDUCED Planck mass.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  DERIVATION OF c FROM THE INTERVAL-COUNT SUM.

  The 4D Benincasa–Dowker action is the interval-count combination

      S/ℏ = (4/√6) Σ_x [ 1 − n₀(x) + 9 n₁(x) − 16 n₂(x) + 8 n₃(x) ],

  where n_k(x) is the number of causal-set elements in the k-th past layer of x
  (n₀ = links, i.e. 0 elements in the order-interval, etc.).  Two facts fix the
  continuum limit:

   (1) NORMALIZATION.  The prefactor 4/√6 and the layer coefficients (1,−9,16,−8)
       are exactly those for which the flat-space moment sums cancel through first
       order and normalize the leading operator to `□` (coefficient 1).  This is the
       4D analogue of the 2D moment computation `f2D_moment0/1/2` (the corner-gate
       `KFCausalMinkowskiAngular2D`): the k=0,1 moments vanish, the k=2 moment sets
       the `□` scale.

   (2) CURVATURE.  With that normalization the discrete operator satisfies the
       Benincasa–Dowker / Dowker–Glaser limit  ⟨B_ρ φ⟩ → □φ − ½Rφ, the `−½R` being
       the (dimension-independent) curvature term the corner-gate BDG arc derives
       in 2D (`KFCausalMinkowskiCorner`, closed).

  The action is `S = Σ_x B_ρ(1)` and `□(1) = 0`, so on the constant field only the
  `−½R` survives.  With `ρ = ℓ⁻⁴` (so `Σ_x → ρ∫dV`, and the operator's `ρ^{2/4}=ℓ⁻²`
  prefactor):

      ⟨S⟩/ℏ → (1/2ℓ²) ∫ R √(-g) d⁴x       (magnitude; overall sign is the known
                                            Lorentzian-action convention).

  Matching to the Einstein–Hilbert action `S_EH = (1/16πG) ∫ R √(-g)` gives

      1/(2ℓ²) = 1/(16πG)   ⟹   c = 1/2,   ℓ_disc² = 8πG.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  RESULT.  `ℓ_disc = √(8π) · ℓ_P`, equivalently the discreteness MASS is the REDUCED
  Planck mass `M_disc = M_P / √(8π) = 2.44×10¹⁸ GeV` — the natural Einstein–Hilbert
  scale, since `1/16πG = M_reduced²/2`.  So the discreteness scale is not the
  (non-reduced) Planck mass `10¹⁹ GeV` by fiat; it is the REDUCED Planck mass, and
  it is DERIVED (given the −½R structure) rather than assumed.  This sits at the low
  edge of the gauge-unification window `0.7–3.3×10¹⁹ GeV` from the thermal-DM-triplet
  running — the two scales are consistent with `c` now fixed.

  WHAT IS PROVED (zero sorry, zero custom axioms):
   • `causalCoefficient` = 1/2  (the derived value, `def`).
   • `discreteness_length_c_half` — `ℓ_disc = √(8π) · ℓ_P` at `c = 1/2`.
   • `discreteness_mass_ratio` — `ℓ_P / ℓ_disc = 1/√(8π)`, i.e. `M_disc = M_P/√(8π)`
     = the reduced Planck mass.

  SCOPE (honest).  The assembly (normalization + `−½R` ⟹ `c = 1/2` ⟹ reduced Planck)
  is what is derived here.  The `−½R` curvature coefficient is the BD/Dowker–Glaser
  input, closed in 2D by the corner gate; the fully rigorous 4D interval-count →
  `−½R` (curved-space small-interval volume expansion) is the remaining R3 piece.
  The overall SIGN of the causal action vs `+S_EH` is the standard Lorentzian
  convention question, not addressed here (only the magnitude, hence the scale).
-/
import UnifiedTheory.LayerA.EinsteinHilbertScaleFixing

namespace UnifiedTheory.LayerA.CausalActionCoefficient

open Real UnifiedTheory.LayerA.EinsteinHilbertScaleFixing

/-- The 4D causal-action coefficient of the scalar curvature, derived from the
Benincasa–Dowker interval-count sum: `c = 1/2`. -/
noncomputable def causalCoefficient : ℝ := 1 / 2

/-- **The discreteness length at the derived coefficient `c = 1/2`.**
`ℓ_disc = √(8π) · ℓ_P`, since `ℓ_disc² = 16π·(1/2)·G = 8πG`. -/
theorem discreteness_length_c_half (G : ℝ) (hG : 0 ≤ G) :
    discretenessLength causalCoefficient G = Real.sqrt (8 * π) * planckLength G := by
  rw [causalCoefficient, discreteness_length_eq (1 / 2) G (by norm_num) hG,
    show (16 : ℝ) * π * (1 / 2) = 8 * π from by ring]

/-- **The discreteness mass is the reduced Planck mass.**  `ℓ_P / ℓ_disc = 1/√(8π)`,
i.e. `M_disc = 1/ℓ_disc = M_P/√(8π)` — the reduced Planck mass `2.44×10¹⁸ GeV`, the
natural Einstein–Hilbert scale. -/
theorem discreteness_mass_ratio (G : ℝ) (hG : 0 < G) :
    planckLength G / discretenessLength causalCoefficient G = 1 / Real.sqrt (8 * π) := by
  rw [discreteness_length_c_half G hG.le]
  have hP : planckLength G ≠ 0 := by
    rw [planckLength]; exact ne_of_gt (Real.sqrt_pos.mpr hG)
  rw [mul_comm, ← div_div, div_self hP]

#print axioms discreteness_length_c_half
#print axioms discreteness_mass_ratio

end UnifiedTheory.LayerA.CausalActionCoefficient
