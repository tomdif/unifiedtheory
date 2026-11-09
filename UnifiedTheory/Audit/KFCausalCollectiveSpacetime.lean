/-
  Finite algebra and limit support for the quantum-geometry spectral test.
  Min-max, fiber construction, infinite-volume resolvents, and the band
  theorem are analytic suppliers in COLLECTIVE_SPACETIME_TEST.md.
-/
import UnifiedTheory.Audit.KFCausalProjectedGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCollectiveSpacetime
noncomputable section
open Filter Topology
open scoped BigOperators Matrix

theorem switch_sum_of_squares (x y z : ℝ) :
    3 * (4 * (x^2+y^2+z^2) - ((x+y)^2+y^2+(y+z)^2)) =
      (3*x-y)^2+(3*z-y)^2+y^2 := by ring

/-- Real and imaginary components give the same bounds for complex fields. -/
theorem switch_form_comparison (x y z : ℝ) :
    (x^2+y^2+z^2)/4 ≤ (x+y)^2+y^2+(y+z)^2 ∧
    (x+y)^2+y^2+(y+z)^2 ≤ 4*(x^2+y^2+z^2) := by
  have upper (a b c : ℝ) : (a+b)^2+b^2+(b+c)^2 ≤ 4*(a^2+b^2+c^2) := by
    have h := switch_sum_of_squares a b c
    nlinarith [sq_nonneg (3*a-b), sq_nonneg (3*c-b), sq_nonneg b]
  constructor
  · have h := upper (x+y) (-y) (y+z)
    nlinarith
  · exact upper x y z

/-- Regularity supplies a geometry-independent uniform probe eigenvector. -/
theorem uniform_adjacency_action {X : Type*} [Fintype X]
    (A : Matrix X X ℝ) (degree : ℝ) (h : ∀ i, ∑ j, A i j = degree) :
    A.mulVec (fun _ => 1) = fun _ => degree := by
  funext i
  simpa [Matrix.mulVec, dotProduct] using h i

/-- A nonnegative excitation sum vanishes on the supplied common kernel. -/
theorem excitation_energy_nonnegative (geometry hopping kappa : ℝ)
    (hg : 0 ≤ geometry) (hh : 0 ≤ hopping) (hk : 0 ≤ kappa) :
    0 ≤ geometry+kappa*hopping := by positivity

/-- The spectral comparison keeps the inverse-square finite-size scaling. -/
theorem inverse_square_gap (gap reference kappa side : ℝ)
    (hk : 0 ≤ kappa)
    (href : 16/side^2 ≤ reference)
    (hgap : kappa*reference/4 ≤ gap) : 4*kappa/side^2 ≤ gap := by
  have hm := mul_le_mul_of_nonneg_left href hk
  calc
    _ = (kappa*(16/side^2))/4 := by ring
    _ ≤ (kappa*reference)/4 := div_le_div_of_nonneg_right hm (by norm_num)
    _ ≤ gap := hgap

/-- The quartic band error becomes a quadratic regulator error after time rescaling. -/
theorem scaled_band_remainder (remainder a C P : ℝ) (ha : 0 < a)
    (h : |remainder| ≤ C*(a*P)^4) :
    |remainder/a^2| ≤ C*a^2*P^4 := by
  rw [abs_div, abs_of_nonneg (sq_nonneg a)]
  apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
  nlinarith [h]

/-- On linear time scaling, a quadratically bounded low-band phase disappears. -/
theorem linear_time_freezing (phase scale : ℕ → ℝ) (C : ℝ)
    (hs : Tendsto scale atTop (𝓝 0))
    (hp : ∀ n, 0 ≤ phase n) (hb : ∀ n, phase n ≤ C*scale n) :
    Tendsto phase atTop (𝓝 0) := by
  apply squeeze_zero hp hb
  simpa using hs.const_mul C

/-- The nonzero spatial coefficient survives a convergent volume limit. -/
theorem limiting_diffusivity (D : ℕ → ℝ) (limit kappa : ℝ)
    (hd : Tendsto D atTop (𝓝 limit)) (h : ∀ n, kappa/4 ≤ D n) :
    kappa/4 ≤ limit :=
  le_of_tendsto_of_tendsto' (tendsto_const_nhds (x := kappa/4)) hd h

#print axioms switch_sum_of_squares
#print axioms switch_form_comparison
#print axioms uniform_adjacency_action
#print axioms excitation_energy_nonnegative
#print axioms inverse_square_gap
#print axioms scaled_band_remainder
#print axioms linear_time_freezing
#print axioms limiting_diffusivity

end
end UnifiedTheory.Audit.KFCausalCollectiveSpacetime
