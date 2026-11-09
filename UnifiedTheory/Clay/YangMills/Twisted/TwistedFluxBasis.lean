/- The transverse step in the electric-flux basis: no fine cancellation is needed.

For any box, set `Z₀ = (Z + Z_tw)/2` and `Z_e = (Z - Z_tw)/2`, so the flux ratio is `y = Z_e/Z₀`. Splitting a box of
transverse extent `2t` into two periodic `t`-boxes, the twist sheet is cut into one closed sheet per copy, so
`Z^split = Z(t)²` and `Z_tw^split = Z_tw(t)²`, which gives `Z₀^split = Z₀² + Z_e²` and `Z_e^split = 2 Z₀ Z_e`.
Define the sector-resolved interface ratios `K₀ = Z₀^split / Z₀(2t)` and `K_e = Z_e^split / Z_e(2t)`.

* `transverse_flux_identity` (exact): `y(2t) = (2y/(1+y²)) · K₀/K_e`.
* `transverse_flux_le`: hence `y(2t) ≤ 2 y(t) · K₀/K_e`.

So the transverse step is multiplicative with factor `K₀/K_e`. By `TwistedSubArea`, the area law only needs
`log(K₀/K_e)` to grow sub-area. In the twist basis, the same condition looked like an `O(y)`-precise cancellation between
`Kper_tw` and `Kper`. In the flux basis it asks only that the two sectors' interface free energies agree to `o(L²)`.
Each of them is physically `O(1)` (a thermal quantity at `T ~ 1/L`). This file proves only the algebra. -/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxBasis

theorem transverse_flux_identity {Z Zt Z2 Zt2 : ℝ} (h1 : Zt < Z) (h0 : 0 < Zt) (h21 : Zt2 < Z2) (h20 : 0 < Zt2) :
    (Z2 - Zt2) / (Z2 + Zt2) =
      (2 * ((Z - Zt) / (Z + Zt)) / (1 + ((Z - Zt) / (Z + Zt)) ^ 2)) *
        (((Z ^ 2 + Zt ^ 2) / 2) / ((Z2 + Zt2) / 2) / (((Z ^ 2 - Zt ^ 2) / 2) / ((Z2 - Zt2) / 2))) := by
  have a : Z + Zt ≠ 0 := by linarith
  have b : Z2 + Zt2 ≠ 0 := by linarith
  have c : Z2 - Zt2 ≠ 0 := by linarith
  have d : Z ^ 2 - Zt ^ 2 ≠ 0 := by nlinarith
  have e : Z ^ 2 + Zt ^ 2 ≠ 0 := by positivity
  have f : (Z + Zt) ^ 2 + (Z - Zt) ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

theorem transverse_flux_le {y y2 K0 Ke : ℝ} (hy : 0 ≤ y) (hK : 0 ≤ K0 / Ke)
    (h : y2 = (2 * y / (1 + y ^ 2)) * (K0 / Ke)) : y2 ≤ 2 * y * (K0 / Ke) := by
  rw [h]; apply mul_le_mul_of_nonneg_right _ hK
  rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg y, mul_nonneg hy (sq_nonneg y)]

end UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxBasis
