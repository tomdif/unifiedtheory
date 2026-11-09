/- An actual ultraviolet obstruction to uniformly bounded coincident Wilson
plaquette fluctuations under the proposed a^-4 normalization. This is NOT an
obstruction to a distribution-valued continuum theory: singular coincident
correlations, derivative seminorms and contact renormalization remain possible.
The group here is U(2); no compact-simple-group or physical coupling
identification is asserted. -/
import UnifiedTheory.Clay.YangMills.WilsonConditionalPolynomial
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCoincidentObstruction
noncomputable section
open MeasureTheory Matrix RegulatedGauge PeriodicLattice4 UnitaryCharacterObservables
open WilsonConditionalPolynomial UnitaryGibbsTraceFluctuation UnitaryHaarNeighborhood
open UnitaryHaarCaps Filter WilsonCrossingKernel
open scoped Topology

/-- A fixed positive constant, independent of cutoff, volume, coupling and center. -/
def floorConstant : ℝ := Real.exp (-9) / (64 * 257^8 * 386^20)

theorem floorConstant_pos : 0 < floorConstant := by
  unfold floorConstant
  positivity

theorem floor_formula (k : ℕ) :
    polynomialFloor (Fin 2) k =
      Real.exp (-9) / (64 * (k : ℝ)^4 * (256*(k : ℝ)^2+1)^8) := by
  simp only [polynomialFloor, gridSize, massLower, Fintype.card_fin,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  norm_num
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem floor_power_lower (k : ℕ) (hk : 0 < k) :
    Real.exp (-9) / (64 * 257^8 * (k : ℝ)^20) ≤ polynomialFloor (Fin 2) k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hsmall : 256*(k : ℝ)^2+1 ≤ 257*(k : ℝ)^2 := by nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 256*(k : ℝ)^2+1) hsmall 8
  have hden : 64*(k : ℝ)^4*(256*(k : ℝ)^2+1)^8 ≤
      64*257^8*(k : ℝ)^20 := by
    calc
      _ ≤ 64*(k : ℝ)^4*(257*(k : ℝ)^2)^8 := by gcongr
      _ = _ := by ring
  rw [floor_formula]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hden

theorem floor_coupling_lower (β : ℝ) :
    floorConstant / (1+|β|)^20 ≤ polynomialFloor (Fin 2) (⌈384*|β|⌉₊+1) := by
  let k : ℕ := ⌈384*|β|⌉₊+1
  have hk : 0 < k := by dsimp [k]; omega
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 384*|β|)
  have hkb : (k : ℝ) ≤ 386*(1+|β|) := by
    dsimp [k]
    push_cast
    nlinarith [abs_nonneg β]
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg k) hkb 20
  calc
    floorConstant / (1+|β|)^20 =
        Real.exp (-9) / (64*257^8*(386*(1+|β|))^20) := by
      unfold floorConstant
      field_simp
    _ ≤ Real.exp (-9) / (64*257^8*(k : ℝ)^20) := by
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
      gcongr
    _ ≤ polynomialFloor (Fin 2) k := floor_power_lower k hk

variable (n : ℕ) [NeZero n]

def plaquetteVariance (β c : ℝ) (x : Vertex n) (μ ν : Fin 4) (center : ℂ) : ℝ :=
  ∫ U, ‖realTrace (Fin 2) (holonomy (Quiver.Symmetrify (Vertex n))
    (Matrix.unitaryGroup (Fin 2) ℂ) (orientedExtension (Vertex n)
      (Matrix.unitaryGroup (Fin 2) ℂ) U) (plaquette n x μ ν))-center‖^2
    ∂gibbsMeasure (Vertex n) (Matrix.unitaryGroup (Fin 2) ℂ)
      (orientedWilsonAction (Vertex n) (Matrix.unitaryGroup (Fin 2) ℂ)
        (unitaryCharacter (MonoidHom.id _)) (base n) (loops n) β c)

/-- This is the full interacting periodic Wilson law, for every center and
with no hypothesis about the amount of fluctuation. -/
theorem actual_variance_lower [Fact (1 < n)] (β c : ℝ) (x : Vertex n)
    (μ ν : Fin 4) (hμν : μ ≠ ν) (center : ℂ) :
    floorConstant / (1+|β|)^20 ≤ plaquetteVariance n β c x μ ν center := by
  apply (floor_coupling_lower β).trans
  have h := full_plaquette_explicit n (Fin 2) β c x μ ν hμν center
  norm_num only [Fintype.card_fin] at h
  exact h

/-- The ordinary coincident variance after multiplying the field by Z*a^-4. -/
def scaledVariance (β c : ℝ) (x : Vertex n) (μ ν : Fin 4) (center : ℂ)
    (a : ℝ) (Z : ℂ) : ℝ :=
  (‖Z‖^2 / a^8) * plaquetteVariance n β c x μ ν center

theorem actual_scaled_lower [Fact (1 < n)] (β c : ℝ) (x : Vertex n)
    (μ ν : Fin 4) (hμν : μ ≠ ν) (center : ℂ) (a : ℝ) (ha : 0 < a) (Z : ℂ) :
    floorConstant * ‖Z‖^2 / (a^8*(1+|β|)^20) ≤
      scaledVariance n β c x μ ν center a Z := by
  have h := mul_le_mul_of_nonneg_left (actual_variance_lower n β c x μ ν hμν center)
    (by positivity : 0 ≤ ‖Z‖^2/a^8)
  change _ ≤ (‖Z‖^2/a^8) * plaquetteVariance n β c x μ ν center
  convert h using 1
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

/-- Any uniform coincident bound must satisfy this cutoff/coupling constraint.
It does not apply to an arbitrary continuous Schwartz seminorm bound. -/
theorem bounded_coincident_constraint [Fact (1 < n)] (β c : ℝ) (x : Vertex n)
    (μ ν : Fin 4) (hμν : μ ≠ ν) (center : ℂ) (a : ℝ) (ha : 0 < a)
    (Z : ℂ) (C : ℝ) (hC : scaledVariance n β c x μ ν center a Z ≤ C) :
    floorConstant * ‖Z‖^2 ≤ C * a^8*(1+|β|)^20 := by
  have h := (actual_scaled_lower n β c x μ ν hμν center a ha Z).trans hC
  have hd : 0 < a^8*(1+|β|)^20 := by positivity
  have hh := (div_le_iff₀ hd).mp h
  simpa only [mul_assoc] using hh

/-- With a_k=exp(-k), beta_k=k, the actual lower bound on the proposed
coincident normalization diverges. This is an exact logarithmic trajectory,
not an asserted physical renormalization-group theorem. -/
theorem logarithmic_floor_tendsto :
    Tendsto (fun k : ℕ => floorConstant /
      (Real.exp (-(k : ℝ))^8*(1+|(k : ℝ)|)^20)) atTop atTop := by
  have ht : Tendsto (fun k : ℕ => (k : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hh := ((Real.tendsto_exp_div_pow_atTop 20).comp ht).const_mul_atTop
    (mul_pos floorConstant_pos (Real.exp_pos (-1)))
  apply tendsto_atTop_mono' _ (Eventually.of_forall (fun k : ℕ => ?_)) hh
  have hprod : Real.exp (k : ℝ) * Real.exp (-(k : ℝ))^8 ≤ 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    norm_num
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have he : Real.exp (k : ℝ) ≤ 1 / Real.exp (-(k : ℝ))^8 :=
    (le_div_iff₀ (by positivity)).mpr hprod
  calc
    (floorConstant * Real.exp (-1)) *
        (Real.exp ((k : ℝ)+1) / ((k : ℝ)+1)^20) =
        floorConstant * (Real.exp (k : ℝ) / (1+|(k : ℝ)|)^20) := by
      rw [abs_of_nonneg (Nat.cast_nonneg k), Real.exp_add, Real.exp_neg]
      field_simp
      ring
    _ ≤ floorConstant * ((1 / Real.exp (-(k : ℝ))^8) / (1+|(k : ℝ)|)^20) := by
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he (by positivity))
        floorConstant_pos.le
    _ = _ := by
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ring

/-- Divergence holds under the actual full Wilson laws along arbitrary
changing periods, sites, offsets and centers. Here Z=1. In particular centering
by each law's own mean cannot give a bounded coincident variance on this path.
No statement about separated Schwartz correlations is inferred. -/
theorem actual_logarithmic_coincident_diverges
    (period : ℕ → ℕ) [∀ k, NeZero (period k)] [∀ k, Fact (1 < period k)]
    (offset : ℕ → ℝ) (site : ∀ k, Vertex (period k))
    (μ ν : Fin 4) (hμν : μ ≠ ν) (center : ℕ → ℂ) :
    Tendsto (fun k => scaledVariance (period k) (k : ℝ) (offset k) (site k) μ ν
      (center k) (Real.exp (-(k : ℝ))) 1) atTop atTop := by
  apply tendsto_atTop_mono' _ (Eventually.of_forall (fun k => ?_)) logarithmic_floor_tendsto
  simpa only [norm_one, one_pow, mul_one] using
    actual_scaled_lower (period k) (k : ℝ) (offset k) (site k) μ ν hμν
      (center k) (Real.exp (-(k : ℝ))) (Real.exp_pos _) 1

end
end UnifiedTheory.Clay.YangMills.WilsonCoincidentObstruction
