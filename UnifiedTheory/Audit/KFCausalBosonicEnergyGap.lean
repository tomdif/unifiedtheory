/- Number-weighted energy and a vacuum-relative gap for the completed
Bose-symmetric particle sum. No added interparticle interaction is asserted. -/
import UnifiedTheory.Audit.KFCausalBosonicFock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBosonicEnergyGap
noncomputable section
open scoped ENNReal
open KFCausalClosedGraphForm KFCausalBosonicFock KFCausalTensorSumEnergyFloor

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem sector_lower (D : Data H K) (δ : ℝ) (hD : LowerBound D δ) (n : ℕ) :
    LowerBound (sector D n).form ((n : ℝ) * δ) := by
  cases n with
  | zero =>
    intro x
    simpa only [Nat.cast_zero, zero_mul] using sector_positive D 0 x
  | succ n =>
    simpa only [Nat.cast_add, Nat.cast_one] using KFCausalBosonicSectorHamiltonian.lower_bound D n δ hD

theorem component_energy_lower (D : Data H K) (δ : ℝ) (hD : LowerBound D δ)
    (x : (fullHamiltonian D).domain) (n : ℕ) :
    ((n : ℝ) * δ) * ‖(x : BosonFock D) n‖ ^ 2 ≤
      (inner ℂ (fullHamiltonian D x n) ((x : BosonFock D) n)).re := by
  obtain ⟨u, hu, hv⟩ := (sectorHamiltonian D n).mem_graph_iff.mp
    ((full_graph D x (fullHamiltonian D x)).mp ((fullHamiltonian D).mem_graph x) n)
  change (u : (sector D n).State) = (x : BosonFock D) n at hu
  change sectorHamiltonian D n u = fullHamiltonian D x n at hv
  rw [← hu, ← hv]
  exact sector_lower D δ hD n u

theorem weighted_summable (D : Data H K) (δ : ℝ) (hδ : 0 ≤ δ) (hD : LowerBound D δ)
    (x : (fullHamiltonian D).domain) :
    Summable (fun n : ℕ => ((n : ℝ) * δ) * ‖(x : BosonFock D) n‖ ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hδ) (sq_nonneg _))
    (component_energy_lower D δ hD x)
  exact (Complex.hasSum_re (lp.hasSum_inner (𝕜 := ℂ) (fullHamiltonian D x) (x : BosonFock D))).summable

theorem number_energy_lower (D : Data H K) (δ : ℝ) (hδ : 0 ≤ δ) (hD : LowerBound D δ)
    (x : (fullHamiltonian D).domain) :
    (∑' n : ℕ, ((n : ℝ) * δ) * ‖(x : BosonFock D) n‖ ^ 2) ≤
      (inner ℂ (fullHamiltonian D x) (x : BosonFock D)).re := by
  rw [lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner (𝕜 := ℂ) _ _)]
  exact Summable.tsum_le_tsum (component_energy_lower D δ hD x)
    (weighted_summable D δ hδ hD x) (Complex.hasSum_re (lp.hasSum_inner (𝕜 := ℂ) _ _)).summable

theorem vacuum_gap (D : Data H K) (δ : ℝ) (hδ : 0 ≤ δ) (hD : LowerBound D δ)
    (x : (fullHamiltonian D).domain) (hx : (x : BosonFock D) 0 = 0) :
    δ * ‖(x : BosonFock D)‖ ^ 2 ≤ (inner ℂ (fullHamiltonian D x) (x : BosonFock D)).re := by
  have hn : HasSum (fun n => ‖(x : BosonFock D) n‖ ^ 2) (‖(x : BosonFock D)‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (x : BosonFock D)
  have he : HasSum (fun n => (inner ℂ (fullHamiltonian D x n) ((x : BosonFock D) n)).re)
      (inner ℂ (fullHamiltonian D x) (x : BosonFock D)).re :=
    Complex.hasSum_re (lp.hasSum_inner (𝕜 := ℂ) (fullHamiltonian D x) (x : BosonFock D))
  apply hasSum_le _ (hn.mul_left δ) he
  intro n
  by_cases hzero : n = 0
  · subst n
    simp [hx]
  · have hc : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
    have hm : δ ≤ (n : ℝ) * δ := by nlinarith
    exact (mul_le_mul_of_nonneg_right hm (sq_nonneg _)).trans
      (component_energy_lower D δ hD x n)

def vacuumCoefficient (D : Data H K) (x : BosonFock D) : ℂ := x 0

theorem zero_energy_kernel (D : Data H K) (δ : ℝ) (hδ : 0 < δ) (hD : LowerBound D δ)
    (x : BosonFock D) (hx : (x, 0) ∈ (fullHamiltonian D).graph) :
    x = vacuumCoefficient D x • vacuum D := by
  apply lp.ext
  funext n
  cases n with
  | zero => simp [vacuum, vacuumCoefficient]
  | succ n =>
    have hg := (full_graph D x 0).mp hx (n + 1)
    obtain ⟨u, hu, hv⟩ := (sectorHamiltonian D (n + 1)).mem_graph_iff.mp hg
    change (u : (sector D (n + 1)).State) = x (n + 1) at hu
    change sectorHamiltonian D (n + 1) u = 0 at hv
    have hl := sector_lower D δ hD (n + 1) u
    change (((n + 1 : ℕ) : ℝ) * δ) * ‖(u : (sector D (n + 1)).State)‖ ^ 2 ≤
      (inner ℂ (sectorHamiltonian D (n + 1) u) (u : (sector D (n + 1)).State)).re at hl
    rw [hv, inner_zero_left, Complex.zero_re] at hl
    have hp : 0 < (((n + 1 : ℕ) : ℝ) * δ) := mul_pos (by positivity) hδ
    have hn : ‖(u : (sector D (n + 1)).State)‖ ^ 2 ≤ 0 :=
      (mul_le_mul_iff_right₀ hp).mp (by simpa only [mul_zero] using hl)
    have hz : (u : (sector D (n + 1)).State) = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hn (sq_nonneg _)))
    have hxn : x (n + 1) = 0 := hu.symm.trans hz
    simp [hxn, vacuum, lp.single_apply]

theorem orthogonal_vacuum_iff (D : Data H K) (x : BosonFock D) :
    inner ℂ (vacuum D) x = 0 ↔ x 0 = 0 := by
  rw [vacuum, lp.inner_single_left]
  change inner ℂ (1 : ℂ) (x 0 : ℂ) = 0 ↔ (x 0 : ℂ) = 0
  simp

theorem orthogonal_energy_gap (D : Data H K) (δ : ℝ) (hδ : 0 ≤ δ) (hD : LowerBound D δ)
    (x : (fullHamiltonian D).domain) (hx : inner ℂ (vacuum D) (x : BosonFock D) = 0) :
    δ * ‖(x : BosonFock D)‖ ^ 2 ≤ (inner ℂ (fullHamiltonian D x) (x : BosonFock D)).re :=
  vacuum_gap D δ hδ hD x ((orthogonal_vacuum_iff D x).mp hx)


end
end UnifiedTheory.Audit.KFCausalBosonicEnergyGap
