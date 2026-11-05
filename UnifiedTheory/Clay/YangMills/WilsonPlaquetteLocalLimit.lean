/- A vanishing threshold with a polynomial source error on any fixed finite
plaquette family. Arbitrary regulator changes and source concentration are
retained. This local slow-mode statement does not construct continuum fields. -/
import UnifiedTheory.Clay.YangMills.WilsonPlaquetteEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPlaquetteLocalLimit
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonGroundHeatBath WilsonPhysicalVariance
open WilsonHighFieldDecay SpatialPlaquetteCutGeometry WilsonPlaquetteCover
open WilsonPlaquetteColumnTail (rate)

def coefficient : ℝ := (4 * SU2ScalarTilt.partition 0 / Real.Gamma (3 / 2)) ^ 2

theorem coefficient_nonneg : 0 ≤ coefficient := sq_nonneg _

theorem cap_squared (β : ℝ) (hβ : 0 ≤ β) :
    (SU2GaussianMass.cap β) ^ 2 = coefficient * β ^ 3 := by
  unfold SU2GaussianMass.cap coefficient
  calc
    _ = (4 * SU2ScalarTilt.partition 0 / Real.Gamma (3 / 2)) ^ 2 *
        β ^ 2 * (Real.sqrt β) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt hβ]; ring

def threshold (β : ℝ) : ℝ := 4 * Real.log β / β

theorem threshold_pos (β : ℝ) (hβ : 1 < β) : 0 < threshold β :=
  div_pos (mul_pos (by norm_num) (Real.log_pos hβ)) (by linarith)

theorem threshold_tendsto : Filter.Tendsto threshold Filter.atTop (nhds 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul 4
  change Filter.Tendsto (fun β : ℝ => 4 * Real.log β / β) Filter.atTop (nhds 0)
  simpa only [pow_one, one_mul, add_zero, mul_zero, mul_div_assoc] using h

/-- The exact polynomial prefactor gives a C/beta error at this vanishing cutoff. -/
theorem rate_threshold (β : ℝ) (hβ : 0 < β) : rate β (threshold β) = coefficient / β := by
  have he : -β * threshold β = -Real.log (β ^ 4) := by
    rw [Real.log_pow]
    unfold threshold
    norm_num only [Nat.cast_ofNat]
    field_simp
  unfold rate
  rw [cap_squared β hβ.le, he, Real.exp_neg, Real.exp_log (pow_pos hβ 4)]
  field_simp

variable (n : ℕ) [NeZero n] {I : Type*} [Fintype I]

theorem local_tail (β : ℝ) (hβ : 1 < β) (q : I → Plaquette n)
    (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (bad n q (fun _ => threshold β)).indicator (fun v => (f v) ^ 2) u
      ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * (Fintype.card I : ℝ) * (coefficient / β) * mass (2 * n) β (by linarith) f := by
  have h := weighted_union n β (by linarith) q (fun _ => threshold β)
    (fun _ => threshold_pos β hβ) f
  simpa only [rate_threshold β (by linarith), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_assoc] using h

omit n [NeZero n] [Fintype I] in
/-- Bounded-mass slow sources concentrate below a vanishing defect threshold
on any fixed finite family, uniformly in its locations and the lattice period. -/
theorem slow_mode_concentration [Finite I] {J : Type*} {l : Filter J}
    (N : J → ℕ) [∀ j, NeZero (N j)] (β : J → ℝ) (hβ : ∀ j, 1 < β j)
    (q : ∀ j, I → Plaquette (N j)) (f : ∀ j, C(Slice (2 * N j), ℝ))
    (hmass : ∀ j, mass (2 * N j) (β j) (by linarith [hβ j]) (f j) ≤ 1)
    (hloss : Filter.Tendsto (fun j => loss (2 * N j) (β j) (by linarith [hβ j]) (f j))
      l (nhds 0)) (hg : Filter.Tendsto β l Filter.atTop) :
    Filter.Tendsto (fun j => threshold (β j)) l (nhds 0) ∧
      Filter.Tendsto (fun j => ∫ u, (bad (N j) (q j) (fun _ => threshold (β j))).indicator
        (fun v => (f j v) ^ 2) u ∂groundLaw (2 * N j) (β j) (by linarith [hβ j])) l (nhds 0) := by
  letI := Fintype.ofFinite I
  refine ⟨threshold_tendsto.comp hg, ?_⟩
  have hi : Filter.Tendsto (fun j => coefficient / β j) l (nhds 0) := by
    simpa only [div_eq_mul_inv, Function.comp_apply, mul_zero] using
      (tendsto_inv_atTop_zero.comp hg).const_mul coefficient
  have ht := (hloss.const_mul 2).add (hi.const_mul (2 * (Fintype.card I : ℝ)))
  simp only [mul_zero, add_zero] at ht
  apply squeeze_zero' _ _ ht
  · exact Filter.Eventually.of_forall (fun j => integral_nonneg (fun u =>
      Set.indicator_nonneg (fun v _ => sq_nonneg (f j v)) u))
  · apply Filter.Eventually.of_forall
    intro j
    have ht := local_tail (N j) (β j) (hβ j) (q j) (f j)
    have hn : 0 ≤ 2 * (Fintype.card I : ℝ) * (coefficient / β j) :=
      mul_nonneg (by positivity) (div_nonneg coefficient_nonneg (by linarith [hβ j]))
    have hm := mul_le_mul_of_nonneg_left (hmass j) hn
    change _ ≤ 2 * loss (2 * N j) (β j) (by linarith [hβ j]) (f j) +
      (2 * (Fintype.card I : ℝ)) * (coefficient / β j)
    linarith

end
end UnifiedTheory.Clay.YangMills.WilsonPlaquetteLocalLimit
