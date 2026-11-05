/- One block step, as a statement about the law. The blocked law is the push-forward of the actual twisted law under a block
map with one staple weight per pair of directions. The weights have total below `1`, so the map is continuous and exactly
gauge covariant. `α < 1/6` is the isotropic range of this condition. `blockW_iso` identifies the isotropic case with
`TwistedBlockMap`.

Proved for all admissible weights, with no smallness of the field. The blocked law is invariant under coarse gauge
transformations (`gauge_blockedLaw`). The twist descends exactly (`cellSign_emb`), so flat fields block to flat fields
(`flat_block`). For every field the coarse action is at most `(4 + 64 e)(1 + 48 e)` times the fine action
(`actionL_blockField_le`); the constant is `4` with no staples and about `120` to `160` at `α = 0.15`, so it says nothing
about stability under iteration. The law splits by the set `Λ` of bad blocks, a subset of the coarse sites. Each bad block
costs `exp(-β δ²)` in density against an extensive prefactor `Z⁻¹` (`blockedPiece_le`), and each piece has a stated support
(`blockedPiece_support`). A density against the push-forward of Haar measure exists, with the classical lower bound
(`exists_effective_action`). That existence is nearly automatic: a push-forward of a density bounded between positive
constants has such a density, against the pushed reference. The content is the lower bound `(β/K) S_c`.

Translations. Every iterate of an admissible map is invariant under translations up to center signs (`iterLaw_tInv`). For such a
law the blocked action is at most `(1 + 16 e)(1 + 12 e)` times the fine action in the mean (`mean_action_stepW`). With no staples
the factor is `1`, against the field-wise `4`, at every step (`iterLaw_action_step`, `iterLaw_mean_defect`). With staples it is still
about `10` at `α = 0.15`, and even at `1` it allows a factor `16` per plaquette, while the free value is about `2.7`. The local form
(`iterLaw_mean_total`) is free of the volume but empty below thresholds in `β` that grow by `16 K` at each step.

Reflection positivity. It survives on the whole closed half, from any reflection-positive measure, when spatial links have
no time staples (`isRP_step_of`), so every iterate of such a map is a gauge-invariant reflection-positive probability
measure on a twisted lattice (`iterLaw_rp`, `iterLaw_gauge`). For every admissible map it survives on the open half
(`blocked_open_reflection_positive`). This is not convergence of anything.

With no staples, on the path-product map. The push-forward of Haar measure is Haar measure (`blockedHaar_zero`) and the density
is an explicit constrained integral at every coarse field (`blockedLaw_zero_eq`), with `effS` continuous, gauge invariant and
Lipschitz in the sum of link distances (`effS_lipschitz`). There is an exact interpolation: `interp V` is a fine field whose
lines are `V`, with fine action exactly `4 S_c(V)` and every fine defect `0` or a coarse defect (`blockField_interp`,
`actionL_interp_eq`, `defect_interp_even`), gauge covariant with no gauge fixing (`interp_act`). At every coarse field it gives
`(β/4) S_c + log Z ≤ effS ≤ 8 β S_c + links · log cap(96 β) + log Z` (`constrainedZ_upper`, `effS_le_interp`, `effS_sub_ge`). It
gives the fine action and the bad blocks conditioned on the coarse field (`constrained_action_tail`, `constrained_bad_blocks`,
`twistedLaw_fine_given_coarse`), and a lower bound on the fully good piece (`constrainedPiece_empty_lower`).

Not proved. Reflection positivity for the isotropic map on the reflection slices is not disproved for the Wilson law;
`smeared_form_negative` is algebra about one covariance, with no link to the block map. Whether the push-forward of Haar measure
is absolutely continuous against Haar measure when there are staples is open (`blockedLaw_ac_iff` is the same two-sided bound as
`exists_effective_action`, and only records that the question does not involve `β`). The interpolation is for the path-product
map only, which the numerics show roughens under iteration. Its entropy term `links · log cap(96 β)` is extensive and is not
separated into a determinant and a remainder, so `effS` has no local form here, and the factor `32` between the classical terms
is not `1`. The conditional bounds are worst case and say nothing unless `β` is above explicit thresholds free of the volume:
`constrained_bad_blocks` needs `β > 16 log cap(96 β)`, about `β > 276` (with the action normalized as in `actionL`, where the
standard coupling is `2 β`), and more for small `δ`. No convergence of any iteration is claimed. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockLaw
import UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalTail
import UnifiedTheory.Clay.YangMills.ReflectedDefectBound
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockStep
noncomputable section
open MeasureTheory PeriodicLattice4 TwistedFlat TwistedHessian TwistedStability TwistedLandau
open TwistedCovariant TwistedBlockMap TwistedLocalization TwistedBadSet TwistedBlockLaw
open PeriodicTimeReflection RegulatedGauge
open WilsonSingleLinkStaples (Q)
open scoped Quaternion ENNReal

/-! ### A block map with one weight per pair of directions -/

section Weighted

variable {N : ℕ} [NeZero N]

/-- Staple weights: `a μ ν` multiplies the two staples of a link `μ` in the direction `ν`. -/
abbrev Wt := Fin 4 → Fin 4 → ℝ

def stapleW (a : Wt) (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) : ℍ[ℝ] :=
  if ν = μ then 0 else a μ ν • ((sUp U μ ν x : ℍ[ℝ]) + (sDown U μ ν x : ℍ[ℝ]))

def blockSumW (a : Wt) (U : Vertex N → Fin 4 → Q) (μ : Fin 4) (x : Vertex N) : ℍ[ℝ] :=
  (lineU U μ x : ℍ[ℝ]) + ∑ ν, stapleW a U μ ν x

/-- The blocked link with weights `a`. -/
def blockW (a : Wt) (U : Vertex N → Fin 4 → Q) (x : Vertex N) (μ : Fin 4) : Q :=
  proj (blockSumW a U μ x)

/-- Total weight of the staples of a link `μ`. -/
def tot (a : Wt) (μ : Fin 4) : ℝ := ∑ ν, if ν = μ then 0 else 2 * a μ ν

/-- Nonnegative weights whose staples cannot cancel the line. -/
structure Adm (a : Wt) : Prop where
  nonneg : ∀ μ ν, 0 ≤ a μ ν
  small : ∀ μ, tot a μ < 1

/-- The isotropic weights of `TwistedBlockMap`. -/
def iso (α : ℝ) : Wt := fun _ _ => α

/-- **The reflection-compatible weights.** A spatial link has no staple crossing a time slice. -/
def aniso (α : ℝ) : Wt := fun μ ν => if μ ≠ 0 ∧ ν = 0 then 0 else α

theorem blockSumW_iso (α : ℝ) (U : Vertex N → Fin 4 → Q) (μ : Fin 4) (x : Vertex N) :
    blockSumW (iso α) U μ x = blockSum U α μ x := by
  unfold blockSumW blockSum stapleW iso
  rw [Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs <;> simp

/-- The isotropic weights give exactly the map of `TwistedBlockMap`. -/
theorem blockW_iso (α : ℝ) (U : Vertex N → Fin 4 → Q) (x : Vertex N) (μ : Fin 4) :
    blockW (iso α) U x μ = blockLink U α x μ := by
  unfold blockW blockLink
  rw [blockSumW_iso]

theorem tot_iso (α : ℝ) (μ : Fin 4) : tot (iso α) μ = 6 * α := by
  unfold tot iso
  fin_cases μ <;> simp [Fin.sum_univ_four] <;> ring

theorem tot_aniso (α : ℝ) (μ : Fin 4) : tot (aniso α) μ = if μ = 0 then 6 * α else 4 * α := by
  unfold tot aniso
  fin_cases μ <;> simp [Fin.sum_univ_four] <;> ring

theorem adm_iso (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 6) : Adm (iso α) :=
  ⟨fun _ _ => h0, fun μ => by rw [tot_iso]; linarith only [h1]⟩

theorem adm_aniso (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 6) : Adm (aniso α) := by
  refine ⟨fun μ ν => ?_, fun μ => ?_⟩
  · unfold aniso
    split_ifs
    · exact le_rfl
    · exact h0
  · rw [tot_aniso]
    split_ifs <;> linarith only [h0, h1]

theorem norm_stapleW_le (a : Wt) (ha : ∀ μ ν, 0 ≤ a μ ν) (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4)
    (x : Vertex N) : ‖stapleW a U μ ν x‖ ≤ if ν = μ then 0 else 2 * a μ ν := by
  unfold stapleW
  split_ifs with h
  · simp
  · rw [norm_smul, Real.norm_of_nonneg (ha μ ν)]
    have : ‖(sUp U μ ν x : ℍ[ℝ]) + (sDown U μ ν x : ℍ[ℝ])‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_coe, norm_coe]
      norm_num
    nlinarith only [this, ha μ ν]

/-- For admissible weights the sum never vanishes, so the map is continuous and exactly covariant. -/
theorem blockSumW_ne (a : Wt) (ha : Adm a) (U : Vertex N → Fin 4 → Q) (μ : Fin 4) (x : Vertex N) :
    blockSumW a U μ x ≠ 0 := by
  intro h0
  have hs : ‖∑ ν, stapleW a U μ ν x‖ ≤ tot a μ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => norm_stapleW_le a ha.nonneg U μ ν x)
  have hl : (lineU U μ x : ℍ[ℝ]) = -∑ ν, stapleW a U μ ν x := eq_neg_of_add_eq_zero_left h0
  have h1 : ‖(lineU U μ x : ℍ[ℝ])‖ = 1 := norm_coe _
  rw [hl, norm_neg] at h1
  linarith only [hs, h1, ha.small μ]

/-! ### Exact gauge covariance -/

theorem stapleW_act (g : Vertex N → Q) (a : Wt) (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4)
    (x : Vertex N) :
    stapleW a (act g U) μ ν x =
      (g x : ℍ[ℝ]) * stapleW a U μ ν x * ((g (step N (step N x μ) μ))⁻¹ : Q) := by
  unfold stapleW
  split_ifs with h
  · simp
  · rw [sUp_act, sDown_act]
    have c (u : Q) : ((g x * u * (g (step N (step N x μ) μ))⁻¹ : Q) : ℍ[ℝ]) =
      (g x : ℍ[ℝ]) * u * ((g (step N (step N x μ) μ))⁻¹ : Q) := rfl
    rw [c, c, mul_smul_comm, smul_mul_assoc, mul_add, add_mul]

theorem blockSumW_act (g : Vertex N → Q) (a : Wt) (U : Vertex N → Fin 4 → Q) (μ : Fin 4)
    (x : Vertex N) :
    blockSumW a (act g U) μ x =
      (g x : ℍ[ℝ]) * blockSumW a U μ x * ((g (step N (step N x μ) μ))⁻¹ : Q) := by
  unfold blockSumW
  simp only [stapleW_act]
  rw [lineU_act, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  rfl

/-- **Gauge covariance of the blocked link, everywhere.** -/
theorem blockW_act (a : Wt) (ha : Adm a) (g : Vertex N → Q) (U : Vertex N → Fin 4 → Q) (x : Vertex N)
    (μ : Fin 4) :
    blockW a (act g U) x μ = g x * blockW a U x μ * (g (step N (step N x μ) μ))⁻¹ := by
  unfold blockW
  rw [blockSumW_act, proj_mul _ _ _ (blockSumW_ne a ha U μ x)]

/-! ### Distance to the line, for every field -/

/-- The four cell defects that a staple pair `ν` of a link `μ` at `x` depends on. -/
def cells (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) : ℝ :=
  cd U μ ν x + cd U μ ν (step N x μ) + cd U μ ν (back x ν) + cd U μ ν (step N (back x ν) μ)

def cells2 (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) : ℝ :=
  cd U μ ν x ^ 2 + cd U μ ν (step N x μ) ^ 2 + cd U μ ν (back x ν) ^ 2 +
    cd U μ ν (step N (back x ν) μ) ^ 2

theorem cd_nonneg (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) : 0 ≤ cd U μ ν x := by
  unfold cd
  split_ifs <;> exact defect_nonneg _ _ _ _

theorem cells_nonneg (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) : 0 ≤ cells U μ ν x := by
  unfold cells
  have := cd_nonneg U μ ν
  linarith only [this x, this (step N x μ), this (back x ν), this (step N (back x ν) μ)]

/-- All cell defects around a link. -/
def cellE (U : Vertex N → Fin 4 → Q) (μ : Fin 4) (x : Vertex N) : ℝ :=
  ∑ ν, if ν = μ then 0 else cells U μ ν x

def cellE2 (U : Vertex N → Fin 4 → Q) (μ : Fin 4) (x : Vertex N) : ℝ :=
  ∑ ν, if ν = μ then 0 else cells2 U μ ν x

theorem cellE_nonneg (U : Vertex N → Fin 4 → Q) (μ : Fin 4) (x : Vertex N) : 0 ≤ cellE U μ x := by
  refine Finset.sum_nonneg fun ν _ => ?_
  split_ifs
  · exact le_rfl
  · exact cells_nonneg _ _ _ _

theorem cellE2_nonneg (U : Vertex N → Fin 4 → Q) (μ : Fin 4) (x : Vertex N) : 0 ≤ cellE2 U μ x := by
  refine Finset.sum_nonneg fun ν _ => ?_
  split_ifs
  · exact le_rfl
  · unfold cells2
    positivity

theorem cellE_sq_le (U : Vertex N → Fin 4 → Q) (μ : Fin 4) (x : Vertex N) :
    cellE U μ x ^ 2 ≤ 16 * cellE2 U μ x := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 4)))
    (f := fun ν => if ν = μ then (0 : ℝ) else cells U μ ν x)
  have hc : ((Finset.univ : Finset (Fin 4)).card : ℝ) = 4 := by simp
  rw [hc] at h1
  have h2 : ∑ ν, (if ν = μ then (0 : ℝ) else cells U μ ν x) ^ 2 ≤
      ∑ ν, 4 * (if ν = μ then (0 : ℝ) else cells2 U μ ν x) := by
    refine Finset.sum_le_sum fun ν _ => ?_
    split_ifs
    · simp
    · unfold cells cells2
      generalize cd U μ ν x = p
      generalize cd U μ ν (step N x μ) = q
      generalize cd U μ ν (back x ν) = r
      generalize cd U μ ν (step N (back x ν) μ) = s
      nlinarith only [sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (p - s), sq_nonneg (q - r),
        sq_nonneg (q - s), sq_nonneg (r - s)]
  rw [← Finset.mul_sum] at h2
  unfold cellE cellE2
  linarith only [h1, h2]

theorem d_le_two (g h : Q) : d g h ≤ 2 := by
  unfold d
  refine (norm_sub_le _ _).trans ?_
  rw [norm_coe, norm_coe]
  norm_num

theorem stapleW_sub (a : Wt) (ha : ∀ μ ν, 0 ≤ a μ ν) (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4)
    (x : Vertex N) :
    ‖stapleW a U μ ν x - (if ν = μ then 0 else 2 * a μ ν) • (lineU U μ x : ℍ[ℝ])‖ ≤
      if ν = μ then 0 else a μ ν * cells U μ ν x := by
  unfold stapleW
  split_ifs with h
  · simp
  · have e : a μ ν • ((sUp U μ ν x : ℍ[ℝ]) + (sDown U μ ν x : ℍ[ℝ])) -
        (2 * a μ ν) • (lineU U μ x : ℍ[ℝ]) =
        a μ ν • (((sUp U μ ν x : ℍ[ℝ]) - lineU U μ x) + ((sDown U μ ν x : ℍ[ℝ]) - lineU U μ x)) := by
      rw [mul_comm 2, mul_smul, two_smul, ← smul_sub]
      congr 1
      abel
    rw [e, norm_smul, Real.norm_of_nonneg (ha μ ν)]
    refine mul_le_mul_of_nonneg_left ?_ (ha μ ν)
    refine (norm_add_le _ _).trans ?_
    have u := sUp_close U μ ν (Ne.symm h) x
    have v := sDown_close U μ ν (Ne.symm h) x
    have u' : ‖(sUp U μ ν x : ℍ[ℝ]) - lineU U μ x‖ = d (sUp U μ ν x) (lineU U μ x) := rfl
    have v' : ‖(sDown U μ ν x : ℍ[ℝ]) - lineU U μ x‖ = d (sDown U μ ν x) (lineU U μ x) := rfl
    rw [u', v']
    unfold cells
    linarith only [u, v]

/-- **The blocked link is near the line for every field**, with no smallness of the field: the bound is
trivially true when the cells are large. Here `e` bounds `2 a μ ν / (1 + tot a μ)`. -/
theorem blockW_close (a : Wt) (ha : ∀ μ ν, 0 ≤ a μ ν) (e : ℝ)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (U : Vertex N → Fin 4 → Q) (μ : Fin 4)
    (x : Vertex N) : d (blockW a U x μ) (lineU U μ x) ≤ e * cellE U μ x := by
  have htot : 0 ≤ tot a μ := by
    refine Finset.sum_nonneg fun ν _ => ?_
    split_ifs
    · exact le_rfl
    · linarith only [ha μ ν]
  set c := 1 + tot a μ with hc
  have hc0 : 0 < c := by linarith only [htot, hc]
  set η := ∑ ν, if ν = μ then 0 else a μ ν * cells U μ ν x with hη
  have hsplit : blockSumW a U μ x - c • (lineU U μ x : ℍ[ℝ]) =
      ∑ ν, (stapleW a U μ ν x - (if ν = μ then 0 else 2 * a μ ν) • (lineU U μ x : ℍ[ℝ])) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hc, add_smul, one_smul]
    unfold blockSumW tot
    abel
  have hnorm : ‖blockSumW a U μ x - c • (lineU U μ x : ℍ[ℝ])‖ ≤ η := by
    rw [hsplit]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => stapleW_sub a ha U μ ν x)
  have h2η : 2 * η ≤ c * (e * cellE U μ x) := by
    have : 2 * η = ∑ ν, if ν = μ then 0 else 2 * a μ ν * cells U μ ν x := by
      rw [hη, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      split_ifs
      · simp
      · ring
    rw [this]
    unfold cellE
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun ν _ => ?_
    split_ifs with h
    · simp
    · have := mul_le_mul_of_nonneg_right (he μ ν h) (cells_nonneg U μ ν x)
      rw [← hc] at this
      linarith only [this]
  have hfin : 2 * η / c ≤ e * cellE U μ x := by
    rw [div_le_iff₀ hc0]
    linarith only [h2η]
  by_cases hlt : η < c
  · exact (proj_close (lineU U μ x) _ c η hc0 hlt hnorm).2.trans hfin
  · have h : 2 ≤ 2 * η / c := by
      rw [le_div_iff₀ hc0]
      linarith only [not_lt.1 hlt]
    exact (d_le_two _ _).trans (h.trans hfin)

end Weighted

/-! ### The coarse lattice inside the fine one -/

section Coarse

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

instance : NeZero (2 * n) := ⟨by have := NeZero.ne n; omega⟩

/-- Doubling, `ZMod n → ZMod (2n)`. -/
def emb1 (t : ZMod n) : ZMod (2 * n) := ((2 * t.val : ℕ) : ZMod (2 * n))

theorem emb1_val (t : ZMod n) : (emb1 n t).val = 2 * t.val := by
  unfold emb1
  rw [ZMod.val_natCast_of_lt]
  have := t.val_lt
  omega

theorem emb1_eq_mod (p : ℕ) : ((2 * (p % n) : ℕ) : ZMod (2 * n)) = ((2 * p : ℕ) : ZMod (2 * n)) := by
  rw [ZMod.natCast_eq_natCast_iff]
  unfold Nat.ModEq
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod]

theorem emb1_add (s t : ZMod n) : emb1 n (s + t) = emb1 n s + emb1 n t := by
  unfold emb1
  rw [ZMod.val_add, emb1_eq_mod]
  push_cast
  ring

theorem emb1_one : emb1 n 1 = 2 := by
  unfold emb1
  rw [ZMod.val_one_eq_one_mod, emb1_eq_mod]
  norm_num

theorem emb1_zero : emb1 n 0 = 0 := by
  simp [emb1]

theorem emb1_neg (t : ZMod n) : emb1 n (-t) = -emb1 n t := by
  have h := emb1_add n (-t) t
  rw [neg_add_cancel, emb1_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem emb1_injective : Function.Injective (emb1 n) := by
  intro s t h
  have := congrArg ZMod.val h
  rw [emb1_val, emb1_val] at this
  exact ZMod.val_injective n (by omega)

theorem emb1_eq_zero (t : ZMod n) : emb1 n t = 0 ↔ t = 0 := by
  constructor
  · intro h
    exact emb1_injective n (h.trans (emb1_zero n).symm)
  · rintro rfl
    exact emb1_zero n

/-- The value of `emb1 t + b` for `b ≤ 1`. -/
theorem emb1_add_val (t : ZMod n) (b : ℕ) (hb : b ≤ 1) :
    (emb1 n t + (b : ZMod (2 * n))).val = 2 * t.val + b := by
  have e : emb1 n t + (b : ZMod (2 * n)) = ((2 * t.val + b : ℕ) : ZMod (2 * n)) := by
    unfold emb1
    push_cast
    rfl
  rw [e, ZMod.val_natCast_of_lt]
  have := t.val_lt
  omega

theorem emb1_add_one_ne (t : ZMod n) : emb1 n t + 1 ≠ 0 := by
  intro h
  have := emb1_add_val n t 1 le_rfl
  rw [Nat.cast_one, h, ZMod.val_zero] at this
  omega

/-- The even sites. -/
def emb (x : Vertex n) : V' := fun i => emb1 n (x i)

theorem emb_injective : Function.Injective (emb n) := by
  intro x y h
  funext i
  exact emb1_injective n (congrFun h i)

theorem step_apply (N : ℕ) (x : Vertex N) (μ i : Fin 4) :
    step N x μ i = x i + if i = μ then 1 else 0 := by
  by_cases h : i = μ
  · subst h
    simp [step]
  · simp [step, h]

theorem emb_step (x : Vertex n) (μ : Fin 4) :
    emb n (step n x μ) = step (2 * n) (step (2 * n) (emb n x) μ) μ := by
  funext i
  simp only [emb, step_apply]
  by_cases h : i = μ
  · simp only [h, if_true]
    rw [emb1_add, emb1_one]
    ring
  · simp only [h, if_false, add_zero]

/-- **The twist descends exactly.** The total center sign of the four cells of a blocked plaquette is the
coarse twist at the blocked plaquette. -/
theorem cellSign_emb (μ ν : Fin 4) (x : Vertex n) :
    cellSign μ ν (emb n x) = ω ^ twistExp μ ν x := by
  have hne (t : ZMod n) : emb1 n t + 1 ≠ 0 := emb1_add_one_ne n t
  unfold cellSign twistExp
  by_cases h : μ = 1 ∧ ν = 2
  · obtain ⟨rfl, rfl⟩ := h
    have e1 : ∀ y : V', step (2 * n) y 1 1 = y 1 + 1 := fun y => by simp [step_apply]
    have e2 : ∀ y : V', step (2 * n) y 2 2 = y 2 + 1 := fun y => by simp [step_apply]
    have e3 : ∀ y : V', step (2 * n) y 2 1 = y 1 := fun y => by simp [step_apply]
    have e4 : ∀ y : V', step (2 * n) y 1 2 = y 2 := fun y => by simp [step_apply]
    have ee (i : Fin 4) : emb n x i = emb1 n (x i) := rfl
    simp only [e1, e2, e3, e4, ee, emb1_eq_zero, hne, true_and, and_false, false_and, if_false,
      pow_zero, mul_one, one_mul]
  · have hz : ∀ y : V', (if μ = 1 ∧ ν = 2 ∧ y 1 = 0 ∧ y 2 = 0 then 1 else 0 : ℕ) = 0 := fun y => by
      rw [if_neg]
      rintro ⟨h1, h2, -⟩
      exact h ⟨h1, h2⟩
    have hz' : (if μ = 1 ∧ ν = 2 ∧ x 1 = 0 ∧ x 2 = 0 then 1 else 0 : ℕ) = 0 := by
      rw [if_neg]
      rintro ⟨h1, h2, -⟩
      exact h ⟨h1, h2⟩
    simp only [hz, hz', pow_zero, mul_one]

/-- The blocked field on the coarse lattice. -/
def blockField (a : Wt) (U : V' → Fin 4 → Q) : Vertex n → Fin 4 → Q :=
  fun x μ => blockW a U (emb n x) μ

/-- **Gauge covariance on the coarse lattice.** A fine gauge transformation acts on the blocked field by
its restriction to the even sites. -/
theorem blockField_act (a : Wt) (ha : Adm a) (g : V' → Q) (U : V' → Fin 4 → Q) :
    blockField n a (act g U) = act (fun x => g (emb n x)) (blockField n a U) := by
  funext x μ
  change blockW a (act g U) (emb n x) μ = g (emb n x) * blockW a U (emb n x) μ * (g (emb n (step n x μ)))⁻¹
  rw [blockW_act a ha, emb_step]

/-- The coarse plaquette defect, by the fine cells it contains and the cells around its four sides. -/
theorem coarse_defect_le (a : Wt) (ha : ∀ μ ν, 0 ≤ a μ ν) (e : ℝ)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (U : V' → Fin 4 → Q) (μ ν : Fin 4)
    (x : Vertex n) :
    defect (blockField n a U) μ ν x ≤
      (defect U μ ν (step (2 * n) (emb n x) μ) +
        defect U μ ν (step (2 * n) (step (2 * n) (emb n x) μ) ν) + defect U μ ν (emb n x) +
        defect U μ ν (step (2 * n) (emb n x) ν)) +
      e * (cellE U μ (emb n x) + cellE U ν (step (2 * n) (step (2 * n) (emb n x) μ) μ) +
        cellE U μ (step (2 * n) (step (2 * n) (emb n x) ν) ν) + cellE U ν (emb n x)) := by
  set y := emb n x with hy
  have b1 := blockW_close a ha e he U μ y
  have b2 := blockW_close a ha e he U ν (step (2 * n) (step (2 * n) y μ) μ)
  have b3 := blockW_close a ha e he U μ (step (2 * n) (step (2 * n) y ν) ν)
  have b4 := blockW_close a ha e he U ν y
  have f := TwistedSeams.four (blockW a U y μ) (blockW a U (step (2 * n) (step (2 * n) y μ) μ) ν)
    (blockW a U (step (2 * n) (step (2 * n) y ν) ν) μ) (blockW a U y ν) (lineU U μ y)
    (lineU U ν (step (2 * n) (step (2 * n) y μ) μ)) (lineU U μ (step (2 * n) (step (2 * n) y ν) ν))
    (lineU U ν y)
  have l := line_loop U μ ν y
  have t := d_triangle (blockW a U y μ * blockW a U (step (2 * n) (step (2 * n) y μ) μ) ν *
        (blockW a U (step (2 * n) (step (2 * n) y ν) ν) μ)⁻¹ * (blockW a U y ν)⁻¹)
    (lineU U μ y * lineU U ν (step (2 * n) (step (2 * n) y μ) μ) *
      (lineU U μ (step (2 * n) (step (2 * n) y ν) ν))⁻¹ * (lineU U ν y)⁻¹) (cellSign μ ν y)
  have hd : defect (blockField n a U) μ ν x =
      d (blockW a U y μ * blockW a U (step (2 * n) (step (2 * n) y μ) μ) ν *
        (blockW a U (step (2 * n) (step (2 * n) y ν) ν) μ)⁻¹ * (blockW a U y ν)⁻¹) (cellSign μ ν y) := by
    unfold defect blockField
    rw [emb_step, emb_step, hy, cellSign_emb]
  rw [hd]
  have hm : e * (cellE U μ y + cellE U ν (step (2 * n) (step (2 * n) y μ) μ) +
      cellE U μ (step (2 * n) (step (2 * n) y ν) ν) + cellE U ν y) =
      e * cellE U μ y + e * cellE U ν (step (2 * n) (step (2 * n) y μ) μ) +
      e * cellE U μ (step (2 * n) (step (2 * n) y ν) ν) + e * cellE U ν y := by ring
  rw [hm]
  linarith only [b1, b2, b3, b4, f, l, t]

/-- Summing over even sites and their four offsets, each fine cell is seen at most once. -/
theorem sum_four_le (μ ν : Fin 4) (h : μ ≠ ν) (g : V' → ℝ) (hg : ∀ z, 0 ≤ g z) :
    ∑ x : Vertex n, (g (step (2 * n) (emb n x) μ) + g (step (2 * n) (step (2 * n) (emb n x) μ) ν) +
        g (emb n x) + g (step (2 * n) (emb n x) ν)) ≤ ∑ z, g z := by
  classical
  let F : Vertex n × Bool × Bool → V' := fun p =>
    fun i => emb1 n (p.1 i) + (((if i = μ ∧ p.2.1 then 1 else 0 : ℕ) +
      (if i = ν ∧ p.2.2 then 1 else 0 : ℕ) : ℕ) : ZMod (2 * n))
  have hval (x : Vertex n) (b c : Bool) (i : Fin 4) :
      (F (x, b, c) i).val = 2 * (x i).val + ((if i = μ ∧ b then 1 else 0 : ℕ) +
        (if i = ν ∧ c then 1 else 0 : ℕ)) := by
    apply emb1_add_val
    by_cases h1 : i = μ
    · have h2 : i ≠ ν := fun h3 => h (h1.symm.trans h3)
      simp only [h2, false_and, if_false]
      split_ifs <;> omega
    · simp only [h1, false_and, if_false]
      split_ifs <;> omega
  have hinj : Function.Injective F := by
    rintro ⟨x, b, c⟩ ⟨x', b', c'⟩ he
    have hv (i : Fin 4) := congrArg ZMod.val (congrFun he i)
    have hb : b = b' := by
      have := hv μ
      rw [hval, hval] at this
      have hhne : μ ≠ ν := h
      simp only [true_and, hhne, false_and, if_false] at this
      cases b <;> cases b' <;> simp at this ⊢ <;> omega
    have hc : c = c' := by
      have := hv ν
      rw [hval, hval] at this
      have hhne : ν ≠ μ := h.symm
      simp only [hhne, false_and, if_false, true_and] at this
      cases c <;> cases c' <;> simp at this ⊢ <;> omega
    subst hb hc
    have hx : x = x' := by
      funext i
      apply ZMod.val_injective
      have := hv i
      rw [hval, hval] at this
      omega
    rw [hx]
  have hsum : ∑ p : Vertex n × Bool × Bool, g (F p) ≤ ∑ z, g z := by
    have e : ∑ p : Vertex n × Bool × Bool, g (F p) = ∑ z ∈ Finset.univ.image F, g z :=
      (Finset.sum_image fun _ _ _ _ he => hinj he).symm
    rw [e]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun z _ _ => hg z
  refine le_trans (le_of_eq ?_) hsum
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have e1 : F (x, true, true) = step (2 * n) (step (2 * n) (emb n x) μ) ν := by
    funext i
    simp only [F, step_apply, emb, and_true]
    by_cases h1 : i = μ <;> by_cases h2 : i = ν <;> simp [h1, h2] <;> ring
  have e2 : F (x, true, false) = step (2 * n) (emb n x) μ := by
    funext i
    simp only [F, step_apply, emb, and_true]
    by_cases h1 : i = μ <;> simp [h1]
  have e3 : F (x, false, true) = step (2 * n) (emb n x) ν := by
    funext i
    simp only [F, step_apply, emb, and_true]
    by_cases h1 : i = ν <;> simp [h1]
  have e4 : F (x, false, false) = emb n x := by
    funext i
    simp [F, emb]
  rw [e1, e2, e3, e4]
  ring

end Coarse

/-! ### The blocked action, for every field -/

section ActionBound

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

theorem sum_emb_le (h : V' → ℝ) (hh : ∀ z, 0 ≤ h z) : ∑ x : Vertex n, h (emb n x) ≤ ∑ z, h z := by
  classical
  have e : ∑ x : Vertex n, h (emb n x) = ∑ z ∈ Finset.univ.image (emb n), h z :=
    (Finset.sum_image fun _ _ _ _ he => emb_injective n he).symm
  rw [e]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun z _ _ => hh z

/-- Squared cell defects summed over the lattice, in either order of the plane. -/
def Aq (U : V' → Fin 4 → Q) (μ ν : Fin 4) : ℝ := ∑ z, cd U μ ν z ^ 2

theorem sum_step (N : ℕ) [NeZero N] (f : Vertex N → ℝ) (μ : Fin 4) : ∑ z, f (step N z μ) = ∑ z, f z :=
  Equiv.sum_comp (TwistedHessian.stepEquiv (N := N) μ) f

theorem sum_back (N : ℕ) [NeZero N] (f : Vertex N → ℝ) (μ : Fin 4) : ∑ z, f (back z μ) = ∑ z, f z :=
  Equiv.sum_comp (Equiv.subRight (Pi.single μ 1 : Vertex N)) f

theorem sum_cells2 (U : V' → Fin 4 → Q) (μ ν : Fin 4) : ∑ z, cells2 U μ ν z = 4 * Aq n U μ ν := by
  unfold cells2 Aq
  simp only [Finset.sum_add_distrib]
  rw [sum_step (2 * n) (fun z => cd U μ ν z ^ 2) μ, sum_back (2 * n) (fun z => cd U μ ν z ^ 2) ν,
    sum_back (2 * n) (fun z => cd U μ ν (step (2 * n) z μ) ^ 2) ν,
    sum_step (2 * n) (fun z => cd U μ ν z ^ 2) μ]
  ring

theorem sum_cellE2 (U : V' → Fin 4 → Q) (μ : Fin 4) :
    ∑ z, cellE2 U μ z = ∑ ν, if ν = μ then 0 else 4 * Aq n U μ ν := by
  unfold cellE2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · simp
  · exact sum_cells2 n U μ ν

theorem plane_expand (f : Fin 4 → Fin 4 → ℝ) :
    ∑ d : Plane, f d.1.1 d.1.2 = f 0 1 + f 0 2 + f 0 3 + f 1 2 + f 1 3 + f 2 3 := by
  rw [TwistedActionJet.plane_sum f]
  simp (decide := true) only [Fin.sum_univ_four, if_true, if_false]
  ring

theorem actionL_eq (N : ℕ) [NeZero N] (U : Vertex N → Fin 4 → Q) :
    actionL U = ∑ d : Plane, ∑ x, defect U d.1.1 d.1.2 x ^ 2 := by
  unfold actionL
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem Aq_lt (U : V' → Fin 4 → Q) (μ ν : Fin 4) (h : μ < ν) :
    Aq n U μ ν = ∑ z, defect U μ ν z ^ 2 := by
  unfold Aq cd
  simp only [h, if_true]

theorem Aq_gt (U : V' → Fin 4 → Q) (μ ν : Fin 4) (h : ν < μ) :
    Aq n U μ ν = ∑ z, defect U ν μ z ^ 2 := by
  have hn : ¬ μ < ν := not_lt.2 h.le
  unfold Aq cd
  simp only [hn, if_false]

/-- The bound on one coarse plaquette, squared. -/
theorem coarse_sq_le (a : Wt) (ha : ∀ μ ν, 0 ≤ a μ ν) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (U : V' → Fin 4 → Q) (μ ν : Fin 4)
    (x : Vertex n) :
    defect (blockField n a U) μ ν x ^ 2 ≤
      (4 + 64 * e) * ((defect U μ ν (step (2 * n) (emb n x) μ) ^ 2 +
        defect U μ ν (step (2 * n) (step (2 * n) (emb n x) μ) ν) ^ 2 + defect U μ ν (emb n x) ^ 2 +
        defect U μ ν (step (2 * n) (emb n x) ν) ^ 2) +
      e * (cellE2 U μ (emb n x) + cellE2 U ν (step (2 * n) (step (2 * n) (emb n x) μ) μ) +
        cellE2 U μ (step (2 * n) (step (2 * n) (emb n x) ν) ν) + cellE2 U ν (emb n x))) := by
  have hb := coarse_defect_le n a ha e he U μ ν x
  have h0 := defect_nonneg (blockField n a U) μ ν x
  set y := emb n x
  set p1 := defect U μ ν (step (2 * n) y μ)
  set p2 := defect U μ ν (step (2 * n) (step (2 * n) y μ) ν)
  set p3 := defect U μ ν y
  set p4 := defect U μ ν (step (2 * n) y ν)
  have c1 := cellE_sq_le U μ y
  have c2 := cellE_sq_le U ν (step (2 * n) (step (2 * n) y μ) μ)
  have c3 := cellE_sq_le U μ (step (2 * n) (step (2 * n) y ν) ν)
  have c4 := cellE_sq_le U ν y
  have n1 := cellE_nonneg U μ y
  have n2 := cellE_nonneg U ν (step (2 * n) (step (2 * n) y μ) μ)
  have n3 := cellE_nonneg U μ (step (2 * n) (step (2 * n) y ν) ν)
  have n4 := cellE_nonneg U ν y
  set E1 := cellE U μ y
  set E2 := cellE U ν (step (2 * n) (step (2 * n) y μ) μ)
  set E3 := cellE U μ (step (2 * n) (step (2 * n) y ν) ν)
  set E4 := cellE U ν y
  set F1 := cellE2 U μ y
  set F2 := cellE2 U ν (step (2 * n) (step (2 * n) y μ) μ)
  set F3 := cellE2 U μ (step (2 * n) (step (2 * n) y ν) ν)
  set F4 := cellE2 U ν y
  set D := defect (blockField n a U) μ ν x
  set M := p1 + p2 + p3 + p4 with hM
  set T := E1 + E2 + E3 + E4 with hT
  set M2 := p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + p4 ^ 2 with hM2
  set T2 := F1 + F2 + F3 + F4 with hT2
  have hM4 : M ^ 2 ≤ 4 * M2 := by
    rw [hM, hM2]
    nlinarith only [sq_nonneg (p1 - p2), sq_nonneg (p1 - p3), sq_nonneg (p1 - p4), sq_nonneg (p2 - p3),
      sq_nonneg (p2 - p4), sq_nonneg (p3 - p4)]
  have hT64 : T ^ 2 ≤ 64 * T2 := by
    have : T ^ 2 ≤ 4 * (E1 ^ 2 + E2 ^ 2 + E3 ^ 2 + E4 ^ 2) := by
      rw [hT]
      nlinarith only [sq_nonneg (E1 - E2), sq_nonneg (E1 - E3), sq_nonneg (E1 - E4), sq_nonneg (E2 - E3),
        sq_nonneg (E2 - E4), sq_nonneg (E3 - E4)]
    rw [hT2]
    linarith only [this, c1, c2, c3, c4]
  have hD : D ≤ M + e * T := hb
  have hS : D ^ 2 ≤ (M + e * T) ^ 2 := pow_le_pow_left₀ h0 hD 2
  have hcross : 2 * (M * T) ≤ 16 * M ^ 2 + T ^ 2 / 16 := by
    nlinarith only [sq_nonneg (4 * M - T / 4)]
  have h1 : e * (2 * (M * T)) ≤ e * (64 * M2 + 4 * T2) :=
    mul_le_mul_of_nonneg_left (by linarith only [hcross, hM4, hT64]) he0
  have h2 : e ^ 2 * T ^ 2 ≤ e ^ 2 * (64 * T2) := mul_le_mul_of_nonneg_left hT64 (sq_nonneg e)
  have hexp : (M + e * T) ^ 2 = M ^ 2 + e * (2 * (M * T)) + e ^ 2 * T ^ 2 := by ring
  have hr : (4 + 64 * e) * (M2 + e * T2) = 4 * M2 + e * (64 * M2 + 4 * T2) + e ^ 2 * (64 * T2) := by ring
  rw [hr]
  linarith only [hS, hexp, hM4, h1, h2]

theorem six_alg (e A01 A02 A03 A12 A13 A23 b01 b02 b03 b12 b13 b23 : ℝ)
    (p01 : b01 ≤ (4 + 64 * e) * (A01 + e * (2 * (4 * A01 + 4 * A02 + 4 * A03) +
      2 * (4 * A01 + 4 * A12 + 4 * A13))))
    (p02 : b02 ≤ (4 + 64 * e) * (A02 + e * (2 * (4 * A01 + 4 * A02 + 4 * A03) +
      2 * (4 * A02 + 4 * A12 + 4 * A23))))
    (p03 : b03 ≤ (4 + 64 * e) * (A03 + e * (2 * (4 * A01 + 4 * A02 + 4 * A03) +
      2 * (4 * A03 + 4 * A13 + 4 * A23))))
    (p12 : b12 ≤ (4 + 64 * e) * (A12 + e * (2 * (4 * A01 + 4 * A12 + 4 * A13) +
      2 * (4 * A02 + 4 * A12 + 4 * A23))))
    (p13 : b13 ≤ (4 + 64 * e) * (A13 + e * (2 * (4 * A01 + 4 * A12 + 4 * A13) +
      2 * (4 * A03 + 4 * A13 + 4 * A23))))
    (p23 : b23 ≤ (4 + 64 * e) * (A23 + e * (2 * (4 * A02 + 4 * A12 + 4 * A23) +
      2 * (4 * A03 + 4 * A13 + 4 * A23)))) :
    b01 + b02 + b03 + b12 + b13 + b23 ≤
      (4 + 64 * e) * (1 + 48 * e) * (A01 + A02 + A03 + A12 + A13 + A23) := by
  linarith only [p01, p02, p03, p12, p13, p23]

/-- One plane of the coarse action. -/
theorem plane_le (a : Wt) (ha : ∀ μ ν, 0 ≤ a μ ν) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (U : V' → Fin 4 → Q) (μ ν : Fin 4) (hne : μ ≠ ν) :
    ∑ x, defect (blockField n a U) μ ν x ^ 2 ≤
      (4 + 64 * e) * (∑ z, defect U μ ν z ^ 2 + e * (2 * ∑ z, cellE2 U μ z + 2 * ∑ z, cellE2 U ν z)) := by
  have hK : 0 ≤ 4 + 64 * e := by positivity
  refine (Finset.sum_le_sum fun x _ => coarse_sq_le n a ha e he0 he U μ ν x).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hK
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have m1 := sum_four_le n μ ν hne (fun z => defect U μ ν z ^ 2) fun z => sq_nonneg _
  have s1 : ∑ x : Vertex n, cellE2 U μ (emb n x) ≤ ∑ z, cellE2 U μ z :=
    sum_emb_le n _ fun z => cellE2_nonneg U μ z
  have s2 : ∑ x : Vertex n, cellE2 U ν (emb n x) ≤ ∑ z, cellE2 U ν z :=
    sum_emb_le n _ fun z => cellE2_nonneg U ν z
  have s3 : ∑ x : Vertex n, cellE2 U ν (step (2 * n) (step (2 * n) (emb n x) μ) μ) ≤
      ∑ z, cellE2 U ν z := by
    refine (sum_emb_le n (fun z => cellE2 U ν (step (2 * n) (step (2 * n) z μ) μ))
      fun z => cellE2_nonneg U ν _).trans (le_of_eq ?_)
    rw [sum_step (2 * n) (fun z => cellE2 U ν (step (2 * n) z μ)) μ,
      sum_step (2 * n) (fun z => cellE2 U ν z) μ]
  have s4 : ∑ x : Vertex n, cellE2 U μ (step (2 * n) (step (2 * n) (emb n x) ν) ν) ≤
      ∑ z, cellE2 U μ z := by
    refine (sum_emb_le n (fun z => cellE2 U μ (step (2 * n) (step (2 * n) z ν) ν))
      fun z => cellE2_nonneg U μ _).trans (le_of_eq ?_)
    rw [sum_step (2 * n) (fun z => cellE2 U μ (step (2 * n) z ν)) ν,
      sum_step (2 * n) (fun z => cellE2 U μ z) ν]
  have hs : ∑ x : Vertex n, (cellE2 U μ (emb n x) + cellE2 U ν (step (2 * n) (step (2 * n) (emb n x) μ) μ) +
      cellE2 U μ (step (2 * n) (step (2 * n) (emb n x) ν) ν) + cellE2 U ν (emb n x)) ≤
      2 * ∑ z, cellE2 U μ z + 2 * ∑ z, cellE2 U ν z := by
    simp only [Finset.sum_add_distrib]
    linarith only [s1, s2, s3, s4]
  have := mul_le_mul_of_nonneg_left hs he0
  exact add_le_add m1 this

/-- The sum of squared cell defects around all links in each direction, in terms of the planes. -/
theorem sum_cellE2_expand (U : V' → Fin 4 → Q) :
    (∑ z, cellE2 U 0 z = 4 * (∑ z, defect U 0 1 z ^ 2) + 4 * (∑ z, defect U 0 2 z ^ 2) +
      4 * (∑ z, defect U 0 3 z ^ 2)) ∧
    (∑ z, cellE2 U 1 z = 4 * (∑ z, defect U 0 1 z ^ 2) + 4 * (∑ z, defect U 1 2 z ^ 2) +
      4 * (∑ z, defect U 1 3 z ^ 2)) ∧
    (∑ z, cellE2 U 2 z = 4 * (∑ z, defect U 0 2 z ^ 2) + 4 * (∑ z, defect U 1 2 z ^ 2) +
      4 * (∑ z, defect U 2 3 z ^ 2)) ∧
    (∑ z, cellE2 U 3 z = 4 * (∑ z, defect U 0 3 z ^ 2) + 4 * (∑ z, defect U 1 3 z ^ 2) +
      4 * (∑ z, defect U 2 3 z ^ 2)) := by
  rw [← Aq_lt n U 0 1 (by decide), ← Aq_lt n U 0 2 (by decide), ← Aq_lt n U 0 3 (by decide),
    ← Aq_lt n U 1 2 (by decide), ← Aq_lt n U 1 3 (by decide), ← Aq_lt n U 2 3 (by decide)]
  have e10 := (Aq_gt n U 1 0 (by decide)).trans (Aq_lt n U 0 1 (by decide)).symm
  have e20 := (Aq_gt n U 2 0 (by decide)).trans (Aq_lt n U 0 2 (by decide)).symm
  have e30 := (Aq_gt n U 3 0 (by decide)).trans (Aq_lt n U 0 3 (by decide)).symm
  have e21 := (Aq_gt n U 2 1 (by decide)).trans (Aq_lt n U 1 2 (by decide)).symm
  have e31 := (Aq_gt n U 3 1 (by decide)).trans (Aq_lt n U 1 3 (by decide)).symm
  have e32 := (Aq_gt n U 3 2 (by decide)).trans (Aq_lt n U 2 3 (by decide)).symm
  simp only [sum_cellE2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Fin.sum_univ_four, e10, e20, e30, e21, e31, e32]

/-- **The blocked action is at most a constant times the action, for every field.** No smallness, no
dependence on the volume, and with no staples the constant is `4`. Worst case, and useless for iteration: it costs a
factor at every step, while by a hand count a smooth field has blocked action about equal to its action. -/
theorem actionL_blockField_le (a : Wt) (ha : ∀ μ ν, 0 ≤ a μ ν) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (U : V' → Fin 4 → Q) :
    actionL (blockField n a U) ≤ (4 + 64 * e) * (1 + 48 * e) * actionL U := by
  obtain ⟨hF0, hF1, hF2, hF3⟩ := sum_cellE2_expand n U
  have hpl := plane_le n a ha e he0 he U
  have p01 := hpl 0 1 (by decide)
  have p02 := hpl 0 2 (by decide)
  have p03 := hpl 0 3 (by decide)
  have p12 := hpl 1 2 (by decide)
  have p13 := hpl 1 3 (by decide)
  have p23 := hpl 2 3 (by decide)
  rw [hF0, hF1] at p01
  rw [hF0, hF2] at p02
  rw [hF0, hF3] at p03
  rw [hF1, hF2] at p12
  rw [hF1, hF3] at p13
  rw [hF2, hF3] at p23
  rw [actionL_eq, actionL_eq, plane_expand (fun μ ν => ∑ x, defect (blockField n a U) μ ν x ^ 2),
    plane_expand (fun μ ν => ∑ x, defect U μ ν x ^ 2)]
  exact six_alg e _ _ _ _ _ _ _ _ _ _ _ _ p01 p02 p03 p12 p13 p23

theorem actionL_flat (N : ℕ) [NeZero N] (U : Vertex N → Fin 4 → Q) (hU : TwistedFlatField U) :
    actionL U = 0 := by
  unfold actionL
  refine Finset.sum_eq_zero ?_
  rintro ⟨x, ⟨⟨μ, ν⟩, h⟩⟩ _
  have hd : defect U μ ν x = 0 := by
    unfold defect d
    rw [hU x μ ν h, sub_self, norm_zero]
  simp only [hd]
  norm_num

theorem flat_of_actionL (N : ℕ) [NeZero N] (V : Vertex N → Fin 4 → Q) (h0 : actionL V ≤ 0) :
    TwistedFlatField V := by
  intro x μ ν h
  have key : ∀ p : PlaquetteIndex N, defect V p.2.1.1 p.2.1.2 p.1 ^ 2 ≤ actionL V := fun p => by
    unfold actionL
    exact Finset.single_le_sum (f := fun p : PlaquetteIndex N => defect V p.2.1.1 p.2.1.2 p.1 ^ 2)
      (fun i _ => sq_nonneg (defect V i.2.1.1 i.2.1.2 i.1)) (Finset.mem_univ p)
  have hd : defect V μ ν x ^ 2 ≤ actionL V := key (x, ⟨(μ, ν), h⟩)
  have hz : defect V μ ν x = 0 := by
    have h1 : defect V μ ν x ^ 2 ≤ 0 := hd.trans h0
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h1 (sq_nonneg _))
  unfold defect d at hz
  exact Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 hz))

/-- **The twist survives at zero action.** A field of zero action blocks to a field of zero coarse action
with the coarse twist. -/
theorem flat_block (a : Wt) (ha : ∀ μ ν, 0 ≤ a μ ν) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (U : V' → Fin 4 → Q) (hU : TwistedFlatField U) :
    TwistedFlatField (blockField n a U) := by
  have h1 := actionL_blockField_le n a ha e he0 he U
  rw [actionL_flat (2 * n) U hU, mul_zero] at h1
  exact flat_of_actionL n _ h1

end ActionBound

/-! ### The blocked law -/

section Law

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

theorem config_ext (N : ℕ) (U U' : Configuration (Vertex N) Q)
    (h : ∀ x μ, linkValue N Q U x μ = linkValue N Q U' x μ) : U = U' := by
  funext e
  rcases e with ⟨x, y, μ, hμ⟩
  cases hμ
  exact h x μ

/-- The block map on configurations, from the lattice of side `2n` to the lattice of side `n`. -/
def blockCfg (a : Wt) (U : Configuration V' Q) : Configuration (Vertex n) Q :=
  fun e => blockW a (linkValue (2 * n) Q U) (emb n e.1) e.2.2.val

theorem link_blockCfg (a : Wt) (U : Configuration V' Q) :
    linkValue n Q (blockCfg n a U) = blockField n a (linkValue (2 * n) Q U) := rfl

theorem continuous_proj_comp {X : Type*} [TopologicalSpace X] (w : X → ℍ[ℝ]) (hw : Continuous w)
    (h0 : ∀ x, w x ≠ 0) : Continuous fun x => proj (w x) := by
  refine continuous_induced_rng.2 ?_
  have e : (Subtype.val ∘ fun x => proj (w x)) = fun x => ‖w x‖⁻¹ • w x := by
    funext x
    exact proj_coe (w x) (h0 x)
  rw [e]
  exact (hw.norm.inv₀ fun x => norm_ne_zero_iff.2 (h0 x)).smul hw

theorem continuous_blockSumW (a : Wt) (μ : Fin 4) (y : V') :
    Continuous fun U : Configuration V' Q => blockSumW a (linkValue (2 * n) Q U) μ y := by
  have hl (x : V') (ρ : Fin 4) : Continuous fun U : Configuration V' Q => linkValue (2 * n) Q U x ρ :=
    continuous_apply _
  have hline (x : V') : Continuous fun U : Configuration V' Q =>
      ((lineU (linkValue (2 * n) Q U) μ x : Q) : ℍ[ℝ]) := by
    unfold lineU
    exact continuous_subtype_val.comp ((hl _ _).mul (hl _ _))
  have hup (ν : Fin 4) : Continuous fun U : Configuration V' Q =>
      ((sUp (linkValue (2 * n) Q U) μ ν y : Q) : ℍ[ℝ]) := by
    unfold sUp
    exact continuous_subtype_val.comp
      (continuous_const.mul ((((hl _ _).mul (hl _ _)).mul (hl _ _)).mul (hl _ _).inv))
  have hdn (ν : Fin 4) : Continuous fun U : Configuration V' Q =>
      ((sDown (linkValue (2 * n) Q U) μ ν y : Q) : ℍ[ℝ]) := by
    unfold sDown sDownY
    exact continuous_subtype_val.comp
      (continuous_const.mul ((((hl _ _).inv.mul (hl _ _)).mul (hl _ _)).mul (hl _ _)))
  unfold blockSumW
  refine (hline y).add (continuous_finset_sum _ fun ν _ => ?_)
  unfold stapleW
  split_ifs
  · exact continuous_const
  · exact ((hup ν).add (hdn ν)).const_smul _

/-- For admissible weights the block map is continuous. -/
theorem continuous_blockCfg (a : Wt) (ha : Adm a) : Continuous (blockCfg n a) := by
  refine continuous_pi fun e => ?_
  exact continuous_proj_comp _ (continuous_blockSumW n a _ _) fun U => blockSumW_ne a ha _ _ _

/-- **The blocked law**: the push-forward of the actual twisted law. -/
def blockedLaw (a : Wt) (β : ℝ) : Measure (Configuration (Vertex n) Q) :=
  (twistedLaw n β).map (blockCfg n a)

/-- The push-forward of the product Haar measure. It is the reference measure of the blocked law. -/
def blockedHaar (a : Wt) : Measure (Configuration (Vertex n) Q) :=
  (referenceMeasure Q V').map (blockCfg n a)

theorem twistedLaw_probability (β : ℝ) : IsProbabilityMeasure (twistedLaw n β) :=
  TwistedReflection.law_probability n Q _ _ WilsonSingleLinkStaples.character_continuous β 2

theorem blockedLaw_probability (a : Wt) (ha : Adm a) (β : ℝ) : IsProbabilityMeasure (blockedLaw n a β) := by
  haveI := twistedLaw_probability n β
  exact Measure.isProbabilityMeasure_map (continuous_blockCfg n a ha).measurable.aemeasurable

theorem blockedHaar_probability (a : Wt) (ha : Adm a) : IsProbabilityMeasure (blockedHaar n a) :=
  Measure.isProbabilityMeasure_map (continuous_blockCfg n a ha).measurable.aemeasurable

/-! ### Gauge invariance -/

theorem action_gauge (β : ℝ) (g : V' → Q) (U : Configuration V' Q) :
    TwistedReflection.action n Q (TwistedReflection.spatialTwist n) WilsonSingleLinkStaples.character β 2
        (gauge V' Q g U) =
      TwistedReflection.action n Q (TwistedReflection.spatialTwist n)
        WilsonSingleLinkStaples.character β 2 U := by
  rw [action_eq_mul, action_eq_mul, TwistedNearFlat.actionOne_eq, TwistedNearFlat.actionOne_eq]
  have e : linkValue (2 * n) Q (gauge V' Q g U) = act g (linkValue (2 * n) Q U) := rfl
  rw [e, actionL_act]

theorem gauge_twistedLaw (β : ℝ) (g : V' → Q) :
    MeasurePreserving (gauge V' Q g) (twistedLaw n β) (twistedLaw n β) :=
  gauge_preserves_gibbsMeasure V' Q _
    (TwistedReflection.continuous_action n Q _ _ WilsonSingleLinkStaples.character_continuous β 2)
    (fun g U => action_gauge n β g U) g

theorem blockCfg_gauge (a : Wt) (ha : Adm a) (g : Vertex n → Q) (U : Configuration V' Q) :
    blockCfg n a (gauge V' Q (Function.extend (emb n) g 1) U) =
      gauge (Vertex n) Q g (blockCfg n a U) := by
  refine config_ext n _ _ fun x μ => ?_
  have e : linkValue (2 * n) Q (gauge V' Q (Function.extend (emb n) g 1) U) =
    act (Function.extend (emb n) g 1) (linkValue (2 * n) Q U) := rfl
  rw [link_blockCfg, e, blockField_act n a ha]
  change Function.extend (emb n) g 1 (emb n x) * blockField n a (linkValue (2 * n) Q U) x μ *
    (Function.extend (emb n) g 1 (emb n (step n x μ)))⁻¹ = g x * _ * (g (step n x μ))⁻¹
  rw [(emb_injective n).extend_apply, (emb_injective n).extend_apply]
  rfl

/-- **The blocked law is invariant under every coarse gauge transformation.** -/
theorem gauge_blockedLaw (a : Wt) (ha : Adm a) (β : ℝ) (g : Vertex n → Q) :
    MeasurePreserving (gauge (Vertex n) Q g) (blockedLaw n a β) (blockedLaw n a β) := by
  have hB := (continuous_blockCfg n a ha).measurable
  refine ⟨(continuous_gauge (Vertex n) Q g).measurable, ?_⟩
  have hG := (continuous_gauge V' Q (Function.extend (emb n) g 1)).measurable
  unfold blockedLaw
  rw [Measure.map_map (continuous_gauge (Vertex n) Q g).measurable hB]
  have e : gauge (Vertex n) Q g ∘ blockCfg n a =
      blockCfg n a ∘ gauge V' Q (Function.extend (emb n) g 1) := by
    funext U
    exact (blockCfg_gauge n a ha g U).symm
  rw [e, ← Measure.map_map hB hG, (gauge_twistedLaw n β _).map_eq]

/-! ### Continuity of the action -/

theorem continuous_actionL (N : ℕ) [NeZero N] :
    Continuous fun V : Configuration (Vertex N) Q => actionL (linkValue N Q V) := by
  have hl (x : Vertex N) (ρ : Fin 4) : Continuous fun V : Configuration (Vertex N) Q => linkValue N Q V x ρ :=
    continuous_apply _
  unfold actionL
  refine continuous_finset_sum _ fun p _ => ?_
  refine Continuous.pow ?_ 2
  unfold defect d
  refine Continuous.norm (Continuous.sub (continuous_subtype_val.comp ?_) continuous_const)
  exact (((hl _ _).mul (hl _ _)).mul (hl _ _).inv).mul (hl _ _).inv

/-! ### The density -/

/-- The fine action. -/
abbrev fineS (β : ℝ) : Configuration V' Q → ℝ :=
  TwistedReflection.action n Q (TwistedReflection.spatialTwist n) WilsonSingleLinkStaples.character β 2

/-- The partition function. -/
abbrev fineZ (β : ℝ) : ℝ≥0∞ := gibbsPartition V' Q (fineS n β)

theorem fineS_eq (β : ℝ) (U : Configuration V' Q) :
    fineS n β U = β * actionL (linkValue (2 * n) Q U) := by
  unfold fineS
  rw [action_eq_mul, TwistedNearFlat.actionOne_eq]

theorem continuous_fineS (β : ℝ) : Continuous (fineS n β) :=
  TwistedReflection.continuous_action n Q _ _ WilsonSingleLinkStaples.character_continuous β 2

theorem measurable_gibbsDensity (β : ℝ) : Measurable (gibbsDensity V' Q (fineS n β)) :=
  (Real.continuous_exp.comp (continuous_fineS n β).neg).measurable.ennreal_ofReal

/-- The twisted law evaluated on a measurable set, as an integral against Haar measure. -/
theorem twistedLaw_apply (β : ℝ) (A : Set (Configuration V' Q)) (hA : MeasurableSet A) :
    twistedLaw n β A = (fineZ n β)⁻¹ * ∫⁻ U in A, gibbsDensity V' Q (fineS n β) U ∂referenceMeasure Q V' := by
  change (fineZ n β)⁻¹ * (referenceMeasure Q V').withDensity (gibbsDensity V' Q (fineS n β)) A = _
  rw [withDensity_apply _ hA]

/-- The number of plaquettes. -/
def fineP : ℕ := Fintype.card (PlaquetteIndex (2 * n))

theorem actionL_le_card (N : ℕ) [NeZero N] (U : Vertex N → Fin 4 → Q) :
    actionL U ≤ 4 * (Fintype.card (PlaquetteIndex N) : ℝ) := by
  unfold actionL
  have h : ∀ p ∈ (Finset.univ : Finset (PlaquetteIndex N)), defect U p.2.1.1 p.2.1.2 p.1 ^ 2 ≤ 4 := by
    intro p _
    have h1 := d_le_two (U p.1 p.2.1.1 * U (step N p.1 p.2.1.1) p.2.1.2 *
      (U (step N p.1 p.2.1.2) p.2.1.1)⁻¹ * (U p.1 p.2.1.2)⁻¹) (ω ^ twistExp p.2.1.1 p.2.1.2 p.1)
    have h2 := defect_nonneg U p.2.1.1 p.2.1.2 p.1
    have h3 : defect U p.2.1.1 p.2.1.2 p.1 ≤ 2 := h1
    nlinarith only [h2, h3]
  refine (Finset.sum_le_card_nsmul _ _ _ h).trans (le_of_eq ?_)
  rw [nsmul_eq_mul, Finset.card_univ]
  ring

/-- **Upper bound on the blocked law.** Against the blocked Haar measure, its density is at most
`Z⁻¹ exp(-(β/K) S_c)`, with `S_c` the coarse action and `K` the constant of `actionL_blockField_le`. -/
theorem blockedLaw_le (a : Wt) (ha : Adm a) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (β : ℝ) (hβ : 0 ≤ β) (A : Set (Configuration (Vertex n) Q))
    (hA : MeasurableSet A) :
    blockedLaw n a β A ≤ (fineZ n β)⁻¹ * ∫⁻ V in A, ENNReal.ofReal (Real.exp
      (-(β / ((4 + 64 * e) * (1 + 48 * e))) * actionL (linkValue n Q V))) ∂blockedHaar n a := by
  have hB := (continuous_blockCfg n a ha).measurable
  unfold blockedLaw blockedHaar
  rw [Measure.map_apply hB hA, twistedLaw_apply n β _ (hB hA)]
  have hg : Measurable fun V : Configuration (Vertex n) Q => ENNReal.ofReal (Real.exp
      (-(β / ((4 + 64 * e) * (1 + 48 * e))) * actionL (linkValue n Q V))) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_actionL n))).measurable.ennreal_ofReal
  rw [setLIntegral_map hA hg hB]
  gcongr with U
  unfold gibbsDensity
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have hK : 0 < (4 + 64 * e) * (1 + 48 * e) := by positivity
  rw [fineS_eq]
  have h2 := actionL_blockField_le n a ha.nonneg e he0 he (linkValue (2 * n) Q U)
  rw [← link_blockCfg] at h2
  have : β / ((4 + 64 * e) * (1 + 48 * e)) * actionL (linkValue n Q (blockCfg n a U)) ≤
      β * actionL (linkValue (2 * n) Q U) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK]
    nlinarith only [mul_le_mul_of_nonneg_left h2 hβ]
  linarith only [this]

/-- **Lower bound on the blocked law.** Against the blocked Haar measure, its density is at least
`Z⁻¹ exp(-4 β P)`, with `P` the number of fine plaquettes. It is a crude bound, extensive in the volume. -/
theorem le_blockedLaw (a : Wt) (ha : Adm a) (β : ℝ) (hβ : 0 ≤ β) (A : Set (Configuration (Vertex n) Q))
    (hA : MeasurableSet A) :
    (fineZ n β)⁻¹ * ENNReal.ofReal (Real.exp (-(β * (4 * (fineP n : ℝ))))) * blockedHaar n a A ≤
      blockedLaw n a β A := by
  have hB := (continuous_blockCfg n a ha).measurable
  unfold blockedLaw blockedHaar
  rw [Measure.map_apply hB hA, Measure.map_apply hB hA, twistedLaw_apply n β _ (hB hA), mul_assoc]
  gcongr
  rw [← setLIntegral_const]
  refine setLIntegral_mono (measurable_gibbsDensity n β) fun U _ => ?_
  unfold gibbsDensity
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  rw [fineS_eq]
  have := mul_le_mul_of_nonneg_left (actionL_le_card (2 * n) (linkValue (2 * n) Q U)) hβ
  have h2 : (Fintype.card (PlaquetteIndex (2 * n)) : ℝ) = fineP n := rfl
  rw [h2] at this
  linarith only [this]

/-- The density relative to the blocked Haar measure exists for all admissible weights, and is pinched between two
explicit functions. Existence is nearly automatic; the upper bound on the density is the content. -/
theorem exists_density (a : Wt) (ha : Adm a) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ ρ : Configuration (Vertex n) Q → ℝ≥0∞, Measurable ρ ∧
      blockedLaw n a β = (blockedHaar n a).withDensity ρ ∧
      ∀ᵐ V ∂blockedHaar n a,
        (fineZ n β)⁻¹ * ENNReal.ofReal (Real.exp (-(β * (4 * (fineP n : ℝ))))) ≤ ρ V ∧
        ρ V ≤ (fineZ n β)⁻¹ * ENNReal.ofReal (Real.exp
          (-(β / ((4 + 64 * e) * (1 + 48 * e))) * actionL (linkValue n Q V))) := by
  haveI := blockedLaw_probability n a ha β
  haveI := blockedHaar_probability n a ha
  set ν := blockedHaar n a with hν
  set L := blockedLaw n a β with hL
  set g : Configuration (Vertex n) Q → ℝ≥0∞ := fun V => ENNReal.ofReal (Real.exp
      (-(β / ((4 + 64 * e) * (1 + 48 * e))) * actionL (linkValue n Q V))) with hg
  have hgm : Measurable g :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_actionL n))).measurable.ennreal_ofReal
  have hup (A : Set (Configuration (Vertex n) Q)) (hA : MeasurableSet A) :
      L A ≤ ∫⁻ V in A, (fineZ n β)⁻¹ * g V ∂ν := by
    rw [lintegral_const_mul _ hgm]
    exact blockedLaw_le n a ha e he0 he β hβ A hA
  have hac : L ≪ ν := by
    refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
    have := hup A hA
    rw [setLIntegral_measure_zero _ _ h0] at this
    exact le_antisymm this (zero_le _)
  have hρ := Measure.withDensity_rnDeriv_eq L ν hac
  have hm := Measure.measurable_rnDeriv L ν
  refine ⟨L.rnDeriv ν, hm, hρ.symm, ?_⟩
  have hint (A : Set (Configuration (Vertex n) Q)) (hA : MeasurableSet A) :
      ∫⁻ V in A, L.rnDeriv ν V ∂ν = L A := by
    rw [← withDensity_apply _ hA, hρ]
  have h1 : L.rnDeriv ν ≤ᵐ[ν] fun V => (fineZ n β)⁻¹ * g V :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite hm fun A hA _ => by
      rw [hint A hA]
      exact hup A hA
  have h2 : (fun _ => (fineZ n β)⁻¹ * ENNReal.ofReal (Real.exp (-(β * (4 * (fineP n : ℝ)))))) ≤ᵐ[ν]
      L.rnDeriv ν :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const fun A hA _ => by
      rw [hint A hA, setLIntegral_const]
      exact le_blockedLaw n a ha β hβ A hA
  filter_upwards [h1, h2] with V h1 h2
  exact ⟨h2, h1⟩

/-- `exists_density` says nothing about Haar measure itself. The blocked law is absolutely continuous with respect to a
reference measure exactly when the push-forward of Haar is. This is the same two-sided bound again; it only records that the
open question with staples does not involve `β`. -/
theorem blockedLaw_ac_iff (a : Wt) (ha : Adm a) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (β : ℝ) (hβ : 0 ≤ β)
    (R : Measure (Configuration (Vertex n) Q)) :
    blockedLaw n a β ≪ R ↔ blockedHaar n a ≪ R := by
  have hZ1 : fineZ n β ≠ ∞ := gibbsPartition_ne_top _ _ _ (continuous_fineS n β)
  have hZ0 : fineZ n β ≠ 0 := (gibbsPartition_pos _ _ _ (continuous_fineS n β)).ne'
  constructor
  · intro h
    refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
    have h1 := le_blockedLaw n a ha β hβ A hA
    rw [h h0] at h1
    have hc : (fineZ n β)⁻¹ * ENNReal.ofReal (Real.exp (-(β * (4 * (fineP n : ℝ))))) ≠ 0 :=
      mul_ne_zero (ENNReal.inv_ne_zero.2 hZ1) (by simpa using Real.exp_pos _)
    have h2 : (fineZ n β)⁻¹ * ENNReal.ofReal (Real.exp (-(β * (4 * (fineP n : ℝ))))) * blockedHaar n a A = 0 :=
      le_antisymm h1 (zero_le _)
    exact (mul_eq_zero.1 h2).resolve_left hc
  · intro h
    refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
    have h1 := blockedLaw_le n a ha e he0 he β hβ A hA
    have h3 : blockedHaar n a A = 0 := h h0
    rw [setLIntegral_measure_zero _ _ h3, mul_zero] at h1
    exact le_antisymm h1 (zero_le _)

/-! ### No staples: the blocked Haar measure is Haar -/

/-- No staples. -/
def zeroW : Wt := fun _ _ => 0

theorem adm_zero : Adm zeroW := by
  refine ⟨fun _ _ => le_rfl, fun μ => ?_⟩
  simp [tot, zeroW]

theorem proj_unit (u : Q) : proj (u : ℍ[ℝ]) = u := by
  have h1 : ‖(u : ℍ[ℝ])‖ = 1 := norm_coe u
  have h0 : (u : ℍ[ℝ]) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  apply Subtype.ext
  rw [proj_coe _ h0, h1, inv_one, one_smul]

theorem blockW_zero (N : ℕ) [NeZero N] (U : Vertex N → Fin 4 → Q) (x : Vertex N) (μ : Fin 4) :
    blockW zeroW U x μ = lineU U μ x := by
  unfold blockW blockSumW stapleW zeroW
  simp only [zero_smul, ite_self, Finset.sum_const_zero, add_zero]
  exact proj_unit _

/-- A fine edge for each coarse link: the first of its two links. -/
def firstEdge (e : Edge (Vertex n)) : Edge V' :=
  (edgeCoordinates (2 * n)).symm (emb n e.1, e.2.2.val)

theorem firstEdge_injective : Function.Injective (firstEdge n) := by
  intro e e' h
  have h1 := (edgeCoordinates (2 * n)).symm.injective h
  have h2 := emb_injective n (congrArg Prod.fst h1)
  have h3 := congrArg Prod.snd h1
  apply (edgeCoordinates n).injective
  exact Prod.ext h2 h3

/-- Translating the first links of the fine field translates the blocked field. -/
theorem blockCfg_zero_mul (h : Configuration (Vertex n) Q) (U : Configuration V' Q) :
    blockCfg n zeroW (Function.extend (firstEdge n) h 1 * U) = h * blockCfg n zeroW U := by
  refine config_ext n _ _ fun x μ => ?_
  rw [link_blockCfg]
  change blockW zeroW _ (emb n x) μ = h ⟨x, step n x μ, forward n x μ⟩ * blockW zeroW _ (emb n x) μ
  rw [blockW_zero, blockW_zero]
  unfold lineU
  have h1 : linkValue (2 * n) Q (Function.extend (firstEdge n) h 1 * U) (emb n x) μ =
      h ⟨x, step n x μ, forward n x μ⟩ * linkValue (2 * n) Q U (emb n x) μ := by
    change Function.extend (firstEdge n) h 1 (firstEdge n ⟨x, step n x μ, forward n x μ⟩) * _ = _
    rw [(firstEdge_injective n).extend_apply]
    rfl
  have h2 : linkValue (2 * n) Q (Function.extend (firstEdge n) h 1 * U)
      (step (2 * n) (emb n x) μ) μ = linkValue (2 * n) Q U (step (2 * n) (emb n x) μ) μ := by
    have hne : ¬∃ e, firstEdge n e = ⟨step (2 * n) (emb n x) μ, step (2 * n) (step (2 * n) (emb n x) μ) μ,
        forward (2 * n) (step (2 * n) (emb n x) μ) μ⟩ := by
      rintro ⟨e, he⟩
      have hf : emb n e.1 = step (2 * n) (emb n x) μ := congrArg Sigma.fst he
      have hμ := congrFun hf μ
      simp only [step_apply, if_true] at hμ
      have v1 := emb1_val n (e.1 μ)
      have v2 := emb1_add_val n (x μ) 1 le_rfl
      rw [Nat.cast_one] at v2
      have : (emb n e.1 μ).val = (emb n x μ + 1).val := by
        rw [hμ]
      change (emb1 n (e.1 μ)).val = (emb1 n (x μ) + 1).val at this
      omega
    change Function.extend (firstEdge n) h 1 ⟨step (2 * n) (emb n x) μ, step (2 * n) (step (2 * n) (emb n x) μ) μ,
        forward (2 * n) (step (2 * n) (emb n x) μ) μ⟩ * _ = _
    rw [Function.extend_apply' _ _ _ hne, Pi.one_apply, one_mul]
    rfl
  rw [h1, h2, mul_assoc]

/-- **With no staples, the push-forward of Haar measure is Haar measure.** -/
theorem blockedHaar_zero : blockedHaar n zeroW = referenceMeasure Q (Vertex n) := by
  have hB := (continuous_blockCfg n zeroW adm_zero).measurable
  haveI : IsProbabilityMeasure (blockedHaar n zeroW) := blockedHaar_probability n zeroW adm_zero
  haveI hfine : (compactHaar Q).IsHaarMeasure := by
    unfold compactHaar
    infer_instance
  haveI hRl : (referenceMeasure Q V').IsMulLeftInvariant := by
    unfold referenceMeasure
    infer_instance
  haveI hL : (blockedHaar n zeroW).IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    have hmul := (measurePreserving_mul_left (referenceMeasure Q V')
      (Function.extend (firstEdge n) h 1))
    unfold blockedHaar
    rw [Measure.map_map (measurable_const_mul h) hB]
    have e : (fun V => h * V) ∘ blockCfg n zeroW =
        blockCfg n zeroW ∘ fun U => Function.extend (firstEdge n) h 1 * U := by
      funext U
      exact (blockCfg_zero_mul n h U).symm
    rw [e, ← Measure.map_map hB hmul.measurable, hmul.map_eq]
  haveI hH : (blockedHaar n zeroW).IsHaarMeasure :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior _ Set.univ isCompact_univ (by simp) (by simp)
      (by simp)
  haveI hR : (referenceMeasure Q (Vertex n)).IsHaarMeasure := by
    unfold referenceMeasure
    infer_instance
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end Law

/-! ### Reflection -/

section Reflection

open PeriodicHalfSplit PeriodicHalfGeometry PeriodicSiteReflection

variable {N : ℕ} [NeZero N]

local notation "θ" => reflectVertex N

/-- The reflected link field. -/
def rf (L : Vertex N → Fin 4 → Q) : Vertex N → Fin 4 → Q := fun x μ =>
  if μ = 0 then (L (θ (step N x 0)) 0)⁻¹ else L (θ x) μ

theorem linkValue_reflect (U : Configuration (Vertex N) Q) :
    linkValue N Q (reflectConfiguration N Q U) = rf (linkValue N Q U) := by
  funext x μ
  unfold rf
  by_cases h : μ = 0
  · subst h
    simpa using reflect_link_time N Q U x
  · simpa [h] using reflect_link_spatial N Q U x μ h

theorem kk_reflect (μ ν : Fin 4) (x : Vertex N) : kk μ ν (θ x) = kk μ ν x := by
  have h1 : θ x 1 = x 1 := by simp [reflectVertex]
  have h2 : θ x 2 = x 2 := by simp [reflectVertex]
  unfold kk twistExp
  simp only [h1, h2]

theorem kk_time (ν : Fin 4) (x : Vertex N) : kk 0 ν x = 0 := by
  unfold kk twistExp
  split_ifs <;> simp_all

theorem back_reflect (x : Vertex N) (ν : Fin 4) (h : ν ≠ 0) : θ (back x ν) = back (θ x) ν := by
  have e : step N (θ (back x ν)) ν = step N (back (θ x) ν) ν := by
    rw [← reflectVertex_step_spatial N _ ν h, step_back, step_back]
  have := congrArg (fun z => back z ν) e
  simpa [back_step] using this

theorem sUp_rf_spatial (L : Vertex N → Fin 4 → Q) (y : Vertex N) (i ν : Fin 4) (hi : i ≠ 0) (hν : ν ≠ 0) :
    sUp (rf L) i ν y = sUp L i ν (θ y) := by
  unfold sUp rf
  simp only [hi, hν, if_false, reflectVertex_step_spatial N _ _ hi, reflectVertex_step_spatial N _ _ hν,
    kk_reflect]
  rw [← reflectVertex_step_spatial N y i hi, kk_reflect]

theorem sDown_rf_spatial (L : Vertex N → Fin 4 → Q) (y : Vertex N) (i ν : Fin 4) (hi : i ≠ 0) (hν : ν ≠ 0) :
    sDown (rf L) i ν y = sDown L i ν (θ y) := by
  unfold sDown sDownY rf
  simp only [hi, hν, if_false, reflectVertex_step_spatial N _ _ hi, back_reflect _ _ hν]
  rw [← back_reflect y ν hν, ← reflectVertex_step_spatial N _ i hi, kk_reflect, kk_reflect]

theorem lineU_rf_spatial (L : Vertex N → Fin 4 → Q) (y : Vertex N) (i : Fin 4) (hi : i ≠ 0) :
    lineU (rf L) i y = lineU L i (θ y) := by
  unfold lineU rf
  simp only [hi, if_false, reflectVertex_step_spatial N _ _ hi]

theorem kk_cross (i : Fin 4) (x : Vertex N) : kk i 0 x = 0 := by
  unfold kk twistExp
  split_ifs <;> simp_all

/-- Reflection exchanges the two time staples of a spatial link. -/
theorem sUp_rf_cross (L : Vertex N → Fin 4 → Q) (y : Vertex N) (i : Fin 4) (hi : i ≠ 0) :
    sUp (rf L) i 0 y = sDown L i 0 (θ y) := by
  unfold sUp sDown sDownY
  simp only [kk_cross, pow_zero, mul_one]
  have hw : θ (step N y 0) = back (θ y) 0 := by
    have := reflectVertex_step_time N y
    rw [← this, back_step]
  have e1 : rf L y 0 = (L (back (θ y) 0) 0)⁻¹ := by
    simp only [rf, if_true]
    rw [hw]
  have e2 : rf L (step N y 0) i = L (back (θ y) 0) i := by
    simp only [rf, hi, if_false]
    rw [hw]
  have e3 : rf L (step N (step N y 0) i) i = L (step N (back (θ y) 0) i) i := by
    simp only [rf, hi, if_false]
    rw [reflectVertex_step_spatial N _ i hi, hw]
  have e4 : rf L (step N (step N y i) i) 0 = (L (step N (step N (back (θ y) 0) i) i) 0)⁻¹ := by
    simp only [rf, if_true]
    have c : step N (step N (step N y i) i) 0 = step N (step N (step N y 0) i) i := by
      simp only [step]
      abel
    rw [c, reflectVertex_step_spatial N _ i hi, reflectVertex_step_spatial N _ i hi, hw]
  rw [e1, e2, e3, e4]
  group

theorem sDown_rf_cross (L : Vertex N → Fin 4 → Q) (y : Vertex N) (i : Fin 4) (hi : i ≠ 0) :
    sDown (rf L) i 0 y = sUp L i 0 (θ y) := by
  unfold sUp sDown sDownY
  simp only [kk_cross, pow_zero, mul_one]
  have hw : θ (back y 0) = step N (θ y) 0 := by
    have := reflectVertex_step_time N (back y 0)
    rw [step_back] at this
    exact this.symm
  have e1 : rf L (back y 0) 0 = (L (θ y) 0)⁻¹ := by
    simp only [rf, if_true]
    rw [step_back]
  have e2 : rf L (back y 0) i = L (step N (θ y) 0) i := by
    simp only [rf, hi, if_false]
    rw [hw]
  have e3 : rf L (step N (back y 0) i) i = L (step N (step N (θ y) 0) i) i := by
    simp only [rf, hi, if_false]
    rw [reflectVertex_step_spatial N _ i hi, hw]
  have e4 : rf L (step N (step N (back y 0) i) i) 0 = (L (step N (step N (θ y) i) i) 0)⁻¹ := by
    simp only [rf, if_true]
    have c : step N (step N (step N (back y 0) i) i) 0 = step N (step N y i) i := by
      have : step N (step N (step N (back y 0) i) i) 0 = step N (step N (step N (back y 0) 0) i) i := by
        simp only [step]
        abel
      rw [this, step_back]
    rw [c, reflectVertex_step_spatial N _ i hi, reflectVertex_step_spatial N _ i hi]
  rw [e1, e2, e3, e4]
  group

/-- **A spatial blocked link reflects to a spatial blocked link**, for all weights. -/
theorem blockW_rf_spatial (a : Wt) (L : Vertex N → Fin 4 → Q) (y : Vertex N)
    (i : Fin 4) (hi : i ≠ 0) : blockW a (rf L) y i = blockW a L (θ y) i := by
  unfold blockW blockSumW
  rw [lineU_rf_spatial L y i hi]
  congr 2
  refine Finset.sum_congr rfl fun ν _ => ?_
  unfold stapleW
  by_cases h : ν = i
  · simp [h]
  · simp only [h, if_false]
    by_cases h0 : ν = 0
    · subst h0
      rw [sUp_rf_cross L y i hi, sDown_rf_cross L y i hi, add_comm]
    · rw [sUp_rf_spatial L y i ν hi h0, sDown_rf_spatial L y i ν hi h0]

theorem coe_inv (q : Q) : ((q⁻¹ : Q) : ℍ[ℝ]) = star (q : ℍ[ℝ]) := rfl

theorem proj_star (w : ℍ[ℝ]) : proj (star w) = (proj w)⁻¹ := by
  by_cases h : w = 0
  · subst h
    have e : proj (0 : ℍ[ℝ]) = 1 := by
      unfold proj
      simp
    simp [e]
  · have hs : star w ≠ 0 := by
      intro h'
      exact h (star_eq_zero.1 h')
    apply Subtype.ext
    rw [coe_inv, proj_coe _ hs, proj_coe _ h, norm_star, Quaternion.star_smul]

/-- The base point of the reflection of a blocked time link. -/
def yStar (y : Vertex N) : Vertex N := θ (step N (step N y 0) 0)

theorem theta_step1 (y : Vertex N) : θ (step N y 0) = step N (yStar y) 0 :=
  (reflectVertex_step_time N (step N y 0)).symm

theorem theta_step0 (y : Vertex N) : θ y = step N (step N (yStar y) 0) 0 := by
  rw [← theta_step1, reflectVertex_step_time]

theorem yStar_step (y : Vertex N) (ν : Fin 4) (h : ν ≠ 0) : yStar (step N y ν) = step N (yStar y) ν := by
  unfold yStar
  have e : step N (step N (step N y ν) 0) 0 = step N (step N (step N y 0) 0) ν := by
    simp only [step]
    abel
  rw [e, reflectVertex_step_spatial N _ ν h]

theorem yStar_back (y : Vertex N) (ν : Fin 4) (h : ν ≠ 0) : yStar (back y ν) = back (yStar y) ν := by
  have e : step N (yStar (back y ν)) ν = step N (back (yStar y) ν) ν := by
    rw [← yStar_step _ ν h, step_back, step_back]
  have := congrArg (fun z => back z ν) e
  simpa [back_step] using this

theorem lineU_rf_time (L : Vertex N → Fin 4 → Q) (y : Vertex N) :
    lineU (rf L) 0 y = (lineU L 0 (yStar y))⁻¹ := by
  unfold lineU
  have e1 : rf L y 0 = (L (step N (yStar y) 0) 0)⁻¹ := by
    simp only [rf, if_true]
    rw [theta_step1]
  have e2 : rf L (step N y 0) 0 = (L (yStar y) 0)⁻¹ := by
    simp only [rf, if_true]
    rfl
  rw [e1, e2, mul_inv_rev]

theorem sUp_rf_time (L : Vertex N → Fin 4 → Q) (y : Vertex N) (ν : Fin 4) (hν : ν ≠ 0) :
    sUp (rf L) 0 ν y = (sUp L 0 ν (yStar y))⁻¹ := by
  unfold sUp
  simp only [kk_time, pow_zero, mul_one, one_mul]
  have e1 : rf L y ν = L (step N (step N (yStar y) 0) 0) ν := by
    simp only [rf, hν, if_false]
    rw [theta_step0]
  have e2 : rf L (step N y ν) 0 = (L (step N (step N (yStar y) ν) 0) 0)⁻¹ := by
    simp only [rf, if_true]
    rw [theta_step1, yStar_step y ν hν]
  have e3 : rf L (step N (step N y ν) 0) 0 = (L (step N (yStar y) ν) 0)⁻¹ := by
    simp only [rf, if_true]
    change (L (yStar (step N y ν)) 0)⁻¹ = _
    rw [yStar_step y ν hν]
  have e4 : rf L (step N (step N y 0) 0) ν = L (yStar y) ν := by
    simp only [rf, hν, if_false]
    rfl
  rw [e1, e2, e3, e4]
  group

theorem sDown_rf_time (L : Vertex N → Fin 4 → Q) (y : Vertex N) (ν : Fin 4) (hν : ν ≠ 0) :
    sDown (rf L) 0 ν y = (sDown L 0 ν (yStar y))⁻¹ := by
  unfold sDown sDownY
  simp only [kk_time, pow_zero, mul_one, one_mul]
  rw [← yStar_back y ν hν]
  generalize back y ν = y'
  have e1 : rf L y' ν = L (step N (step N (yStar y') 0) 0) ν := by
    simp only [rf, hν, if_false]
    rw [theta_step0]
  have e2 : rf L y' 0 = (L (step N (yStar y') 0) 0)⁻¹ := by
    simp only [rf, if_true]
    rw [theta_step1]
  have e3 : rf L (step N y' 0) 0 = (L (yStar y') 0)⁻¹ := by
    simp only [rf, if_true]
    rfl
  have e4 : rf L (step N (step N y' 0) 0) ν = L (yStar y') ν := by
    simp only [rf, hν, if_false]
    rfl
  rw [e1, e2, e3, e4]
  group

/-- **A blocked time link reflects to the inverse of a blocked time link.** -/
theorem blockW_rf_time (a : Wt) (L : Vertex N → Fin 4 → Q) (y : Vertex N) :
    blockW a (rf L) y 0 = (blockW a L (yStar y) 0)⁻¹ := by
  unfold blockW
  rw [← proj_star]
  congr 1
  unfold blockSumW
  rw [star_add, star_sum, lineU_rf_time, coe_inv]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  unfold stapleW
  by_cases h : ν = 0
  · simp [h]
  · simp only [h, if_false]
    rw [sUp_rf_time L y ν h, sDown_rf_time L y ν h, coe_inv, coe_inv, Quaternion.star_smul, star_add]

/-- The block map depends only on the links it visibly uses. -/
theorem blockW_congr (a : Wt) (L L' : Vertex N → Fin 4 → Q) (y : Vertex N) (μ : Fin 4)
    (h1 : L y μ = L' y μ) (h2 : L (step N y μ) μ = L' (step N y μ) μ)
    (h3 : ∀ ν, ν ≠ μ → a μ ν ≠ 0 →
      L y ν = L' y ν ∧ L (step N y ν) μ = L' (step N y ν) μ ∧
      L (step N (step N y ν) μ) μ = L' (step N (step N y ν) μ) μ ∧
      L (step N (step N y μ) μ) ν = L' (step N (step N y μ) μ) ν ∧
      L (back y ν) ν = L' (back y ν) ν ∧ L (back y ν) μ = L' (back y ν) μ ∧
      L (step N (back y ν) μ) μ = L' (step N (back y ν) μ) μ ∧
      L (step N (step N (back y ν) μ) μ) ν = L' (step N (step N (back y ν) μ) μ) ν) :
    blockW a L y μ = blockW a L' y μ := by
  unfold blockW blockSumW lineU
  rw [h1, h2]
  congr 2
  refine Finset.sum_congr rfl fun ν _ => ?_
  unfold stapleW
  by_cases h : ν = μ
  · simp [h]
  · simp only [h, if_false]
    by_cases h0 : a μ ν = 0
    · rw [h0, zero_smul, zero_smul]
    · obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h3 ν h h0
      unfold sUp sDown sDownY
      rw [c1, c2, c3, c4, c5, c6, c7, c8]

end Reflection

section ReflectionLaw

open PeriodicHalfSplit PeriodicHalfGeometry PeriodicSiteReflection

variable (m : ℕ) [NeZero m]

local notation "Vc" => Vertex (2 * m)
local notation "Vf" => Vertex (2 * (2 * m))

theorem emb_reflect (n : ℕ) [NeZero n] (x : Vertex n) :
    emb n (reflectVertex n x) = reflectVertex (2 * n) (emb n x) := by
  funext j
  unfold emb reflectVertex
  by_cases h : j = 0
  · simp [h, emb1_neg]
  · simp [h]

/-- **The block map commutes with the reflection**, for all weights. -/
theorem blockCfg_reflect (n : ℕ) [NeZero n] (a : Wt) (U : Configuration (Vertex (2 * n)) Q) :
    blockCfg n a (reflectConfiguration (2 * n) Q U) = reflectConfiguration n Q (blockCfg n a U) := by
  refine config_ext n _ _ fun x μ => ?_
  rw [linkValue_reflect, link_blockCfg, linkValue_reflect, link_blockCfg]
  unfold rf blockField
  by_cases h : μ = 0
  · subst h
    simp only [if_true]
    change blockW a (rf _) (emb n x) 0 = _
    rw [blockW_rf_time, emb_reflect, emb_step]
    rfl
  · simp only [h, if_false]
    change blockW a (rf _) (emb n x) μ = _
    rw [blockW_rf_spatial a _ _ μ h, emb_reflect]

theorem aniso_time (α : ℝ) (i : Fin 4) (h : i ≠ 0) : aniso α i 0 = 0 := by
  simp [aniso, h]

/-- Two fine fields that agree on the closed upper half agree on its links. -/
theorem closed_agree (W W' : Configuration Vf Q)
    (h1 : (splitConfiguration (2 * m) Q W).1 = (splitConfiguration (2 * m) Q W').1)
    (h2 : (splitConfiguration (2 * m) Q W).2.1 = (splitConfiguration (2 * m) Q W').2.1)
    (x : Vf) (μ : Fin 4) (hp : Boundary (2 * m) (x, μ) ∨ Positive (2 * m) (x, μ)) :
    linkValue (2 * (2 * m)) Q W x μ = linkValue (2 * (2 * m)) Q W' x μ := by
  rcases hp with hp | hp
  · exact congrFun h1 ⟨(x, μ), hp⟩
  · exact congrFun h2 ⟨(x, μ), hp⟩

theorem closed_spatial (x : Vf) (μ : Fin 4) (hμ : μ ≠ 0) (ht : (x 0).val ≤ 2 * m) :
    Boundary (2 * m) (x, μ) ∨ Positive (2 * m) (x, μ) := by
  by_cases h0 : (x 0).val = 0
  · exact Or.inl ⟨hμ, Or.inl h0⟩
  · by_cases h1 : (x 0).val = 2 * m
    · exact Or.inl ⟨hμ, Or.inr h1⟩
    · refine Or.inr ?_
      simp only [Positive, hμ, if_false]
      omega

theorem closed_time (x : Vf) (ht : (x 0).val < 2 * m) :
    Boundary (2 * m) (x, 0) ∨ Positive (2 * m) (x, 0) := by
  refine Or.inr ?_
  simpa [Positive] using ht

theorem step_time_coord (N : ℕ) (x : Vertex N) (ν : Fin 4) (h : ν ≠ 0) : step N x ν 0 = x 0 := by
  rw [step_apply]
  simp [h.symm]

theorem back_time_coord (N : ℕ) (x : Vertex N) (ν : Fin 4) (h : ν ≠ 0) : back x ν 0 = x 0 := by
  simp [back, h.symm]

theorem step0_coord (N : ℕ) (x : Vertex N) : step N x 0 0 = x 0 + 1 := by
  rw [step_apply]
  simp

theorem emb1_add_val2 (n : ℕ) [NeZero n] (t : ZMod n) (b : ℕ) (hb : 2 * t.val + b < 2 * n) :
    (emb1 n t + (b : ZMod (2 * n))).val = 2 * t.val + b := by
  have e : emb1 n t + (b : ZMod (2 * n)) = ((2 * t.val + b : ℕ) : ZMod (2 * n)) := by
    unfold emb1
    push_cast
    rfl
  rw [e, ZMod.val_natCast_of_lt hb]

/-- **The closed coarse half of the blocked field is a function of the closed fine half.** -/
theorem half_local (a : Wt) (hz : ∀ i, i ≠ 0 → a i 0 = 0) (W W' : Configuration Vf Q)
    (h1 : (splitConfiguration (2 * m) Q W).1 = (splitConfiguration (2 * m) Q W').1)
    (h2 : (splitConfiguration (2 * m) Q W).2.1 = (splitConfiguration (2 * m) Q W').2.1)
    (x : Vc) (μ : Fin 4) (hp : Boundary m (x, μ) ∨ Positive m (x, μ)) :
    blockField (2 * m) a (linkValue (2 * (2 * m)) Q W) x μ =
      blockField (2 * m) a (linkValue (2 * (2 * m)) Q W') x μ := by
  have ag := closed_agree m W W' h1 h2
  unfold blockField
  obtain ⟨y, hy⟩ : ∃ y, y = emb (2 * m) x := ⟨_, rfl⟩
  rw [← hy]
  have hy0 : y 0 = emb1 (2 * m) (x 0) := by rw [hy]; rfl
  have hval : (y 0).val = 2 * (x 0).val := by rw [hy0]; exact emb1_val (2 * m) (x 0)
  by_cases hμ : μ = 0
  · subst hμ
    have hv : (x 0).val < m := by
      rcases hp with hp | hp
      · exact absurd rfl hp.1
      · simpa [Positive] using hp
    have v1 : (step (2 * (2 * m)) y 0 0).val = 2 * (x 0).val + 1 := by
      rw [step0_coord, hy0]
      have := emb1_add_val2 (2 * m) (x 0) 1 (by omega)
      rwa [Nat.cast_one] at this
    have v2 : (step (2 * (2 * m)) (step (2 * (2 * m)) y 0) 0 0).val = 2 * (x 0).val + 2 := by
      rw [step0_coord, step0_coord, hy0]
      have := emb1_add_val2 (2 * m) (x 0) 2 (by omega)
      rw [add_assoc]
      norm_num at this ⊢
      exact this
    refine blockW_congr _ _ _ _ _ (ag _ _ (closed_time m _ (by omega))) (ag _ _ (closed_time m _ (by omega))) ?_
    intro ν hν _
    have t1 : (step (2 * (2 * m)) y ν 0).val = 2 * (x 0).val := by rw [step_time_coord _ _ _ hν, hval]
    have t2 : (step (2 * (2 * m)) (step (2 * (2 * m)) y ν) 0 0).val = 2 * (x 0).val + 1 := by
      rw [step_step_comm y ν 0, step_time_coord _ _ _ hν, v1]
    have t3 : (back y ν 0).val = 2 * (x 0).val := by rw [back_time_coord _ _ _ hν, hval]
    have t4 : (step (2 * (2 * m)) (back y ν) 0 0).val = 2 * (x 0).val + 1 := by
      rw [step0_coord, back_time_coord _ _ _ hν, ← step0_coord, v1]
    have t5 : (step (2 * (2 * m)) (step (2 * (2 * m)) (back y ν) 0) 0 0).val = 2 * (x 0).val + 2 := by
      rw [step0_coord, step0_coord, back_time_coord _ _ _ hν, ← step0_coord, ← step0_coord, v2]
    exact ⟨ag _ _ (closed_spatial m _ _ hν (by omega)), ag _ _ (closed_time m _ (by omega)),
      ag _ _ (closed_time m _ (by omega)), ag _ _ (closed_spatial m _ _ hν (by omega)),
      ag _ _ (closed_spatial m _ _ hν (by omega)), ag _ _ (closed_time m _ (by omega)),
      ag _ _ (closed_time m _ (by omega)), ag _ _ (closed_spatial m _ _ hν (by omega))⟩
  · have hv : (x 0).val ≤ m := by
      rcases hp with hp | hp
      · rcases hp.2 with h | h <;> simp only at h <;> omega
      · simp only [Positive, hμ, if_false] at hp
        omega
    have hs (z : Vf) (ρ : Fin 4) (hρ : ρ ≠ 0) (hz : z 0 = y 0) :
        linkValue (2 * (2 * m)) Q W z ρ = linkValue (2 * (2 * m)) Q W' z ρ :=
      ag _ _ (closed_spatial m _ _ hρ (by rw [hz, hval]; omega))
    refine blockW_congr _ _ _ _ _ (hs _ _ hμ rfl) (hs _ _ hμ (step_time_coord _ _ _ hμ)) ?_
    intro ν hν ha
    have hν0 : ν ≠ 0 := by
      rintro rfl
      exact ha (hz μ hμ)
    have c (z : Vf) (ρ : Fin 4) (hρ : ρ ≠ 0) (hz : z 0 = y 0) : step (2 * (2 * m)) z ρ 0 = y 0 :=
      (step_time_coord _ _ _ hρ).trans hz
    have cb : back y ν 0 = y 0 := back_time_coord _ _ _ hν0
    exact ⟨hs _ _ hν0 rfl, hs _ _ hμ (c _ _ hν0 rfl), hs _ _ hμ (c _ _ hμ (c _ _ hν0 rfl)),
      hs _ _ hν0 (c _ _ hμ (c _ _ hμ rfl)), hs _ _ hν0 cb, hs _ _ hμ cb, hs _ _ hμ (c _ _ hμ cb),
      hs _ _ hν0 (c _ _ hμ (c _ _ hμ cb))⟩

/-- The two coordinates of the closed coarse half. -/
theorem half_coords (a : Wt) (hz : ∀ i, i ≠ 0 → a i 0 = 0) (W W' : Configuration Vf Q)
    (h1 : (splitConfiguration (2 * m) Q W).1 = (splitConfiguration (2 * m) Q W').1)
    (h2 : (splitConfiguration (2 * m) Q W).2.1 = (splitConfiguration (2 * m) Q W').2.1) :
    (splitConfiguration m Q (blockCfg (2 * m) a W)).1 =
        (splitConfiguration m Q (blockCfg (2 * m) a W')).1 ∧
      (splitConfiguration m Q (blockCfg (2 * m) a W)).2.1 =
        (splitConfiguration m Q (blockCfg (2 * m) a W')).2.1 := by
  constructor
  · funext b
    exact half_local m a hz W W' h1 h2 b.val.1 b.val.2 (Or.inl b.property)
  · funext p
    exact half_local m a hz W W' h1 h2 p.val.1 p.val.2 (Or.inr p.property)

/-- Reflection positivity of a measure on the lattice of side `2m`, for every continuous observable of the
closed half. -/
def IsRP (μ : Measure (Configuration (Vertex (2 * m)) Q)) : Prop :=
  ∀ f : BoundaryConfiguration m Q × HalfConfiguration m Q → ℂ, Continuous f →
    0 ≤ (∫ V, star (observable m Q f (reflectConfiguration (2 * m) Q V)) * observable m Q f V ∂μ).re ∧
    (∫ V, star (observable m Q f (reflectConfiguration (2 * m) Q V)) * observable m Q f V ∂μ).im = 0

theorem isRP_twistedLaw (β : ℝ) : IsRP m (twistedLaw m β) := fun f hf =>
  TwistedReflection.reflection_positive m Q (TwistedReflection.spatialTwist m)
    (TwistedReflection.spatialTwist_invariant m) WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_continuous WilsonSingleLinkStaples.character_classFunction
    WilsonSingleLinkStaples.character_inverse_re β 2 f hf

/-- **Reflection positivity survives a block step with no time staples on spatial links, from any
reflection-positive measure.** For admissible weights with `a i 0 = 0`, the push-forward of a reflection positive
measure is reflection positive for every continuous observable of a closed coarse half. It says nothing about
`TwistedBlockMap`'s isotropic map: its spatial links on a reflection slice have staples on both sides. -/
theorem isRP_step_of (a : Wt) (ha : Adm a) (hz : ∀ i, i ≠ 0 → a i 0 = 0) (μ : Measure (Configuration Vf Q))
    (hμ : IsRP (2 * m) μ) : IsRP m (μ.map (blockCfg (2 * m) a)) := by
  intro f hf
  have hBc := continuous_blockCfg (2 * m) a ha
  set B := blockCfg (2 * m) a with hB
  let G : BoundaryConfiguration (2 * m) Q × HalfConfiguration (2 * m) Q → ℂ := fun z =>
    f ((splitConfiguration m Q (B (assemble (2 * m) Q (z.1, (z.2, 1))))).1,
      (splitConfiguration m Q (B (assemble (2 * m) Q (z.1, (z.2, 1))))).2.1)
  have hG : Continuous G := by
    have hc : Continuous fun z : BoundaryConfiguration (2 * m) Q × HalfConfiguration (2 * m) Q =>
        splitConfiguration m Q (B (assemble (2 * m) Q (z.1, (z.2, 1)))) :=
      (continuous_splitConfiguration m Q).comp (hBc.comp ((continuous_assemble (2 * m) Q).comp
        (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))))
    exact hf.comp (hc.fst.prodMk hc.snd.fst)
  have hobs (U : Configuration Vf Q) :
      observable m Q f (B U) = observable (2 * m) Q G U := by
    set W := assemble (2 * m) Q ((splitConfiguration (2 * m) Q U).1,
      ((splitConfiguration (2 * m) Q U).2.2, 1)) with hW
    have hsW := split_assemble (2 * m) Q ((splitConfiguration (2 * m) Q U).1,
      ((splitConfiguration (2 * m) Q U).2.2, 1))
    rw [← hW] at hsW
    have hsθ := split_reflection (2 * m) Q U
    obtain ⟨a1, a2⟩ := half_coords m a hz (reflectConfiguration (2 * (2 * m)) Q U) W
      (by rw [hsθ, hsW]) (by rw [hsθ, hsW])
    have hc := blockCfg_reflect (2 * m) a U
    rw [← hB] at hc
    have hsc := split_reflection m Q (B U)
    rw [← hc] at hsc
    have e1 : (splitConfiguration m Q (B U)).1 =
        (splitConfiguration m Q (B (reflectConfiguration (2 * (2 * m)) Q U))).1 := by rw [hsc]
    have e2 : (splitConfiguration m Q (B U)).2.2 =
        (splitConfiguration m Q (B (reflectConfiguration (2 * (2 * m)) Q U))).2.1 := by rw [hsc]
    change f ((splitConfiguration m Q (B U)).1, (splitConfiguration m Q (B U)).2.2) =
      f ((splitConfiguration m Q (B W)).1, (splitConfiguration m Q (B W)).2.1)
    rw [e1, e2, a1, a2]
  have hθc : Continuous (reflectConfiguration (2 * m) Q) := ReflectedDefectBound.continuous_reflection Q (2 * m)
  have hobsc : Continuous (observable m Q f) := by
    have : Continuous fun V : Configuration (Vertex (2 * m)) Q =>
        f ((splitConfiguration m Q V).1, (splitConfiguration m Q V).2.2) :=
      hf.comp ((continuous_splitConfiguration m Q).fst.prodMk
        (continuous_splitConfiguration m Q).snd.snd)
    exact this
  have hint : Continuous fun V : Configuration (Vertex (2 * m)) Q =>
      star (observable m Q f (reflectConfiguration (2 * m) Q V)) * observable m Q f V :=
    (continuous_star.comp (hobsc.comp hθc)).mul hobsc
  have hmap : (∫ V, star (observable m Q f (reflectConfiguration (2 * m) Q V)) * observable m Q f V
      ∂μ.map B) =
      ∫ U, star (observable (2 * m) Q G (reflectConfiguration (2 * (2 * m)) Q U)) *
        observable (2 * m) Q G U ∂μ := by
    rw [integral_map hBc.measurable.aemeasurable hint.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    have hc := blockCfg_reflect (2 * m) a U
    change star (observable m Q f (reflectConfiguration (2 * m) Q (blockCfg (2 * m) a U))) *
      observable m Q f (blockCfg (2 * m) a U) = _
    rw [← hc, ← hB, hobs, hobs]
  rw [hmap]
  exact hμ G hG

theorem isRP_step (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 6) (μ : Measure (Configuration Vf Q))
    (hμ : IsRP (2 * m) μ) : IsRP m (μ.map (blockCfg (2 * m) (aniso α))) :=
  isRP_step_of m _ (adm_aniso α h0 h1) (aniso_time α) μ hμ

/-- **The blocked law of the reflection-compatible map is reflection positive.** -/
theorem blocked_reflection_positive (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 6) (β : ℝ) :
    IsRP m (blockedLaw (2 * m) (aniso α) β) :=
  isRP_step m α h0 h1 _ (isRP_twistedLaw (2 * m) β)

theorem emb1_sub_one_val (n : ℕ) [NeZero n] (t : ZMod n) (ht : 0 < t.val) :
    (emb1 n t - 1).val = 2 * t.val - 1 := by
  have e : emb1 n t - 1 = ((2 * t.val - 1 : ℕ) : ZMod (2 * n)) := by
    obtain ⟨k, hk⟩ : ∃ k, 2 * t.val = k + 1 := ⟨2 * t.val - 1, by omega⟩
    have h' : 2 * t.val - 1 = k := by omega
    unfold emb1
    rw [h', hk]
    push_cast
    ring
  have hl := t.val_lt
  rw [e, ZMod.val_natCast_of_lt (by omega)]

/-- **The open coarse half is a function of the closed fine half, for all weights.** A positive spatial link
sits strictly inside the half, so its time staples stay there. Only the spatial links on the reflection slices
reach both sides. -/
theorem pos_local (a : Wt) (W W' : Configuration Vf Q)
    (h1 : (splitConfiguration (2 * m) Q W).1 = (splitConfiguration (2 * m) Q W').1)
    (h2 : (splitConfiguration (2 * m) Q W).2.1 = (splitConfiguration (2 * m) Q W').2.1)
    (x : Vc) (μ : Fin 4) (hp : Positive m (x, μ)) :
    blockField (2 * m) a (linkValue (2 * (2 * m)) Q W) x μ =
      blockField (2 * m) a (linkValue (2 * (2 * m)) Q W') x μ := by
  have ag := closed_agree m W W' h1 h2
  unfold blockField
  obtain ⟨y, hy⟩ : ∃ y, y = emb (2 * m) x := ⟨_, rfl⟩
  rw [← hy]
  have hy0 : y 0 = emb1 (2 * m) (x 0) := by rw [hy]; rfl
  have hval : (y 0).val = 2 * (x 0).val := by rw [hy0]; exact emb1_val (2 * m) (x 0)
  by_cases hμ : μ = 0
  · subst hμ
    have hv : (x 0).val < m := by simpa [Positive] using hp
    have v1 : (step (2 * (2 * m)) y 0 0).val = 2 * (x 0).val + 1 := by
      rw [step0_coord, hy0]
      have := emb1_add_val2 (2 * m) (x 0) 1 (by omega)
      rwa [Nat.cast_one] at this
    have v2 : (step (2 * (2 * m)) (step (2 * (2 * m)) y 0) 0 0).val = 2 * (x 0).val + 2 := by
      rw [step0_coord, step0_coord, hy0]
      have := emb1_add_val2 (2 * m) (x 0) 2 (by omega)
      rw [add_assoc]
      norm_num at this ⊢
      exact this
    refine blockW_congr _ _ _ _ _ (ag _ _ (closed_time m _ (by omega))) (ag _ _ (closed_time m _ (by omega))) ?_
    intro ν hν _
    have t1 : (step (2 * (2 * m)) y ν 0).val = 2 * (x 0).val := by rw [step_time_coord _ _ _ hν, hval]
    have t2 : (step (2 * (2 * m)) (step (2 * (2 * m)) y ν) 0 0).val = 2 * (x 0).val + 1 := by
      rw [step_step_comm y ν 0, step_time_coord _ _ _ hν, v1]
    have t3 : (back y ν 0).val = 2 * (x 0).val := by rw [back_time_coord _ _ _ hν, hval]
    have t4 : (step (2 * (2 * m)) (back y ν) 0 0).val = 2 * (x 0).val + 1 := by
      rw [step0_coord, back_time_coord _ _ _ hν, ← step0_coord, v1]
    have t5 : (step (2 * (2 * m)) (step (2 * (2 * m)) (back y ν) 0) 0 0).val = 2 * (x 0).val + 2 := by
      rw [step0_coord, step0_coord, back_time_coord _ _ _ hν, ← step0_coord, ← step0_coord, v2]
    exact ⟨ag _ _ (closed_spatial m _ _ hν (by omega)), ag _ _ (closed_time m _ (by omega)),
      ag _ _ (closed_time m _ (by omega)), ag _ _ (closed_spatial m _ _ hν (by omega)),
      ag _ _ (closed_spatial m _ _ hν (by omega)), ag _ _ (closed_time m _ (by omega)),
      ag _ _ (closed_time m _ (by omega)), ag _ _ (closed_spatial m _ _ hν (by omega))⟩
  · have hv : 0 < (x 0).val ∧ (x 0).val < m := by simpa only [Positive, hμ, if_false] using hp
    have hs (z : Vf) (ρ : Fin 4) (hρ : ρ ≠ 0) (hz : z 0 = y 0) :
        linkValue (2 * (2 * m)) Q W z ρ = linkValue (2 * (2 * m)) Q W' z ρ :=
      ag _ _ (closed_spatial m _ _ hρ (by rw [hz, hval]; omega))
    refine blockW_congr _ _ _ _ _ (hs _ _ hμ rfl) (hs _ _ hμ (step_time_coord _ _ _ hμ)) ?_
    intro ν hν _
    have c (z : Vf) (ρ : Fin 4) (hρ : ρ ≠ 0) (hz : z 0 = y 0) : step (2 * (2 * m)) z ρ 0 = y 0 :=
      (step_time_coord _ _ _ hρ).trans hz
    by_cases hν0 : ν = 0
    · subst hν0
      have u1 : (step (2 * (2 * m)) y 0 0).val = 2 * (x 0).val + 1 := by
        rw [step0_coord, hy0]
        have := emb1_add_val2 (2 * m) (x 0) 1 (by omega)
        rwa [Nat.cast_one] at this
      have u2 : (back y 0 0).val = 2 * (x 0).val - 1 := by
        have e : back y 0 0 = emb1 (2 * m) (x 0) - 1 := by
          rw [← hy0]
          simp [back]
        rw [e]
        exact emb1_sub_one_val (2 * m) (x 0) hv.1
      have cu (z : Vf) (hz : (z 0).val = 2 * (x 0).val + 1) : Boundary (2 * m) (z, μ) ∨ Positive (2 * m) (z, μ) :=
        closed_spatial m _ _ hμ (by omega)
      have cd' (z : Vf) (hz : (z 0).val = 2 * (x 0).val - 1) : Boundary (2 * m) (z, μ) ∨ Positive (2 * m) (z, μ) :=
        closed_spatial m _ _ hμ (by omega)
      have ctd (z : Vf) (hz : (z 0).val = 2 * (x 0).val - 1) : Boundary (2 * m) (z, 0) ∨ Positive (2 * m) (z, 0) :=
        closed_time m _ (by omega)
      have ct (z : Vf) (hz : (z 0).val = 2 * (x 0).val) : Boundary (2 * m) (z, 0) ∨ Positive (2 * m) (z, 0) :=
        closed_time m _ (by omega)
      have sc (z : Vf) : step (2 * (2 * m)) z μ 0 = z 0 := step_time_coord _ _ _ hμ
      refine ⟨ag _ _ (ct _ hval), ag _ _ (cu _ u1), ag _ _ (cu _ (by rw [sc]; exact u1)),
        ag _ _ (ct _ (by rw [sc, sc]; exact hval)), ag _ _ (ctd _ u2), ag _ _ (cd' _ u2),
        ag _ _ (cd' _ (by rw [sc]; exact u2)), ag _ _ (ctd _ (by rw [sc, sc]; exact u2))⟩
    · have cb : back y ν 0 = y 0 := back_time_coord _ _ _ hν0
      exact ⟨hs _ _ hν0 rfl, hs _ _ hμ (c _ _ hν0 rfl), hs _ _ hμ (c _ _ hμ (c _ _ hν0 rfl)),
        hs _ _ hν0 (c _ _ hμ (c _ _ hμ rfl)), hs _ _ hν0 cb, hs _ _ hμ cb, hs _ _ hμ (c _ _ hμ cb),
        hs _ _ hν0 (c _ _ hμ (c _ _ hμ cb))⟩

/-- **For every admissible map, reflection positivity survives on the open half.** This includes the isotropic
map of `TwistedBlockMap`, for `α < 1/6`. The observable may not depend on the coarse spatial links on the two
reflection slices, the ones whose staples cross. So blocked correlators of observables at distinct positive
times keep their reflection-positive structure, and only the slices themselves are lost. -/
theorem blocked_open_reflection_positive (a : Wt) (ha : Adm a) (β : ℝ) (f : HalfConfiguration m Q → ℂ)
    (hf : Continuous f) :
    0 ≤ (∫ V, star (f (splitConfiguration m Q V).2.1) *
        f (splitConfiguration m Q (reflectConfiguration (2 * m) Q V)).2.1 ∂blockedLaw (2 * m) a β).re ∧
    (∫ V, star (f (splitConfiguration m Q V).2.1) *
        f (splitConfiguration m Q (reflectConfiguration (2 * m) Q V)).2.1 ∂blockedLaw (2 * m) a β).im = 0 := by
  have hBc := continuous_blockCfg (2 * m) a ha
  set B := blockCfg (2 * m) a with hB
  let G : BoundaryConfiguration (2 * m) Q × HalfConfiguration (2 * m) Q → ℂ := fun z =>
    f (splitConfiguration m Q (B (assemble (2 * m) Q (z.1, (z.2, 1))))).2.1
  have hG : Continuous G := by
    have hc : Continuous fun z : BoundaryConfiguration (2 * m) Q × HalfConfiguration (2 * m) Q =>
        splitConfiguration m Q (B (assemble (2 * m) Q (z.1, (z.2, 1)))) :=
      (continuous_splitConfiguration m Q).comp (hBc.comp ((continuous_assemble (2 * m) Q).comp
        (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))))
    exact hf.comp hc.snd.fst
  have hpos (U : Configuration Vf Q) :
      f (splitConfiguration m Q (B (reflectConfiguration (2 * (2 * m)) Q U))).2.1 =
        observable (2 * m) Q G U := by
    set W := assemble (2 * m) Q ((splitConfiguration (2 * m) Q U).1,
      ((splitConfiguration (2 * m) Q U).2.2, 1)) with hW
    have hsW := split_assemble (2 * m) Q ((splitConfiguration (2 * m) Q U).1,
      ((splitConfiguration (2 * m) Q U).2.2, 1))
    rw [← hW] at hsW
    have hsθ := split_reflection (2 * m) Q U
    have a2 : (splitConfiguration m Q (B (reflectConfiguration (2 * (2 * m)) Q U))).2.1 =
        (splitConfiguration m Q (B W)).2.1 := by
      funext p
      exact pos_local m a _ W (by rw [hsθ, hsW]) (by rw [hsθ, hsW]) p.val.1 p.val.2 p.property
    change _ = f (splitConfiguration m Q (B W)).2.1
    rw [a2]
  have hθf : Continuous (reflectConfiguration (2 * (2 * m)) Q) :=
    ReflectedDefectBound.continuous_reflection Q (2 * (2 * m))
  have hθc : Continuous (reflectConfiguration (2 * m) Q) := ReflectedDefectBound.continuous_reflection Q (2 * m)
  have hsc := continuous_splitConfiguration m Q
  have hint : Continuous fun V : Configuration (Vertex (2 * m)) Q =>
      star (f (splitConfiguration m Q V).2.1) *
        f (splitConfiguration m Q (reflectConfiguration (2 * m) Q V)).2.1 :=
    (continuous_star.comp (hf.comp hsc.snd.fst)).mul (hf.comp (hsc.comp hθc).snd.fst)
  have hmap : (∫ V, star (f (splitConfiguration m Q V).2.1) *
        f (splitConfiguration m Q (reflectConfiguration (2 * m) Q V)).2.1 ∂blockedLaw (2 * m) a β) =
      ∫ U, star (observable (2 * m) Q G (reflectConfiguration (2 * (2 * m)) Q U)) *
        observable (2 * m) Q G U ∂twistedLaw (2 * m) β := by
    unfold blockedLaw
    rw [integral_map hBc.measurable.aemeasurable hint.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    have hc := blockCfg_reflect (2 * m) a U
    have hθθ : reflectConfiguration (2 * (2 * m)) Q (reflectConfiguration (2 * (2 * m)) Q U) = U :=
      reflectConfiguration_involutive (2 * (2 * m)) Q U
    have h1 := hpos U
    have h2 := hpos (reflectConfiguration (2 * (2 * m)) Q U)
    rw [hθθ] at h2
    change star (f (splitConfiguration m Q (blockCfg (2 * m) a U)).2.1) *
      f (splitConfiguration m Q (reflectConfiguration (2 * m) Q (blockCfg (2 * m) a U))).2.1 = _
    rw [← hc, ← hB, h1, h2]
  rw [hmap]
  exact TwistedReflection.reflection_positive (2 * m) Q (TwistedReflection.spatialTwist (2 * m))
    (TwistedReflection.spatialTwist_invariant (2 * m)) WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_continuous WilsonSingleLinkStaples.character_classFunction
    WilsonSingleLinkStaples.character_inverse_re β 2 G hG

end ReflectionLaw

/-! ### Weights in the two families -/

section Families

theorem he_iso (α : ℝ) (h0 : 0 ≤ α) (μ ν : Fin 4) (_ : ν ≠ μ) :
    2 * iso α μ ν ≤ 2 * α / (1 + 6 * α) * (1 + tot (iso α) μ) := by
  rw [tot_iso]
  have : (1 + 6 * α) ≠ 0 := by positivity
  simp only [iso]
  rw [div_mul_cancel₀ _ this]

theorem he_aniso (α : ℝ) (h0 : 0 ≤ α) (μ ν : Fin 4) (_ : ν ≠ μ) :
    2 * aniso α μ ν ≤ 2 * α / (1 + 4 * α) * (1 + tot (aniso α) μ) := by
  have hp : 0 < 1 + 4 * α := by positivity
  have he0 : 0 ≤ 2 * α / (1 + 4 * α) := by positivity
  have hc : 2 * α / (1 + 4 * α) * (1 + 4 * α) = 2 * α := div_mul_cancel₀ _ hp.ne'
  have hb : 2 * α ≤ 2 * α / (1 + 4 * α) * (1 + tot (aniso α) μ) := by
    rw [tot_aniso]
    split_ifs
    · nlinarith only [hc, mul_nonneg he0 h0]
    · exact hc.ge
  by_cases h : μ ≠ 0 ∧ ν = 0
  · have e : aniso α μ ν = 0 := by simp [aniso, h]
    rw [e, mul_zero]
    exact le_trans (by linarith only [h0]) hb
  · have e : aniso α μ ν = α := by simp only [aniso, if_neg h]
    rw [e]
    exact hb

theorem he_zero (μ ν : Fin 4) (_ : ν ≠ μ) : 2 * zeroW μ ν ≤ 0 * (1 + tot zeroW μ) := by
  simp [zeroW]

end Families

/-! ### The effective action -/

section EffectiveAction

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- **The effective action relative to the blocked Haar measure.** It exists for all admissible weights, as an almost
everywhere finite function, with `Z` the partition function: `(β/K) S_c + log Z ≤ S_eff ≤ 4 β P + log Z`. Existence is the
conditional expectation of `exp(-β S)` given the block map, so it is nearly automatic. The lower bound is the content; the upper
bound is compactness, and is extensive. No smoothness, locality or smallness of `S_eff` is claimed. -/
theorem exists_effective_action (a : Wt) (ha : Adm a) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ Seff : Configuration (Vertex n) Q → ℝ, Measurable Seff ∧
      blockedLaw n a β = (blockedHaar n a).withDensity (fun V => ENNReal.ofReal (Real.exp (-Seff V))) ∧
      ∀ᵐ V ∂blockedHaar n a,
        β / ((4 + 64 * e) * (1 + 48 * e)) * actionL (linkValue n Q V) + Real.log (fineZ n β).toReal ≤ Seff V ∧
        Seff V ≤ β * (4 * (fineP n : ℝ)) + Real.log (fineZ n β).toReal := by
  obtain ⟨ρ, hρm, hρ, hb⟩ := exists_density n a ha e he0 he β hβ
  have hZ1 : fineZ n β ≠ ∞ := gibbsPartition_ne_top _ _ _ (continuous_fineS n β)
  have hZ0 : fineZ n β ≠ 0 := (gibbsPartition_pos _ _ _ (continuous_fineS n β)).ne'
  set Zr := (fineZ n β).toReal with hZr
  have hZp : 0 < Zr := ENNReal.toReal_pos hZ0 hZ1
  have hinv (x : ℝ) (hx : 0 ≤ x) : (fineZ n β)⁻¹ * ENNReal.ofReal x = ENNReal.ofReal (x / Zr) := by
    rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 hZp.le), ENNReal.ofReal_inv_of_pos hZp, hZr,
      ENNReal.ofReal_toReal hZ1]
  refine ⟨fun V => -Real.log (ρ V).toReal, (hρm.ennreal_toReal.log).neg, ?_, ?_⟩
  · rw [hρ]
    refine withDensity_congr_ae ?_
    filter_upwards [hb] with V hV
    rw [hinv _ (Real.exp_pos _).le, hinv _ (Real.exp_pos _).le] at hV
    have h1 : 0 < ρ V := lt_of_lt_of_le (by simpa using div_pos (Real.exp_pos _) hZp) hV.1
    have h2 : ρ V ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hV.2
    have h3 : 0 < (ρ V).toReal := ENNReal.toReal_pos h1.ne' h2
    simp only [neg_neg]
    rw [Real.exp_log h3, ENNReal.ofReal_toReal h2]
  · filter_upwards [hb] with V hV
    rw [hinv _ (Real.exp_pos _).le, hinv _ (Real.exp_pos _).le] at hV
    have h1 : 0 < ρ V := lt_of_lt_of_le (by simpa using div_pos (Real.exp_pos _) hZp) hV.1
    have h2 : ρ V ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hV.2
    have h3 : 0 < (ρ V).toReal := ENNReal.toReal_pos h1.ne' h2
    have hup := (ENNReal.le_ofReal_iff_toReal_le h2 (div_pos (Real.exp_pos _) hZp).le).1 hV.2
    have hlo := (ENNReal.ofReal_le_iff_le_toReal h2).1 hV.1
    have l1 := Real.log_le_log h3 hup
    have l2 := Real.log_le_log (div_pos (Real.exp_pos _) hZp) hlo
    rw [Real.log_div (Real.exp_pos _).ne' hZp.ne', Real.log_exp] at l1 l2
    constructor
    · have : -(β / ((4 + 64 * e) * (1 + 48 * e))) * actionL (linkValue n Q V) =
          -(β / ((4 + 64 * e) * (1 + 48 * e)) * actionL (linkValue n Q V)) := by ring
      linarith only [l1, this]
    · linarith only [l2]

/-- **With no staples, the effective action is a density against Haar measure itself**, for every `β ≥ 0` and
every volume, and the classical lower bound holds with the constant `1/4`. -/
theorem effective_action_zero (β : ℝ) (hβ : 0 ≤ β) :
    ∃ Seff : Configuration (Vertex n) Q → ℝ, Measurable Seff ∧
      blockedLaw n zeroW β =
        (referenceMeasure Q (Vertex n)).withDensity (fun V => ENNReal.ofReal (Real.exp (-Seff V))) ∧
      ∀ᵐ V ∂referenceMeasure Q (Vertex n),
        β / 4 * actionL (linkValue n Q V) + Real.log (fineZ n β).toReal ≤ Seff V ∧
        Seff V ≤ β * (4 * (fineP n : ℝ)) + Real.log (fineZ n β).toReal := by
  have h := exists_effective_action n zeroW adm_zero 0 le_rfl he_zero β hβ
  rw [blockedHaar_zero] at h
  have e : (4 + 64 * (0 : ℝ)) * (1 + 48 * 0) = 4 := by norm_num
  simpa only [e] using h

end EffectiveAction

/-! ### Blocks and corners of the coarse lattice -/

section Coordinates

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- Every fine coordinate is `2t` or `2t + 1`. -/
theorem fine_cases (s : ZMod (2 * n)) : (∃ t, s = emb1 n t) ∨ ∃ t, s = emb1 n t + 1 := by
  have hs := s.val_lt
  have hq : s.val / 2 < n := by omega
  have hq' : ((s.val / 2 : ℕ) : ZMod n).val = s.val / 2 := ZMod.val_natCast_of_lt hq
  rcases Nat.mod_two_eq_zero_or_one s.val with h | h
  · left
    refine ⟨((s.val / 2 : ℕ) : ZMod n), ZMod.val_injective _ ?_⟩
    rw [emb1_val, hq']
    omega
  · right
    refine ⟨((s.val / 2 : ℕ) : ZMod n), ZMod.val_injective _ ?_⟩
    have := emb1_add_val n ((s.val / 2 : ℕ) : ZMod n) 1 le_rfl
    rw [Nat.cast_one] at this
    rw [this, hq']
    omega

/-- The coarse coordinate rounded down. -/
def dn (s : ZMod (2 * n)) : ZMod n := ((s.val / 2 : ℕ) : ZMod n)

/-- The coarse coordinate rounded up. -/
def up (s : ZMod (2 * n)) : ZMod n := (((s.val + 1) / 2 : ℕ) : ZMod n)

theorem odd_val (t : ZMod n) : (emb1 n t + 1).val = 2 * t.val + 1 := by
  have := emb1_add_val n t 1 le_rfl
  rwa [Nat.cast_one] at this

theorem dn_even (t : ZMod n) : dn n (emb1 n t) = t := by
  unfold dn
  rw [emb1_val, Nat.mul_div_cancel_left _ (by norm_num)]
  exact ZMod.natCast_zmod_val t

theorem dn_odd (t : ZMod n) : dn n (emb1 n t + 1) = t := by
  unfold dn
  rw [odd_val]
  have : (2 * t.val + 1) / 2 = t.val := by omega
  rw [this]
  exact ZMod.natCast_zmod_val t

theorem emb1_sub_one (t : ZMod n) : emb1 n t - 1 = emb1 n (t - 1) + 1 := by
  have h : emb1 n t = emb1 n (t - 1) + 2 := by
    have := emb1_add n (t - 1) 1
    rw [sub_add_cancel, emb1_one] at this
    exact this
  rw [h]
  ring

theorem dn_sub_one (t : ZMod n) : dn n (emb1 n t - 1) = t - 1 := by
  rw [emb1_sub_one, dn_odd]

theorem up_even (t : ZMod n) : up n (emb1 n t) = t := by
  unfold up
  rw [emb1_val]
  have : (2 * t.val + 1) / 2 = t.val := by omega
  rw [this]
  exact ZMod.natCast_zmod_val t

theorem up_odd (t : ZMod n) : up n (emb1 n t + 1) = t + 1 := by
  unfold up
  rw [odd_val]
  have : (2 * t.val + 1 + 1) / 2 = t.val + 1 := by omega
  rw [this]
  push_cast
  rw [ZMod.natCast_zmod_val]

theorem even_emb1 (t : ZMod n) : Even (emb1 n t).val := by
  rw [emb1_val]
  exact even_two_mul _

theorem odd_emb1 (t : ZMod n) : ¬ Even (emb1 n t + 1).val := by
  rw [odd_val]
  simp [parity_simps]

theorem emb1_succ_succ (t : ZMod n) : emb1 n t + 1 + 1 = emb1 n (t + 1) := by
  rw [emb1_add, emb1_one]
  ring

/-- Stepping from an even coordinate rounds up by one more, and makes the coordinate odd. -/
theorem up_succ_even (s : ZMod (2 * n)) (h : Even s.val) : up n (s + 1) = up n s + 1 ∧ ¬ Even (s + 1).val := by
  rcases fine_cases n s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact ⟨by rw [up_odd, up_even], odd_emb1 n t⟩
  · exact absurd h (odd_emb1 n t)

/-- Stepping from an odd coordinate keeps the rounded-up value, and makes the coordinate even. -/
theorem up_succ_odd (s : ZMod (2 * n)) (h : ¬ Even s.val) : up n (s + 1) = up n s ∧ Even (s + 1).val := by
  rcases fine_cases n s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact absurd (even_emb1 n t) h
  · rw [emb1_succ_succ]
    exact ⟨by rw [up_even, up_odd], even_emb1 n _⟩

theorem up_eq_zero (s : ZMod (2 * n)) (h : Even s.val) : up n s = 0 ↔ s = 0 := by
  rcases fine_cases n s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [up_even, emb1_eq_zero]
  · exact absurd h (odd_emb1 n t)

theorem up_inj (s s' : ZMod (2 * n)) (h : up n s = up n s') (hp : Even s.val ↔ Even s'.val) : s = s' := by
  rcases fine_cases n s with ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> rcases fine_cases n s' with ⟨t', rfl⟩ | ⟨t', rfl⟩
  · rw [up_even, up_even] at h
    rw [h]
  · exact absurd (hp.1 (even_emb1 n t)) (odd_emb1 n t')
  · exact absurd (hp.2 (even_emb1 n t')) (odd_emb1 n t)
  · rw [up_odd, up_odd] at h
    rw [add_right_cancel h]

/-- The block containing a fine site: its coordinates, rounded down. -/
def blockOf (z : V') : Vertex n := fun i => dn n (z i)

/-- A corner of the coarse lattice: the coordinates of a fine site, rounded up. -/
def corner (z : V') : Vertex n := fun i => up n (z i)

theorem back_apply (N : ℕ) (x : Vertex N) (ν i : Fin 4) : back x ν i = x i - if i = ν then 1 else 0 := by
  by_cases h : i = ν
  · subst h
    simp [back]
  · simp [back, h]

theorem blockOf_emb (x : Vertex n) : blockOf n (emb n x) = x := by
  funext i
  exact dn_even n (x i)

theorem blockOf_step_emb (x : Vertex n) (μ : Fin 4) : blockOf n (step (2 * n) (emb n x) μ) = x := by
  funext i
  change dn n (step (2 * n) (emb n x) μ i) = x i
  rw [step_apply]
  by_cases h : i = μ
  · simp only [h, if_true]
    exact dn_odd n (x μ)
  · simp only [h, if_false, add_zero]
    exact dn_even n (x i)

theorem blockOf_back_emb (x : Vertex n) (ν : Fin 4) : blockOf n (back (emb n x) ν) = back x ν := by
  funext i
  change dn n (back (emb n x) ν i) = back x ν i
  rw [back_apply, back_apply]
  by_cases h : i = ν
  · simp only [h, if_true]
    exact dn_sub_one n (x ν)
  · simp only [h, if_false, sub_zero]
    exact dn_even n (x i)

theorem blockOf_step_back_emb (x : Vertex n) (μ ν : Fin 4) (hne : ν ≠ μ) :
    blockOf n (step (2 * n) (back (emb n x) ν) μ) = back x ν := by
  funext i
  change dn n (step (2 * n) (back (emb n x) ν) μ i) = back x ν i
  rw [step_apply, back_apply, back_apply]
  by_cases h : i = ν
  · have h2 : i ≠ μ := fun e => hne (h.symm.trans e)
    simp only [h, if_true, hne, if_false, add_zero]
    exact dn_sub_one n (x ν)
  · by_cases h2 : i = μ
    · subst h2
      simp only [h, if_true, if_false, sub_zero]
      exact dn_odd n (x i)
    · simp only [h, h2, if_false, sub_zero, add_zero]
      exact dn_even n (x i)

theorem blockOf_step_step_emb (x : Vertex n) (μ ν : Fin 4) (hne : ν ≠ μ) :
    blockOf n (step (2 * n) (step (2 * n) (emb n x) μ) ν) = x := by
  funext i
  change dn n (step (2 * n) (step (2 * n) (emb n x) μ) ν i) = x i
  rw [step_apply, step_apply]
  by_cases h : i = ν
  · have h2 : i ≠ μ := fun e => hne (h.symm.trans e)
    simp only [h, if_true, hne, if_false, add_zero]
    exact dn_odd n (x ν)
  · by_cases h2 : i = μ
    · subst h2
      simp only [h, if_true, if_false, add_zero]
      exact dn_odd n (x i)
    · simp only [h, h2, if_false, add_zero]
      exact dn_even n (x i)

theorem corner_emb (x : Vertex n) : corner n (emb n x) = x := by
  funext i
  exact up_even n (x i)

theorem corner_step_even (z : V') (μ : Fin 4) (h : Even (z μ).val) :
    corner n (step (2 * n) z μ) = step n (corner n z) μ := by
  funext i
  change up n (step (2 * n) z μ i) = step n (corner n z) μ i
  rw [step_apply, step_apply]
  by_cases hi : i = μ
  · subst hi
    simp only [if_true]
    exact (up_succ_even n _ h).1
  · simp only [hi, if_false, add_zero]
    rfl

theorem corner_step_odd (z : V') (μ : Fin 4) (h : ¬ Even (z μ).val) :
    corner n (step (2 * n) z μ) = corner n z := by
  funext i
  change up n (step (2 * n) z μ i) = up n (z i)
  rw [step_apply]
  by_cases hi : i = μ
  · subst hi
    simp only [if_true]
    exact (up_succ_odd n _ h).1
  · simp only [hi, if_false, add_zero]

theorem coord_step_ne (z : V') (μ ν : Fin 4) (h : ν ≠ μ) : step (2 * n) z μ ν = z ν := by
  rw [step_apply]
  simp [h]

/-- A site is determined by its corner and the parity of its coordinates. -/
theorem corner_parity_inj : Function.Injective fun z : V' =>
    (corner n z, fun i => decide (Even (z i).val)) := by
  intro z z' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  funext i
  refine up_inj n _ _ (congrFun h1 i) ?_
  have := congrFun h2 i
  simpa using this

end Coordinates

/-! ### An exact interpolation for the path-product map -/

section Interp

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- **A fine field with prescribed lines.** A fine link at an even coordinate carries the coarse link at the corner of its
base point, and a link at an odd coordinate is `1`. -/
def interp (V : Vertex n → Fin 4 → Q) : V' → Fin 4 → Q :=
  fun z ρ => if Even (z ρ).val then V (corner n z) ρ else 1

theorem interp_even (V : Vertex n → Fin 4 → Q) (z : V') (ρ : Fin 4) (h : Even (z ρ).val) :
    interp n V z ρ = V (corner n z) ρ := if_pos h

theorem interp_odd (V : Vertex n → Fin 4 → Q) (z : V') (ρ : Fin 4) (h : ¬ Even (z ρ).val) :
    interp n V z ρ = 1 := if_neg h

/-- Its lines are the coarse field. -/
theorem lineU_interp (V : Vertex n → Fin 4 → Q) (x : Vertex n) (μ : Fin 4) :
    lineU (interp n V) μ (emb n x) = V x μ := by
  unfold lineU
  have h0 : Even (emb n x μ).val := even_emb1 n (x μ)
  have h1 : ¬ Even (step (2 * n) (emb n x) μ μ).val := by
    rw [step_apply]
    simpa using odd_emb1 n (x μ)
  rw [interp_even n V _ _ h0, interp_odd n V _ _ h1, mul_one, corner_emb]

/-- **The interpolation is a right inverse of the path-product map.** -/
theorem blockField_interp (V : Vertex n → Fin 4 → Q) : blockField n zeroW (interp n V) = V := by
  funext x μ
  change blockW zeroW (interp n V) (emb n x) μ = V x μ
  rw [blockW_zero, lineU_interp]

theorem twistExp_corner (μ ν : Fin 4) (z : V') (hμ : Even (z μ).val) (hν : Even (z ν).val) :
    twistExp μ ν (corner n z) = twistExp μ ν z := by
  unfold twistExp
  by_cases h : μ = 1 ∧ ν = 2
  · obtain ⟨rfl, rfl⟩ := h
    have e1 : corner n z 1 = 0 ↔ z 1 = 0 := up_eq_zero n _ hμ
    have e2 : corner n z 2 = 0 ↔ z 2 = 0 := up_eq_zero n _ hν
    simp only [e1, e2]
  · have h1 : ∀ {a b : Prop}, ¬ (μ = 1 ∧ ν = 2 ∧ a ∧ b) := fun hh => h ⟨hh.1, hh.2.1⟩
    rw [if_neg h1, if_neg h1]

theorem twistExp_odd (μ ν : Fin 4) (z : V') (h : ¬ (Even (z μ).val ∧ Even (z ν).val)) :
    twistExp μ ν z = 0 := by
  unfold twistExp
  rw [if_neg]
  rintro ⟨rfl, rfl, h1, h2⟩
  apply h
  rw [h1, h2]
  simp

/-- On a cell with both coordinates even, the defect of the interpolation is a coarse defect. -/
theorem defect_interp_even (V : Vertex n → Fin 4 → Q) (μ ν : Fin 4) (hne : μ ≠ ν) (z : V')
    (hμ : Even (z μ).val) (hν : Even (z ν).val) :
    defect (interp n V) μ ν z = defect V μ ν (corner n z) := by
  unfold defect
  have e1 : Even (step (2 * n) z μ ν).val := by rwa [coord_step_ne n z μ ν hne.symm]
  have e2 : Even (step (2 * n) z ν μ).val := by rwa [coord_step_ne n z ν μ hne]
  rw [interp_even n V _ _ hμ, interp_even n V _ _ e1, interp_even n V _ _ e2, interp_even n V _ _ hν,
    corner_step_even n z μ hμ, corner_step_even n z ν hν, twistExp_corner n μ ν z hμ hν]

/-- On every other cell the interpolation has no defect. -/
theorem defect_interp_odd (V : Vertex n → Fin 4 → Q) (μ ν : Fin 4) (hne : μ ≠ ν) (z : V')
    (h : ¬ (Even (z μ).val ∧ Even (z ν).val)) : defect (interp n V) μ ν z = 0 := by
  unfold defect
  rw [twistExp_odd n μ ν z h, pow_zero]
  have hprod : interp n V z μ * interp n V (step (2 * n) z μ) ν * (interp n V (step (2 * n) z ν) μ)⁻¹ *
      (interp n V z ν)⁻¹ = 1 := by
    have c1 : step (2 * n) z μ ν = z ν := coord_step_ne n z μ ν hne.symm
    have c2 : step (2 * n) z ν μ = z μ := coord_step_ne n z ν μ hne
    by_cases hμ : Even (z μ).val
    · have hν : ¬ Even (z ν).val := fun hν => h ⟨hμ, hν⟩
      have a2 : interp n V (step (2 * n) z μ) ν = 1 := interp_odd n V _ _ (by rwa [c1])
      have a3 : interp n V (step (2 * n) z ν) μ = V (corner n z) μ := by
        rw [interp_even n V _ _ (by rwa [c2]), corner_step_odd n z ν hν]
      rw [interp_even n V _ _ hμ, a2, a3, interp_odd n V _ _ hν]
      group
    · have a3 : interp n V (step (2 * n) z ν) μ = 1 := interp_odd n V _ _ (by rwa [c2])
      rw [interp_odd n V _ _ hμ, a3]
      by_cases hν : Even (z ν).val
      · have a2 : interp n V (step (2 * n) z μ) ν = V (corner n z) ν := by
          rw [interp_even n V _ _ (by rwa [c1]), corner_step_odd n z μ hμ]
        rw [a2, interp_even n V _ _ hν]
        group
      · have a2 : interp n V (step (2 * n) z μ) ν = 1 := interp_odd n V _ _ (by rwa [c1])
        rw [a2, interp_odd n V _ _ hν]
        group
  rw [hprod]
  simp [d]

theorem card_even_pair (μ ν : Fin 4) (h : μ ≠ ν) :
    (Finset.univ.filter fun b : Fin 4 → Bool => b μ = true ∧ b ν = true).card = 4 := by
  revert μ ν
  decide

theorem corner_parity_bij : Function.Bijective fun z : V' =>
    (corner n z, fun i => decide (Even (z i).val)) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨corner_parity_inj n, ?_⟩
  simp [ZMod.card]
  ring

/-- Each coarse plaquette appears on exactly four fine cells: corner and parity are coordinates on the fine lattice. -/
theorem sum_cells_eq (g : Vertex n → ℝ) (μ ν : Fin 4) (hne : μ ≠ ν) :
    ∑ z : V', (if Even (z μ).val ∧ Even (z ν).val then g (corner n z) else 0) = 4 * ∑ x, g x := by
  classical
  let h : Vertex n × (Fin 4 → Bool) → ℝ := fun p => if p.2 μ = true ∧ p.2 ν = true then g p.1 else 0
  have e1 : ∑ z : V', (if Even (z μ).val ∧ Even (z ν).val then g (corner n z) else 0) =
      ∑ z : V', h (corner n z, fun i => decide (Even (z i).val)) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [h]
  have e2 : ∑ z : V', h (corner n z, fun i => decide (Even (z i).val)) = ∑ p, h p :=
    (corner_parity_bij n).sum_comp h
  have e3 : ∑ p, h p = 4 * ∑ x, g x := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [h]
    rw [← Finset.sum_filter, Finset.sum_const, card_even_pair μ ν hne, nsmul_eq_mul]
    norm_num
  rw [e1, e2, e3]

/-- **The action of the interpolation is exactly four times the coarse action, for every coarse field.** So every coarse
field is the image of a fine field of comparable action. Together with `actionL_blockField_le` at `e = 0`, the least fine action
with prescribed lines is between `S_c/4` and `4 S_c`. The factor `16` between these is not closed here; by a hand count a smooth
interpolation of a smooth field would have fine action near `S_c`. -/
theorem actionL_interp_eq (V : Vertex n → Fin 4 → Q) : actionL (interp n V) = 4 * actionL V := by
  rw [actionL_eq, actionL_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hne : p.1.1 ≠ p.1.2 := p.2.ne
  have e : ∑ z : V', defect (interp n V) p.1.1 p.1.2 z ^ 2 =
      ∑ z : V', (if Even (z p.1.1).val ∧ Even (z p.1.2).val then
        (fun x => defect V p.1.1 p.1.2 x ^ 2) (corner n z) else 0) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases h : Even (z p.1.1).val ∧ Even (z p.1.2).val
    · rw [if_pos h, defect_interp_even n V _ _ hne z h.1 h.2]
    · rw [if_neg h, defect_interp_odd n V _ _ hne z h]
      norm_num
  rw [e]
  exact sum_cells_eq n (fun x => defect V p.1.1 p.1.2 x ^ 2) _ _ hne

theorem actionL_interp_le (V : Vertex n → Fin 4 → Q) : actionL (interp n V) ≤ 4 * actionL V :=
  (actionL_interp_eq n V).le

/-- Every fine defect of the interpolation is `0` or a coarse defect. -/
theorem defect_interp_le (V : Vertex n → Fin 4 → Q) (δ : ℝ) (hδ : 0 ≤ δ)
    (hV : ∀ (x : Vertex n) (μ ν : Fin 4), μ < ν → defect V μ ν x ≤ δ) (z : V') (μ ν : Fin 4) (h : μ < ν) :
    defect (interp n V) μ ν z ≤ δ := by
  by_cases he : Even (z μ).val ∧ Even (z ν).val
  · rw [defect_interp_even n V μ ν h.ne z he.1 he.2]
    exact hV _ _ _ h
  · rw [defect_interp_odd n V μ ν h.ne z he]
    exact hδ

/-- **The interpolation is gauge covariant, with no gauge fixing.** A coarse gauge transformation acts on it by the fine
gauge transformation that takes the value at the corner of each site. -/
theorem interp_act (g : Vertex n → Q) (V : Vertex n → Fin 4 → Q) :
    interp n (act g V) = act (fun z => g (corner n z)) (interp n V) := by
  funext z ρ
  change _ = g (corner n z) * interp n V z ρ * (g (corner n (step (2 * n) z ρ)))⁻¹
  by_cases h : Even (z ρ).val
  · rw [interp_even n _ _ _ h, interp_even n _ _ _ h, corner_step_even n z ρ h]
    rfl
  · rw [interp_odd n _ _ _ h, interp_odd n _ _ _ h, corner_step_odd n z ρ h]
    group

/-- **With staples the interpolation is a near inverse, at small fields.** If every coarse defect is at most `δ`, the
blocked field of the interpolation is within `12 e δ` of `V`, link by link. It is not an exact inverse, and there is no
constrained integral with staples, so the bounds below do not extend. -/
theorem blockField_interp_close (a : Wt) (ha : ∀ μ ν, 0 ≤ a μ ν) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (V : Vertex n → Fin 4 → Q) (δ : ℝ) (hδ : 0 ≤ δ)
    (hV : ∀ (x : Vertex n) (μ ν : Fin 4), μ < ν → defect V μ ν x ≤ δ) (x : Vertex n) (μ : Fin 4) :
    d (blockField n a (interp n V) x μ) (V x μ) ≤ 12 * e * δ := by
  have h1 := blockW_close a ha e he (interp n V) μ (emb n x)
  rw [lineU_interp] at h1
  have hc (ν : Fin 4) (hν : ν ≠ μ) (z : V') : cd (interp n V) μ ν z ≤ δ := by
    unfold cd
    split_ifs with h
    · exact defect_interp_le n V δ hδ hV z μ ν h
    · exact defect_interp_le n V δ hδ hV z ν μ (lt_of_le_of_ne (not_lt.1 h) hν)
  have hE : cellE (interp n V) μ (emb n x) ≤ 12 * δ := by
    have h : ∀ ν, (if ν = μ then 0 else cells (interp n V) μ ν (emb n x)) ≤ if ν = μ then 0 else 4 * δ := by
      intro ν
      split_ifs with hν
      · exact le_rfl
      · unfold cells
        linarith only [hc ν hν (emb n x), hc ν hν (step (2 * n) (emb n x) μ), hc ν hν (back (emb n x) ν),
          hc ν hν (step (2 * n) (back (emb n x) ν) μ)]
    refine (Finset.sum_le_sum fun ν _ => h ν).trans (le_of_eq ?_)
    fin_cases μ <;> simp [Fin.sum_univ_four] <;> ring
  have := mul_le_mul_of_nonneg_left hE he0
  change d (blockW a (interp n V) (emb n x) μ) (V x μ) ≤ _
  nlinarith only [h1, this]

end Interp

/-! ### The split according to the bad blocks -/

section Split

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

theorem continuous_defect (N : ℕ) [NeZero N] (μ ν : Fin 4) (x : Vertex N) :
    Continuous fun U : Configuration (Vertex N) Q => defect (linkValue N Q U) μ ν x := by
  have hl (x : Vertex N) (ρ : Fin 4) : Continuous fun V : Configuration (Vertex N) Q => linkValue N Q V x ρ :=
    continuous_apply _
  unfold defect d
  refine Continuous.norm (Continuous.sub (continuous_subtype_val.comp ?_) continuous_const)
  exact (((hl _ _).mul (hl _ _)).mul (hl _ _).inv).mul (hl _ _).inv

open Classical in
/-- The bad blocks: the coarse sites `x` whose block, the fine sites with coordinates `2 xᵢ` or `2 xᵢ + 1`, is the base
of a fine plaquette with defect above `δ`. Every fine plaquette has its base in exactly one block. -/
def badBlocks (δ : ℝ) (U : Configuration V' Q) : Finset (Vertex n) :=
  (badPlaq n (linkValue (2 * n) Q U) δ).image fun p => blockOf n p.1

theorem mem_badBlocks (δ : ℝ) (U : Configuration V' Q) (x : Vertex n) :
    x ∈ badBlocks n δ U ↔ ∃ p : PlaquetteIndex (2 * n), blockOf n p.1 = x ∧
      δ < defect (linkValue (2 * n) Q U) p.2.1.1 p.2.1.2 p.1 := by
  classical
  unfold badBlocks badPlaq
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨p, h1, h2⟩ => ⟨p, h2, h1⟩, fun ⟨p, h2, h1⟩ => ⟨p, h1, h2⟩⟩

/-- **Each bad block costs its own `δ²` of action.** Blocks do not share plaquettes, so there is no overlap factor. -/
theorem card_badBlocks_le (δ : ℝ) (hδ0 : 0 ≤ δ) (U : Configuration V' Q) :
    ((badBlocks n δ U).card : ℝ) * δ ^ 2 ≤ actionL (linkValue (2 * n) Q U) := by
  classical
  have h1 : ((badBlocks n δ U).card : ℝ) ≤ ((badPlaq n (linkValue (2 * n) Q U) δ).card : ℝ) := by
    exact_mod_cast Finset.card_image_le
  have h2 := card_badPlaq_le n (linkValue (2 * n) Q U) δ hδ0
  have := mul_le_mul_of_nonneg_right h1 (sq_nonneg δ)
  linarith only [this, h2]

theorem defect_le_of_good (δ : ℝ) (U : Configuration V' Q) (z : V') (hz : blockOf n z ∉ badBlocks n δ U)
    (μ ν : Fin 4) (h : μ < ν) : defect (linkValue (2 * n) Q U) μ ν z ≤ δ := by
  by_contra hc
  exact hz ((mem_badBlocks n δ U _).2 ⟨(z, ⟨(μ, ν), h⟩), rfl, not_le.1 hc⟩)

theorem cd_le_of_good (δ : ℝ) (U : Configuration V' Q) (z : V') (hz : blockOf n z ∉ badBlocks n δ U)
    (μ ν : Fin 4) (hne : ν ≠ μ) : cd (linkValue (2 * n) Q U) μ ν z ≤ δ := by
  unfold cd
  split_ifs with h
  · exact defect_le_of_good n δ U z hz μ ν h
  · exact defect_le_of_good n δ U z hz ν μ (lt_of_le_of_ne (not_lt.1 h) hne)

theorem measurableSet_mem_badBlocks (δ : ℝ) (x : Vertex n) :
    MeasurableSet {U : Configuration V' Q | x ∈ badBlocks n δ U} := by
  have e : {U : Configuration V' Q | x ∈ badBlocks n δ U} =
      ⋃ p : {p : PlaquetteIndex (2 * n) // blockOf n p.1 = x},
        {U | δ < defect (linkValue (2 * n) Q U) p.val.2.1.1 p.val.2.1.2 p.val.1} := by
    ext U
    simp only [Set.mem_setOf_eq, mem_badBlocks, Set.mem_iUnion, Subtype.exists, exists_prop]
  rw [e]
  refine MeasurableSet.iUnion fun p => ?_
  exact (isOpen_lt continuous_const (continuous_defect (2 * n) _ _ _)).measurableSet

theorem measurableSet_badBlocks (δ : ℝ) (Λ : Finset (Vertex n)) :
    MeasurableSet {U : Configuration V' Q | badBlocks n δ U = Λ} := by
  classical
  have e : {U : Configuration V' Q | badBlocks n δ U = Λ} =
      ⋂ x : Vertex n, {U | x ∈ badBlocks n δ U ↔ x ∈ Λ} := by
    ext U
    simp [Finset.ext_iff]
  rw [e]
  refine MeasurableSet.iInter fun x => ?_
  have hm := measurableSet_mem_badBlocks n δ x
  by_cases hl : x ∈ Λ
  · simpa only [hl, iff_true] using hm
  · simpa only [hl, iff_false] using hm.compl

/-- The part of the blocked law coming from fine fields with exactly the bad blocks `Λ`. -/
def blockedPiece (a : Wt) (β δ : ℝ) (Λ : Finset (Vertex n)) : Measure (Configuration (Vertex n) Q) :=
  ((twistedLaw n β).restrict {U | badBlocks n δ U = Λ}).map (blockCfg n a)

theorem blockedPiece_apply (a : Wt) (ha : Adm a) (β δ : ℝ) (Λ : Finset (Vertex n))
    (A : Set (Configuration (Vertex n) Q)) (hA : MeasurableSet A) :
    blockedPiece n a β δ Λ A = twistedLaw n β (blockCfg n a ⁻¹' A ∩ {U | badBlocks n δ U = Λ}) := by
  have hB := (continuous_blockCfg n a ha).measurable
  unfold blockedPiece
  rw [Measure.map_apply hB hA, Measure.restrict_apply (hB hA)]

/-- The blocked law is the sum of its pieces. This holds for any measurable partition of the fine fields; the content
of the split is in `blockedPiece_le` and `blockedPiece_support`. -/
theorem sum_blockedPiece (a : Wt) (ha : Adm a) (β δ : ℝ) :
    ∑ Λ, blockedPiece n a β δ Λ = blockedLaw n a β := by
  classical
  have hB := (continuous_blockCfg n a ha).measurable
  refine Measure.ext fun A hA => ?_
  rw [Measure.finset_sum_apply]
  simp only [blockedPiece_apply n a ha β δ _ A hA]
  unfold blockedLaw
  rw [Measure.map_apply hB hA]
  have hpre := sum_measure_preimage_singleton (μ := (twistedLaw n β).restrict (blockCfg n a ⁻¹' A))
    (f := badBlocks n δ) Finset.univ (fun Λ _ => measurableSet_badBlocks n δ Λ)
  simp only [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hpre
  rw [← hpre]
  refine Finset.sum_congr rfl fun Λ _ => ?_
  have hΛ : MeasurableSet (badBlocks n δ ⁻¹' {Λ}) := measurableSet_badBlocks n δ Λ
  rw [Measure.restrict_apply hΛ]
  congr 1
  ext U
  simp [and_comm]

/-- **Each bad block costs `exp(-β δ²)` in density.** Relative to the blocked Haar measure, the piece with bad blocks `Λ`
has density at most `Z⁻¹ exp(-β δ² |Λ|)`. The prefactor `Z⁻¹` is extensive, so this alone does not make any piece small. -/
theorem blockedPiece_le (a : Wt) (ha : Adm a) (β δ : ℝ) (hβ : 0 ≤ β) (hδ0 : 0 ≤ δ) (Λ : Finset (Vertex n))
    (A : Set (Configuration (Vertex n) Q)) (hA : MeasurableSet A) :
    blockedPiece n a β δ Λ A ≤
      (fineZ n β)⁻¹ * ENNReal.ofReal (Real.exp (-(β * ((Λ.card : ℝ) * δ ^ 2)))) * blockedHaar n a A := by
  have hB := (continuous_blockCfg n a ha).measurable
  rw [blockedPiece_apply n a ha β δ Λ A hA]
  have hS := (hB hA).inter (measurableSet_badBlocks n δ Λ)
  rw [twistedLaw_apply n β _ hS, mul_assoc]
  gcongr
  unfold blockedHaar
  rw [Measure.map_apply hB hA]
  calc
    _ ≤ ∫⁻ _ in blockCfg n a ⁻¹' A ∩ {U | badBlocks n δ U = Λ},
          ENNReal.ofReal (Real.exp (-(β * ((Λ.card : ℝ) * δ ^ 2)))) ∂referenceMeasure Q V' := by
      refine setLIntegral_mono measurable_const fun U hU => ?_
      unfold gibbsDensity
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      rw [fineS_eq]
      have hΛ : badBlocks n δ U = Λ := hU.2
      have h2 := card_badBlocks_le n δ hδ0 U
      rw [hΛ] at h2
      nlinarith only [mul_le_mul_of_nonneg_left h2 hβ]
    _ = ENNReal.ofReal (Real.exp (-(β * ((Λ.card : ℝ) * δ ^ 2)))) *
          referenceMeasure Q V' (blockCfg n a ⁻¹' A ∩ {U | badBlocks n δ U = Λ}) := setLIntegral_const _ _
    _ ≤ _ := by
      gcongr
      exact Set.inter_subset_left

theorem cellE_le_of_good (U : V' → Fin 4 → Q) (δ : ℝ) (μ : Fin 4) (y : V') (hg : LinkGood U δ y μ) :
    cellE U μ y ≤ 12 * δ := by
  have h : ∀ ν, (if ν = μ then 0 else cells U μ ν y) ≤ if ν = μ then 0 else 4 * δ := by
    intro ν
    split_ifs with hν
    · exact le_rfl
    · obtain ⟨g1, g2, g3, g4⟩ := hg ν hν
      unfold cells
      linarith only [g1, g2, g3, g4]
  refine (Finset.sum_le_sum fun ν _ => h ν).trans (le_of_eq ?_)
  fin_cases μ <;> simp [Fin.sum_univ_four] <;> ring

/-- If the cells around the four sides of a coarse plaquette are small, its defect is at most `(4 + 48 e) δ`, whatever
the field does elsewhere. With isotropic weights `e ≤ 1/3`, so this is `20 δ`. -/
theorem coarse_defect_good (a : Wt) (ha : ∀ μ ν, 0 ≤ a μ ν) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (U : V' → Fin 4 → Q) (δ : ℝ) (μ ν : Fin 4) (hμν : μ < ν)
    (x : Vertex n) (h1 : LinkGood U δ (emb n x) μ)
    (h2 : LinkGood U δ (step (2 * n) (step (2 * n) (emb n x) μ) μ) ν)
    (h3 : LinkGood U δ (step (2 * n) (step (2 * n) (emb n x) ν) ν) μ) (h4 : LinkGood U δ (emb n x) ν) :
    defect (blockField n a U) μ ν x ≤ (4 + 48 * e) * δ := by
  have hb := coarse_defect_le n a ha e he U μ ν x
  have hcd (z : V') : cd U μ ν z = defect U μ ν z := by
    unfold cd
    simp only [hμν, if_true]
  have hne : ν ≠ μ := hμν.ne'
  obtain ⟨g1, g2, -, -⟩ := h1 ν hne
  obtain ⟨-, -, g3, g4⟩ := h3 ν hne
  rw [hcd] at g1 g2 g3 g4
  rw [back_step, step_step_comm (emb n x) ν μ] at g4
  rw [back_step] at g3
  have c1 := cellE_le_of_good n U δ μ _ h1
  have c2 := cellE_le_of_good n U δ ν _ h2
  have c3 := cellE_le_of_good n U δ μ _ h3
  have c4 := cellE_le_of_good n U δ ν _ h4
  have hm := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add c1 c2) c3) c4) he0
  have : e * (12 * δ + 12 * δ + 12 * δ + 12 * δ) = 48 * e * δ := by ring
  rw [this] at hm
  have : (4 + 48 * e) * δ = 4 * δ + 48 * e * δ := by ring
  rw [this]
  linarith only [hb, hm, g1, g2, g3, g4]

/-- The blocked link at a coarse site sees only its own block and the blocks just below it, in the other directions. -/
def LinkClear (Λ : Finset (Vertex n)) (y : Vertex n) (ρ : Fin 4) : Prop :=
  y ∉ Λ ∧ ∀ σ, σ ≠ ρ → back y σ ∉ Λ

theorem linkGood_of_clear (δ : ℝ) (U : Configuration V' Q) (y : Vertex n) (ρ : Fin 4)
    (h : LinkClear n (badBlocks n δ U) y ρ) : LinkGood (linkValue (2 * n) Q U) δ (emb n y) ρ := by
  intro ν hν
  have hb := h.2 ν hν
  refine ⟨cd_le_of_good n δ U _ ?_ ρ ν hν, cd_le_of_good n δ U _ ?_ ρ ν hν, cd_le_of_good n δ U _ ?_ ρ ν hν,
    cd_le_of_good n δ U _ ?_ ρ ν hν⟩
  · rw [blockOf_emb]
    exact h.1
  · rw [blockOf_step_emb]
    exact h.1
  · rw [blockOf_back_emb]
    exact hb
  · rw [blockOf_step_back_emb n y ρ ν hν]
    exact hb

/-- The coarse fields on which every plaquette whose blocks avoid `Λ` has small defect. -/
def SmallOff (e δ : ℝ) (Λ : Finset (Vertex n)) : Set (Configuration (Vertex n) Q) :=
  {V | ∀ (x : Vertex n) (μ ν : Fin 4), μ < ν → LinkClear n Λ x μ → LinkClear n Λ (step n x μ) ν →
    LinkClear n Λ (step n x ν) μ → LinkClear n Λ x ν → defect (linkValue n Q V) μ ν x ≤ (4 + 48 * e) * δ}

theorem measurableSet_smallOff (e δ : ℝ) (Λ : Finset (Vertex n)) : MeasurableSet (SmallOff n e δ Λ) := by
  have : IsClosed (SmallOff n e δ Λ) := by
    simp only [SmallOff, Set.setOf_forall]
    refine isClosed_iInter fun x => isClosed_iInter fun μ => isClosed_iInter fun ν =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => ?_
    exact isClosed_le (continuous_defect n μ ν x) continuous_const
  exact this.measurableSet

/-- **The support of each piece.** The piece with bad blocks `Λ` lives on coarse fields whose plaquettes away from `Λ`
have defect at most `(4 + 48 e) δ`. In particular the piece `Λ = ∅`, in which every fine plaquette has defect at most `δ`,
lives on fields with all coarse defects small. -/
theorem blockedPiece_support (a : Wt) (ha : Adm a) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (β δ : ℝ) (Λ : Finset (Vertex n)) :
    blockedPiece n a β δ Λ (SmallOff n e δ Λ)ᶜ = 0 := by
  rw [blockedPiece_apply n a ha β δ Λ _ (measurableSet_smallOff n e δ Λ).compl]
  have hsub : blockCfg n a ⁻¹' (SmallOff n e δ Λ)ᶜ ∩ {U | badBlocks n δ U = Λ} = ∅ := by
    ext U
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro hnot hΛ
    apply hnot
    intro x μ ν hμν n1 n2 n3 n4
    rw [← hΛ] at n1 n2 n3 n4
    have g1 := linkGood_of_clear n δ U _ _ n1
    have g2 := linkGood_of_clear n δ U _ _ n2
    have g3 := linkGood_of_clear n δ U _ _ n3
    have g4 := linkGood_of_clear n δ U _ _ n4
    rw [emb_step] at g2 g3
    exact coarse_defect_good n a ha.nonneg e he0 he _ δ μ ν hμν x g1 g2 g3 g4
  rw [hsub, measure_empty]

/-- With no staples a coarse plaquette sees only its own block: if `x` is not a bad block, the plaquettes based at `x`
have defect at most `4 δ`. -/
theorem coarse_defect_block (δ : ℝ) (U : Configuration V' Q) (x : Vertex n) (hx : x ∉ badBlocks n δ U)
    (μ ν : Fin 4) (h : μ < ν) : defect (blockField n zeroW (linkValue (2 * n) Q U)) μ ν x ≤ 4 * δ := by
  have hne : ν ≠ μ := h.ne'
  have hb := coarse_defect_le n zeroW (fun _ _ => le_rfl) 0 he_zero (linkValue (2 * n) Q U) μ ν x
  have g1 := defect_le_of_good n δ U (step (2 * n) (emb n x) μ) (by rwa [blockOf_step_emb]) μ ν h
  have g2 := defect_le_of_good n δ U (step (2 * n) (step (2 * n) (emb n x) μ) ν)
    (by rwa [blockOf_step_step_emb n x μ ν hne]) μ ν h
  have g3 := defect_le_of_good n δ U (emb n x) (by rwa [blockOf_emb]) μ ν h
  have g4 := defect_le_of_good n δ U (step (2 * n) (emb n x) ν) (by rwa [blockOf_step_emb]) μ ν h
  linarith only [hb, g1, g2, g3, g4]

/-- The coarse fields on which every plaquette based outside `Λ` has defect at most `4 δ`. -/
def SmallAt (δ : ℝ) (Λ : Finset (Vertex n)) : Set (Configuration (Vertex n) Q) :=
  {V | ∀ (x : Vertex n) (μ ν : Fin 4), μ < ν → x ∉ Λ → defect (linkValue n Q V) μ ν x ≤ 4 * δ}

end Split

/-! ### The constrained integral, with no staples

With no staples the fine field can be solved for its blocked value. Left translation of the first link of each pair
translates the blocked field, so the density is an honest integral over the fine fields with the given lines, for every
coarse field. The map here is the path product, which the numerics show roughens under iteration. The translation trick
does not extend to staples, since a staple depends on first links of other blocks. -/

section Constrained

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- Left translation of the first links by a coarse field. -/
def phi (h : Configuration (Vertex n) Q) : Configuration V' Q := Function.extend (firstEdge n) h 1

theorem phi_first (h : Configuration (Vertex n) Q) (c : Edge (Vertex n)) : phi n h (firstEdge n c) = h c :=
  (firstEdge_injective n).extend_apply h 1 c

theorem phi_other (h : Configuration (Vertex n) Q) (e : Edge V') (he : ¬∃ c, firstEdge n c = e) :
    phi n h e = 1 := by
  unfold phi
  rw [Function.extend_apply' _ _ _ he]
  rfl

theorem continuous_phi : Continuous (phi n) := by
  refine continuous_pi fun e => ?_
  by_cases he : ∃ c, firstEdge n c = e
  · obtain ⟨c, rfl⟩ := he
    simp only [phi_first]
    exact continuous_apply c
  · simp only [phi_other n _ e he]
    exact continuous_const

/-- The fine field `U`, translated so that its blocked field is `V`. -/
def glue (V : Configuration (Vertex n) Q) (U : Configuration V' Q) : Configuration V' Q :=
  phi n (V * (blockCfg n zeroW U)⁻¹) * U

theorem block_glue (V : Configuration (Vertex n) Q) (U : Configuration V' Q) :
    blockCfg n zeroW (glue n V U) = V := by
  unfold glue phi
  rw [blockCfg_zero_mul]
  group

theorem glue_mul (h : Configuration (Vertex n) Q) (U : Configuration V' Q) :
    glue n (h * blockCfg n zeroW U) U = phi n h * U := by
  unfold glue
  rw [mul_inv_cancel_right]

theorem continuous_glue : Continuous fun p : Configuration (Vertex n) Q × Configuration V' Q => glue n p.1 p.2 := by
  have hB := continuous_blockCfg n zeroW adm_zero
  unfold glue
  exact ((continuous_phi n).comp (continuous_fst.mul (hB.comp continuous_snd).inv)).mul continuous_snd

/-- **The constrained partition function**, for every coarse field. -/
def constrainedZ (β : ℝ) (V : Configuration (Vertex n) Q) : ℝ :=
  ∫ U, Real.exp (-fineS n β (glue n V U)) ∂referenceMeasure Q V'

theorem continuous_weight (β : ℝ) :
    Continuous fun p : Configuration (Vertex n) Q × Configuration V' Q =>
      Real.exp (-fineS n β (glue n p.1 p.2)) :=
  Real.continuous_exp.comp ((continuous_fineS n β).comp (continuous_glue n)).neg

theorem continuous_glue_right (V : Configuration (Vertex n) Q) : Continuous fun U => glue n V U := by
  have hB := continuous_blockCfg n zeroW adm_zero
  unfold glue
  exact ((continuous_phi n).comp (continuous_const.mul hB.inv)).mul continuous_id

theorem continuous_weight_right (β : ℝ) (V : Configuration (Vertex n) Q) :
    Continuous fun U => Real.exp (-fineS n β (glue n V U)) :=
  Real.continuous_exp.comp ((continuous_fineS n β).comp (continuous_glue_right n V)).neg

theorem integrable_weight (β : ℝ) (V : Configuration (Vertex n) Q) :
    Integrable (fun U => Real.exp (-fineS n β (glue n V U))) (referenceMeasure Q V') :=
  (continuous_weight_right n β V).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_constrainedZ (β : ℝ) : Continuous (constrainedZ n β) := by
  have h : Continuous fun V : Configuration (Vertex n) Q =>
      ∫ U in Set.univ, Real.exp (-fineS n β (glue n V U)) ∂referenceMeasure Q V' :=
    continuous_parametric_integral_of_continuous (μ := referenceMeasure Q V')
      (f := fun (V : Configuration (Vertex n) Q) U => Real.exp (-fineS n β (glue n V U)))
      (continuous_weight n β) isCompact_univ
  refine h.congr fun V => ?_
  rw [Measure.restrict_univ]
  rfl

theorem constrainedZ_lower (β : ℝ) (hβ : 0 ≤ β) (V : Configuration (Vertex n) Q) :
    Real.exp (-(β * (4 * (fineP n : ℝ)))) ≤ constrainedZ n β V := by
  have hc : ∫ _ : Configuration V' Q, Real.exp (-(β * (4 * (fineP n : ℝ)))) ∂referenceMeasure Q V' =
      Real.exp (-(β * (4 * (fineP n : ℝ)))) := by
    simp
  rw [← hc]
  refine integral_mono (integrable_const _) (integrable_weight n β V) fun U => ?_
  apply Real.exp_le_exp.2
  rw [fineS_eq]
  have := mul_le_mul_of_nonneg_left (actionL_le_card (2 * n) (linkValue (2 * n) Q (glue n V U))) hβ
  have h2 : (Fintype.card (PlaquetteIndex (2 * n)) : ℝ) = fineP n := rfl
  rw [h2] at this
  linarith only [this]

theorem constrainedZ_pos (β : ℝ) (hβ : 0 ≤ β) (V : Configuration (Vertex n) Q) : 0 < constrainedZ n β V :=
  (Real.exp_pos _).trans_le (constrainedZ_lower n β hβ V)

/-- **The classical bound at every coarse field**: the density is at most `exp(-(β/4) S_c(V))`, up to `Z⁻¹`. -/
theorem constrainedZ_upper (β : ℝ) (hβ : 0 ≤ β) (V : Configuration (Vertex n) Q) :
    constrainedZ n β V ≤ Real.exp (-(β / 4 * actionL (linkValue n Q V))) := by
  have hc : ∫ _ : Configuration V' Q, Real.exp (-(β / 4 * actionL (linkValue n Q V))) ∂referenceMeasure Q V' =
      Real.exp (-(β / 4 * actionL (linkValue n Q V))) := by
    simp
  rw [← hc]
  refine integral_mono (integrable_weight n β V) (integrable_const _) fun U => ?_
  apply Real.exp_le_exp.2
  rw [fineS_eq]
  have h2 := actionL_blockField_le n zeroW (fun _ _ => le_rfl) 0 le_rfl he_zero (linkValue (2 * n) Q (glue n V U))
  rw [← link_blockCfg, block_glue] at h2
  norm_num at h2
  nlinarith only [mul_le_mul_of_nonneg_left h2 hβ]

theorem glue_gauge (g : Vertex n → Q) (V : Configuration (Vertex n) Q) (U : Configuration V' Q) :
    glue n (gauge (Vertex n) Q g V) (gauge V' Q (Function.extend (emb n) g 1) U) =
      gauge V' Q (Function.extend (emb n) g 1) (glue n V U) := by
  funext e
  unfold glue
  rw [blockCfg_gauge n zeroW adm_zero]
  by_cases he : ∃ c, firstEdge n c = e
  · obtain ⟨c, rfl⟩ := he
    change phi n _ (firstEdge n c) * _ = _ * (phi n _ (firstEdge n c) * _) * _
    rw [phi_first, phi_first]
    have hs : Function.extend (emb n) g 1 (firstEdge n c).1 = g c.1 :=
      (emb_injective n).extend_apply g 1 c.1
    simp only [Pi.mul_apply, Pi.inv_apply, RegulatedGauge.gauge, mul_inv_rev, hs]
    group
  · change phi n _ e * _ = _ * (phi n _ e * _) * _
    rw [phi_other n _ e he, phi_other n _ e he]
    simp [RegulatedGauge.gauge]

/-- **Gauge invariance at every coarse field.** -/
theorem constrainedZ_gauge (β : ℝ) (g : Vertex n → Q) (V : Configuration (Vertex n) Q) :
    constrainedZ n β (gauge (Vertex n) Q g V) = constrainedZ n β V := by
  have hp := gauge_preserves_reference Q V' (Function.extend (emb n) g 1)
  have hc := continuous_weight_right n β (gauge (Vertex n) Q g V)
  have h1 := integral_map (μ := referenceMeasure Q V') hp.measurable.aemeasurable
    (f := fun U => Real.exp (-fineS n β (glue n (gauge (Vertex n) Q g V) U))) hc.aestronglyMeasurable
  rw [hp.map_eq] at h1
  change ∫ U, Real.exp (-fineS n β (glue n (gauge (Vertex n) Q g V) U)) ∂referenceMeasure Q V' = _
  rw [h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  change Real.exp (-fineS n β (glue n (gauge (Vertex n) Q g V) (gauge V' Q _ U))) =
    Real.exp (-fineS n β (glue n V U))
  rw [glue_gauge]
  congr 2
  exact action_gauge n β _ _

/-! #### The density -/

/-- **Disintegration of Haar measure over the path-product map.** For any measurable weight, the integral over the fine
fields with blocked field in `A` is an integral over `A` of the constrained integrals. -/
theorem lintegral_block_zero (w : Configuration V' Q → ℝ≥0∞) (hwm : Measurable w)
    (A : Set (Configuration (Vertex n) Q)) (hA : MeasurableSet A) :
    ∫⁻ U in blockCfg n zeroW ⁻¹' A, w U ∂referenceMeasure Q V' =
      ∫⁻ V in A, ∫⁻ U, w (glue n V U) ∂referenceMeasure Q V' ∂referenceMeasure Q (Vertex n) := by
  have hB := (continuous_blockCfg n zeroW adm_zero).measurable
  haveI hRl : (referenceMeasure Q V').IsMulLeftInvariant := by
    unfold referenceMeasure
    infer_instance
  haveI hRr : (referenceMeasure Q (Vertex n)).IsMulRightInvariant := by
    unfold referenceMeasure
    infer_instance
  have hglue : Measurable fun p : Configuration (Vertex n) Q × Configuration V' Q => glue n p.1 p.2 :=
    (continuous_glue n).measurable
  have hphi : Measurable fun p : Configuration (Vertex n) Q × Configuration V' Q => phi n p.1 * p.2 :=
    (((continuous_phi n).comp continuous_fst).mul continuous_snd).measurable
  have hind : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hA
  have e1 : ∫⁻ V in A, ∫⁻ U, w (glue n V U) ∂referenceMeasure Q V' ∂referenceMeasure Q (Vertex n) =
      ∫⁻ V, ∫⁻ U, A.indicator (fun _ => (1 : ℝ≥0∞)) V * w (glue n V U) ∂referenceMeasure Q V'
        ∂referenceMeasure Q (Vertex n) := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun V => ?_
    by_cases hV : V ∈ A
    · simp only [Set.indicator_of_mem hV, one_mul]
    · simp only [Set.indicator_of_notMem hV, zero_mul, lintegral_zero]
  rw [e1, lintegral_lintegral_swap]
  · have e2 (U : Configuration V' Q) :
        ∫⁻ V, A.indicator (fun _ => (1 : ℝ≥0∞)) V * w (glue n V U) ∂referenceMeasure Q (Vertex n) =
          ∫⁻ h, A.indicator (fun _ => (1 : ℝ≥0∞)) (blockCfg n zeroW (phi n h * U)) * w (phi n h * U)
            ∂referenceMeasure Q (Vertex n) := by
      rw [← lintegral_mul_right_eq_self _ (blockCfg n zeroW U)]
      refine lintegral_congr fun h => ?_
      rw [glue_mul]
      have : blockCfg n zeroW (phi n h * U) = h * blockCfg n zeroW U := blockCfg_zero_mul n h U
      rw [this]
    simp only [e2]
    rw [lintegral_lintegral_swap]
    · have e3 (h : Configuration (Vertex n) Q) :
          ∫⁻ U, A.indicator (fun _ => (1 : ℝ≥0∞)) (blockCfg n zeroW (phi n h * U)) * w (phi n h * U)
            ∂referenceMeasure Q V' =
            ∫⁻ U, A.indicator (fun _ => (1 : ℝ≥0∞)) (blockCfg n zeroW U) * w U ∂referenceMeasure Q V' :=
        lintegral_mul_left_eq_self
          (fun U => A.indicator (fun _ => (1 : ℝ≥0∞)) (blockCfg n zeroW U) * w U) (phi n h)
      simp only [e3]
      rw [lintegral_const, measure_univ, mul_one, ← lintegral_indicator (hB hA)]
      refine lintegral_congr fun U => ?_
      by_cases hU : blockCfg n zeroW U ∈ A <;> simp [hU, Set.indicator]
    · have hphi' : Measurable fun p : Configuration V' Q × Configuration (Vertex n) Q => phi n p.2 * p.1 :=
        (((continuous_phi n).comp continuous_snd).mul continuous_fst).measurable
      exact ((hind.comp (hB.comp hphi')).mul (hwm.comp hphi')).aemeasurable
  · refine AEMeasurable.mul ?_ ?_
    · exact (hind.comp measurable_fst).aemeasurable
    · exact (hwm.comp hglue).aemeasurable

/-- **The density of the blocked law, as a constrained integral.** -/
theorem blockedLaw_zero_apply (β : ℝ) (A : Set (Configuration (Vertex n) Q)) (hA : MeasurableSet A) :
    blockedLaw n zeroW β A = (fineZ n β)⁻¹ *
      ∫⁻ V in A, ENNReal.ofReal (constrainedZ n β V) ∂referenceMeasure Q (Vertex n) := by
  have hB := (continuous_blockCfg n zeroW adm_zero).measurable
  unfold blockedLaw
  rw [Measure.map_apply hB hA, twistedLaw_apply n β _ (hB hA),
    lintegral_block_zero n _ (measurable_gibbsDensity n β) A hA]
  congr 1
  refine lintegral_congr fun V => ?_
  unfold constrainedZ
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_weight n β V)
    (Filter.Eventually.of_forall fun U => (Real.exp_pos _).le)]
  rfl

/-- The effective action of the path-product map, defined at every coarse field. -/
def effS (β : ℝ) (V : Configuration (Vertex n) Q) : ℝ :=
  Real.log (fineZ n β).toReal - Real.log (constrainedZ n β V)

theorem continuous_effS (β : ℝ) (hβ : 0 ≤ β) : Continuous (effS n β) := by
  unfold effS
  exact continuous_const.sub ((continuous_constrainedZ n β).log fun V => (constrainedZ_pos n β hβ V).ne')

/-- **With no staples, `exp(-effS)` is the density of the blocked law against Haar measure.** -/
theorem blockedLaw_zero_eq (β : ℝ) (hβ : 0 ≤ β) :
    blockedLaw n zeroW β = (referenceMeasure Q (Vertex n)).withDensity
      (fun V => ENNReal.ofReal (Real.exp (-effS n β V))) := by
  have hZ1 : fineZ n β ≠ ∞ := gibbsPartition_ne_top _ _ _ (continuous_fineS n β)
  have hZ0 : fineZ n β ≠ 0 := (gibbsPartition_pos _ _ _ (continuous_fineS n β)).ne'
  have hZp : 0 < (fineZ n β).toReal := ENNReal.toReal_pos hZ0 hZ1
  have hm : Measurable fun V : Configuration (Vertex n) Q => ENNReal.ofReal (constrainedZ n β V) :=
    (continuous_constrainedZ n β).measurable.ennreal_ofReal
  refine Measure.ext fun A hA => ?_
  rw [blockedLaw_zero_apply n β A hA, withDensity_apply _ hA, ← lintegral_const_mul _ hm]
  refine lintegral_congr fun V => ?_
  have hp := constrainedZ_pos n β hβ V
  have e : Real.exp (-effS n β V) = (fineZ n β).toReal⁻¹ * constrainedZ n β V := by
    unfold effS
    rw [neg_sub, Real.exp_sub, Real.exp_log hp, Real.exp_log hZp, div_eq_inv_mul]
  rw [e, ENNReal.ofReal_mul (inv_nonneg.2 hZp.le), ENNReal.ofReal_inv_of_pos hZp, ENNReal.ofReal_toReal hZ1]

/-- The effective action at every coarse field, with the crude upper bound: `(β/4) S_c + log Z ≤ effS ≤ 4 β P + log Z`.
`effS_le_interp` is the upper bound with a classical term. -/
theorem effS_bounds (β : ℝ) (hβ : 0 ≤ β) (V : Configuration (Vertex n) Q) :
    β / 4 * actionL (linkValue n Q V) + Real.log (fineZ n β).toReal ≤ effS n β V ∧
      effS n β V ≤ β * (4 * (fineP n : ℝ)) + Real.log (fineZ n β).toReal := by
  have hp := constrainedZ_pos n β hβ V
  have h1 := Real.log_le_log hp (constrainedZ_upper n β hβ V)
  have h2 := Real.log_le_log (Real.exp_pos _) (constrainedZ_lower n β hβ V)
  rw [Real.log_exp] at h1 h2
  unfold effS
  constructor <;> linarith only [h1, h2]

theorem effS_gauge (β : ℝ) (g : Vertex n → Q) (V : Configuration (Vertex n) Q) :
    effS n β (gauge (Vertex n) Q g V) = effS n β V := by
  unfold effS
  rw [constrainedZ_gauge]

/-! #### Regularity in the coarse field -/

theorem actionL_diff (L L' : V' → Fin 4 → Q) :
    actionL L ≤ actionL L' + 24 * ∑ μ, ∑ x, d (L x μ) (L' x μ) := by
  have hp (p : PlaquetteIndex (2 * n)) :
      defect L p.2.1.1 p.2.1.2 p.1 ^ 2 ≤ defect L' p.2.1.1 p.2.1.2 p.1 ^ 2 +
        4 * (d (L p.1 p.2.1.1) (L' p.1 p.2.1.1) +
          d (L (step (2 * n) p.1 p.2.1.1) p.2.1.2) (L' (step (2 * n) p.1 p.2.1.1) p.2.1.2) +
          d (L (step (2 * n) p.1 p.2.1.2) p.2.1.1) (L' (step (2 * n) p.1 p.2.1.2) p.2.1.1) +
          d (L p.1 p.2.1.2) (L' p.1 p.2.1.2)) := by
    rcases p with ⟨x, ⟨⟨μ, ν⟩, h⟩⟩
    simp only
    set S := d (L x μ) (L' x μ) + d (L (step (2 * n) x μ) ν) (L' (step (2 * n) x μ) ν) +
      d (L (step (2 * n) x ν) μ) (L' (step (2 * n) x ν) μ) + d (L x ν) (L' x ν) with hS
    have hf := TwistedSeams.four (L x μ) (L (step (2 * n) x μ) ν) (L (step (2 * n) x ν) μ) (L x ν)
      (L' x μ) (L' (step (2 * n) x μ) ν) (L' (step (2 * n) x ν) μ) (L' x ν)
    have ht := d_triangle (L x μ * L (step (2 * n) x μ) ν * (L (step (2 * n) x ν) μ)⁻¹ * (L x ν)⁻¹)
      (L' x μ * L' (step (2 * n) x μ) ν * (L' (step (2 * n) x ν) μ)⁻¹ * (L' x ν)⁻¹) (ω ^ twistExp μ ν x)
    have h1 : defect L μ ν x ≤ defect L' μ ν x + S := by
      change d _ _ ≤ d _ _ + S
      linarith only [hf, ht]
    have hb1 : defect L μ ν x ≤ 2 := d_le_two _ _
    have hb2 : defect L' μ ν x ≤ 2 := d_le_two _ _
    have hn1 := defect_nonneg L μ ν x
    have hn2 := defect_nonneg L' μ ν x
    have hSn : 0 ≤ S := by
      rw [hS]
      exact add_nonneg (add_nonneg (add_nonneg (d_nonneg _ _) (d_nonneg _ _)) (d_nonneg _ _)) (d_nonneg _ _)
    by_cases hle : defect L μ ν x ≤ defect L' μ ν x
    · nlinarith only [hle, hn1, hn2, hSn]
    · have hlt := not_le.1 hle
      nlinarith only [h1, hlt, hb1, hb2, hn1, hn2, hSn]
  unfold actionL
  refine (Finset.sum_le_sum fun p _ => hp p).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, six_count n (fun x μ => d (L x μ) (L' x μ))]
  ring

theorem sum_glue_dist (V W : Configuration (Vertex n) Q) (U : Configuration V' Q) :
    ∑ μ, ∑ x, d (linkValue (2 * n) Q (glue n V U) x μ) (linkValue (2 * n) Q (glue n W U) x μ) =
      ∑ c, d (V c) (W c) := by
  classical
  have h1 : ∑ μ, ∑ x, d (linkValue (2 * n) Q (glue n V U) x μ) (linkValue (2 * n) Q (glue n W U) x μ) =
      ∑ e, d (glue n V U e) (glue n W U e) := by
    rw [← Equiv.sum_comp (edgeCoordinates (2 * n)).symm, Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  rw [h1]
  have hrest (e : Edge V') (he : e ∉ Finset.univ.image (firstEdge n)) :
      d (glue n V U e) (glue n W U e) = 0 := by
    have hne : ¬∃ c, firstEdge n c = e := by
      rintro ⟨c, rfl⟩
      exact he (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    change d (phi n _ e * U e) (phi n _ e * U e) = 0
    rw [phi_other n _ e hne, phi_other n _ e hne]
    simp [d]
  rw [← Finset.sum_subset (Finset.subset_univ _) fun e _ he => hrest e he,
    Finset.sum_image fun _ _ _ _ he => firstEdge_injective n he]
  refine Finset.sum_congr rfl fun c _ => ?_
  change d (phi n _ (firstEdge n c) * U _) (phi n _ (firstEdge n c) * U _) = _
  rw [phi_first, phi_first, d_mul_right]
  change d (V c * _) (W c * _) = _
  rw [d_mul_right]

/-- **The effective action is Lipschitz, link by link, with a constant free of the volume.** Changing the coarse field
changes `effS` by at most `24 β` times the sum of the link distances, at every coarse field. So its dependence on one
link is bounded locally, even though the number of terms in `effS` is not. This is regularity, not the decay of an
influence with distance, and the constant grows with `β`. -/
theorem effS_lipschitz (β : ℝ) (hβ : 0 ≤ β) (V W : Configuration (Vertex n) Q) :
    effS n β V - effS n β W ≤ 24 * β * ∑ c, d (V c) (W c) := by
  set D := ∑ c, d (V c) (W c) with hD
  have hpt (U : Configuration V' Q) :
      Real.exp (-fineS n β (glue n W U)) ≤
        Real.exp (24 * β * D) * Real.exp (-fineS n β (glue n V U)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [fineS_eq, fineS_eq]
    have h := actionL_diff n (linkValue (2 * n) Q (glue n V U)) (linkValue (2 * n) Q (glue n W U))
    rw [sum_glue_dist] at h
    have := mul_le_mul_of_nonneg_left h hβ
    linarith only [this]
  have hint : constrainedZ n β W ≤ Real.exp (24 * β * D) * constrainedZ n β V := by
    unfold constrainedZ
    rw [← integral_const_mul]
    exact integral_mono (integrable_weight n β W) ((integrable_weight n β V).const_mul _) hpt
  have hVp := constrainedZ_pos n β hβ V
  have hWp := constrainedZ_pos n β hβ W
  have hl := Real.log_le_log hWp hint
  rw [Real.log_mul (Real.exp_pos _).ne' hVp.ne', Real.log_exp] at hl
  unfold effS
  linarith only [hl]

end Constrained

/-! #### The split at each coarse field -/

section ConstrainedSplit

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- The part of the constrained integral from fine fields with exactly the bad blocks `Λ`. -/
def constrainedPiece (β δ : ℝ) (Λ : Finset (Vertex n)) (V : Configuration (Vertex n) Q) : ℝ :=
  ∫ U in {U | badBlocks n δ (glue n V U) = Λ}, Real.exp (-fineS n β (glue n V U)) ∂referenceMeasure Q V'

theorem measurableSet_piece (δ : ℝ) (Λ : Finset (Vertex n)) (V : Configuration (Vertex n) Q) :
    MeasurableSet {U : Configuration V' Q | badBlocks n δ (glue n V U) = Λ} :=
  (continuous_glue_right n V).measurable (measurableSet_badBlocks n δ Λ)

/-- At every coarse field, the constrained integral is the sum of its pieces. As for `sum_blockedPiece`, this holds for
any measurable partition. -/
theorem sum_constrainedPiece (β δ : ℝ) (V : Configuration (Vertex n) Q) :
    ∑ Λ, constrainedPiece n β δ Λ V = constrainedZ n β V := by
  classical
  unfold constrainedPiece constrainedZ
  rw [← integral_biUnion_finset Finset.univ (fun Λ _ => measurableSet_piece n δ Λ V) ?_
    (fun Λ _ => (integrable_weight n β V).integrableOn)]
  · have hu : ⋃ Λ ∈ (Finset.univ : Finset (Finset (Vertex n))),
        {U | badBlocks n δ (glue n V U) = Λ} = Set.univ := by
      ext U
      simp
    rw [hu, Measure.restrict_univ]
  · intro Λ _ Λ' _ hne
    refine Set.disjoint_left.2 fun U hU hU' => hne ?_
    exact hU.symm.trans hU'

/-- **A piece vanishes unless every large coarse plaquette is based in a bad block.** If a plaquette of `V` based outside
`Λ` has defect above `4 δ`, the piece `Λ` is zero. -/
theorem constrainedPiece_support (β δ : ℝ) (Λ : Finset (Vertex n)) (V : Configuration (Vertex n) Q)
    (hV : V ∉ SmallAt n δ Λ) : constrainedPiece n β δ Λ V = 0 := by
  have hempty : {U : Configuration V' Q | badBlocks n δ (glue n V U) = Λ} = ∅ := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hΛ
    apply hV
    intro x μ ν hμν hx
    rw [← hΛ] at hx
    have h := coarse_defect_block n δ (glue n V U) x hx μ ν hμν
    rw [← link_blockCfg, block_glue] at h
    exact h
  unfold constrainedPiece
  rw [hempty, Measure.restrict_empty, integral_zero_measure]

/-- **Each bad block costs `exp(-β δ²)`, at every coarse field.** -/
theorem constrainedPiece_le (β δ : ℝ) (hβ : 0 ≤ β) (hδ0 : 0 ≤ δ) (Λ : Finset (Vertex n))
    (V : Configuration (Vertex n) Q) :
    constrainedPiece n β δ Λ V ≤ Real.exp (-(β * ((Λ.card : ℝ) * δ ^ 2))) := by
  have hm := measurableSet_piece n δ Λ V
  have hbound : ∫ U in {U | badBlocks n δ (glue n V U) = Λ}, Real.exp (-fineS n β (glue n V U))
        ∂referenceMeasure Q V' ≤
      ∫ _ in {U | badBlocks n δ (glue n V U) = Λ}, Real.exp (-(β * ((Λ.card : ℝ) * δ ^ 2)))
        ∂referenceMeasure Q V' := by
    refine setIntegral_mono_on (integrable_weight n β V).integrableOn (integrable_const _) hm fun U hU => ?_
    apply Real.exp_le_exp.2
    rw [fineS_eq]
    have hΛ : badBlocks n δ (glue n V U) = Λ := hU
    have h2 := card_badBlocks_le n δ hδ0 (glue n V U)
    rw [hΛ] at h2
    nlinarith only [mul_le_mul_of_nonneg_left h2 hβ]
  refine le_trans hbound ?_
  rw [setIntegral_const, smul_eq_mul]
  have hmass : (referenceMeasure Q V').real {U | badBlocks n δ (glue n V U) = Λ} ≤ 1 := measureReal_le_one
  have hexp := Real.exp_pos (-(β * ((Λ.card : ℝ) * δ ^ 2)))
  nlinarith only [hmass, hexp]

theorem constrainedPiece_nonneg (β δ : ℝ) (Λ : Finset (Vertex n)) (V : Configuration (Vertex n) Q) :
    0 ≤ constrainedPiece n β δ Λ V :=
  setIntegral_nonneg (measurableSet_piece n δ Λ V) fun _ _ => (Real.exp_pos _).le

/-! #### The lower bound at each coarse field, from the interpolation -/

/-- The interpolation of a coarse configuration. -/
def interpCfg (V : Configuration (Vertex n) Q) : Configuration V' Q :=
  fun e => interp n (linkValue n Q V) e.1 e.2.2.val

theorem link_interpCfg (V : Configuration (Vertex n) Q) :
    linkValue (2 * n) Q (interpCfg n V) = interp n (linkValue n Q V) := rfl

theorem blockCfg_interpCfg (V : Configuration (Vertex n) Q) : blockCfg n zeroW (interpCfg n V) = V := by
  refine config_ext n _ _ fun x μ => ?_
  rw [link_blockCfg, link_interpCfg, blockField_interp]

/-- The second fine edge of a coarse link. -/
def secondEdge (e : Edge (Vertex n)) : Edge V' :=
  (edgeCoordinates (2 * n)).symm (step (2 * n) (emb n e.1) e.2.2.val, e.2.2.val)

theorem secondEdge_injective : Function.Injective (secondEdge n) := by
  intro e e' h
  have h1 := (edgeCoordinates (2 * n)).symm.injective h
  have h3 : e.2.2.val = e'.2.2.val := congrArg Prod.snd h1
  have h2 : step (2 * n) (emb n e.1) e.2.2.val = step (2 * n) (emb n e'.1) e'.2.2.val := congrArg Prod.fst h1
  rw [h3] at h2
  have h4 := emb_injective n ((TwistedHessian.stepEquiv (N := 2 * n) e'.2.2.val).injective h2)
  apply (edgeCoordinates n).injective
  exact Prod.ext h4 h3

theorem blockCfg_zero_apply (U : Configuration V' Q) (c : Edge (Vertex n)) :
    blockCfg n zeroW U c = U (firstEdge n c) * U (secondEdge n c) := by
  change blockW zeroW (linkValue (2 * n) Q U) (emb n c.1) c.2.2.val = _
  rw [blockW_zero]
  rfl

theorem glue_first (V : Configuration (Vertex n) Q) (U : Configuration V' Q) (c : Edge (Vertex n)) :
    glue n V U (firstEdge n c) = V c * (U (secondEdge n c))⁻¹ := by
  change phi n _ (firstEdge n c) * U (firstEdge n c) = _
  rw [phi_first]
  change V c * (blockCfg n zeroW U c)⁻¹ * _ = _
  rw [blockCfg_zero_apply]
  group

theorem glue_other (V : Configuration (Vertex n) Q) (U : Configuration V' Q) (e : Edge V')
    (he : ¬∃ c, firstEdge n c = e) : glue n V U e = U e := by
  change phi n _ e * U e = _
  rw [phi_other n _ e he, one_mul]

theorem interpCfg_first (V : Configuration (Vertex n) Q) (c : Edge (Vertex n)) :
    interpCfg n V (firstEdge n c) = V c := by
  rcases c with ⟨x, y, μ, hμ⟩
  cases hμ
  change interp n (linkValue n Q V) (emb n x) μ = linkValue n Q V x μ
  rw [interp_even n _ _ _ (even_emb1 n (x μ)), corner_emb]

theorem interpCfg_second (V : Configuration (Vertex n) Q) (c : Edge (Vertex n)) :
    interpCfg n V (secondEdge n c) = 1 := by
  rcases c with ⟨x, y, μ, hμ⟩
  cases hμ
  change interp n (linkValue n Q V) (step (2 * n) (emb n x) μ) μ = 1
  refine interp_odd n _ _ _ ?_
  rw [step_apply]
  simpa using odd_emb1 n (x μ)

theorem d_glue_first (V : Configuration (Vertex n) Q) (U : Configuration V' Q) (c : Edge (Vertex n)) :
    d (glue n V U (firstEdge n c)) (interpCfg n V (firstEdge n c)) =
      d (U (secondEdge n c)) (interpCfg n V (secondEdge n c)) := by
  rw [glue_first, interpCfg_first, interpCfg_second]
  have h1 := d_mul_left (V c) (U (secondEdge n c))⁻¹ 1
  rw [mul_one] at h1
  rw [h1]
  have h2 := d_inv (U (secondEdge n c)) 1
  rwa [inv_one] at h2

/-- The translated field is as close to the interpolation as the free field is, up to a factor `2` in the sum. -/
theorem sum_glue_sq_le (V : Configuration (Vertex n) Q) (U : Configuration V' Q) :
    ∑ e, d (glue n V U e) (interpCfg n V e) ^ 2 ≤ 2 * ∑ e, d (U e) (interpCfg n V e) ^ 2 := by
  classical
  set f : Edge V' → ℝ := fun e => d (U e) (interpCfg n V e) ^ 2 with hf
  have hf0 : ∀ e, 0 ≤ f e := fun e => sq_nonneg _
  set S := Finset.univ.image (firstEdge n) with hS
  rw [← Finset.sum_add_sum_compl S]
  have h1 : ∑ e ∈ S, d (glue n V U e) (interpCfg n V e) ^ 2 ≤ ∑ e, f e := by
    rw [hS, Finset.sum_image fun _ _ _ _ he => firstEdge_injective n he]
    simp only [d_glue_first]
    have e1 : ∑ c, d (U (secondEdge n c)) (interpCfg n V (secondEdge n c)) ^ 2 =
        ∑ e ∈ Finset.univ.image (secondEdge n), f e := by
      rw [Finset.sum_image fun _ _ _ _ he => secondEdge_injective n he]
    rw [e1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun e _ _ => hf0 e
  have h2 : ∑ e ∈ Sᶜ, d (glue n V U e) (interpCfg n V e) ^ 2 ≤ ∑ e, f e := by
    have e2 : ∑ e ∈ Sᶜ, d (glue n V U e) (interpCfg n V e) ^ 2 = ∑ e ∈ Sᶜ, f e := by
      refine Finset.sum_congr rfl fun e he => ?_
      have hne : ¬∃ c, firstEdge n c = e := by
        rintro ⟨c, rfl⟩
        exact (Finset.mem_compl.1 he) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      rw [glue_other n V U e hne]
    rw [e2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun e _ _ => hf0 e
  linarith only [h1, h2]

/-- The action of a field near another: a factor `2` on the action, and a quadratic term in the distances. -/
theorem actionL_quad (L L' : V' → Fin 4 → Q) :
    actionL L ≤ 2 * actionL L' + 48 * ∑ μ, ∑ x, d (L x μ) (L' x μ) ^ 2 := by
  have hp (p : PlaquetteIndex (2 * n)) :
      defect L p.2.1.1 p.2.1.2 p.1 ^ 2 ≤ 2 * defect L' p.2.1.1 p.2.1.2 p.1 ^ 2 +
        8 * (d (L p.1 p.2.1.1) (L' p.1 p.2.1.1) ^ 2 +
          d (L (step (2 * n) p.1 p.2.1.1) p.2.1.2) (L' (step (2 * n) p.1 p.2.1.1) p.2.1.2) ^ 2 +
          d (L (step (2 * n) p.1 p.2.1.2) p.2.1.1) (L' (step (2 * n) p.1 p.2.1.2) p.2.1.1) ^ 2 +
          d (L p.1 p.2.1.2) (L' p.1 p.2.1.2) ^ 2) := by
    rcases p with ⟨x, ⟨⟨μ, ν⟩, h⟩⟩
    simp only
    have hf := TwistedSeams.four (L x μ) (L (step (2 * n) x μ) ν) (L (step (2 * n) x ν) μ) (L x ν)
      (L' x μ) (L' (step (2 * n) x μ) ν) (L' (step (2 * n) x ν) μ) (L' x ν)
    have ht := d_triangle (L x μ * L (step (2 * n) x μ) ν * (L (step (2 * n) x ν) μ)⁻¹ * (L x ν)⁻¹)
      (L' x μ * L' (step (2 * n) x μ) ν * (L' (step (2 * n) x ν) μ)⁻¹ * (L' x ν)⁻¹) (ω ^ twistExp μ ν x)
    set a := d (L x μ) (L' x μ)
    set b := d (L (step (2 * n) x μ) ν) (L' (step (2 * n) x μ) ν)
    set c := d (L (step (2 * n) x ν) μ) (L' (step (2 * n) x ν) μ)
    set e := d (L x ν) (L' x ν)
    have h1 : defect L μ ν x ≤ defect L' μ ν x + (a + b + c + e) := by
      change d _ _ ≤ d _ _ + _
      linarith only [hf, ht]
    have hn1 := defect_nonneg L μ ν x
    have hsq := pow_le_pow_left₀ hn1 h1 2
    nlinarith only [hsq, sq_nonneg (defect L' μ ν x - (a + b + c + e)), sq_nonneg (a - b), sq_nonneg (a - c),
      sq_nonneg (a - e), sq_nonneg (b - c), sq_nonneg (b - e), sq_nonneg (c - e)]
  unfold actionL
  refine (Finset.sum_le_sum fun p _ => hp p).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    six_count n (fun x μ => d (L x μ) (L' x μ) ^ 2)]
  ring

/-- **The fine action of the translated field, by the coarse action and the distance of the free field to the
interpolation.** -/
theorem action_glue_le (V : Configuration (Vertex n) Q) (U : Configuration V' Q) :
    actionL (linkValue (2 * n) Q (glue n V U)) ≤
      8 * actionL (linkValue n Q V) + 96 * ∑ e, d (U e) (interpCfg n V e) ^ 2 := by
  have h1 := actionL_quad n (linkValue (2 * n) Q (glue n V U)) (linkValue (2 * n) Q (interpCfg n V))
  have h2 : ∑ μ, ∑ x, d (linkValue (2 * n) Q (glue n V U) x μ) (linkValue (2 * n) Q (interpCfg n V) x μ) ^ 2 =
      ∑ e, d (glue n V U e) (interpCfg n V e) ^ 2 := by
    rw [← Equiv.sum_comp (edgeCoordinates (2 * n)).symm, Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  rw [h2] at h1
  have h3 := sum_glue_sq_le n V U
  have h4 := actionL_interp_le n (linkValue n Q V)
  rw [link_interpCfg] at h1
  linarith only [h1, h3, h4]

/-- **A lower bound on the constrained integral at every coarse field.** The classical term has a constant free of the
volume; the entropy term `mass(96 β)^links` is extensive. Together with `constrainedZ_upper` this pins `log constrainedZ`
between `-(β/4) S_c` and `-8 β S_c - links · log cap(96 β)`. -/
theorem constrainedZ_lower_interp (β : ℝ) (hβ : 0 ≤ β) (V : Configuration (Vertex n) Q) :
    Real.exp (-(β * (8 * actionL (linkValue n Q V)))) * SU2GaussianMass.mass (96 * β) ^ linkCount n ≤
      constrainedZ n β V := by
  have hprod : (∫ U : Configuration V' Q, ∏ e, Real.exp (-(96 * β) * d (U e) (interpCfg n V e) ^ 2)
        ∂referenceMeasure Q V') = SU2GaussianMass.mass (96 * β) ^ linkCount n := by
    unfold referenceMeasure
    have h := integral_fintype_prod_eq_prod (ι := Edge V') (E := fun _ => Q)
      (fun e q => Real.exp (-(96 * β) * d q (interpCfg n V e) ^ 2)) (μ := fun _ => compactHaar Q)
    refine h.trans ?_
    simp only [gaussian_translate, Finset.prod_const, Finset.card_univ, linkCount]
  have hcontP : Continuous fun U : Configuration V' Q =>
      ∏ e, Real.exp (-(96 * β) * d (U e) (interpCfg n V e) ^ 2) := by
    refine continuous_finset_prod _ fun e _ => ?_
    unfold d
    fun_prop
  have hint : Integrable (fun U : Configuration V' Q => ∏ e, Real.exp (-(96 * β) * d (U e) (interpCfg n V e) ^ 2))
      (referenceMeasure Q V') := hcontP.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← hprod, ← integral_const_mul]
  unfold constrainedZ
  refine integral_mono (hint.const_mul _) (integrable_weight n β V) fun U => ?_
  change _ * _ ≤ _
  rw [← Real.exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.2
  rw [fineS_eq, ← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (action_glue_le n V U) hβ
  nlinarith only [h]

theorem cap_pos' (s : ℝ) (hs : 3 / 4 ≤ s) : 0 < SU2GaussianMass.cap s := by
  have h1 := SU2GaussianMass.mass_cap_lower s hs
  have h2 := SU2GaussianMass.cap_nonneg s (by linarith only [hs])
  rcases h2.lt_or_eq with h | h
  · exact h
  · rw [← h, mul_zero] at h1
    norm_num at h1

/-- The form in which the lower bound is used. -/
theorem one_le_constrainedZ (β : ℝ) (hβ : 1 / 128 ≤ β) (V : Configuration (Vertex n) Q) :
    1 ≤ Real.exp (β * (8 * actionL (linkValue n Q V))) * SU2GaussianMass.cap (96 * β) ^ linkCount n *
      constrainedZ n β V := by
  have hβ0 : 0 ≤ β := by linarith only [hβ]
  have h1 := constrainedZ_lower_interp n β hβ0 V
  have hc := SU2GaussianMass.mass_cap_lower (96 * β) (by linarith only [hβ])
  have hc0 := cap_pos' (96 * β) (by linarith only [hβ])
  set M := SU2GaussianMass.mass (96 * β)
  set C := SU2GaussianMass.cap (96 * β)
  have hE : Real.exp (β * (8 * actionL (linkValue n Q V))) * Real.exp (-(β * (8 * actionL (linkValue n Q V)))) = 1 := by
    rw [← Real.exp_add]
    simp
  have hpow : 1 ≤ C ^ linkCount n * M ^ linkCount n := by
    rw [← mul_pow, mul_comm C M]
    exact one_le_pow₀ hc
  have hmul : 0 ≤ Real.exp (β * (8 * actionL (linkValue n Q V))) * C ^ linkCount n := by positivity
  have h2 := mul_le_mul_of_nonneg_left h1 hmul
  calc
    1 ≤ C ^ linkCount n * M ^ linkCount n := hpow
    _ = Real.exp (β * (8 * actionL (linkValue n Q V))) * C ^ linkCount n *
        (Real.exp (-(β * (8 * actionL (linkValue n Q V)))) * M ^ linkCount n) := by
      rw [show Real.exp (β * (8 * actionL (linkValue n Q V))) * C ^ linkCount n *
          (Real.exp (-(β * (8 * actionL (linkValue n Q V)))) * M ^ linkCount n) =
          (Real.exp (β * (8 * actionL (linkValue n Q V))) * Real.exp (-(β * (8 * actionL (linkValue n Q V))))) *
            (C ^ linkCount n * M ^ linkCount n) by ring, hE, one_mul]
    _ ≤ _ := h2

/-- **The effective action, at every coarse field, with a classical upper bound.** This replaces the crude `4 β P` of
`effS_bounds`, which is extensive in `β`, by a term extensive only in `log β`. The two sides differ by a factor `32` in
the classical term and by the entropy term, which is not separated into a determinant and a remainder. -/
theorem effS_le_interp (β : ℝ) (hβ : 1 / 128 ≤ β) (V : Configuration (Vertex n) Q) :
    effS n β V ≤ Real.log (fineZ n β).toReal + β * (8 * actionL (linkValue n Q V)) +
      (linkCount n : ℝ) * Real.log (SU2GaussianMass.cap (96 * β)) := by
  have hβ0 : 0 ≤ β := by linarith only [hβ]
  have hc0 := cap_pos' (96 * β) (by linarith only [hβ])
  have hp := constrainedZ_pos n β hβ0 V
  have h := one_le_constrainedZ n β hβ V
  have hl := Real.log_le_log one_pos h
  rw [Real.log_one, Real.log_mul (by positivity) hp.ne', Real.log_mul (Real.exp_pos _).ne' (by positivity),
    Real.log_exp, Real.log_pow] at hl
  unfold effS
  linarith only [hl]

/-- **The effective action against any other coarse field.** The density of the blocked law at `V` is at most
`exp(-(β/4) S_c(V) + 8 β S_c(W)) cap(96 β)^links` times its density at `W`. So the classical term wins against the entropy term
only when `S_c(V)` per link is above `4 log cap(96 β)/β`. At a flat `W` the term `8 β S_c(W)` is absent. -/
theorem effS_sub_ge (β : ℝ) (hβ : 1 / 128 ≤ β) (V W : Configuration (Vertex n) Q) :
    β / 4 * actionL (linkValue n Q V) - β * (8 * actionL (linkValue n Q W)) -
        (linkCount n : ℝ) * Real.log (SU2GaussianMass.cap (96 * β)) ≤ effS n β V - effS n β W := by
  have h1 := (effS_bounds n β (by linarith only [hβ]) V).1
  have h2 := effS_le_interp n β hβ W
  linarith only [h1, h2]

/-! #### The fine field at a given coarse field -/

/-- **The fine action is controlled by the coarse action, at every coarse field.** Conditioned on the blocked field
`V`, the probability that the fine action is at least `s` is at most `exp(β (8 S_c(V) - s)) cap(96 β)^links`. So the fine
action per link is at most `8 S_c(V)/links + log cap(96 β)/β`, up to an event exponentially small in the volume. This is
a converse of `actionL_blockField_le`, which holds field by field; this one holds only in probability, and it is worst case. A
Haar field has action about `3` per link, so the bound says something from about `β > 3.6`, and it is about ten times the free
value of the fine action at `β = 8`, by a hand count. -/
theorem constrained_action_tail (β s : ℝ) (hβ : 1 / 128 ≤ β) (V : Configuration (Vertex n) Q) :
    ∫ U in {U | s ≤ actionL (linkValue (2 * n) Q (glue n V U))}, Real.exp (-fineS n β (glue n V U))
        ∂referenceMeasure Q V' ≤
      Real.exp (β * (8 * actionL (linkValue n Q V) - s)) * SU2GaussianMass.cap (96 * β) ^ linkCount n *
        constrainedZ n β V := by
  have hβ0 : 0 ≤ β := by linarith only [hβ]
  have hm : MeasurableSet {U : Configuration V' Q | s ≤ actionL (linkValue (2 * n) Q (glue n V U))} :=
    (isClosed_le continuous_const ((continuous_actionL (2 * n)).comp (continuous_glue_right n V))).measurableSet
  have h1 : ∫ U in {U | s ≤ actionL (linkValue (2 * n) Q (glue n V U))}, Real.exp (-fineS n β (glue n V U))
        ∂referenceMeasure Q V' ≤ Real.exp (-(β * s)) := by
    have hb : ∫ U in {U | s ≤ actionL (linkValue (2 * n) Q (glue n V U))}, Real.exp (-fineS n β (glue n V U))
          ∂referenceMeasure Q V' ≤
        ∫ _ in {U | s ≤ actionL (linkValue (2 * n) Q (glue n V U))}, Real.exp (-(β * s)) ∂referenceMeasure Q V' := by
      refine setIntegral_mono_on (integrable_weight n β V).integrableOn (integrable_const _) hm fun U hU => ?_
      apply Real.exp_le_exp.2
      rw [fineS_eq]
      have hs : s ≤ actionL (linkValue (2 * n) Q (glue n V U)) := hU
      nlinarith only [mul_le_mul_of_nonneg_left hs hβ0]
    refine hb.trans ?_
    rw [setIntegral_const, smul_eq_mul]
    have hmass : (referenceMeasure Q V').real {U | s ≤ actionL (linkValue (2 * n) Q (glue n V U))} ≤ 1 :=
      measureReal_le_one
    have hexp := Real.exp_pos (-(β * s))
    nlinarith only [hmass, hexp]
  refine h1.trans ?_
  have h2 := one_le_constrainedZ n β hβ V
  have hexp := Real.exp_pos (-(β * s))
  have e : Real.exp (β * (8 * actionL (linkValue n Q V) - s)) * SU2GaussianMass.cap (96 * β) ^ linkCount n *
      constrainedZ n β V = Real.exp (-(β * s)) * (Real.exp (β * (8 * actionL (linkValue n Q V))) *
        SU2GaussianMass.cap (96 * β) ^ linkCount n * constrainedZ n β V) := by
    rw [show β * (8 * actionL (linkValue n Q V) - s) = -(β * s) + β * (8 * actionL (linkValue n Q V)) by ring,
      Real.exp_add]
    ring
  rw [e]
  exact le_mul_of_one_le_right hexp.le h2

/-- **Bad blocks at a given coarse field.** Conditioned on the blocked field `V`, the probability of at least `r` bad
blocks is at most `exp(β (8 S_c(V) - r δ²)) cap(96 β)^links`. The bound is below `1` only for `r δ²` above
`8 S_c(V) + links · log cap(96 β)/β`. Since `r ≤ n⁴`, a nonempty event needs `δ < 2`, and `links = 64 n⁴`, it says nothing
unless `β > 16 log cap(96 β)`, about `β > 276`. At `δ = 1` this is about `β > 1250`, at `δ = 1/2` about `β > 5570`, and these
are for all blocks bad; a small bad fraction costs its inverse. The thresholds are free of the volume. -/
theorem constrained_bad_blocks (β δ : ℝ) (r : ℕ) (hβ : 1 / 128 ≤ β) (hδ0 : 0 ≤ δ)
    (V : Configuration (Vertex n) Q) :
    ∫ U in {U | r ≤ (badBlocks n δ (glue n V U)).card}, Real.exp (-fineS n β (glue n V U))
        ∂referenceMeasure Q V' ≤
      Real.exp (β * (8 * actionL (linkValue n Q V) - (r : ℝ) * δ ^ 2)) *
        SU2GaussianMass.cap (96 * β) ^ linkCount n * constrainedZ n β V := by
  refine le_trans ?_ (constrained_action_tail n β ((r : ℝ) * δ ^ 2) hβ V)
  refine setIntegral_mono_set (integrable_weight n β V).integrableOn
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) (Filter.Eventually.of_forall fun U hU => ?_)
  have hr : (r : ℝ) ≤ ((badBlocks n δ (glue n V U)).card : ℝ) := by exact_mod_cast hU
  have h2 := card_badBlocks_le n δ hδ0 (glue n V U)
  have := mul_le_mul_of_nonneg_right hr (sq_nonneg δ)
  exact this.trans h2

end ConstrainedSplit

section ConstrainedLaw

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- **The fine action given the coarse action, under the law.** On the event that the blocked field has action at most
`c`, the fine action exceeds `s` with conditional probability at most `exp(β (8 c - s)) cap(96 β)^links`. No lower bound on
the probability of the conditioning event is needed. That is the only gain over `action_tail`, which already bounds the
joint probability by `exp(-β s) cap(24 β)^links`: this bound carries the factor `P(A)`, so it says more only when `A` is rare.
For `c` of order `links · log cap(96 β)/β`, it gives a fine action of the same order. -/
theorem twistedLaw_fine_given_coarse (β s c : ℝ) (hβ : 1 / 128 ≤ β) (A : Set (Configuration (Vertex n) Q))
    (hA : MeasurableSet A) (hc : ∀ V ∈ A, actionL (linkValue n Q V) ≤ c) :
    twistedLaw n β (blockCfg n zeroW ⁻¹' A ∩ {U | s ≤ actionL (linkValue (2 * n) Q U)}) ≤
      ENNReal.ofReal (Real.exp (β * (8 * c - s)) * SU2GaussianMass.cap (96 * β) ^ linkCount n) *
        blockedLaw n zeroW β A := by
  have hβ0 : 0 ≤ β := by linarith only [hβ]
  have hB := (continuous_blockCfg n zeroW adm_zero).measurable
  have hE : MeasurableSet {U : Configuration V' Q | s ≤ actionL (linkValue (2 * n) Q U)} :=
    (isClosed_le continuous_const (continuous_actionL (2 * n))).measurableSet
  set E := {U : Configuration V' Q | s ≤ actionL (linkValue (2 * n) Q U)} with hEdef
  set g := gibbsDensity V' Q (fineS n β) with hg
  have hgm : Measurable g := measurable_gibbsDensity n β
  set K := Real.exp (β * (8 * c - s)) * SU2GaussianMass.cap (96 * β) ^ linkCount n with hK
  have hc0 := cap_pos' (96 * β) (by linarith only [hβ])
  have hK0 : 0 ≤ K := by positivity
  rw [twistedLaw_apply n β _ ((hB hA).inter hE), blockedLaw_zero_apply n β A hA]
  have e1 : ∫⁻ U in blockCfg n zeroW ⁻¹' A ∩ E, g U ∂referenceMeasure Q V' =
      ∫⁻ U in blockCfg n zeroW ⁻¹' A, E.indicator g U ∂referenceMeasure Q V' := by
    rw [lintegral_indicator hE, Measure.restrict_restrict hE, Set.inter_comm]
  rw [e1, lintegral_block_zero n _ (hgm.indicator hE) A hA, mul_left_comm]
  gcongr
  rw [← lintegral_const_mul _ (continuous_constrainedZ n β).measurable.ennreal_ofReal]
  refine setLIntegral_mono' hA fun V hV => ?_
  have hS := hc V hV
  have hexp : Real.exp (-(β * s)) ≤ K * constrainedZ n β V := by
    have h2 := one_le_constrainedZ n β hβ V
    have hZ := constrainedZ_pos n β hβ0 V
    have hle : Real.exp (β * (8 * actionL (linkValue n Q V))) ≤ Real.exp (β * (8 * c)) := by
      apply Real.exp_le_exp.2
      nlinarith only [mul_le_mul_of_nonneg_left hS hβ0]
    have hCL : 0 ≤ SU2GaussianMass.cap (96 * β) ^ linkCount n := by positivity
    have h3 : 1 ≤ Real.exp (β * (8 * c)) * SU2GaussianMass.cap (96 * β) ^ linkCount n * constrainedZ n β V := by
      refine h2.trans ?_
      gcongr
    have e : K * constrainedZ n β V = Real.exp (-(β * s)) *
        (Real.exp (β * (8 * c)) * SU2GaussianMass.cap (96 * β) ^ linkCount n * constrainedZ n β V) := by
      rw [hK, show β * (8 * c - s) = -(β * s) + β * (8 * c) by ring, Real.exp_add]
      ring
    rw [e]
    exact le_mul_of_one_le_right (Real.exp_pos _).le h3
  calc
    ∫⁻ U, E.indicator g (glue n V U) ∂referenceMeasure Q V' ≤
        ∫⁻ _, ENNReal.ofReal (Real.exp (-(β * s))) ∂referenceMeasure Q V' := by
      refine lintegral_mono fun U => ?_
      by_cases hU : glue n V U ∈ E
      · rw [Set.indicator_of_mem hU]
        unfold g gibbsDensity
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        rw [fineS_eq]
        have hs : s ≤ actionL (linkValue (2 * n) Q (glue n V U)) := hU
        nlinarith only [mul_le_mul_of_nonneg_left hs hβ0]
      · rw [Set.indicator_of_notMem hU]
        exact zero_le _
    _ = ENNReal.ofReal (Real.exp (-(β * s))) := by
      rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (K * constrainedZ n β V) := ENNReal.ofReal_le_ofReal hexp
    _ = ENNReal.ofReal K * ENNReal.ofReal (constrainedZ n β V) := ENNReal.ofReal_mul hK0

/-- **Bad blocks given the coarse action, under the law.** -/
theorem twistedLaw_bad_given_coarse (β δ c : ℝ) (r : ℕ) (hβ : 1 / 128 ≤ β) (hδ0 : 0 ≤ δ)
    (A : Set (Configuration (Vertex n) Q)) (hA : MeasurableSet A) (hc : ∀ V ∈ A, actionL (linkValue n Q V) ≤ c) :
    twistedLaw n β (blockCfg n zeroW ⁻¹' A ∩ {U | r ≤ (badBlocks n δ U).card}) ≤
      ENNReal.ofReal (Real.exp (β * (8 * c - (r : ℝ) * δ ^ 2)) * SU2GaussianMass.cap (96 * β) ^ linkCount n) *
        blockedLaw n zeroW β A := by
  refine le_trans (measure_mono ?_) (twistedLaw_fine_given_coarse n β ((r : ℝ) * δ ^ 2) c hβ A hA hc)
  refine Set.inter_subset_inter_right _ fun U hU => ?_
  have hr : (r : ℝ) ≤ ((badBlocks n δ U).card : ℝ) := by exact_mod_cast hU
  have := mul_le_mul_of_nonneg_right hr (sq_nonneg δ)
  exact this.trans (card_badBlocks_le n δ hδ0 U)

/-! #### The small-field piece at a given coarse field -/

/-- The Haar mass of a ball around the identity. -/
def ballMass (ε : ℝ) : ℝ := (compactHaar Q).real {q : Q | d q 1 ≤ ε}

theorem ball_translate (b : Q) (ε : ℝ) : (compactHaar Q).real {q : Q | d q b ≤ ε} = ballMass ε := by
  haveI hfine : (compactHaar Q).IsHaarMeasure := by
    unfold compactHaar
    infer_instance
  unfold ballMass
  have e : {q : Q | d q 1 ≤ ε} = (fun h => b * h) ⁻¹' {q : Q | d q b ≤ ε} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    have := d_mul_left b q 1
    rw [mul_one] at this
    rw [this]
  rw [e]
  simp only [measureReal_def]
  rw [measure_preimage_mul]

theorem ballMass_pos (ε : ℝ) (hε : 0 < ε) : 0 < ballMass ε := by
  haveI hfine : (compactHaar Q).IsHaarMeasure := by
    unfold compactHaar
    infer_instance
  have hopen : IsOpen {q : Q | d q 1 < ε} := by
    refine isOpen_lt ?_ continuous_const
    unfold d
    fun_prop
  have hmem : (1 : Q) ∈ {q : Q | d q 1 < ε} := by
    simp [d, hε]
  have h0 := hopen.measure_pos (compactHaar Q) ⟨1, hmem⟩
  have hsub : {q : Q | d q 1 < ε} ⊆ {q : Q | d q 1 ≤ ε} := fun q (hq : d q 1 < ε) => (hq.le : d q 1 ≤ ε)
  have h1 := h0.trans_le (measure_mono hsub)
  unfold ballMass
  rw [measureReal_def]
  exact ENNReal.toReal_pos h1.ne' (measure_ne_top _ _)

/-- The ball mass, by the Gaussian mass. Together with `SU2GaussianMass.mass_cap_lower`, it gives
`ballMass ε ≥ 1/cap(s) - exp(-s ε²)` for `s ≥ 3/4`, which is positive for `s` of order `log(1/ε)/ε²`. -/
theorem mass_le_ball (s ε : ℝ) (hs : 0 ≤ s) (hε : 0 ≤ ε) :
    SU2GaussianMass.mass s ≤ ballMass ε + Real.exp (-s * ε ^ 2) := by
  haveI hfine : (compactHaar Q).IsHaarMeasure := by
    unfold compactHaar
    infer_instance
  have hm : MeasurableSet {q : Q | d q 1 ≤ ε} := by
    refine (isClosed_le ?_ continuous_const).measurableSet
    unfold d
    fun_prop
  have hint : Integrable (SU2GaussianMass.weight s) (compactHaar Q) :=
    (SU2GaussianMass.weight_continuous s).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hw : ∀ q : Q, SU2GaussianMass.weight s q = Real.exp (-s * d q 1 ^ 2) := fun q => rfl
  have h1 : ∫ q in {q : Q | d q 1 ≤ ε}, SU2GaussianMass.weight s q ∂compactHaar Q ≤ ballMass ε := by
    have hb : ∫ q in {q : Q | d q 1 ≤ ε}, SU2GaussianMass.weight s q ∂compactHaar Q ≤
        ∫ _ in {q : Q | d q 1 ≤ ε}, (1 : ℝ) ∂compactHaar Q := by
      refine setIntegral_mono_on hint.integrableOn (integrable_const _) hm fun q _ => ?_
      rw [hw]
      apply Real.exp_le_one_iff.2
      nlinarith only [mul_nonneg hs (sq_nonneg (d q 1))]
    refine hb.trans (le_of_eq ?_)
    rw [setIntegral_const, smul_eq_mul, mul_one]
    rfl
  have h2 : ∫ q in {q : Q | d q 1 ≤ ε}ᶜ, SU2GaussianMass.weight s q ∂compactHaar Q ≤ Real.exp (-s * ε ^ 2) := by
    have hb : ∫ q in {q : Q | d q 1 ≤ ε}ᶜ, SU2GaussianMass.weight s q ∂compactHaar Q ≤
        ∫ _ in {q : Q | d q 1 ≤ ε}ᶜ, Real.exp (-s * ε ^ 2) ∂compactHaar Q := by
      refine setIntegral_mono_on hint.integrableOn (integrable_const _) hm.compl fun q hq => ?_
      rw [hw]
      apply Real.exp_le_exp.2
      have hlt : ε < d q 1 := not_le.1 hq
      have : ε ^ 2 ≤ d q 1 ^ 2 := pow_le_pow_left₀ hε hlt.le 2
      nlinarith only [mul_le_mul_of_nonneg_left this hs]
    refine hb.trans ?_
    rw [setIntegral_const, smul_eq_mul]
    have hmass : (compactHaar Q).real {q : Q | d q 1 ≤ ε}ᶜ ≤ 1 := measureReal_le_one
    have hexp := Real.exp_pos (-s * ε ^ 2)
    nlinarith only [hmass, hexp]
  have hsplit := integral_add_compl hm hint
  unfold SU2GaussianMass.mass
  rw [← hsplit]
  exact add_le_add h1 h2

/-- The fine fields within `ε` of the interpolation, on every link. -/
def nearInterp (ε : ℝ) (V : Configuration (Vertex n) Q) : Set (Configuration V' Q) :=
  Set.pi Set.univ fun e => {q : Q | d q (interpCfg n V e) ≤ ε}

theorem measurableSet_nearInterp (ε : ℝ) (V : Configuration (Vertex n) Q) :
    MeasurableSet (nearInterp n ε V) := by
  refine MeasurableSet.univ_pi fun e => ?_
  refine (isClosed_le ?_ continuous_const).measurableSet
  unfold d
  fun_prop

theorem measure_nearInterp (ε : ℝ) (V : Configuration (Vertex n) Q) :
    (referenceMeasure Q V').real (nearInterp n ε V) = ballMass ε ^ linkCount n := by
  unfold nearInterp referenceMeasure
  rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  have e (i : Edge V') : (compactHaar Q {q : Q | d q (interpCfg n V i) ≤ ε}).toReal = ballMass ε := by
    have := ball_translate (interpCfg n V i) ε
    rwa [measureReal_def] at this
  simp only [e, Finset.prod_const, Finset.card_univ, linkCount]

theorem d_glue_interp_le (ε : ℝ) (V : Configuration (Vertex n) Q) (U : Configuration V' Q)
    (hU : U ∈ nearInterp n ε V) (e : Edge V') : d (glue n V U e) (interpCfg n V e) ≤ ε := by
  by_cases he : ∃ c, firstEdge n c = e
  · obtain ⟨c, rfl⟩ := he
    rw [d_glue_first]
    exact hU _ (Set.mem_univ _)
  · rw [glue_other n V U e he]
    exact hU _ (Set.mem_univ _)

/-- Near the interpolation, every fine defect is at most its value on the interpolation plus `4 ε`. -/
theorem defect_glue_le (ε : ℝ) (V : Configuration (Vertex n) Q) (U : Configuration V' Q)
    (hU : U ∈ nearInterp n ε V) (z : V') (μ ν : Fin 4) :
    defect (linkValue (2 * n) Q (glue n V U)) μ ν z ≤
      defect (interp n (linkValue n Q V)) μ ν z + 4 * ε := by
  set L := linkValue (2 * n) Q (glue n V U)
  set L' := interp n (linkValue n Q V)
  have hl (x : V') (ρ : Fin 4) : d (L x ρ) (L' x ρ) ≤ ε :=
    d_glue_interp_le n ε V U hU ⟨x, step (2 * n) x ρ, forward (2 * n) x ρ⟩
  have hf := TwistedSeams.four (L z μ) (L (step (2 * n) z μ) ν) (L (step (2 * n) z ν) μ) (L z ν)
    (L' z μ) (L' (step (2 * n) z μ) ν) (L' (step (2 * n) z ν) μ) (L' z ν)
  have ht := d_triangle (L z μ * L (step (2 * n) z μ) ν * (L (step (2 * n) z ν) μ)⁻¹ * (L z ν)⁻¹)
    (L' z μ * L' (step (2 * n) z μ) ν * (L' (step (2 * n) z ν) μ)⁻¹ * (L' z ν)⁻¹) (ω ^ twistExp μ ν z)
  change d _ _ ≤ d _ _ + _
  linarith only [hf, ht, hl z μ, hl (step (2 * n) z μ) ν, hl (step (2 * n) z ν) μ, hl z ν]

/-- **A lower bound on the small-field piece at a given coarse field.** If every coarse defect of `V` is at most `δ'`, and
`δ' + 4 ε ≤ δ`, the fine fields within `ε` of the interpolation have no bad block at `δ`, and they alone contribute this
much. The prefactor is extensive, so this does not say that the piece dominates; in a large volume at fixed `β` and `δ`
the fully good piece should not dominate at all, and `constrained_bad_blocks` is the statement that scales. -/
theorem constrainedPiece_empty_lower (β δ δ' ε : ℝ) (hβ : 0 ≤ β) (hδ' : 0 ≤ δ')
    (hδ : δ' + 4 * ε ≤ δ) (V : Configuration (Vertex n) Q)
    (hV : ∀ (x : Vertex n) (μ ν : Fin 4), μ < ν → defect (linkValue n Q V) μ ν x ≤ δ') :
    Real.exp (-(β * (8 * actionL (linkValue n Q V) + 32 * ε ^ 2 * (fineP n : ℝ)))) * ballMass ε ^ linkCount n ≤
      constrainedPiece n β δ ∅ V := by
  have hN := measurableSet_nearInterp n ε V
  have hsub : nearInterp n ε V ⊆ {U | badBlocks n δ (glue n V U) = ∅} := by
    intro U hU
    change badBlocks n δ (glue n V U) = ∅
    refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨p, -, hp⟩ := (mem_badBlocks n δ _ x).1 hx
    have h1 := defect_glue_le n ε V U hU p.1 p.2.1.1 p.2.1.2
    have h2 := defect_interp_le n _ δ' hδ' hV p.1 p.2.1.1 p.2.1.2 p.2.2
    linarith only [hp, h1, h2, hδ]
  have hS (U : Configuration V' Q) (hU : U ∈ nearInterp n ε V) :
      actionL (linkValue (2 * n) Q (glue n V U)) ≤
        8 * actionL (linkValue n Q V) + 32 * ε ^ 2 * (fineP n : ℝ) := by
    have h4 := actionL_interp_le n (linkValue n Q V)
    have hp : ∀ p : PlaquetteIndex (2 * n), defect (linkValue (2 * n) Q (glue n V U)) p.2.1.1 p.2.1.2 p.1 ^ 2 ≤
        2 * defect (interp n (linkValue n Q V)) p.2.1.1 p.2.1.2 p.1 ^ 2 + 32 * ε ^ 2 := by
      intro p
      have h1 := defect_glue_le n ε V U hU p.1 p.2.1.1 p.2.1.2
      have hn := defect_nonneg (linkValue (2 * n) Q (glue n V U)) p.2.1.1 p.2.1.2 p.1
      have hsq := pow_le_pow_left₀ hn h1 2
      nlinarith only [hsq, sq_nonneg (defect (interp n (linkValue n Q V)) p.2.1.1 p.2.1.2 p.1 - 4 * ε)]
    have hsum : actionL (linkValue (2 * n) Q (glue n V U)) ≤
        2 * actionL (interp n (linkValue n Q V)) + 32 * ε ^ 2 * (fineP n : ℝ) := by
      unfold actionL
      refine (Finset.sum_le_sum fun p _ => hp p).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold fineP
      ring
    linarith only [hsum, h4]
  unfold constrainedPiece
  calc
    _ = ∫ _ in nearInterp n ε V, Real.exp (-(β * (8 * actionL (linkValue n Q V) +
          32 * ε ^ 2 * (fineP n : ℝ)))) ∂referenceMeasure Q V' := by
      rw [setIntegral_const, measure_nearInterp, smul_eq_mul, mul_comm]
    _ ≤ ∫ U in nearInterp n ε V, Real.exp (-fineS n β (glue n V U)) ∂referenceMeasure Q V' := by
      refine setIntegral_mono_on (integrable_const _) (integrable_weight n β V).integrableOn hN fun U hU => ?_
      apply Real.exp_le_exp.2
      rw [fineS_eq]
      nlinarith only [mul_le_mul_of_nonneg_left (hS U hU) hβ]
    _ ≤ _ := setIntegral_mono_set (integrable_weight n β V).integrableOn
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) (Filter.Eventually.of_forall hsub)

/-- **The fully good piece is positive for small coarse fields.** It is positive when all coarse defects are below `δ`, and
it vanishes when some coarse defect exceeds `4 δ` (`constrainedPiece_support`). Between `δ` and `4 δ` nothing is proved. -/
theorem constrainedPiece_empty_pos (β δ δ' : ℝ) (hβ : 0 ≤ β) (hδ' : 0 ≤ δ') (hδ : δ' < δ)
    (V : Configuration (Vertex n) Q)
    (hV : ∀ (x : Vertex n) (μ ν : Fin 4), μ < ν → defect (linkValue n Q V) μ ν x ≤ δ') :
    0 < constrainedPiece n β δ ∅ V := by
  have hε : 0 < (δ - δ') / 4 := by linarith only [hδ]
  have h := constrainedPiece_empty_lower n β δ δ' ((δ - δ') / 4) hβ hδ' (by linarith only []) V hV
  refine lt_of_lt_of_le (mul_pos (Real.exp_pos _) (pow_pos (ballMass_pos _ hε) _)) h

end ConstrainedLaw

/-! ### The properties that survive every step

No estimate improves here. This records only what each step preserves exactly: a probability measure, gauge invariance and
reflection positivity. It claims no convergence. The fine-to-coarse tail is not iterated: each step loses the constant of
`actionL_blockField_le`, so at fixed `β` an iterated tail is empty after a few steps. -/

section Iterate

open PeriodicHalfSplit PeriodicSiteReflection

/-- Reflection-compatible weights with separate values: `s` for spatial staples of spatial links, `t` for staples of time
links, and no time staples on spatial links. -/
def twoW (s t : ℝ) : Wt := fun μ ν => if μ = 0 then t else if ν = 0 then 0 else s

theorem tot_two (s t : ℝ) (μ : Fin 4) : tot (twoW s t) μ = if μ = 0 then 6 * t else 4 * s := by
  unfold tot twoW
  fin_cases μ <;> simp [Fin.sum_univ_four] <;> ring

theorem adm_two (s t : ℝ) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (hs : 4 * s < 1) (ht : 6 * t < 1) : Adm (twoW s t) := by
  refine ⟨fun μ ν => ?_, fun μ => ?_⟩
  · unfold twoW
    split_ifs
    · exact ht0
    · exact le_rfl
    · exact hs0
  · rw [tot_two]
    split_ifs
    · exact ht
    · exact hs

theorem two_time (s t : ℝ) (i : Fin 4) (h : i ≠ 0) : twoW s t i 0 = 0 := by
  simp [twoW, h]

/-- `j` steps of the map with weights `a`, down to the lattice of side `2m`, from the twisted law on the lattice of side
`2^(j+1) m`. -/
def iterLaw (a : Wt) (β : ℝ) : ℕ → (m : ℕ) → [NeZero m] → Measure (Configuration (Vertex (2 * m)) Q)
  | 0, m, _ => twistedLaw m β
  | j + 1, m, _ => (iterLaw a β j (2 * m)).map (blockCfg (2 * m) a)

theorem iterLaw_probability (a : Wt) (ha : Adm a) (β : ℝ) :
    ∀ (j m : ℕ) [NeZero m], IsProbabilityMeasure (iterLaw a β j m)
  | 0, m, _ => twistedLaw_probability m β
  | j + 1, m, _ => by
    haveI := iterLaw_probability a ha β j (2 * m)
    exact Measure.isProbabilityMeasure_map (continuous_blockCfg (2 * m) a ha).measurable.aemeasurable

/-- **Every iterate of a reflection-compatible map is reflection positive.** This covers `aniso α` and `twoW s t`. -/
theorem iterLaw_rp (a : Wt) (ha : Adm a) (hz : ∀ i, i ≠ 0 → a i 0 = 0) (β : ℝ) :
    ∀ (j m : ℕ) [NeZero m], IsRP m (iterLaw a β j m)
  | 0, m, _ => isRP_twistedLaw m β
  | j + 1, m, _ => isRP_step_of m a ha hz _ (iterLaw_rp a ha hz β j (2 * m))

/-- A block step preserves invariance under all gauge transformations. -/
theorem gauge_map (n : ℕ) [NeZero n] (a : Wt) (ha : Adm a) (μ : Measure (Configuration (Vertex (2 * n)) Q))
    (hμ : ∀ g, MeasurePreserving (gauge (Vertex (2 * n)) Q g) μ μ) (g : Vertex n → Q) :
    MeasurePreserving (gauge (Vertex n) Q g) (μ.map (blockCfg n a)) (μ.map (blockCfg n a)) := by
  have hB := (continuous_blockCfg n a ha).measurable
  refine ⟨(continuous_gauge (Vertex n) Q g).measurable, ?_⟩
  have hG := (continuous_gauge (Vertex (2 * n)) Q (Function.extend (emb n) g 1)).measurable
  rw [Measure.map_map (continuous_gauge (Vertex n) Q g).measurable hB]
  have e : gauge (Vertex n) Q g ∘ blockCfg n a =
      blockCfg n a ∘ gauge (Vertex (2 * n)) Q (Function.extend (emb n) g 1) := by
    funext U
    exact (blockCfg_gauge n a ha g U).symm
  rw [e, ← Measure.map_map hB hG, (hμ _).map_eq]

/-- **Every iterate is gauge invariant.** -/
theorem iterLaw_gauge (a : Wt) (ha : Adm a) (β : ℝ) :
    ∀ (j m : ℕ) [NeZero m] (g : Vertex (2 * m) → Q),
      MeasurePreserving (gauge (Vertex (2 * m)) Q g) (iterLaw a β j m) (iterLaw a β j m)
  | 0, m, _, g => gauge_twistedLaw m β g
  | j + 1, m, _, g => gauge_map (2 * m) a ha _ (fun g' => iterLaw_gauge a ha β j (2 * m) g') g

end Iterate

/-! ### Translations, and the mean of the blocked action

The field-wise constant `4` of `actionL_blockField_le` is not lost in the mean. For a law invariant under translations up to a
center sign, a coarse plaquette sees four cells in one of four parallel fine planes, so the blocked action is at most the fine
action in the mean, with no factor. For the path-product map this holds at every step, since the blocked law is again invariant.
This is sharp for smooth fields by a hand count, and it does not separate noise from a smooth background: per plaquette it allows
a factor `16` at each step, while the free value is about `2.7`. -/

section Mean

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- Translation of the links by one step in direction `κ`. -/
def shiftE (κ : Fin 4) : Edge V' ≃ Edge V' :=
  (edgeCoordinates (2 * n)).trans
    ((Equiv.prodCongr (TwistedHessian.stepEquiv κ) (Equiv.refl _)).trans (edgeCoordinates (2 * n)).symm)

open Classical in
/-- The exponent of the center sign that moves the twist one step in direction `κ`. Directions `0` and `3` need none. -/
def sgnE (κ : Fin 4) (x : V') (μ : Fin 4) : ℕ :=
  if ((κ = 1 ∧ μ = 2) ∨ (κ = 2 ∧ μ = 1)) ∧ x 1 = 0 ∧ x 2 = 0 then 1 else 0

/-- Translation by one step, with the compensating center sign. -/
def shiftCfg (κ : Fin 4) (U : Configuration V' Q) : Configuration V' Q :=
  fun e => ω ^ sgnE n κ e.1 e.2.2.val * U (shiftE n κ e)

theorem link_shiftCfg (κ : Fin 4) (U : Configuration V' Q) (x : V') (μ : Fin 4) :
    linkValue (2 * n) Q (shiftCfg n κ U) x μ =
      ω ^ sgnE n κ x μ * linkValue (2 * n) Q U (step (2 * n) x κ) μ := rfl

theorem shiftCfg_preserving (κ : Fin 4) :
    MeasurePreserving (shiftCfg n κ) (referenceMeasure Q V') (referenceMeasure Q V') := by
  classical
  have h₁ : MeasurePreserving (fun (U : Configuration V' Q) e => U (shiftE n κ e))
      (referenceMeasure Q V') (referenceMeasure Q V') := by
    have h := measurePreserving_piCongrLeft (fun _ : Edge V' => compactHaar Q) (shiftE n κ).symm
    convert h using 1
    funext U e
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have h₂ : MeasurePreserving (fun (U : Configuration V' Q) e => ω ^ sgnE n κ e.1 e.2.2.val * U e)
      (referenceMeasure Q V') (referenceMeasure Q V') :=
    measurePreserving_pi (μ := fun _ : Edge V' => compactHaar Q) (fun _ => compactHaar Q)
      (f := fun e q => ω ^ sgnE n κ e.1 e.2.2.val * q) fun e => measurePreserving_mul_left _ _
  exact h₂.comp h₁

/-- The signs move the twist. -/
theorem sign_move (κ : Fin 4) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    (ω : Q) ^ sgnE n κ x μ * ω ^ sgnE n κ (step (2 * n) x μ) ν * ω ^ sgnE n κ (step (2 * n) x ν) μ *
      ω ^ sgnE n κ x ν * ω ^ twistExp μ ν (step (2 * n) x κ) = ω ^ twistExp μ ν x := by
  classical
  have hww : (ω : Q) * ω = 1 := TwistedTransfer.ω_mul_ω
  unfold sgnE twistExp
  simp only [step_apply]
  fin_cases κ <;> fin_cases μ <;> fin_cases ν <;> first | exact absurd h (by decide) | skip
  all_goals
    simp (decide := true) only [Fin.mk_zero, Fin.mk_one, Fin.reduceFinMk, zero_add, Nat.reduceAdd, add_zero, if_true, if_false,
      Fin.isValue, true_and, false_and, and_false, and_true, or_false, false_or, reduceCtorEq, one_ne_zero, zero_ne_one]
  all_goals (try split_ifs) <;> (try simp_all)

theorem four_signs (a b c e : ℕ) (A B C E : Q) :
    (ω ^ a * A) * (ω ^ b * B) * (ω ^ c * C)⁻¹ * (ω ^ e * E)⁻¹ =
      ((ω : Q) ^ a * ω ^ b * ω ^ c * ω ^ e) * (A * B * C⁻¹ * E⁻¹) := by
  have hinv (k : ℕ) (X : Q) : (ω ^ k * X)⁻¹ = ω ^ k * X⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (z_sq k)]
    exact (z_comm k X⁻¹).symm.eq
  rw [hinv, hinv, (z_comm b A).symm.mul_mul_mul_comm, (z_comm c (A * B)).symm.mul_mul_mul_comm,
    (z_comm e (A * B * C⁻¹)).symm.mul_mul_mul_comm]

/-- **A plaquette defect of the translated field is the defect at the translated plaquette.** -/
theorem defect_shiftCfg (κ : Fin 4) (U : Configuration V' Q) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    defect (linkValue (2 * n) Q (shiftCfg n κ U)) μ ν x = defect (linkValue (2 * n) Q U) μ ν (step (2 * n) x κ) := by
  unfold defect
  simp only [link_shiftCfg]
  rw [four_signs, ← sign_move n κ x μ ν h, d_mul_left, step_step_comm x μ κ, step_step_comm x ν κ]

theorem action_shiftCfg (κ : Fin 4) (U : Configuration V' Q) :
    actionL (linkValue (2 * n) Q (shiftCfg n κ U)) = actionL (linkValue (2 * n) Q U) := by
  rw [actionL_eq, actionL_eq]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [defect_shiftCfg n κ U _ p.1.1 p.1.2 p.2]
  exact Equiv.sum_comp (TwistedHessian.stepEquiv (N := 2 * n) κ)
    fun z => defect (linkValue (2 * n) Q U) p.1.1 p.1.2 z ^ 2

theorem pow_eq_of_mod (a b : ℕ) (h : a % 2 = b % 2) : (ω : Q) ^ a = ω ^ b := by
  have hw : (ω : Q) ^ 2 = 1 := by
    rw [sq]
    exact TwistedTransfer.ω_mul_ω
  rw [pow_eq_pow_mod a hw, pow_eq_pow_mod b hw, h]

theorem omega_ne_one : (ω : Q) ≠ 1 := by
  intro h
  have h1 : ((ω : Q) : ℍ[ℝ]) = ((1 : Q) : ℍ[ℝ]) := congrArg _ h
  rw [ω_coe] at h1
  have h2 := congrArg (fun q : ℍ[ℝ] => q.re) h1
  norm_num at h2

theorem mod_of_pow_eq (a b : ℕ) (h : (ω : Q) ^ a = ω ^ b) : a % 2 = b % 2 := by
  by_contra hne
  have e1 := pow_eq_of_mod a (a % 2) (by omega)
  have e2 := pow_eq_of_mod b (b % 2) (by omega)
  rw [e1, e2] at h
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rw [ha, hb] at h
  · exact hne (by omega)
  · exact omega_ne_one (by simpa using h.symm)
  · exact omega_ne_one (by simpa using h)
  · exact hne (by omega)

/-- `sign_move` as a congruence, for a plaquette in either order. -/
theorem cell_mod (κ : Fin 4) (x : V') (μ ν : Fin 4) (hne : μ ≠ ν) :
    (sgnE n κ x μ + sgnE n κ (step (2 * n) x μ) ν + sgnE n κ (step (2 * n) x ν) μ + sgnE n κ x ν +
      kk μ ν (step (2 * n) x κ)) % 2 = kk μ ν x % 2 := by
  unfold kk
  rcases lt_or_gt_of_ne hne with h | h
  · simp only [h, if_true]
    refine mod_of_pow_eq _ _ ?_
    rw [← sign_move n κ x μ ν h]
    simp only [pow_add]
  · have hn : ¬ μ < ν := not_lt.2 h.le
    simp only [hn, if_false]
    have := mod_of_pow_eq _ _ (show (ω : Q) ^ (sgnE n κ x ν + sgnE n κ (step (2 * n) x ν) μ + sgnE n κ (step (2 * n) x μ) ν +
        sgnE n κ x μ + twistExp ν μ (step (2 * n) x κ)) = ω ^ twistExp ν μ x by
      rw [← sign_move n κ x ν μ h]
      simp only [pow_add])
    omega

theorem z_inv (k : ℕ) (X : Q) : (ω ^ k * X)⁻¹ = ω ^ k * X⁻¹ := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (z_sq k)]
  exact (z_comm k X⁻¹).symm.eq

theorem z_mul (a b : ℕ) (A B : Q) : (ω ^ a * A) * (ω ^ b * B) = ω ^ (a + b) * (A * B) := by
  rw [(z_comm b A).symm.mul_mul_mul_comm, pow_add]

theorem z_fix (P R S T X : Q) (h : P * R = S * T) : P * (R * X) = S * (T * X) := by
  rw [← mul_assoc, h, mul_assoc]

theorem lineU_shift (κ μ : Fin 4) (U : Configuration V' Q) (y : V') :
    lineU (linkValue (2 * n) Q (shiftCfg n κ U)) μ y =
      ω ^ (sgnE n κ y μ + sgnE n κ (step (2 * n) y μ) μ) * lineU (linkValue (2 * n) Q U) μ (step (2 * n) y κ) := by
  unfold lineU
  simp only [link_shiftCfg]
  rw [z_mul, step_step_comm y μ κ]

/-- **The upper staple moves like the line.** The center signs of the two cells of a staple are what makes this exact. -/
theorem sUp_shift (κ μ ν : Fin 4) (hne : μ ≠ ν) (U : Configuration V' Q) (y : V') :
    sUp (linkValue (2 * n) Q (shiftCfg n κ U)) μ ν y =
      ω ^ (sgnE n κ y μ + sgnE n κ (step (2 * n) y μ) μ) * sUp (linkValue (2 * n) Q U) μ ν (step (2 * n) y κ) := by
  unfold sUp
  simp only [link_shiftCfg]
  rw [z_inv, z_mul, z_mul, z_mul]
  have c1 := cell_mod n κ y μ ν hne
  have c2 := cell_mod n κ (step (2 * n) y μ) μ ν hne
  rw [step_step_comm y μ ν, step_step_comm y μ κ] at c2
  simp only [step_step_comm (step (2 * n) y ν) μ κ, step_step_comm (step (2 * n) y μ) μ κ, step_step_comm y ν κ,
    step_step_comm y μ κ]
  have e1 : (ω : Q) ^ kk μ ν y * ω ^ kk μ ν (step (2 * n) y μ) *
      ω ^ (sgnE n κ y ν + sgnE n κ (step (2 * n) y ν) μ + sgnE n κ (step (2 * n) (step (2 * n) y ν) μ) μ +
        sgnE n κ (step (2 * n) (step (2 * n) y μ) μ) ν) =
      ω ^ (sgnE n κ y μ + sgnE n κ (step (2 * n) y μ) μ) *
        (ω ^ kk μ ν (step (2 * n) y κ) * ω ^ kk μ ν (step (2 * n) (step (2 * n) y κ) μ)) := by
    simp only [← pow_add]
    refine pow_eq_of_mod _ _ ?_
    omega
  exact z_fix _ _ _ _ _ e1

/-- The lower staple, based below the line, moves like the line above it. -/
theorem sDownY_shift (κ μ ν : Fin 4) (hne : μ ≠ ν) (U : Configuration V' Q) (y : V') :
    sDownY (linkValue (2 * n) Q (shiftCfg n κ U)) μ ν y =
      ω ^ (sgnE n κ (step (2 * n) y ν) μ + sgnE n κ (step (2 * n) (step (2 * n) y ν) μ) μ) *
        sDownY (linkValue (2 * n) Q U) μ ν (step (2 * n) y κ) := by
  unfold sDownY
  simp only [link_shiftCfg]
  rw [z_inv, z_mul, z_mul, z_mul]
  have c1 := cell_mod n κ y μ ν hne
  have c2 := cell_mod n κ (step (2 * n) y μ) μ ν hne
  rw [step_step_comm y μ ν, step_step_comm y μ κ] at c2
  simp only [step_step_comm (step (2 * n) y μ) μ κ, step_step_comm y μ κ]
  have e1 : (ω : Q) ^ kk μ ν y * ω ^ kk μ ν (step (2 * n) y μ) *
      ω ^ (sgnE n κ y ν + sgnE n κ y μ + sgnE n κ (step (2 * n) y μ) μ +
        sgnE n κ (step (2 * n) (step (2 * n) y μ) μ) ν) =
      ω ^ (sgnE n κ (step (2 * n) y ν) μ + sgnE n κ (step (2 * n) (step (2 * n) y ν) μ) μ) *
        (ω ^ kk μ ν (step (2 * n) y κ) * ω ^ kk μ ν (step (2 * n) (step (2 * n) y κ) μ)) := by
    simp only [← pow_add]
    refine pow_eq_of_mod _ _ ?_
    omega
  exact z_fix _ _ _ _ _ e1

theorem back_step_comm (y : V') (ν κ : Fin 4) : back (step (2 * n) y κ) ν = step (2 * n) (back y ν) κ := by
  simp only [back, step]
  abel

theorem sDown_shift (κ μ ν : Fin 4) (hne : μ ≠ ν) (U : Configuration V' Q) (y : V') :
    sDown (linkValue (2 * n) Q (shiftCfg n κ U)) μ ν y =
      ω ^ (sgnE n κ y μ + sgnE n κ (step (2 * n) y μ) μ) * sDown (linkValue (2 * n) Q U) μ ν (step (2 * n) y κ) := by
  unfold sDown
  rw [sDownY_shift n κ μ ν hne, step_back, back_step_comm]

/-- **The block sum moves as a whole, for all weights.** -/
theorem blockSumW_shift (a : Wt) (κ μ : Fin 4) (U : Configuration V' Q) (y : V') :
    blockSumW a (linkValue (2 * n) Q (shiftCfg n κ U)) μ y =
      ((ω ^ (sgnE n κ y μ + sgnE n κ (step (2 * n) y μ) μ) : Q) : ℍ[ℝ]) *
        blockSumW a (linkValue (2 * n) Q U) μ (step (2 * n) y κ) := by
  set s : Q := ω ^ (sgnE n κ y μ + sgnE n κ (step (2 * n) y μ) μ) with hs
  unfold blockSumW
  rw [mul_add, Finset.mul_sum, lineU_shift]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  unfold stapleW
  by_cases h : ν = μ
  · simp [h]
  · simp only [h, if_false]
    have hne : μ ≠ ν := Ne.symm h
    rw [sUp_shift n κ μ ν hne, sDown_shift n κ μ ν hne, mul_smul_comm, mul_add]
    rfl

theorem blockW_shift (a : Wt) (ha : Adm a) (κ μ : Fin 4) (U : Configuration V' Q) (y : V') :
    blockW a (linkValue (2 * n) Q (shiftCfg n κ U)) y μ =
      ω ^ (sgnE n κ y μ + sgnE n κ (step (2 * n) y μ) μ) * blockW a (linkValue (2 * n) Q U) (step (2 * n) y κ) μ := by
  unfold blockW
  rw [blockSumW_shift]
  have h := proj_mul (ω ^ (sgnE n κ y μ + sgnE n κ (step (2 * n) y μ) μ)) 1
    (blockSumW a (linkValue (2 * n) Q U) μ (step (2 * n) y κ)) (blockSumW_ne a ha _ _ _)
  simpa using h

/-- A measure invariant under all translations, up to the center signs. -/
def TInv (m : Measure (Configuration V' Q)) : Prop := ∀ κ, MeasurePreserving (shiftCfg n κ) m m

theorem twistedLaw_tInv (β : ℝ) : TInv n (twistedLaw n β) := by
  intro κ
  have hp := shiftCfg_preserving n κ
  refine ⟨hp.measurable, Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply hp.measurable hA, twistedLaw_apply n β _ (hp.measurable hA), twistedLaw_apply n β _ hA]
  congr 1
  have hg : ∀ U, gibbsDensity V' Q (fineS n β) (shiftCfg n κ U) = gibbsDensity V' Q (fineS n β) U := by
    intro U
    unfold gibbsDensity
    rw [fineS_eq, fineS_eq, action_shiftCfg]
  rw [← hp.setLIntegral_comp_preimage hA (measurable_gibbsDensity n β)]
  simp only [hg]

/-- A function on the torus invariant under all unit steps is constant. -/
theorem const_of_step (g : V' → ℝ) (hg : ∀ κ x, g (step (2 * n) x κ) = g x) (x y : V') : g y = g x := by
  have hk (κ : Fin 4) (k : ℕ) (z : V') : g (z + k • Pi.single κ (1 : ZMod (2 * n))) = g z := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul, ← add_assoc]
      exact (hg κ _).trans ih
  have hc (κ : Fin 4) (c : ZMod (2 * n)) (z : V') : g (z + Pi.single κ c) = g z := by
    have e : (Pi.single κ c : V') = c.val • Pi.single κ (1 : ZMod (2 * n)) := by
      funext i
      by_cases hi : i = κ
      · subst hi
        simp
      · simp [Pi.single_apply, hi]
    rw [e]
    exact hk κ _ z
  have hy : y = x + Pi.single 0 (y 0 - x 0) + Pi.single 1 (y 1 - x 1) + Pi.single 2 (y 2 - x 2) +
      Pi.single 3 (y 3 - x 3) := by
    funext i
    fin_cases i <;> simp
  rw [hy, hc, hc, hc, hc]

/-- For an invariant measure, the mean squared defect in a plane does not depend on the site. -/
theorem mean_defect_const (m : Measure (Configuration V' Q)) (hm : TInv n m) (μ ν : Fin 4) (h : μ < ν) (x y : V') :
    ∫ U, defect (linkValue (2 * n) Q U) μ ν y ^ 2 ∂m = ∫ U, defect (linkValue (2 * n) Q U) μ ν x ^ 2 ∂m := by
  refine const_of_step n (fun z => ∫ U, defect (linkValue (2 * n) Q U) μ ν z ^ 2 ∂m) (fun κ z => ?_) x y
  have hc : Continuous fun U : Configuration V' Q => defect (linkValue (2 * n) Q U) μ ν z ^ 2 :=
    (continuous_defect (2 * n) μ ν z).pow 2
  have hi : ∫ U, defect (linkValue (2 * n) Q U) μ ν z ^ 2 ∂m =
      ∫ U, defect (linkValue (2 * n) Q (shiftCfg n κ U)) μ ν z ^ 2 ∂m := by
    have := integral_map (μ := m) (hm κ).measurable.aemeasurable
      (f := fun U => defect (linkValue (2 * n) Q U) μ ν z ^ 2) hc.aestronglyMeasurable
    rwa [(hm κ).map_eq] at this
  beta_reduce
  rw [hi]
  simp only [defect_shiftCfg n κ _ z μ ν h]

theorem integral_four {X : Type*} [MeasurableSpace X] (m : Measure X) (f1 f2 f3 f4 : X → ℝ) (i1 : Integrable f1 m)
    (i2 : Integrable f2 m) (i3 : Integrable f3 m) (i4 : Integrable f4 m) :
    ∫ U, 4 * (f1 U + f2 U + f3 U + f4 U) ∂m = 4 * (∫ U, f1 U ∂m + ∫ U, f2 U ∂m + ∫ U, f3 U ∂m + ∫ U, f4 U ∂m) := by
  rw [integral_const_mul]
  have a1 : ∫ U, (f1 U + f2 U) ∂m = ∫ U, f1 U ∂m + ∫ U, f2 U ∂m := integral_add i1 i2
  have a2 : ∫ U, (f1 U + f2 U + f3 U) ∂m = ∫ U, (f1 U + f2 U) ∂m + ∫ U, f3 U ∂m :=
    integral_add (f := fun U => f1 U + f2 U) (i1.add i2) i3
  have a3 : ∫ U, (f1 U + f2 U + f3 U + f4 U) ∂m = ∫ U, (f1 U + f2 U + f3 U) ∂m + ∫ U, f4 U ∂m :=
    integral_add (f := fun U => f1 U + f2 U + f3 U) ((i1.add i2).add i3) i4
  rw [a3, a2, a1]

theorem integrable_cont (m : Measure (Configuration V' Q)) [IsProbabilityMeasure m]
    (f : Configuration V' Q → ℝ) (hf : Continuous f) : Integrable f m :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **The mean squared defect of a coarse plaquette, with no staples.** It is at most `16` times the mean squared defect of a fine
plaquette in the same plane. -/
theorem mean_coarse_defect (m : Measure (Configuration V' Q)) [IsProbabilityMeasure m] (hm : TInv n m) (μ ν : Fin 4)
    (h : μ < ν) (x : Vertex n) (z : V') :
    ∫ U, defect (linkValue n Q (blockCfg n zeroW U)) μ ν x ^ 2 ∂m ≤
      16 * ∫ U, defect (linkValue (2 * n) Q U) μ ν z ^ 2 ∂m := by
  set G := fun y : V' => ∫ U, defect (linkValue (2 * n) Q U) μ ν y ^ 2 ∂m with hG
  have hconst (y : V') : G y = G z := mean_defect_const n m hm μ ν h z y
  have hci (y : V') := integrable_cont n m _ ((continuous_defect (2 * n) μ ν y).pow 2)
  have hcL : Continuous fun U : Configuration V' Q => defect (linkValue n Q (blockCfg n zeroW U)) μ ν x ^ 2 :=
    ((continuous_defect n μ ν x).comp (continuous_blockCfg n zeroW adm_zero)).pow 2
  set y := emb n x with hy
  have hpt (U : Configuration V' Q) : defect (linkValue n Q (blockCfg n zeroW U)) μ ν x ^ 2 ≤
      4 * (defect (linkValue (2 * n) Q U) μ ν (step (2 * n) y μ) ^ 2 +
        defect (linkValue (2 * n) Q U) μ ν (step (2 * n) (step (2 * n) y μ) ν) ^ 2 +
        defect (linkValue (2 * n) Q U) μ ν y ^ 2 + defect (linkValue (2 * n) Q U) μ ν (step (2 * n) y ν) ^ 2) := by
    have := coarse_sq_le n zeroW (fun _ _ => le_rfl) 0 le_rfl he_zero (linkValue (2 * n) Q U) μ ν x
    rw [link_blockCfg]
    simpa using this
  have hsum : ∫ U, 4 * (defect (linkValue (2 * n) Q U) μ ν (step (2 * n) y μ) ^ 2 +
        defect (linkValue (2 * n) Q U) μ ν (step (2 * n) (step (2 * n) y μ) ν) ^ 2 +
        defect (linkValue (2 * n) Q U) μ ν y ^ 2 + defect (linkValue (2 * n) Q U) μ ν (step (2 * n) y ν) ^ 2) ∂m =
      16 * G z := by
    rw [integral_four m _ _ _ _ (hci _) (hci _) (hci _) (hci _)]
    change 4 * (G _ + G _ + G _ + G _) = _
    rw [hconst (step (2 * n) y μ), hconst (step (2 * n) (step (2 * n) y μ) ν), hconst y, hconst (step (2 * n) y ν)]
    ring
  rw [← hsum]
  exact integral_mono (integrable_cont n m _ hcL) (integrable_cont n m _ (by
    have c (w : V') := (continuous_defect (2 * n) μ ν w).pow 2
    exact continuous_const.mul (((c _).add (c _)).add (c _) |>.add (c _)))) hpt

theorem cd_sq_continuous (μ ν : Fin 4) (z : V') :
    Continuous fun U : Configuration V' Q => cd (linkValue (2 * n) Q U) μ ν z ^ 2 := by
  unfold cd
  split_ifs
  · exact (continuous_defect (2 * n) _ _ _).pow 2
  · exact (continuous_defect (2 * n) _ _ _).pow 2

theorem cd_symm (L : V' → Fin 4 → Q) (μ ν : Fin 4) (hne : μ ≠ ν) (z : V') : cd L μ ν z = cd L ν μ z := by
  unfold cd
  rcases lt_or_gt_of_ne hne with h | h
  · simp [h, not_lt.2 h.le]
  · simp [h, not_lt.2 h.le]

/-- The mean of a squared cell defect at the origin. -/
def gg (m : Measure (Configuration V' Q)) (μ ν : Fin 4) : ℝ := ∫ U, cd (linkValue (2 * n) Q U) μ ν 0 ^ 2 ∂m

theorem mean_cd_const (m : Measure (Configuration V' Q)) (hm : TInv n m) (μ ν : Fin 4) (hne : μ ≠ ν) (z : V') :
    ∫ U, cd (linkValue (2 * n) Q U) μ ν z ^ 2 ∂m = gg n m μ ν := by
  unfold gg cd
  rcases lt_or_gt_of_ne hne with h | h
  · simp only [h, if_true]
    exact mean_defect_const n m hm μ ν h 0 z
  · simp only [not_lt.2 h.le, if_false]
    exact mean_defect_const n m hm ν μ h 0 z

theorem integral_cells2 (m : Measure (Configuration V' Q)) [IsProbabilityMeasure m] (hm : TInv n m) (μ ν : Fin 4)
    (hne : μ ≠ ν) (y : V') : ∫ U, cells2 (linkValue (2 * n) Q U) μ ν y ∂m = 4 * gg n m μ ν := by
  have hi (z : V') := integrable_cont n m _ (cd_sq_continuous n μ ν z)
  have h4 := integral_four m _ _ _ _ (hi y) (hi (step (2 * n) y μ)) (hi (back y ν)) (hi (step (2 * n) (back y ν) μ))
  unfold cells2
  rw [integral_const_mul] at h4
  have hne4 : (4 : ℝ) ≠ 0 := by norm_num
  have h5 := mul_left_cancel₀ hne4 h4
  rw [h5]
  simp only [mean_cd_const n m hm μ ν hne]
  ring

theorem cells2_continuous (μ ν : Fin 4) (y : V') :
    Continuous fun U : Configuration V' Q => cells2 (linkValue (2 * n) Q U) μ ν y := by
  unfold cells2
  exact (((cd_sq_continuous n μ ν _).add (cd_sq_continuous n μ ν _)).add (cd_sq_continuous n μ ν _)).add
    (cd_sq_continuous n μ ν _)

theorem cellE2_continuous (μ : Fin 4) (y : V') :
    Continuous fun U : Configuration V' Q => cellE2 (linkValue (2 * n) Q U) μ y := by
  unfold cellE2
  refine continuous_finset_sum _ fun ν _ => ?_
  split_ifs
  · exact continuous_const
  · exact cells2_continuous n μ ν y

/-- The mean of all squared cell defects around a link. -/
def eeL (m : Measure (Configuration V' Q)) (μ : Fin 4) : ℝ := ∑ ν, if ν = μ then 0 else 4 * gg n m μ ν

theorem integral_cellE2 (m : Measure (Configuration V' Q)) [IsProbabilityMeasure m] (hm : TInv n m) (μ : Fin 4) (y : V') :
    ∫ U, cellE2 (linkValue (2 * n) Q U) μ y ∂m = eeL n m μ := by
  unfold cellE2 eeL
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun ν _ => ?_
    split_ifs with h
    · simp
    · exact integral_cells2 n m hm μ ν (Ne.symm h) y
  · intro ν _
    split_ifs
    · exact integrable_const _
    · exact integrable_cont n m _ (cells2_continuous n μ ν y)

/-- The mean squared defect of a coarse plaquette, for all weights. -/
theorem mean_coarse_defectW (a : Wt) (ha : Adm a) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (m : Measure (Configuration V' Q)) [IsProbabilityMeasure m]
    (hm : TInv n m) (μ ν : Fin 4) (h : μ < ν) (x : Vertex n) :
    ∫ U, defect (linkValue n Q (blockCfg n a U)) μ ν x ^ 2 ∂m ≤
      (4 + 64 * e) * (4 * gg n m μ ν + e * (2 * eeL n m μ + 2 * eeL n m ν)) := by
  have hne : μ ≠ ν := h.ne
  set y := emb n x with hy
  have hdef (z : V') : ∫ U, defect (linkValue (2 * n) Q U) μ ν z ^ 2 ∂m = gg n m μ ν := by
    rw [← mean_cd_const n m hm μ ν hne z]
    unfold cd
    simp only [h, if_true]
  have hid (z : V') := integrable_cont n m _ ((continuous_defect (2 * n) μ ν z).pow 2)
  have hie (ρ : Fin 4) (z : V') := integrable_cont n m _ (cellE2_continuous n ρ z)
  have hM := integral_four m _ _ _ _ (hid (step (2 * n) y μ)) (hid (step (2 * n) (step (2 * n) y μ) ν)) (hid y)
    (hid (step (2 * n) y ν))
  have hT := integral_four m _ _ _ _ (hie μ y) (hie ν (step (2 * n) (step (2 * n) y μ) μ))
    (hie μ (step (2 * n) (step (2 * n) y ν) ν)) (hie ν y)
  rw [integral_const_mul, hdef, hdef, hdef, hdef] at hM
  rw [integral_const_mul, integral_cellE2 n m hm, integral_cellE2 n m hm, integral_cellE2 n m hm,
    integral_cellE2 n m hm] at hT
  have hne4 : (4 : ℝ) ≠ 0 := by norm_num
  have hM' := mul_left_cancel₀ hne4 hM
  have hT' := mul_left_cancel₀ hne4 hT
  have hcL : Continuous fun U : Configuration V' Q => defect (linkValue n Q (blockCfg n a U)) μ ν x ^ 2 :=
    ((continuous_defect n μ ν x).comp (continuous_blockCfg n a ha)).pow 2
  let fM : Configuration V' Q → ℝ := fun U => defect (linkValue (2 * n) Q U) μ ν (step (2 * n) y μ) ^ 2 +
      defect (linkValue (2 * n) Q U) μ ν (step (2 * n) (step (2 * n) y μ) ν) ^ 2 + defect (linkValue (2 * n) Q U) μ ν y ^ 2 +
      defect (linkValue (2 * n) Q U) μ ν (step (2 * n) y ν) ^ 2
  let fT : Configuration V' Q → ℝ := fun U => cellE2 (linkValue (2 * n) Q U) μ y +
      cellE2 (linkValue (2 * n) Q U) ν (step (2 * n) (step (2 * n) y μ) μ) +
      cellE2 (linkValue (2 * n) Q U) μ (step (2 * n) (step (2 * n) y ν) ν) + cellE2 (linkValue (2 * n) Q U) ν y
  have hcM : Continuous fM :=
    (((continuous_defect (2 * n) μ ν _).pow 2 |>.add ((continuous_defect (2 * n) μ ν _).pow 2)).add
      ((continuous_defect (2 * n) μ ν _).pow 2)).add ((continuous_defect (2 * n) μ ν _).pow 2)
  have hcT : Continuous fT :=
    (((cellE2_continuous n μ _).add (cellE2_continuous n ν _)).add (cellE2_continuous n μ _)).add (cellE2_continuous n ν _)
  have iM : Integrable fM m := integrable_cont n m _ hcM
  have iT : Integrable fT m := integrable_cont n m _ hcT
  have hmono : ∫ U, defect (linkValue n Q (blockCfg n a U)) μ ν x ^ 2 ∂m ≤
      ∫ U, (4 + 64 * e) * (fM U + e * fT U) ∂m := by
    refine integral_mono (integrable_cont n m _ hcL) ((iM.add (iT.const_mul e)).const_mul _) fun U => ?_
    have := coarse_sq_le n a ha.nonneg e he0 he (linkValue (2 * n) Q U) μ ν x
    rw [← link_blockCfg] at this
    exact this
  refine hmono.trans (le_of_eq ?_)
  have hA : ∫ U, (fM U + e * fT U) ∂m = ∫ U, fM U ∂m + ∫ U, e * fT U ∂m :=
    integral_add (f := fM) (g := fun U => e * fT U) iM (iT.const_mul e)
  have hM2 : ∫ U, fM U ∂m = _ := hM'
  have hT2 : ∫ U, fT U ∂m = _ := hT'
  rw [integral_const_mul, hA, integral_const_mul, hM2, hT2]
  ring

/-- **The blocked action, in the mean, for all weights.** For a translation invariant law it is at most `(1 + 16 e)(1 + 12 e)` times
the fine action. The field-wise constant of `actionL_blockField_le` is `(4 + 64 e)(1 + 48 e)`. With no staples this is `1`, against
`4`, and there is no loss at all. It is still about `10` at isotropic `α = 0.15`, since the staple terms are bounded by Cauchy-Schwarz,
while the free ratio is below `1`. -/
theorem mean_action_stepW (a : Wt) (ha : Adm a) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (m : Measure (Configuration V' Q)) [IsProbabilityMeasure m]
    (hm : TInv n m) :
    ∫ U, actionL (linkValue n Q (blockCfg n a U)) ∂m ≤
      (1 + 16 * e) * (1 + 12 * e) * ∫ U, actionL (linkValue (2 * n) Q U) ∂m := by
  have hci (μ ν : Fin 4) (y : V') : Integrable (fun U => defect (linkValue (2 * n) Q U) μ ν y ^ 2) m :=
    integrable_cont n m _ ((continuous_defect (2 * n) μ ν y).pow 2)
  have hcc (μ ν : Fin 4) (x : Vertex n) : Integrable (fun U => defect (linkValue n Q (blockCfg n a U)) μ ν x ^ 2) m :=
    integrable_cont n m _ (((continuous_defect n μ ν x).comp (continuous_blockCfg n a ha)).pow 2)
  have hdef (μ ν : Fin 4) (h : μ < ν) (z : V') : ∫ U, defect (linkValue (2 * n) Q U) μ ν z ^ 2 ∂m = gg n m μ ν := by
    rw [← mean_cd_const n m hm μ ν h.ne z]
    unfold cd
    simp only [h, if_true]
  have hnv : ((Finset.univ : Finset (Vertex (2 * n))).card : ℝ) = 16 * ((Finset.univ : Finset (Vertex n)).card : ℝ) := by
    simp [Finset.card_univ, ZMod.card]
    ring
  set c : ℝ := ((Finset.univ : Finset (Vertex n)).card : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  have hE : ∀ U : Configuration V' Q, actionL (linkValue n Q (blockCfg n a U)) =
      ∑ p : Plane, ∑ x, defect (linkValue n Q (blockCfg n a U)) p.1.1 p.1.2 x ^ 2 := fun U => actionL_eq n _
  have hF : ∀ U : Configuration V' Q, actionL (linkValue (2 * n) Q U) =
      ∑ p : Plane, ∑ z, defect (linkValue (2 * n) Q U) p.1.1 p.1.2 z ^ 2 := fun U => actionL_eq (2 * n) _
  simp only [hE, hF]
  rw [integral_finset_sum _ fun p _ => integrable_finset_sum _ fun x _ => hcc _ _ x,
    integral_finset_sum _ fun p _ => integrable_finset_sum _ fun y _ => hci _ _ y]
  have hfine (p : Plane) : ∫ U, ∑ z, defect (linkValue (2 * n) Q U) p.1.1 p.1.2 z ^ 2 ∂m = 16 * c * gg n m p.1.1 p.1.2 := by
    rw [integral_finset_sum _ fun y _ => hci _ _ y]
    simp only [hdef _ _ p.2]
    rw [Finset.sum_const, nsmul_eq_mul, hnv]
  have hcoarse (p : Plane) : ∫ U, ∑ x, defect (linkValue n Q (blockCfg n a U)) p.1.1 p.1.2 x ^ 2 ∂m ≤
      c * ((4 + 64 * e) * (4 * gg n m p.1.1 p.1.2 + e * (2 * eeL n m p.1.1 + 2 * eeL n m p.1.2))) := by
    rw [integral_finset_sum _ fun x _ => hcc _ _ x]
    refine (Finset.sum_le_sum fun x _ => mean_coarse_defectW n a ha e he0 he m hm _ _ p.2 x).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
  simp only [hfine]
  refine (Finset.sum_le_sum fun p _ => hcoarse p).trans (le_of_eq ?_)
  rw [plane_expand (fun μ ν => c * ((4 + 64 * e) * (4 * gg n m μ ν + e * (2 * eeL n m μ + 2 * eeL n m ν)))),
    plane_expand (fun μ ν => 16 * c * gg n m μ ν)]
  have sy (μ ν : Fin 4) (hne : μ ≠ ν) : gg n m ν μ = gg n m μ ν := by
    unfold gg
    simp only [cd_symm _ _ ν μ (Ne.symm hne)]
  have e0 : eeL n m 0 = 4 * gg n m 0 1 + 4 * gg n m 0 2 + 4 * gg n m 0 3 := by
    simp (decide := true) [eeL, Fin.sum_univ_four]
  have e1 : eeL n m 1 = 4 * gg n m 0 1 + 4 * gg n m 1 2 + 4 * gg n m 1 3 := by
    simp (decide := true) [eeL, Fin.sum_univ_four, sy 0 1 (by decide)]
  have e2 : eeL n m 2 = 4 * gg n m 0 2 + 4 * gg n m 1 2 + 4 * gg n m 2 3 := by
    simp (decide := true) [eeL, Fin.sum_univ_four, sy 0 2 (by decide), sy 1 2 (by decide)]
  have e3 : eeL n m 3 = 4 * gg n m 0 3 + 4 * gg n m 1 3 + 4 * gg n m 2 3 := by
    simp (decide := true) [eeL, Fin.sum_univ_four, sy 0 3 (by decide), sy 1 3 (by decide), sy 2 3 (by decide)]
  simp only [e0, e1, e2, e3]
  ring

/-- With no staples there is no factor at all. -/
theorem mean_action_step (m : Measure (Configuration V' Q)) [IsProbabilityMeasure m] (hm : TInv n m) :
    ∫ U, actionL (linkValue n Q (blockCfg n zeroW U)) ∂m ≤ ∫ U, actionL (linkValue (2 * n) Q U) ∂m := by
  have h := mean_action_stepW n zeroW adm_zero 0 le_rfl he_zero m hm
  simpa using h

end Mean

/-! #### Iterating the mean bound -/

section MeanIterate

variable (m : ℕ) [NeZero m]

theorem sgnE_emb (κ μ : Fin 4) (x : Vertex (2 * m)) :
    sgnE (2 * m) κ (emb (2 * m) x) μ = sgnE m κ x μ := by
  classical
  unfold sgnE
  have e (i : Fin 4) : emb (2 * m) x i = 0 ↔ x i = 0 := emb1_eq_zero (2 * m) (x i)
  simp only [e]

theorem sgnE_step_self (κ μ : Fin 4) (y : Vertex (2 * (2 * m))) (x : Vertex (2 * m)) (hy : y = emb (2 * m) x)
    (z : Vertex (2 * (2 * m))) (hz : (κ = 1 ∧ μ = 2 ∧ z 1 = y 1 + 1) ∨ (κ = 2 ∧ μ = 1 ∧ z 2 = y 2 + 1) ∨
      (κ = 1 ∧ μ = 2 ∧ z 2 = y 2 + 1) ∨ (κ = 2 ∧ μ = 1 ∧ z 1 = y 1 + 1) ∨ ¬ ((κ = 1 ∧ μ = 2) ∨ (κ = 2 ∧ μ = 1))) :
    sgnE (2 * m) κ z μ = 0 := by
  classical
  have hne (i : Fin 4) : y i + 1 ≠ 0 := by
    rw [hy]
    exact emb1_add_one_ne (2 * m) (x i)
  unfold sgnE
  rw [if_neg]
  rintro ⟨h1, h2, h3⟩
  rcases hz with ⟨-, -, e⟩ | ⟨-, -, e⟩ | ⟨-, -, e⟩ | ⟨-, -, e⟩ | e
  · exact hne 1 (e ▸ h2)
  · exact hne 2 (e ▸ h3)
  · exact hne 2 (e ▸ h3)
  · exact hne 1 (e ▸ h2)
  · exact e h1

/-- **Every admissible map commutes with translation:** two fine steps with their signs are one coarse step with its sign. -/
theorem block_shift (a : Wt) (ha : Adm a) (κ : Fin 4) (U : Configuration (Vertex (2 * (2 * m))) Q) :
    blockCfg (2 * m) a (shiftCfg (2 * m) κ (shiftCfg (2 * m) κ U)) = shiftCfg m κ (blockCfg (2 * m) a U) := by
  refine config_ext (2 * m) _ _ fun x μ => ?_
  rw [link_shiftCfg, link_blockCfg, link_blockCfg]
  change blockW a _ (emb (2 * m) x) μ = _ * blockW a _ (emb (2 * m) (step (2 * m) x κ)) μ
  rw [blockW_shift (2 * m) a ha, blockW_shift (2 * m) a ha, emb_step]
  set y := emb (2 * m) x with hy
  have hs (a b : Fin 4) (z : Vertex (2 * (2 * m))) : step (2 * (2 * m)) z a b = z b + if b = a then 1 else 0 :=
    step_apply _ z a b
  have s1 : sgnE (2 * m) κ (step (2 * (2 * m)) y κ) μ = 0 := by
    refine sgnE_step_self m κ μ y x hy _ ?_
    by_cases c1 : κ = 1 ∧ μ = 2
    · exact Or.inl ⟨c1.1, c1.2, by rw [hs, c1.1]; simp⟩
    · by_cases c2 : κ = 2 ∧ μ = 1
      · exact Or.inr (Or.inl ⟨c2.1, c2.2, by rw [hs, c2.1]; simp⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by tauto))))
  have s2 : sgnE (2 * m) κ (step (2 * (2 * m)) y μ) μ = 0 := by
    refine sgnE_step_self m κ μ y x hy _ ?_
    by_cases c1 : κ = 1 ∧ μ = 2
    · exact Or.inr (Or.inr (Or.inl ⟨c1.1, c1.2, by rw [hs, c1.2]; simp⟩))
    · by_cases c2 : κ = 2 ∧ μ = 1
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c2.1, c2.2, by rw [hs, c2.2]; simp⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by tauto))))
  have s3 : sgnE (2 * m) κ (step (2 * (2 * m)) (step (2 * (2 * m)) y κ) μ) μ = 0 := by
    refine sgnE_step_self m κ μ y x hy _ ?_
    by_cases c1 : κ = 1 ∧ μ = 2
    · exact Or.inl ⟨c1.1, c1.2, by rw [hs, hs, c1.1, c1.2]; simp⟩
    · by_cases c2 : κ = 2 ∧ μ = 1
      · exact Or.inr (Or.inl ⟨c2.1, c2.2, by rw [hs, hs, c2.1, c2.2]; simp⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by tauto))))
  rw [s1, s2, s3, sgnE_emb]
  simp only [add_zero, pow_zero, one_mul]

/-- Blocking keeps the invariance. -/
theorem tInv_block (a : Wt) (ha : Adm a) (μ' : Measure (Configuration (Vertex (2 * (2 * m))) Q)) (h : TInv (2 * m) μ') :
    TInv m (μ'.map (blockCfg (2 * m) a)) := by
  intro κ
  have hB := (continuous_blockCfg (2 * m) a ha).measurable
  have hR := (shiftCfg_preserving m κ).measurable
  refine ⟨hR, ?_⟩
  rw [Measure.map_map hR hB]
  have e : shiftCfg m κ ∘ blockCfg (2 * m) a =
      blockCfg (2 * m) a ∘ (shiftCfg (2 * m) κ ∘ shiftCfg (2 * m) κ) := by
    funext U
    exact (block_shift m a ha κ U).symm
  rw [e, ← Measure.map_map hB ((h κ).measurable.comp (h κ).measurable),
    ← Measure.map_map (h κ).measurable (h κ).measurable, (h κ).map_eq, (h κ).map_eq]

end MeanIterate

section MeanLaw

/-- **Every iterate of an admissible map is invariant under translations, up to the center signs.** Unlike reflection positivity,
this needs no condition on the weights beyond admissibility. -/
theorem iterLaw_tInv (a : Wt) (ha : Adm a) (β : ℝ) : ∀ (j m : ℕ) [NeZero m], TInv m (iterLaw a β j m)
  | 0, m, _ => twistedLaw_tInv m β
  | j + 1, m, _ => tInv_block m a ha _ (iterLaw_tInv a ha β j (2 * m))

/-- The mean action of each iterate, against the previous one, for all admissible weights. -/
theorem iterLaw_action_stepW (a : Wt) (ha : Adm a) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (β : ℝ) (j m : ℕ) [NeZero m] :
    ∫ V, actionL (linkValue (2 * m) Q V) ∂iterLaw a β (j + 1) m ≤
      (1 + 16 * e) * (1 + 12 * e) * ∫ U, actionL (linkValue (2 * (2 * m)) Q U) ∂iterLaw a β j (2 * m) := by
  haveI := iterLaw_probability a ha β j (2 * m)
  have hB := continuous_blockCfg (2 * m) a ha
  have h := mean_action_stepW (2 * m) a ha e he0 he (iterLaw a β j (2 * m)) (iterLaw_tInv a ha β j (2 * m))
  change ∫ V, actionL (linkValue (2 * m) Q V) ∂(iterLaw a β j (2 * m)).map (blockCfg (2 * m) a) ≤ _
  rw [integral_map hB.measurable.aemeasurable (continuous_actionL (2 * m)).aestronglyMeasurable]
  exact h

/-- **The blocked action does not increase in the mean, at any step of the path-product map.** -/
theorem iterLaw_action_step (β : ℝ) (j m : ℕ) [NeZero m] :
    ∫ V, actionL (linkValue (2 * m) Q V) ∂iterLaw zeroW β (j + 1) m ≤
      ∫ U, actionL (linkValue (2 * (2 * m)) Q U) ∂iterLaw zeroW β j (2 * m) := by
  haveI := iterLaw_probability zeroW adm_zero β j (2 * m)
  have hB := continuous_blockCfg (2 * m) zeroW adm_zero
  have h := mean_action_step (2 * m) (iterLaw zeroW β j (2 * m)) (iterLaw_tInv zeroW adm_zero β j (2 * m))
  change ∫ V, actionL (linkValue (2 * m) Q V) ∂(iterLaw zeroW β j (2 * m)).map (blockCfg (2 * m) zeroW) ≤ _
  rw [integral_map hB.measurable.aemeasurable (continuous_actionL (2 * m)).aestronglyMeasurable]
  exact h

/-- **A local mean bound on the blocked defect, at every step, free of the volume.** The mean squared defect of a plaquette after
`j` steps of the path-product map is at most `16^j` times the bound of `TwistedLocalTail.defect_sq_le_log`. This is worst case: it
says something only while `16^j · (7/2) (-log mass(6 β))/β < 4`, about `β > 162` at `j = 1` and `β > 3640` at `j = 2`, and it does not see
the free value of about `2.7^j`. -/
theorem iterLaw_mean_defect (β : ℝ) (hβ : 0 < β) : ∀ (j m : ℕ) [NeZero m] (x : Vertex (2 * m)) (μ ν : Fin 4), μ < ν →
    ∫ V, defect (linkValue (2 * m) Q V) μ ν x ^ 2 ∂iterLaw zeroW β j m ≤
      16 ^ j * (7 / 2 * -Real.log (SU2GaussianMass.mass (6 * β)) / β)
  | 0, m, _, x, μ, ν, h => by
    simpa using TwistedLocalTail.defect_sq_le_log m β hβ μ ν h x
  | j + 1, m, _, x, μ, ν, h => by
    haveI := iterLaw_probability zeroW adm_zero β j (2 * m)
    have hB := continuous_blockCfg (2 * m) zeroW adm_zero
    have h1 := mean_coarse_defect (2 * m) (iterLaw zeroW β j (2 * m)) (iterLaw_tInv zeroW adm_zero β j (2 * m)) μ ν h x 0
    have h2 := iterLaw_mean_defect β hβ j (2 * m) 0 μ ν h
    change ∫ V, defect (linkValue (2 * m) Q V) μ ν x ^ 2 ∂(iterLaw zeroW β j (2 * m)).map (blockCfg (2 * m) zeroW) ≤ _
    rw [integral_map hB.measurable.aemeasurable ((continuous_defect (2 * m) μ ν x).pow 2).aestronglyMeasurable]
    refine h1.trans ?_
    rw [pow_succ]
    nlinarith only [h2]

end MeanLaw

section MeanTotal

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

theorem planes_alg (m : Measure (Configuration V' Q)) (e : ℝ) :
    ∑ p : Plane, (4 + 64 * e) * (4 * gg n m p.1.1 p.1.2 + e * (2 * eeL n m p.1.1 + 2 * eeL n m p.1.2)) =
      16 * ((1 + 16 * e) * (1 + 12 * e)) * ∑ p : Plane, gg n m p.1.1 p.1.2 := by
  rw [plane_expand (fun μ ν => (4 + 64 * e) * (4 * gg n m μ ν + e * (2 * eeL n m μ + 2 * eeL n m ν))),
    plane_expand (fun μ ν => gg n m μ ν)]
  have sy (μ ν : Fin 4) (hne : μ ≠ ν) : gg n m ν μ = gg n m μ ν := by
    unfold gg
    simp only [cd_symm _ _ ν μ (Ne.symm hne)]
  have e0 : eeL n m 0 = 4 * gg n m 0 1 + 4 * gg n m 0 2 + 4 * gg n m 0 3 := by
    simp (decide := true) [eeL, Fin.sum_univ_four]
  have e1 : eeL n m 1 = 4 * gg n m 0 1 + 4 * gg n m 1 2 + 4 * gg n m 1 3 := by
    simp (decide := true) [eeL, Fin.sum_univ_four, sy 0 1 (by decide)]
  have e2 : eeL n m 2 = 4 * gg n m 0 2 + 4 * gg n m 1 2 + 4 * gg n m 2 3 := by
    simp (decide := true) [eeL, Fin.sum_univ_four, sy 0 2 (by decide), sy 1 2 (by decide)]
  have e3 : eeL n m 3 = 4 * gg n m 0 3 + 4 * gg n m 1 3 + 4 * gg n m 2 3 := by
    simp (decide := true) [eeL, Fin.sum_univ_four, sy 0 3 (by decide), sy 1 3 (by decide), sy 2 3 (by decide)]
  simp only [e0, e1, e2, e3]
  ring

/-- The six mean squared defects at a coarse site, by those at a fine site, for all weights. -/
theorem mean_plane_total (a : Wt) (ha : Adm a) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (m : Measure (Configuration V' Q)) [IsProbabilityMeasure m]
    (hm : TInv n m) (x : Vertex n) (z : V') :
    ∑ p : Plane, ∫ U, defect (linkValue n Q (blockCfg n a U)) p.1.1 p.1.2 x ^ 2 ∂m ≤
      16 * ((1 + 16 * e) * (1 + 12 * e)) * ∑ p : Plane, ∫ U, defect (linkValue (2 * n) Q U) p.1.1 p.1.2 z ^ 2 ∂m := by
  have hdef (p : Plane) : ∫ U, defect (linkValue (2 * n) Q U) p.1.1 p.1.2 z ^ 2 ∂m = gg n m p.1.1 p.1.2 := by
    rw [← mean_cd_const n m hm _ _ p.2.ne z]
    unfold cd
    simp only [p.2, if_true]
  simp only [hdef]
  rw [← planes_alg]
  exact Finset.sum_le_sum fun p _ => mean_coarse_defectW n a ha e he0 he m hm _ _ p.2 x

/-- The six mean squared defects at a site of the bare lattice. -/
theorem law_plane_total (β : ℝ) (hβ : 0 < β) (x : V') :
    ∑ p : Plane, ∫ U, defect (linkValue (2 * n) Q U) p.1.1 p.1.2 x ^ 2 ∂twistedLaw n β ≤
      21 * (-Real.log (SU2GaussianMass.mass (6 * β)) / β) := by
  have h (p : Plane) : ∫ U, defect (linkValue (2 * n) Q U) p.1.1 p.1.2 x ^ 2 ∂twistedLaw n β ≤
      7 / 2 * (-Real.log (SU2GaussianMass.mass (6 * β)) / β) := by
    have := TwistedLocalTail.defect_sq_le_log n β hβ p.1.1 p.1.2 p.2 x
    rw [mul_div_assoc] at this
    exact this
  refine (Finset.sum_le_sum fun p _ => h p).trans (le_of_eq ?_)
  rw [plane_expand (fun _ _ => 7 / 2 * (-Real.log (SU2GaussianMass.mass (6 * β)) / β))]
  ring

end MeanTotal

section MeanTotalLaw

/-- **A local mean bound for every iterate of every admissible map, free of the volume.** The six mean squared defects at a site after
`j` steps sum to at most `(16 K)^j · 21 (-log mass(6 β))/β`, with `K = (1 + 16 e)(1 + 12 e)`. The six always sum to at most `24`, so
this is worst case and empty once the right side reaches `24`: at isotropic `α = 0.15`, `j = 1` needs `β` above about `2200` and `j = 2` above
about `5.6 · 10⁵`. -/
theorem iterLaw_mean_total (a : Wt) (ha : Adm a) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ μ ν, ν ≠ μ → 2 * a μ ν ≤ e * (1 + tot a μ)) (β : ℝ) (hβ : 0 < β) :
    ∀ (j m : ℕ) [NeZero m] (x : Vertex (2 * m)),
      ∑ p : Plane, ∫ V, defect (linkValue (2 * m) Q V) p.1.1 p.1.2 x ^ 2 ∂iterLaw a β j m ≤
        (16 * ((1 + 16 * e) * (1 + 12 * e))) ^ j * (21 * (-Real.log (SU2GaussianMass.mass (6 * β)) / β))
  | 0, m, _, x => by
    simpa using law_plane_total m β hβ x
  | j + 1, m, _, x => by
    haveI := iterLaw_probability a ha β j (2 * m)
    have hB := continuous_blockCfg (2 * m) a ha
    have h1 := mean_plane_total (2 * m) a ha e he0 he (iterLaw a β j (2 * m)) (iterLaw_tInv a ha β j (2 * m)) x 0
    have h2 := iterLaw_mean_total a ha e he0 he β hβ j (2 * m) 0
    have e1 (p : Plane) : ∫ V, defect (linkValue (2 * m) Q V) p.1.1 p.1.2 x ^ 2 ∂iterLaw a β (j + 1) m =
        ∫ U, defect (linkValue (2 * m) Q (blockCfg (2 * m) a U)) p.1.1 p.1.2 x ^ 2 ∂iterLaw a β j (2 * m) := by
      change ∫ V, defect (linkValue (2 * m) Q V) p.1.1 p.1.2 x ^ 2 ∂(iterLaw a β j (2 * m)).map (blockCfg (2 * m) a) = _
      rw [integral_map hB.measurable.aemeasurable ((continuous_defect (2 * m) _ _ x).pow 2).aestronglyMeasurable]
    simp only [e1]
    have hK : 0 ≤ 16 * ((1 + 16 * e) * (1 + 12 * e)) := by positivity
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 hK).trans (le_of_eq ?_))
    rw [pow_succ]
    ring

end MeanTotalLaw

/-! ### The mechanism for time staples, as algebra about one covariance

This has no link to `blockCfg` or to the Wilson law. Take the correlator `l^|s - t|` with `0 < l < 1`, which is reflection
positive (`chain_rp`). Smear it across time at the even sites, `V_s = φ(2s) + α (φ(2s + 1) + φ(2s - 1))`, the linear form of a
spatial link with a time staple. The form `E[(a V_0 + b V_{-1}) (a V_0 + b V_1)]`, which reflection positivity at `s ↦ -s` would
make nonnegative, is then negative for some `a, b`, at every `α > 0` (`smeared_form_negative`). With `α = 0`, the case of `aniso`,
the form is a square (`smeared_zero_rp`). A coarse observable sums aliased modes, so a pure `l` is not directly realised, and
`every α > 0` does not carry over: the exact free ratios for the blocked winding are above `1` at `α = 0.05` and at `α = 0.1`. -/

section Chain

/-- The correlator of one free mode. -/
def chainCov (l : ℝ) (s t : ℤ) : ℝ := l ^ (s - t).natAbs

/-- The unsmeared chain is reflection positive at `s ↦ -s`. -/
theorem chain_rp (l : ℝ) (a : ℕ → ℝ) (m : ℕ) :
    0 ≤ ∑ s ∈ Finset.range m, ∑ t ∈ Finset.range m, a s * a t * chainCov l (s : ℤ) (-(t : ℤ)) := by
  have e : ∑ s ∈ Finset.range m, ∑ t ∈ Finset.range m, a s * a t * chainCov l (s : ℤ) (-(t : ℤ)) =
      (∑ s ∈ Finset.range m, a s * l ^ s) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    have hn : ((s : ℤ) - -(t : ℤ)).natAbs = s + t := by omega
    unfold chainCov
    rw [hn, pow_add]
    ring
  rw [e]
  positivity

/-- The correlator of the smeared variables at the even sites. -/
def smearCov (l α : ℝ) (s t : ℤ) : ℝ :=
  chainCov l (2 * s) (2 * t) +
    α * (chainCov l (2 * s) (2 * t + 1) + chainCov l (2 * s) (2 * t - 1)) +
    α * (chainCov l (2 * s + 1) (2 * t) + chainCov l (2 * s - 1) (2 * t)) +
    α ^ 2 * (chainCov l (2 * s + 1) (2 * t + 1) + chainCov l (2 * s + 1) (2 * t - 1) +
      chainCov l (2 * s - 1) (2 * t + 1) + chainCov l (2 * s - 1) (2 * t - 1))

theorem smear_00 (l α : ℝ) : smearCov l α 0 0 = 1 + 4 * α * l + α ^ 2 * (2 + 2 * l ^ 2) := by
  unfold smearCov chainCov
  norm_num
  ring

theorem smear_10 (l α : ℝ) : smearCov l α 1 0 = (l + α * (1 + l ^ 2)) ^ 2 := by
  unfold smearCov chainCov
  norm_num
  ring

theorem smear_1m1 (l α : ℝ) : smearCov l α 1 (-1) = l ^ 2 * (l + α * (1 + l ^ 2)) ^ 2 := by
  unfold smearCov chainCov
  norm_num
  ring

/-- For a single covariance `l^|s - t|` with `0 < l < 1`, the smeared form is negative for some `a, b`, at every `α > 0`. This is
algebra, and is not a statement about blocked observables, which sum aliased modes. -/
theorem smeared_form_negative (l α : ℝ) (h0 : 0 < l) (h1 : l < 1) (hα : 0 < α) :
    ∃ a b : ℝ, a ^ 2 * smearCov l α 0 0 + 2 * (a * b) * smearCov l α 1 0 + b ^ 2 * smearCov l α 1 (-1) < 0 := by
  rw [smear_00, smear_10, smear_1m1]
  set K := l + α * (1 + l ^ 2) with hK
  set D := 1 + 4 * α * l + α ^ 2 * (2 + 2 * l ^ 2) with hD
  have hKp : 0 < K := by positivity
  have hDp : 0 < D := by positivity
  refine ⟨-K ^ 2, D, ?_⟩
  have hneg : D * l ^ 2 - K ^ 2 = (l ^ 2 - 1) * (2 * α * l + α ^ 2 * (1 + l ^ 2)) := by
    rw [hD, hK]
    ring
  have hlt : l ^ 2 - 1 < 0 := by nlinarith only [h0, h1]
  have hpos : 0 < 2 * α * l + α ^ 2 * (1 + l ^ 2) := by positivity
  have h3 : D * l ^ 2 - K ^ 2 < 0 := by
    rw [hneg]
    exact mul_neg_of_neg_of_pos hlt hpos
  have e : (-K ^ 2) ^ 2 * D + 2 * (-K ^ 2 * D) * K ^ 2 + D ^ 2 * (l ^ 2 * K ^ 2) =
      K ^ 2 * D * (D * l ^ 2 - K ^ 2) := by ring
  rw [e]
  exact mul_neg_of_pos_of_neg (by positivity) h3

/-- With no smearing the form is a square. -/
theorem smeared_zero_rp (l a b : ℝ) :
    0 ≤ a ^ 2 * smearCov l 0 0 0 + 2 * (a * b) * smearCov l 0 1 0 + b ^ 2 * smearCov l 0 1 (-1) := by
  rw [smear_00, smear_10, smear_1m1]
  have : a ^ 2 * (1 + 4 * 0 * l + 0 ^ 2 * (2 + 2 * l ^ 2)) + 2 * (a * b) * (l + 0 * (1 + l ^ 2)) ^ 2 +
      b ^ 2 * (l ^ 2 * (l + 0 * (1 + l ^ 2)) ^ 2) = (a + b * l ^ 2) ^ 2 := by ring
  rw [this]
  positivity

end Chain

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockStep
