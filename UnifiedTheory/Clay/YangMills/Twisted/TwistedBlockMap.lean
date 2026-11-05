/- A block-spin map on the twisted lattice, by a factor 2. The new link is the unit-quaternion projection
of the two-link line plus `α` times the six staples, each staple corrected by the center sign of the
two plaquettes it crosses, so the twist does not cancel the sum. The map is gauge covariant, fixes the
flat field's lines, and stays within `4δ` of the line when the nearby defects are at most `δ < 1/2`. The
blocked plaquette then has defect at most `20δ`, measured against the total center sign of its cells.

This is a worst-case bound, and a smooth field really does scale its defect by 4. It does not show the
statistical stability of the defects under blocking. It says nothing about the law of the blocked field. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedCovariant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockMap
noncomputable section
open PeriodicLattice4 TwistedFlat TwistedHessian TwistedStability TwistedLandau TwistedCovariant
open WilsonSingleLinkStaples (Q)
open scoped Quaternion

variable {N : ℕ} [NeZero N]

theorem d_comm (g h : Q) : d g h = d h g := norm_sub_rev _ _

theorem z_comm (k : ℕ) (g : Q) : Commute ((ω : Q) ^ k) g := (ω_commute g).pow_left k

theorem z_sq (k : ℕ) : (ω : Q) ^ k * ω ^ k = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, sq, TwistedTransfer.ω_mul_ω, one_pow]

/-- The center exponent and the defect of the plaquette in the plane of `μ, ν`, in either order. -/
def kk (μ ν : Fin 4) (x : Vertex N) : ℕ := if μ < ν then twistExp μ ν x else twistExp ν μ x

def cd (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) : ℝ :=
  if μ < ν then defect U μ ν x else defect U ν μ x

theorem d_quot (A B : Q) (k : ℕ) : d (A * B⁻¹) (ω ^ k) = d A (ω ^ k * B) := by
  have := d_mul_right B (A * B⁻¹) (ω ^ k)
  rw [inv_mul_cancel_right] at this
  exact this.symm

theorem d_swap (A B : Q) (k : ℕ) : d A (ω ^ k * B) = d B (ω ^ k * A) := by
  have h := d_mul_left ((ω : Q) ^ k) A (ω ^ k * B)
  rw [← mul_assoc, z_sq, one_mul] at h
  rw [← h, d_comm]

/-- Moving a link across a cell in either orientation. -/
theorem cell_rel (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (h : μ ≠ ν) (x : Vertex N) :
    d (U x ν * U (step N x ν) μ) (ω ^ kk μ ν x * (U x μ * U (step N x μ) ν)) = cd U μ ν x := by
  unfold kk cd
  rcases lt_or_gt_of_ne h with hl | hl
  · simp only [hl, if_true]
    rw [d_swap]
    have e : U x μ * U (step N x μ) ν * (U (step N x ν) μ)⁻¹ * (U x ν)⁻¹ =
        (U x μ * U (step N x μ) ν) * (U x ν * U (step N x ν) μ)⁻¹ := by group
    change _ = d (U x μ * U (step N x μ) ν * (U (step N x ν) μ)⁻¹ * (U x ν)⁻¹) _
    rw [e, d_quot]
  · have hn : ¬ μ < ν := not_lt.2 hl.le
    simp only [hn, if_false]
    have e : U x ν * U (step N x ν) μ * (U (step N x μ) ν)⁻¹ * (U x μ)⁻¹ =
        (U x ν * U (step N x ν) μ) * (U x μ * U (step N x μ) ν)⁻¹ := by group
    change _ = d (U x ν * U (step N x ν) μ * (U (step N x μ) ν)⁻¹ * (U x μ)⁻¹) _
    rw [e, d_quot]

/-! ### Staples -/

theorem up_close (a b a' e c r f z0 z1 : Q) (hz0 : ∀ g, Commute z0 g) (hz1 : ∀ g, Commute z1 g)
    (h00 : z0 * z0 = 1) (h11 : z1 * z1 = 1) :
    d (z0 * z1 * (e * c * r * f⁻¹)) (a * a') ≤ d (e * c) (z0 * (a * b)) + d (b * r) (z1 * (a' * f)) := by
  have hz : z0 * z1 * z0 = z1 := by rw [(hz0 z1).eq, mul_assoc, h00, mul_one]
  have hz' : z1 * a * z1 = a := by rw [(hz1 a).eq, mul_assoc, h11, mul_one]
  set M := z1 * (a * b * r * f⁻¹) with hM
  have s1 : d (z0 * z1 * (e * c * r * f⁻¹)) M = d (e * c) (z0 * (a * b)) := by
    have e1 : z0 * z1 * (e * c * r * f⁻¹) = (z0 * z1) * (e * c) * (r * f⁻¹) := by group
    have e2 : M = (z0 * z1) * (z0 * (a * b)) * (r * f⁻¹) := by
      have : (z0 * z1) * (z0 * (a * b)) * (r * f⁻¹) = (z0 * z1 * z0) * (a * b) * (r * f⁻¹) := by group
      rw [this, hz, hM]
      group
    rw [e1, e2, d_mul_right, d_mul_left]
  have s2 : d M (a * a') = d (b * r) (z1 * (a' * f)) := by
    have e1 : M = (z1 * a) * (b * r) * f⁻¹ := by
      rw [hM]
      group
    have e2 : a * a' = (z1 * a) * (z1 * (a' * f)) * f⁻¹ := by
      have : (z1 * a) * (z1 * (a' * f)) * f⁻¹ = (z1 * a * z1) * a' * (f * f⁻¹) := by group
      rw [this, hz', mul_inv_cancel, mul_one]
    rw [e1]
    nth_rewrite 1 [e2]
    rw [d_mul_right, d_mul_left]
  have t := d_triangle (z0 * z1 * (e * c * r * f⁻¹)) M (a * a')
  linarith only [t, s1, s2]

theorem down_close (e a₀ a₁ f c0 c1 b0 z0 z1 : Q) (hz0 : ∀ g, Commute z0 g)
    (hz1 : ∀ g, Commute z1 g) :
    d (z0 * z1 * (e⁻¹ * a₀ * a₁ * f)) (c0 * c1) ≤
      d (e * c0) (z0 * (a₀ * b0)) + d (b0 * c1) (z1 * (a₁ * f)) := by
  set M := z0 * (e⁻¹ * a₀ * b0) * c1 with hM
  have s1 : d (z0 * z1 * (e⁻¹ * a₀ * a₁ * f)) M = d (b0 * c1) (z1 * (a₁ * f)) := by
    have e1 : z0 * z1 * (e⁻¹ * a₀ * a₁ * f) = (z0 * (e⁻¹ * a₀)) * (z1 * (a₁ * f)) := by
      have : z1 * (e⁻¹ * a₀) = (e⁻¹ * a₀) * z1 := (hz1 _).eq
      calc z0 * z1 * (e⁻¹ * a₀ * a₁ * f) = z0 * (z1 * (e⁻¹ * a₀)) * (a₁ * f) := by group
        _ = z0 * ((e⁻¹ * a₀) * z1) * (a₁ * f) := by rw [this]
        _ = _ := by group
    have e2 : M = (z0 * (e⁻¹ * a₀)) * (b0 * c1) := by
      rw [hM]
      group
    rw [e1, e2, d_mul_left, d_comm]
  have s2 : d M (c0 * c1) = d (e * c0) (z0 * (a₀ * b0)) := by
    have hc : e * z0 * e⁻¹ = z0 := by
      rw [← (hz0 e).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hM, d_mul_right, ← d_mul_left e, d_comm]
    have : e * (z0 * (e⁻¹ * a₀ * b0)) = (e * z0 * e⁻¹) * (a₀ * b0) := by group
    rw [this, hc]
  have t := d_triangle (z0 * z1 * (e⁻¹ * a₀ * a₁ * f)) M (c0 * c1)
  linarith only [t, s1, s2]

/-- The two-link line. -/
def lineU (U : Vertex N → Fin 4 → Q) (μ : Fin 4) (x : Vertex N) : Q := U x μ * U (step N x μ) μ

/-- The upper staple, corrected by the center sign of its two cells. -/
def sUp (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) : Q :=
  ω ^ kk μ ν x * ω ^ kk μ ν (step N x μ) *
    (U x ν * U (step N x ν) μ * U (step N (step N x ν) μ) μ * (U (step N (step N x μ) μ) ν)⁻¹)

/-- The lower staple, based at `y`, the site below the line. -/
def sDownY (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (y : Vertex N) : Q :=
  ω ^ kk μ ν y * ω ^ kk μ ν (step N y μ) *
    ((U y ν)⁻¹ * U y μ * U (step N y μ) μ * U (step N (step N y μ) μ) ν)

def sDown (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) : Q := sDownY U μ ν (back x ν)

theorem sUp_close (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (h : μ ≠ ν) (x : Vertex N) :
    d (sUp U μ ν x) (lineU U μ x) ≤ cd U μ ν x + cd U μ ν (step N x μ) := by
  have c1 := cell_rel U μ ν h x
  have c2 := cell_rel U μ ν h (step N x μ)
  rw [step_step_comm x μ ν] at c2
  rw [← c1, ← c2]
  exact up_close _ (U (step N x μ) ν) _ _ _ _ _ _ _ (z_comm _) (z_comm _) (z_sq _) (z_sq _)

theorem sDownY_close (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (h : μ ≠ ν) (y : Vertex N) :
    d (sDownY U μ ν y) (lineU U μ (step N y ν)) ≤ cd U μ ν y + cd U μ ν (step N y μ) := by
  have c1 := cell_rel U μ ν h y
  have c2 := cell_rel U μ ν h (step N y μ)
  rw [step_step_comm y μ ν] at c2
  rw [← c1, ← c2]
  exact down_close _ _ _ _ _ _ (U (step N y μ) ν) _ _ (z_comm _) (z_comm _)

theorem sDown_close (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (h : μ ≠ ν) (x : Vertex N) :
    d (sDown U μ ν x) (lineU U μ x) ≤ cd U μ ν (back x ν) + cd U μ ν (step N (back x ν) μ) := by
  have := sDownY_close U μ ν h (back x ν)
  rwa [step_back] at this

/-! ### Projection to the unit quaternions -/

open Classical in
/-- The unit quaternion in the direction of `w`. -/
def proj (w : ℍ[ℝ]) : Q :=
  if h : w = 0 then 1 else
    ⟨‖w‖⁻¹ • w, by
      have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 h
      have hq : ((‖w‖⁻¹ * ‖w‖⁻¹ * Quaternion.normSq w : ℝ) : ℍ[ℝ]) = 1 := by
        rw [Quaternion.normSq_eq_norm_mul_self]
        have : ‖w‖⁻¹ * ‖w‖⁻¹ * (‖w‖ * ‖w‖) = 1 := by field_simp
        rw [this]
        rfl
      rw [Unitary.mem_iff, Quaternion.star_smul, smul_mul_smul_comm, smul_mul_smul_comm,
        Quaternion.star_mul_self, Quaternion.self_mul_star]
      have hc (a b : ℝ) : a • ((b : ℝ) : ℍ[ℝ]) = ((a * b : ℝ) : ℍ[ℝ]) := by
        ext <;> simp
      rw [hc, hq]
      exact ⟨rfl, rfl⟩⟩

theorem proj_coe (w : ℍ[ℝ]) (h : w ≠ 0) : ((proj w : Q) : ℍ[ℝ]) = ‖w‖⁻¹ • w := by
  unfold proj
  rw [dif_neg h]

/-- The projection stays near a unit quaternion that the vector is near. -/
theorem proj_close (u : Q) (w : ℍ[ℝ]) (c η : ℝ) (hc : 0 < c) (hη : η < c)
    (h : ‖w - c • (u : ℍ[ℝ])‖ ≤ η) : w ≠ 0 ∧ d (proj w) u ≤ 2 * η / c := by
  have hcu : ‖c • (u : ℍ[ℝ])‖ = c := by
    rw [norm_smul, norm_coe, mul_one, Real.norm_of_nonneg hc.le]
  have hlow : c - η ≤ ‖w‖ := by
    have := norm_sub_norm_le (c • (u : ℍ[ℝ])) w
    rw [hcu, norm_sub_rev] at this
    linarith only [this, h]
  have hw : 0 < ‖w‖ := by linarith only [hlow, hη]
  have hw0 : w ≠ 0 := norm_pos_iff.1 hw
  refine ⟨hw0, ?_⟩
  have hup : |‖w‖ - c| ≤ η := by
    have := abs_norm_sub_norm_le w (c • (u : ℍ[ℝ]))
    rw [hcu] at this
    exact this.trans h
  unfold d
  rw [proj_coe w hw0]
  have split : ‖w‖⁻¹ • w - (u : ℍ[ℝ]) = (‖w‖⁻¹ - c⁻¹) • w + c⁻¹ • (w - c • (u : ℍ[ℝ])) := by
    rw [sub_smul, smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    abel
  rw [split]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  have e1 : |‖w‖⁻¹ - c⁻¹| * ‖w‖ = |‖w‖ - c| / c := by
    have : ‖w‖⁻¹ - c⁻¹ = -(‖w‖ - c) / (‖w‖ * c) := by
      field_simp
      ring
    rw [this, abs_div, abs_neg, abs_of_pos (mul_pos hw hc)]
    field_simp
  rw [e1]
  have e2 : c⁻¹ * ‖w - c • (u : ℍ[ℝ])‖ ≤ η / c := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have e3 : |‖w‖ - c| / c ≤ η / c := div_le_div_of_nonneg_right hup hc.le
  have e4 : 2 * η / c = η / c + η / c := by ring
  rw [e4]
  linarith only [e2, e3]

/-- The projection is equivariant under left and right multiplication. -/
theorem proj_mul (g h : Q) (w : ℍ[ℝ]) (hw : w ≠ 0) :
    proj ((g : ℍ[ℝ]) * w * (h : ℍ[ℝ])) = g * proj w * h := by
  have hn : ‖(g : ℍ[ℝ]) * w * (h : ℍ[ℝ])‖ = ‖w‖ := by
    rw [norm_mul, norm_mul, norm_coe, norm_coe, one_mul, mul_one]
  have hne : (g : ℍ[ℝ]) * w * (h : ℍ[ℝ]) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact hw (norm_eq_zero.1 hn.symm)
  apply Subtype.ext
  rw [proj_coe _ hne, hn]
  change _ = (g : ℍ[ℝ]) * ((proj w : Q) : ℍ[ℝ]) * (h : ℍ[ℝ])
  rw [proj_coe w hw, mul_smul_comm, smul_mul_assoc]

/-! ### The block map -/

/-- The sum of the line and the signed staples. -/
def blockSum (U : Vertex N → Fin 4 → Q) (α : ℝ) (μ : Fin 4) (x : Vertex N) : ℍ[ℝ] :=
  (lineU U μ x : ℍ[ℝ]) + α • ∑ ν, if ν = μ then 0 else
    ((sUp U μ ν x : ℍ[ℝ]) + (sDown U μ ν x : ℍ[ℝ]))

/-- The blocked link, from `x` to `x + 2μ`. -/
def blockLink (U : Vertex N → Fin 4 → Q) (α : ℝ) (x : Vertex N) (μ : Fin 4) : Q :=
  proj (blockSum U α μ x)

/-- The cells that the blocked link at `x` depends on have defect at most `δ`. -/
def LinkGood (U : Vertex N → Fin 4 → Q) (δ : ℝ) (x : Vertex N) (μ : Fin 4) : Prop :=
  ∀ ν, ν ≠ μ → cd U μ ν x ≤ δ ∧ cd U μ ν (step N x μ) ≤ δ ∧ cd U μ ν (back x ν) ≤ δ ∧
    cd U μ ν (step N (back x ν) μ) ≤ δ

theorem blockSum_sub (U : Vertex N → Fin 4 → Q) (α : ℝ) (hα : 0 ≤ α) (δ : ℝ) (μ : Fin 4)
    (x : Vertex N) (hg : LinkGood U δ x μ) :
    ‖blockSum U α μ x - (1 + 6 * α) • (lineU U μ x : ℍ[ℝ])‖ ≤ 12 * α * δ := by
  set ℓ : ℍ[ℝ] := (lineU U μ x : ℍ[ℝ]) with hℓ
  let E : Fin 4 → ℍ[ℝ] := fun ν => if ν = μ then 0 else
    (((sUp U μ ν x : ℍ[ℝ]) - ℓ) + ((sDown U μ ν x : ℍ[ℝ]) - ℓ))
  have hE (ν : Fin 4) : ‖E ν‖ ≤ if ν = μ then 0 else 4 * δ := by
    by_cases h : ν = μ
    · simp [E, h]
    · simp only [E, h, if_false]
      obtain ⟨g1, g2, g3, g4⟩ := hg ν h
      have u := sUp_close U μ ν (Ne.symm h) x
      have v := sDown_close U μ ν (Ne.symm h) x
      refine (norm_add_le _ _).trans ?_
      have u' : ‖(sUp U μ ν x : ℍ[ℝ]) - ℓ‖ = d (sUp U μ ν x) (lineU U μ x) := rfl
      have v' : ‖(sDown U μ ν x : ℍ[ℝ]) - ℓ‖ = d (sDown U μ ν x) (lineU U μ x) := rfl
      rw [u', v']
      linarith only [u, v, g1, g2, g3, g4]
  have hsum : ∑ ν, (if ν = μ then (4 * δ : ℝ) * 0 else 4 * δ) = 12 * δ := by
    fin_cases μ <;> simp [Fin.sum_univ_four] <;> ring
  have hsplit : blockSum U α μ x - (1 + 6 * α) • ℓ = α • ∑ ν, E ν := by
    have hl : (∑ ν : Fin 4, if ν = μ then (0 : ℍ[ℝ]) else (ℓ + ℓ)) = (6 : ℝ) • ℓ := by
      fin_cases μ <;> simp [Fin.sum_univ_four] <;> (ext <;> simp <;> ring)
    have hE' : ∑ ν, E ν = (∑ ν : Fin 4, if ν = μ then (0 : ℍ[ℝ]) else
        ((sUp U μ ν x : ℍ[ℝ]) + (sDown U μ ν x : ℍ[ℝ]))) - (6 : ℝ) • ℓ := by
      rw [← hl, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ν _ => ?_
      by_cases h : ν = μ
      · simp [E, h]
      · simp only [E, h, if_false]
        abel
    rw [hE', smul_sub, smul_smul]
    unfold blockSum
    rw [add_smul, one_smul, mul_comm α 6]
    abel
  rw [hsplit, norm_smul, Real.norm_of_nonneg hα]
  have hb : ‖∑ ν, E ν‖ ≤ 12 * δ := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun ν _ => hE ν).trans (le_of_eq ?_)
    rw [← hsum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp
  have := mul_le_mul_of_nonneg_left hb hα
  linarith only [this]

/-- **The blocked link stays near the line, for every weight `α ≥ 0`.** -/
theorem blockLink_close (U : Vertex N → Fin 4 → Q) (α : ℝ) (hα : 0 ≤ α) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ < 1 / 2) (μ : Fin 4) (x : Vertex N) (hg : LinkGood U δ x μ) :
    blockSum U α μ x ≠ 0 ∧ d (blockLink U α x μ) (lineU U μ x) ≤ 4 * δ := by
  have hc : 0 < 1 + 6 * α := by positivity
  have hs := blockSum_sub U α hα δ μ x hg
  have hη : 12 * α * δ < 1 + 6 * α := by nlinarith only [hα, hδ, hδ0]
  obtain ⟨h0, h1⟩ := proj_close (lineU U μ x) _ _ _ hc hη hs
  refine ⟨h0, h1.trans ?_⟩
  rw [div_le_iff₀ hc]
  nlinarith only [mul_nonneg hα hδ0, hδ0]

/-- The flat field's blocked link is its line. -/
theorem blockLink_flat (α : ℝ) (hα : 0 ≤ α) (μ : Fin 4) (x : Vertex N) :
    blockLink (flatLink (N := N)) α x μ = lineU flatLink μ x := by
  have hd (y : Vertex N) (a b : Fin 4) (hab : a < b) : defect (flatLink (N := N)) a b y = 0 := by
    unfold defect
    rw [flatLink_flat y a b hab]
    unfold d
    rw [sub_self, norm_zero]
  have hz (y : Vertex N) (a b : Fin 4) (hne : a ≠ b) : cd (flatLink (N := N)) a b y ≤ 0 := by
    unfold cd
    split_ifs with hab
    · exact (hd y a b hab).le
    · exact (hd y b a (lt_of_le_of_ne (not_lt.1 hab) hne.symm)).le
  have hg : LinkGood (flatLink (N := N)) 0 x μ := fun ν hν =>
    ⟨hz _ _ _ hν.symm, hz _ _ _ hν.symm, hz _ _ _ hν.symm, hz _ _ _ hν.symm⟩
  have h := (blockLink_close flatLink α hα 0 le_rfl (by norm_num) μ x hg).2
  rw [mul_zero] at h
  have h0 : d (blockLink flatLink α x μ) (lineU flatLink μ x) = 0 := le_antisymm h (d_nonneg _ _)
  apply Subtype.ext
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)

/-! ### Gauge covariance -/

theorem lineU_act (g : Vertex N → Q) (U : Vertex N → Fin 4 → Q) (μ : Fin 4) (x : Vertex N) :
    lineU (act g U) μ x = g x * lineU U μ x * (g (step N (step N x μ) μ))⁻¹ := by
  simp only [lineU, act]
  group

theorem sUp_act (g : Vertex N → Q) (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) :
    sUp (act g U) μ ν x = g x * sUp U μ ν x * (g (step N (step N x μ) μ))⁻¹ := by
  have hs : step N (step N (step N x ν) μ) μ = step N (step N (step N x μ) μ) ν := by
    simp only [step]
    abel
  simp only [sUp, act, hs]
  generalize hz : (ω : Q) ^ kk μ ν x * ω ^ kk μ ν (step N x μ) = z
  have hc : Commute z (g x) := by
    rw [← hz]
    exact (z_comm _ _).mul_left (z_comm _ _)
  rw [← mul_assoc (g x) z, ← hc.eq]
  group

theorem sDownY_act (g : Vertex N → Q) (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (y : Vertex N) :
    sDownY (act g U) μ ν y =
      g (step N y ν) * sDownY U μ ν y * (g (step N (step N (step N y μ) μ) ν))⁻¹ := by
  simp only [sDownY, act]
  generalize hz : (ω : Q) ^ kk μ ν y * ω ^ kk μ ν (step N y μ) = z
  have hc : Commute z (g (step N y ν)) := by
    rw [← hz]
    exact (z_comm _ _).mul_left (z_comm _ _)
  rw [← mul_assoc (g (step N y ν)) z, ← hc.eq]
  group

theorem sDown_act (g : Vertex N → Q) (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) :
    sDown (act g U) μ ν x = g x * sDown U μ ν x * (g (step N (step N x μ) μ))⁻¹ := by
  have h := sDownY_act g U μ ν (back x ν)
  have hs : step N (step N (step N (back x ν) μ) μ) ν = step N (step N x μ) μ := by
    have : step N (step N (step N (back x ν) μ) μ) ν = step N (step N (step N (back x ν) ν) μ) μ := by
      simp only [step]
      abel
    rw [this, step_back]
  rw [hs, step_back] at h
  exact h

theorem blockSum_act (g : Vertex N → Q) (U : Vertex N → Fin 4 → Q) (α : ℝ) (μ : Fin 4)
    (x : Vertex N) :
    blockSum (act g U) α μ x =
      (g x : ℍ[ℝ]) * blockSum U α μ x * ((g (step N (step N x μ) μ))⁻¹ : Q) := by
  set G : ℍ[ℝ] := (g x : ℍ[ℝ])
  set H : ℍ[ℝ] := (((g (step N (step N x μ) μ))⁻¹ : Q) : ℍ[ℝ])
  have c (u : Q) : ((g x * u * (g (step N (step N x μ) μ))⁻¹ : Q) : ℍ[ℝ]) = G * u * H := rfl
  unfold blockSum
  simp only [lineU_act, sUp_act, sDown_act, c]
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 2
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases h : ν = μ
  · simp [h]
  · simp only [h, if_false, mul_add, add_mul]

/-- **Gauge covariance of the blocked link.** Only the gauge transformation at the two ends enters. -/
theorem blockLink_act (g : Vertex N → Q) (U : Vertex N → Fin 4 → Q) (α : ℝ) (x : Vertex N) (μ : Fin 4)
    (h : blockSum U α μ x ≠ 0) :
    blockLink (act g U) α x μ = g x * blockLink U α x μ * (g (step N (step N x μ) μ))⁻¹ := by
  unfold blockLink
  rw [blockSum_act, proj_mul _ _ _ h]

/-! ### The covariant split of a fluctuation -/

/-- **Rough and smooth parts of a fluctuation at the block scale.** With all defects at most `δ`, a field
`φ` splits as its `U`-covariant block average plus a remainder. The remainder is at most `L` times the
total gradient of `φ`. The average has gradient at most `2/L + 6Lδ` times `φ`, and at most the gradient
of `φ` up to `8Lδ`. All of it is uniform in the lattice size. It is the linear form of a background and
fluctuation split, in `L²`, and does not separate the two in the measure. -/
theorem cov_split (U : Vertex N → Fin 4 → Q) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ δ) (L : ℕ) (hL : 1 ≤ L) (φ : QField N) (i : Fin 4) :
    ‖φ - BlockShifts.blockAvg (covShift U) L φ‖ ≤ L * ∑ ν, ‖(covShift U ν).D φ‖ ∧
      ‖(covShift U i).D (BlockShifts.blockAvg (covShift U) L φ)‖ ≤
        (2 / (L : ℝ) + 3 * L * (2 * δ)) * ‖φ‖ ∧
      ‖(covShift U i).D (BlockShifts.blockAvg (covShift U) L φ)‖ ≤
        ‖(covShift U i).D φ‖ + 4 * L * (2 * δ) * ‖φ‖ := by
  have h := BlockShifts.smooth_grad (covShift U) L hL (2 * δ) (by positivity)
    (fun μ ν x => cov_comm U δ hδ0 hδ μ ν x) φ i
  exact ⟨BlockShifts.sub_blockAvg_le _ L hL φ, h.1, h.2⟩

/-! ### The blocked plaquette -/

theorem mul_close (A B z w : Q) : d (A * B) (z * w) ≤ d A z + d B w := by
  have t := d_triangle (A * B) (z * B) (z * w)
  rw [d_mul_right, d_mul_left] at t
  exact t

theorem conj_close (g P : Q) (k : ℕ) : d (g * P * g⁻¹) (ω ^ k) = d P (ω ^ k) := by
  have hc : g * (ω : Q) ^ k * g⁻¹ = ω ^ k := by
    rw [← (z_comm k g).eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [← hc, d_mul_right, d_mul_left, hc]

/-- The doubled plaquette as a product of conjugates of its four cells. -/
theorem loop2 (h00 h10 h01 h11 h02 h12 v00 v01 v10 v11 v20 v21 : Q) :
    (h00 * h10) * (v20 * v21) * (h02 * h12)⁻¹ * (v00 * v01)⁻¹ =
      (h00 * (h10 * v20 * h11⁻¹ * v10⁻¹) * h00⁻¹) *
        ((h00 * v10) * (h11 * v21 * h12⁻¹ * v11⁻¹) * (h00 * v10)⁻¹) *
        (h00 * v10 * h01⁻¹ * v00⁻¹) * (v00 * (h01 * v11 * h02⁻¹ * v01⁻¹) * v00⁻¹) := by
  group

/-- The total center sign of the four cells of a doubled plaquette. -/
def cellSign (μ ν : Fin 4) (x : Vertex N) : Q :=
  ω ^ twistExp μ ν (step N x μ) * ω ^ twistExp μ ν (step N (step N x μ) ν) * ω ^ twistExp μ ν x *
    ω ^ twistExp μ ν (step N x ν)

/-- The doubled line plaquette has defect at most the sum of its four cells. -/
theorem line_loop (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) :
    d (lineU U μ x * lineU U ν (step N (step N x μ) μ) * (lineU U μ (step N (step N x ν) ν))⁻¹ *
        (lineU U ν x)⁻¹) (cellSign μ ν x) ≤
      defect U μ ν (step N x μ) + defect U μ ν (step N (step N x μ) ν) + defect U μ ν x +
        defect U μ ν (step N x ν) := by
  have hs1 : step N (step N (step N x μ) ν) μ = step N (step N (step N x μ) μ) ν :=
    step_step_comm (step N x μ) ν μ
  have hs2 : step N (step N (step N x μ) ν) ν = step N (step N (step N x ν) ν) μ := by
    simp only [step]
    abel
  have hs3 : step N (step N x ν) μ = step N (step N x μ) ν := (step_step_comm x μ ν).symm
  have d10 : d (U (step N x μ) μ * U (step N (step N x μ) μ) ν * (U (step N (step N x μ) ν) μ)⁻¹ *
      (U (step N x μ) ν)⁻¹) (ω ^ twistExp μ ν (step N x μ)) = defect U μ ν (step N x μ) := rfl
  have d11 : d (U (step N (step N x μ) ν) μ * U (step N (step N (step N x μ) μ) ν) ν *
      (U (step N (step N (step N x ν) ν) μ) μ)⁻¹ * (U (step N (step N x μ) ν) ν)⁻¹)
      (ω ^ twistExp μ ν (step N (step N x μ) ν)) = defect U μ ν (step N (step N x μ) ν) := by
    unfold defect
    rw [hs1, hs2]
  have d00 : d (U x μ * U (step N x μ) ν * (U (step N x ν) μ)⁻¹ * (U x ν)⁻¹) (ω ^ twistExp μ ν x) =
      defect U μ ν x := rfl
  have d01 : d (U (step N x ν) μ * U (step N (step N x μ) ν) ν * (U (step N (step N x ν) ν) μ)⁻¹ *
      (U (step N x ν) ν)⁻¹) (ω ^ twistExp μ ν (step N x ν)) = defect U μ ν (step N x ν) := by
    unfold defect
    rw [hs3]
  unfold lineU cellSign
  rw [loop2 (U x μ) (U (step N x μ) μ) (U (step N x ν) μ) (U (step N (step N x μ) ν) μ)
    (U (step N (step N x ν) ν) μ) (U (step N (step N (step N x ν) ν) μ) μ)
    (U x ν) (U (step N x ν) ν) (U (step N x μ) ν) (U (step N (step N x μ) ν) ν)
    (U (step N (step N x μ) μ) ν) (U (step N (step N (step N x μ) μ) ν) ν)]
  refine (mul_close _ _ _ _).trans ?_
  have a := mul_close (U x μ * (U (step N x μ) μ * U (step N (step N x μ) μ) ν *
      (U (step N (step N x μ) ν) μ)⁻¹ * (U (step N x μ) ν)⁻¹) * (U x μ)⁻¹ *
    ((U x μ * U (step N x μ) ν) * (U (step N (step N x μ) ν) μ * U (step N (step N (step N x μ) μ) ν) ν *
      (U (step N (step N (step N x ν) ν) μ) μ)⁻¹ * (U (step N (step N x μ) ν) ν)⁻¹) *
      (U x μ * U (step N x μ) ν)⁻¹))
    (U x μ * U (step N x μ) ν * (U (step N x ν) μ)⁻¹ * (U x ν)⁻¹)
    (ω ^ twistExp μ ν (step N x μ) * ω ^ twistExp μ ν (step N (step N x μ) ν)) (ω ^ twistExp μ ν x)
  have b := mul_close (U x μ * (U (step N x μ) μ * U (step N (step N x μ) μ) ν *
      (U (step N (step N x μ) ν) μ)⁻¹ * (U (step N x μ) ν)⁻¹) * (U x μ)⁻¹)
    ((U x μ * U (step N x μ) ν) * (U (step N (step N x μ) ν) μ * U (step N (step N (step N x μ) μ) ν) ν *
      (U (step N (step N (step N x ν) ν) μ) μ)⁻¹ * (U (step N (step N x μ) ν) ν)⁻¹) *
      (U x μ * U (step N x μ) ν)⁻¹)
    (ω ^ twistExp μ ν (step N x μ)) (ω ^ twistExp μ ν (step N (step N x μ) ν))
  rw [conj_close, conj_close, d10, d11] at b
  rw [d00] at a
  rw [conj_close, d01]
  linarith only [a, b]

/-- **The blocked plaquette.** With the nearby defects at most `δ < 1/2`, its defect against the total
center sign of its cells is at most `20 δ`. A smooth field shows that a factor `4` is unavoidable. -/
theorem blocked_defect (U : Vertex N → Fin 4 → Q) (α : ℝ) (hα : 0 ≤ α) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ < 1 / 2) (μ ν : Fin 4) (x : Vertex N)
    (h1 : LinkGood U δ x μ) (h2 : LinkGood U δ (step N (step N x μ) μ) ν)
    (h3 : LinkGood U δ (step N (step N x ν) ν) μ) (h4 : LinkGood U δ x ν)
    (c1 : defect U μ ν (step N x μ) ≤ δ) (c2 : defect U μ ν (step N (step N x μ) ν) ≤ δ)
    (c3 : defect U μ ν x ≤ δ) (c4 : defect U μ ν (step N x ν) ≤ δ) :
    d (blockLink U α x μ * blockLink U α (step N (step N x μ) μ) ν *
        (blockLink U α (step N (step N x ν) ν) μ)⁻¹ * (blockLink U α x ν)⁻¹) (cellSign μ ν x) ≤
      20 * δ := by
  have b1 := (blockLink_close U α hα δ hδ0 hδ μ x h1).2
  have b2 := (blockLink_close U α hα δ hδ0 hδ ν _ h2).2
  have b3 := (blockLink_close U α hα δ hδ0 hδ μ _ h3).2
  have b4 := (blockLink_close U α hα δ hδ0 hδ ν x h4).2
  have f := TwistedSeams.four (blockLink U α x μ) (blockLink U α (step N (step N x μ) μ) ν)
    (blockLink U α (step N (step N x ν) ν) μ) (blockLink U α x ν) (lineU U μ x)
    (lineU U ν (step N (step N x μ) μ)) (lineU U μ (step N (step N x ν) ν)) (lineU U ν x)
  have l := line_loop U μ ν x
  have t := d_triangle (blockLink U α x μ * blockLink U α (step N (step N x μ) μ) ν *
        (blockLink U α (step N (step N x ν) ν) μ)⁻¹ * (blockLink U α x ν)⁻¹)
    (lineU U μ x * lineU U ν (step N (step N x μ) μ) * (lineU U μ (step N (step N x ν) ν))⁻¹ *
        (lineU U ν x)⁻¹) (cellSign μ ν x)
  linarith only [b1, b2, b3, b4, f, l, t, c1, c2, c3, c4]

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockMap
