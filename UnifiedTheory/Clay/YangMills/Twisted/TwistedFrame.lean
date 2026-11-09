/- Alignment of a nearly anticommuting pair of unit quaternions to `i, j` by one rotation. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedStability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedFrame
noncomputable section
open TwistedFlat TwistedStability
open WilsonSingleLinkStaples (Q)
open scoped Quaternion

/-- A quaternion of unit norm, as an element of `Q`. -/
def mkQ (x : ℍ[ℝ]) (h : Quaternion.normSq x = 1) : Q :=
  ⟨x, by
    rw [Unitary.mem_iff, Quaternion.star_mul_self, Quaternion.self_mul_star, h]
    simp⟩

theorem qI_sq : qI * qI = ω := by
  apply Subtype.ext
  change ((qI : Q) : ℍ[ℝ]) * ((qI : Q) : ℍ[ℝ]) = -1
  ext <;> simp [qI]

theorem qJ_sq : qJ * qJ = ω := by
  apply Subtype.ext
  change ((qJ : Q) : ℍ[ℝ]) * ((qJ : Q) : ℍ[ℝ]) = -1
  ext <;> simp [qJ]

theorem qI_qJ_anti : qI * qJ = ω * (qJ * qI) := by
  apply Subtype.ext
  change ((qI : Q) : ℍ[ℝ]) * ((qJ : Q) : ℍ[ℝ]) = (-1) * (((qJ : Q) : ℍ[ℝ]) * ((qI : Q) : ℍ[ℝ]))
  ext <;> simp [qI, qJ]

theorem coe_sq (u : Q) (h : u * u = ω) : (u : ℍ[ℝ]) * (u : ℍ[ℝ]) = -1 :=
  congrArg Subtype.val h

theorem inv_of_sq (v : Q) (h : v * v = ω) : v⁻¹ = ω * v := by
  have hωω : (ω : Q) * ω = 1 := by
    apply Subtype.ext
    change ((-1 : ℍ[ℝ]) * (-1)) = 1
    simp
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, ((ω_commute v).symm).eq, mul_assoc, h, hωω]

/-- Turning `u` to `v`, given an element `w` anticommuting with `v`. The rotation also fixes any `c`
commuting with both `w` and the product `v * u`. -/
theorem turn (u v w c : Q) (hu : u * u = ω) (hv : v * v = ω) (hw : w * v = ω * (v * w))
    (hvu : (v * u) * c = c * (v * u)) (hwc : w * c = c * w) :
    ∃ r : Q, r * u * r⁻¹ = v ∧ r * c * r⁻¹ = c := by
  by_cases hq : (v : ℍ[ℝ]) * (u : ℍ[ℝ]) = 1
  · -- `u = -v`; conjugate by `w`.
    have huv : u = ω * v := by
      have h1 : v * u = 1 := Subtype.ext hq
      have h2 : u = v⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      rw [h2, inv_of_sq v hv]
    refine ⟨w, ?_, ?_⟩
    · rw [huv]
      have hωω : (ω : Q) * ω = 1 := by
        apply Subtype.ext
        change ((-1 : ℍ[ℝ]) * (-1)) = 1
        simp
      calc w * (ω * v) * w⁻¹ = ω * (w * v) * w⁻¹ := by
            rw [← mul_assoc w, ← (ω_commute w).eq]
            simp only [mul_assoc]
        _ = ω * (ω * (v * w)) * w⁻¹ := by rw [hw]
        _ = (ω * ω) * v := by group
        _ = v := by rw [hωω, one_mul]
    · rw [hwc]
      group
  · set q : ℍ[ℝ] := 1 - (v : ℍ[ℝ]) * (u : ℍ[ℝ]) with hqd
    have hq0 : q ≠ 0 := fun h => hq (by rw [hqd, sub_eq_zero] at h; exact h.symm)
    have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq0
    have hnorm : Quaternion.normSq ((‖q‖⁻¹ : ℝ) • q) = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, norm_smul, norm_inv, norm_norm]
      field_simp
    let r : Q := mkQ ((‖q‖⁻¹ : ℝ) • q) hnorm
    have hrc : ((r : Q) : ℍ[ℝ]) = (‖q‖⁻¹ : ℝ) • q := rfl
    have hcom : q * (u : ℍ[ℝ]) = (v : ℍ[ℝ]) * q := by
      rw [hqd, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, coe_sq u hu, ← mul_assoc,
        coe_sq v hv]
      noncomm_ring
    have hcq : q * (c : ℍ[ℝ]) = (c : ℍ[ℝ]) * q := by
      have h1 : (v : ℍ[ℝ]) * (u : ℍ[ℝ]) * (c : ℍ[ℝ]) = (c : ℍ[ℝ]) * ((v : ℍ[ℝ]) * (u : ℍ[ℝ])) :=
        congrArg Subtype.val hvu
      rw [hqd, sub_mul, mul_sub, one_mul, mul_one, h1]
    refine ⟨r, ?_, ?_⟩
    · have h : r * u = v * r := by
        apply Subtype.ext
        change ((r : Q) : ℍ[ℝ]) * (u : ℍ[ℝ]) = (v : ℍ[ℝ]) * ((r : Q) : ℍ[ℝ])
        rw [hrc, smul_mul_assoc, mul_smul_comm, hcom]
      rw [h]
      group
    · have h : r * c = c * r := by
        apply Subtype.ext
        change ((r : Q) : ℍ[ℝ]) * (c : ℍ[ℝ]) = (c : ℍ[ℝ]) * ((r : Q) : ℍ[ℝ])
        rw [hrc, smul_mul_assoc, mul_smul_comm, hcq]
      rw [h]
      group

/-- An exact anticommuting pair is a rotation of `i, j`. -/
theorem exact_frame (e f : Q) (he : e * e = ω) (hf : f * f = ω) (hef : e * f = ω * (f * e)) :
    ∃ R : Q, R * e * R⁻¹ = qI ∧ R * f * R⁻¹ = qJ := by
  obtain ⟨r₁, h₁, -⟩ := turn e qI qJ 1 he qI_sq (by
    rw [qI_qJ_anti]
    have hωω : (ω : Q) * ω = 1 := by
      apply Subtype.ext
      change ((-1 : ℍ[ℝ]) * (-1)) = 1
      simp
    rw [← mul_assoc, hωω, one_mul]) (by simp) (by simp)
  set f₁ := r₁ * f * r₁⁻¹ with hf₁
  have hf₁sq : f₁ * f₁ = ω := by
    rw [hf₁]
    calc r₁ * f * r₁⁻¹ * (r₁ * f * r₁⁻¹) = r₁ * (f * f) * r₁⁻¹ := by group
      _ = ω := by rw [hf, ((ω_commute r₁).symm).eq]; group
  have hanti : qI * f₁ = ω * (f₁ * qI) := by
    rw [← h₁, hf₁]
    calc r₁ * e * r₁⁻¹ * (r₁ * f * r₁⁻¹) = r₁ * (e * f) * r₁⁻¹ := by group
      _ = r₁ * (ω * (f * e)) * r₁⁻¹ := by rw [hef]
      _ = ω * (r₁ * (f * e) * r₁⁻¹) := by
          rw [← mul_assoc r₁, ← (ω_commute r₁).eq]
          simp only [mul_assoc]
      _ = _ := by group
  have hωω : (ω : Q) * ω = 1 := by
    apply Subtype.ext
    change ((-1 : ℍ[ℝ]) * (-1)) = 1
    simp
  -- `f₁` and `qJ` both anticommute with `qI`, so `J f₁`-type products commute with it.
  have ha : f₁ * qI = ω * (qI * f₁) := by
    rw [hanti, ← mul_assoc, hωω, one_mul]
  have hb : qJ * qI = ω * (qI * qJ) := by
    rw [qI_qJ_anti, ← mul_assoc, hωω, one_mul]
  obtain ⟨r₂, h₂, hc⟩ := turn f₁ qJ qI qI hf₁sq qJ_sq qI_qJ_anti (by
    calc qJ * f₁ * qI = qJ * (f₁ * qI) := mul_assoc _ _ _
      _ = qJ * (ω * (qI * f₁)) := by rw [ha]
      _ = ω * (qJ * qI) * f₁ := by
          rw [← mul_assoc qJ, ← (ω_commute qJ).eq]
          simp only [mul_assoc]
      _ = ω * (ω * (qI * qJ)) * f₁ := by rw [hb]
      _ = (ω * ω) * (qI * (qJ * f₁)) := by simp only [mul_assoc]
      _ = _ := by rw [hωω, one_mul]) rfl
  refine ⟨r₂ * r₁, ?_, ?_⟩
  · calc r₂ * r₁ * e * (r₂ * r₁)⁻¹ = r₂ * (r₁ * e * r₁⁻¹) * r₂⁻¹ := by group
      _ = qI := by rw [h₁]; exact hc
  · calc r₂ * r₁ * f * (r₂ * r₁)⁻¹ = r₂ * f₁ * r₂⁻¹ := by rw [hf₁]; group
      _ = qJ := h₂

/-! ### The nearest exact frame -/

/-- Real-variable data of a nearly anticommuting pair. -/
theorem anti_bounds (a0 a1 a2 a3 b0 b1 b2 b3 κ : ℝ)
    (na : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 = 1) (nb : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2 = 1)
    (h0 : 0 ≤ κ) (h1 : κ ≤ 1)
    (he : (2 * (a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3)) ^ 2 + (2 * (a0 * b1 + b0 * a1)) ^ 2 +
      (2 * (a0 * b2 + b0 * a2)) ^ 2 + (2 * (a0 * b3 + b0 * a3)) ^ 2 ≤ κ ^ 2) :
    4 * a0 ^ 2 ≤ κ ^ 2 ∧ 4 * b0 ^ 2 ≤ κ ^ 2 ∧ (a1 * b1 + a2 * b2 + a3 * b3) ^ 2 ≤ 9 / 16 * κ ^ 2 := by
  set E0 := 2 * (a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3) with hE0
  set E1 := 2 * (a0 * b1 + b0 * a1) with hE1
  set E2 := 2 * (a0 * b2 + b0 * a2) with hE2
  set E3 := 2 * (a0 * b3 + b0 * a3) with hE3
  have hb0 : (2 * b0) ^ 2 ≤ κ ^ 2 := by
    have hid : 2 * b0 = a0 * E0 + a1 * E1 + a2 * E2 + a3 * E3 := by
      rw [hE0, hE1, hE2, hE3]
      linear_combination (-2 * b0) * na
    rw [hid]
    have := cs4 a0 a1 a2 a3 E0 E1 E2 E3
    rw [na, one_mul] at this
    linarith only [this, he]
  have ha0 : (2 * a0) ^ 2 ≤ κ ^ 2 := by
    have hid : 2 * a0 = b0 * E0 + b1 * E1 + b2 * E2 + b3 * E3 := by
      rw [hE0, hE1, hE2, hE3]
      linear_combination (-2 * a0) * nb
    rw [hid]
    have := cs4 b0 b1 b2 b3 E0 E1 E2 E3
    rw [nb, one_mul] at this
    linarith only [this, he]
  have e1 : (2 * a0) ^ 2 = 4 * a0 ^ 2 := by ring
  have e2 : (2 * b0) ^ 2 = 4 * b0 ^ 2 := by ring
  refine ⟨by linarith only [ha0, e1], by linarith only [hb0, e2], ?_⟩
  have hκ2 : κ ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  have hab : (a0 * b0) ^ 2 ≤ κ ^ 2 / 16 := by
    have : (2 * a0) ^ 2 * (2 * b0) ^ 2 ≤ κ ^ 2 * 1 :=
      mul_le_mul ha0 (hb0.trans hκ2) (sq_nonneg _) (sq_nonneg _)
    have e : (2 * a0) ^ 2 * (2 * b0) ^ 2 = 16 * (a0 * b0) ^ 2 := by ring
    linarith only [this, e]
  have hE0sq : E0 ^ 2 ≤ κ ^ 2 := by linarith only [he, sq_nonneg E1, sq_nonneg E2, sq_nonneg E3]
  have hse : a1 * b1 + a2 * b2 + a3 * b3 = a0 * b0 - E0 / 2 := by
    rw [hE0]
    ring
  rw [hse]
  have hq : (a0 * b0 - E0 / 2) ^ 2 ≤ 3 * (a0 * b0) ^ 2 + 3 / 2 * (E0 / 2) ^ 2 := by
    nlinarith only [sq_nonneg (2 * (a0 * b0) + E0 / 2)]
  have he2 : (E0 / 2) ^ 2 = E0 ^ 2 / 4 := by ring
  linarith only [hq, hab, hE0sq, he2]

theorem imag_sq (p q r : ℝ) (h : p ^ 2 + q ^ 2 + r ^ 2 = 1) :
    (⟨0, p, q, r⟩ : ℍ[ℝ]) * ⟨0, p, q, r⟩ = -1 := by
  ext <;> simp <;> nlinarith only [h]

theorem imag_anti (p q r u v w : ℝ) (h : p * u + q * v + r * w = 0) :
    (⟨0, p, q, r⟩ : ℍ[ℝ]) * ⟨0, u, v, w⟩ = (-1) * ((⟨0, u, v, w⟩ : ℍ[ℝ]) * ⟨0, p, q, r⟩) := by
  ext <;> simp <;> nlinarith only [h]

/-- Normalization of a nonzero imaginary quaternion: distance bound to a unit quaternion `x`
with the same imaginary direction after removing a part `y` orthogonal to it. -/
theorem exists_frame_pair (a b : Q) (κ : ℝ) (h0 : 0 ≤ κ) (h12 : κ ≤ 1 / 2)
    (hab : d (a * b) (ω * (b * a)) ≤ κ) :
    ∃ e f : Q, e * e = ω ∧ f * f = ω ∧ e * f = ω * (f * e) ∧ d a e ≤ κ ∧ d b f ≤ 2 * κ := by
  have h1 : κ ≤ 1 := by linarith only [h12]
  have hκ4 : κ ^ 2 ≤ 1 / 4 := by nlinarith only [h0, h12]
  have na := unit_normSq a
  have nb := unit_normSq b
  have sqd := pow_le_pow_left₀ (d_nonneg _ _) hab 2
  have hcoe : ((a * b : Q) : ℍ[ℝ]) - ((ω * (b * a) : Q) : ℍ[ℝ]) =
      (a : ℍ[ℝ]) * b + (b : ℍ[ℝ]) * a := by
    change (a : ℍ[ℝ]) * b - (-1) * ((b : ℍ[ℝ]) * a) = _
    simp
  unfold d at sqd
  rw [hcoe, sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def'] at sqd
  simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] at sqd
  generalize hA : (a : ℍ[ℝ]) = A at *
  generalize hB : (b : ℍ[ℝ]) = B at *
  obtain ⟨a0, a1, a2, a3⟩ := A
  obtain ⟨b0, b1, b2, b3⟩ := B
  simp only at na nb sqd
  obtain ⟨ha0, hb0, hs⟩ := anti_bounds a0 a1 a2 a3 b0 b1 b2 b3 κ na nb h0 h1 (by
    linarith only [sqd])
  have hκ2 : κ ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  set s := a1 * b1 + a2 * b2 + a3 * b3 with hsd
  set Asq := a1 ^ 2 + a2 ^ 2 + a3 ^ 2 with hAsq
  set Bsq := b1 ^ 2 + b2 ^ 2 + b3 ^ 2 with hBsq
  have hAlow : 3 / 4 ≤ Asq := by linarith only [na, ha0, hκ2]
  set α := Real.sqrt Asq with hα
  have hαsq : α ^ 2 = Asq := Real.sq_sqrt (by linarith only [hAlow])
  have hα0 : 0 < α := Real.sqrt_pos.mpr (by linarith only [hAlow])
  set t := s / α with ht
  have htsq : t ^ 2 ≤ 3 / 4 * κ ^ 2 := by
    rw [ht, div_pow, hαsq, div_le_iff₀ (by linarith only [hAlow])]
    have : 9 / 16 * κ ^ 2 ≤ 3 / 4 * κ ^ 2 * Asq := by
      nlinarith only [mul_le_mul_of_nonneg_left hAlow (by positivity : 0 ≤ κ ^ 2)]
    linarith only [hs, this]
  -- the orthogonal part of `B`
  set c1 := b1 - t * (a1 / α) with hc1
  set c2 := b2 - t * (a2 / α) with hc2
  set c3 := b3 - t * (a3 / α) with hc3
  have hdot : (a1 / α) * c1 + (a2 / α) * c2 + (a3 / α) * c3 = 0 := by
    rw [hc1, hc2, hc3]
    have hαne := hα0.ne'
    have e : (a1 / α) * (b1 - t * (a1 / α)) + (a2 / α) * (b2 - t * (a2 / α)) +
        (a3 / α) * (b3 - t * (a3 / α)) = s / α - t * (Asq / α ^ 2) := by
      rw [hsd, hAsq]
      ring
    rw [e, hαsq, ← ht, div_self (by linarith only [hAlow] : Asq ≠ 0)]
    ring
  have hCsq : c1 ^ 2 + c2 ^ 2 + c3 ^ 2 = Bsq - t ^ 2 := by
    rw [hc1, hc2, hc3, hBsq]
    have hαne := hα0.ne'
    have hAu : (a1 / α) ^ 2 + (a2 / α) ^ 2 + (a3 / α) ^ 2 = 1 := by
      have : (a1 / α) ^ 2 + (a2 / α) ^ 2 + (a3 / α) ^ 2 = Asq / α ^ 2 := by
        rw [hAsq]
        ring
      rw [this, hαsq, div_self (by linarith only [hAlow] : Asq ≠ 0)]
    have hdt : (a1 / α) * b1 + (a2 / α) * b2 + (a3 / α) * b3 = t := by
      rw [ht, hsd]
      ring
    linear_combination t ^ 2 * hAu - 2 * t * hdt
  set γsq := c1 ^ 2 + c2 ^ 2 + c3 ^ 2 with hγsq
  have hγlow : 1 / 2 ≤ γsq := by
    rw [hCsq]
    linarith only [nb, hb0, hκ4, htsq, hBsq]
  set γ := Real.sqrt γsq with hγ
  have hγ2 : γ ^ 2 = γsq := Real.sq_sqrt (by linarith only [hγlow])
  have hγ0 : 0 < γ := Real.sqrt_pos.mpr (by linarith only [hγlow])
  -- the exact frame
  have hne : Quaternion.normSq (⟨0, a1 / α, a2 / α, a3 / α⟩ : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_def']
    simp only
    have : (a1 / α) ^ 2 + (a2 / α) ^ 2 + (a3 / α) ^ 2 = Asq / α ^ 2 := by
      rw [hAsq]
      ring
    rw [hαsq, div_self (by linarith only [hAlow] : Asq ≠ 0)] at this
    linarith only [this]
  have hnf : Quaternion.normSq (⟨0, c1 / γ, c2 / γ, c3 / γ⟩ : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_def']
    simp only
    have : (c1 / γ) ^ 2 + (c2 / γ) ^ 2 + (c3 / γ) ^ 2 = γsq / γ ^ 2 := by
      rw [hγsq]
      ring
    rw [hγ2, div_self (by linarith only [hγlow] : γsq ≠ 0)] at this
    linarith only [this]
  have hne' : (a1 / α) ^ 2 + (a2 / α) ^ 2 + (a3 / α) ^ 2 = 1 := by
    rw [Quaternion.normSq_def'] at hne
    simp only at hne
    linarith only [hne]
  have hnf' : (c1 / γ) ^ 2 + (c2 / γ) ^ 2 + (c3 / γ) ^ 2 = 1 := by
    rw [Quaternion.normSq_def'] at hnf
    simp only at hnf
    linarith only [hnf]
  refine ⟨mkQ _ hne, mkQ _ hnf, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change (⟨0, a1 / α, a2 / α, a3 / α⟩ : ℍ[ℝ]) * ⟨0, a1 / α, a2 / α, a3 / α⟩ = -1
    exact imag_sq _ _ _ hne'
  · apply Subtype.ext
    change (⟨0, c1 / γ, c2 / γ, c3 / γ⟩ : ℍ[ℝ]) * ⟨0, c1 / γ, c2 / γ, c3 / γ⟩ = -1
    exact imag_sq _ _ _ hnf'
  · apply Subtype.ext
    change (⟨0, a1 / α, a2 / α, a3 / α⟩ : ℍ[ℝ]) * ⟨0, c1 / γ, c2 / γ, c3 / γ⟩ =
      (-1) * ((⟨0, c1 / γ, c2 / γ, c3 / γ⟩ : ℍ[ℝ]) * ⟨0, a1 / α, a2 / α, a3 / α⟩)
    apply imag_anti
    have : (a1 / α) * (c1 / γ) + (a2 / α) * (c2 / γ) + (a3 / α) * (c3 / γ) =
        ((a1 / α) * c1 + (a2 / α) * c2 + (a3 / α) * c3) / γ := by ring
    rw [this, hdot, zero_div]
  · -- the first frame vector
    have hsq : d a (mkQ _ hne) ^ 2 ≤ κ ^ 2 := by
      unfold d
      change ‖(a : ℍ[ℝ]) - ⟨0, a1 / α, a2 / α, a3 / α⟩‖ ^ 2 ≤ _
      rw [hA, sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
      simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub]
      have hαle : α ≤ 1 := by
        rw [hα]
        apply Real.sqrt_le_one.mpr
        linarith only [na, sq_nonneg a0]
      have hdiff : 1 - α ≤ a0 ^ 2 := by
        have : a0 ^ 2 = 1 - α ^ 2 := by rw [hαsq, hAsq]; linarith only [na]
        rw [this]
        nlinarith only [hαle, hα0.le]
      have hid : (a0 - 0) ^ 2 + (a1 - a1 / α) ^ 2 + (a2 - a2 / α) ^ 2 + (a3 - a3 / α) ^ 2 =
          a0 ^ 2 + (1 - 1 / α) ^ 2 * Asq := by
        rw [hAsq]
        ring
      have hid2 : (1 - 1 / α) ^ 2 * Asq = (1 - α) ^ 2 := by
        rw [← hαsq]
        field_simp
        ring
      rw [hid, hid2]
      have hd0 : 0 ≤ 1 - α := by linarith only [hαle]
      have h3 : (1 - α) ^ 2 ≤ (a0 ^ 2) ^ 2 := pow_le_pow_left₀ hd0 hdiff 2
      have ha1 : a0 ^ 2 ≤ 1 / 4 := by linarith only [ha0, hκ2]
      have h4 : (a0 ^ 2) ^ 2 ≤ a0 ^ 2 := by nlinarith only [ha1, sq_nonneg a0]
      linarith only [h3, h4, ha0, sq_nonneg a0, sq_nonneg κ]
    exact abs_le_of_sq_le_sq' hsq h0 |>.2
  · -- the second frame vector
    have hsq : d b (mkQ _ hnf) ^ 2 ≤ (2 * κ) ^ 2 := by
      unfold d
      change ‖(b : ℍ[ℝ]) - ⟨0, c1 / γ, c2 / γ, c3 / γ⟩‖ ^ 2 ≤ _
      rw [hB, sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
      simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub]
      have hγsqv : γ ^ 2 = 1 - b0 ^ 2 - t ^ 2 := by
        rw [hγ2, hCsq, hBsq]
        linarith only [nb]
      have hγle : γ ≤ 1 := by
        rw [hγ]
        apply Real.sqrt_le_one.mpr
        rw [hCsq, hBsq]
        linarith only [nb, sq_nonneg b0, sq_nonneg t]
      have hdiff : 1 - γ ≤ b0 ^ 2 + t ^ 2 := by
        nlinarith only [hγle, hγ0.le, hγsqv]
      have hu : (a1 / α) ^ 2 + (a2 / α) ^ 2 + (a3 / α) ^ 2 = 1 := hne'
      have hid : (b0 - 0) ^ 2 + (b1 - c1 / γ) ^ 2 + (b2 - c2 / γ) ^ 2 + (b3 - c3 / γ) ^ 2 =
          b0 ^ 2 + t ^ 2 * ((a1 / α) ^ 2 + (a2 / α) ^ 2 + (a3 / α) ^ 2) +
            (1 - 1 / γ) ^ 2 * γsq +
            2 * t * (1 - 1 / γ) * ((a1 / α) * c1 + (a2 / α) * c2 + (a3 / α) * c3) := by
        have e1 : b1 = c1 + t * (a1 / α) := by rw [hc1]; ring
        have e2 : b2 = c2 + t * (a2 / α) := by rw [hc2]; ring
        have e3 : b3 = c3 + t * (a3 / α) := by rw [hc3]; ring
        rw [e1, e2, e3, hγsq]
        ring
      have hid2 : (1 - 1 / γ) ^ 2 * γsq = (1 - γ) ^ 2 := by
        rw [← hγ2]
        field_simp
        ring
      rw [hid, hdot, hu, hid2]
      have hd0 : 0 ≤ 1 - γ := by linarith only [hγle]
      have hsum : b0 ^ 2 + t ^ 2 ≤ κ ^ 2 := by linarith only [hb0, htsq, sq_nonneg κ]
      have h3 : (1 - γ) ^ 2 ≤ (κ ^ 2) ^ 2 := pow_le_pow_left₀ hd0 (hdiff.trans hsum) 2
      have h4 : (κ ^ 2) ^ 2 ≤ κ ^ 2 := by nlinarith only [hκ2, sq_nonneg κ]
      have e : (2 * κ) ^ 2 = 4 * κ ^ 2 := by ring
      rw [e]
      linarith only [h3, h4, hsum, sq_nonneg κ]
    exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2

/-- **Alignment.** A nearly anticommuting pair is a rotation of `i, j`, up to a fixed multiple of
the failure of anticommutation. -/
theorem align (a b : Q) (κ : ℝ) (h0 : 0 ≤ κ) (h1 : κ ≤ 1 / 2) (hab : d (a * b) (ω * (b * a)) ≤ κ) :
    ∃ R : Q, d (R * a * R⁻¹) qI ≤ κ ∧ d (R * b * R⁻¹) qJ ≤ 2 * κ := by
  obtain ⟨e, f, he, hf, hef, hae, hbf⟩ := exists_frame_pair a b κ h0 h1 hab
  obtain ⟨R, hRe, hRf⟩ := exact_frame e f he hf hef
  refine ⟨R, ?_, ?_⟩
  · rw [← hRe, d_mul_right, d_mul_left]
    exact hae
  · rw [← hRf, d_mul_right, d_mul_left]
    exact hbf

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedFrame
