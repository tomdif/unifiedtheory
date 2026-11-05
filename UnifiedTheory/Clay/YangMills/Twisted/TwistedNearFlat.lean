/- Small twisted action forces a link field near a center-shifted flat field. Combined with the
Landau bound, the squared distance is at most `N²·S` once `S ≤ (1/(1408 N⁵))²`, and with the action
tail this localizes the quantum measure in that distance. The coupling must be large in the lattice
size, so this concerns neither a physical trajectory nor a spectral gap. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedAxial
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSeams
import UnifiedTheory.Clay.YangMills.Twisted.TwistedTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedNearFlat
noncomputable section
open PeriodicLattice4 TwistedFlat TwistedStability TwistedLandau TwistedAxial TwistedSeams
open TwistedLocalization TwistedFrame
open WilsonSingleLinkStaples (Q)
open scoped Quaternion

variable {N : ℕ}

/-- The point with given coordinates. -/
def pt (t r u s : ZMod N) : Vertex N := ![t, r, u, s]

theorem pt_eta (x : Vertex N) : pt (x 0) (x 1) (x 2) (x 3) = x := by
  funext i
  fin_cases i <;> rfl

theorem pt_step0 (t r u s : ZMod N) : step N (pt t r u s) 0 = pt (t + 1) r u s := by
  funext i
  fin_cases i <;> simp [step, pt]

theorem pt_step1 (t r u s : ZMod N) : step N (pt t r u s) 1 = pt t (r + 1) u s := by
  funext i
  fin_cases i <;> simp [step, pt]

theorem pt_step2 (t r u s : ZMod N) : step N (pt t r u s) 2 = pt t r (u + 1) s := by
  funext i
  fin_cases i <;> simp [step, pt]

theorem pt_step3 (t r u s : ZMod N) : step N (pt t r u s) 3 = pt t r u (s + 1) := by
  funext i
  fin_cases i <;> simp [step, pt]

/-- Coordinates form of a link field. -/
def coordOf (A : Vertex N → Fin 4 → Q) (μ : Fin 4) : ZMod N → ZMod N → ZMod N → ZMod N → Q :=
  fun t r u s => A (pt t r u s) μ

variable [NeZero N]

/-- Axial gauge and uniformly small defects give the seam structure. -/
theorem cells_of_axial (A : Vertex N → Fin 4 → Q) (hA : Axial A) (ε : ℝ) (h0 : 0 ≤ ε)
    (hε : ∀ x μ ν, μ < ν → defect A μ ν x ≤ ε) :
    Cells (coordOf A 0) (coordOf A 1) (coordOf A 2) (coordOf A 3) ε := by
  have zero_exp (μ ν : Fin 4) (h : ¬ (μ = 1 ∧ ν = 2)) (x : Vertex N) : twistExp μ ν x = 0 := by
    unfold twistExp
    rw [if_neg]
    tauto
  refine
    { nonneg := h0
      p01 := fun t r u s => ?_
      p02 := fun t r u s => ?_
      p03 := fun t r u s => ?_
      p12 := fun t r u s => ?_
      p13 := fun t r u s => ?_
      p23 := fun t r u s => ?_
      a2 := fun t r u s h => hA.p2 _ h
      a1 := fun t r s h => hA.p1 _ rfl h
      a3 := fun t s h => hA.p3 _ rfl rfl h
      a0 := fun t h => hA.p0 _ rfl rfl rfl h }
  · have h := hε (pt t r u s) 0 1 (by decide)
    unfold defect at h
    rwa [pt_step0, pt_step1, zero_exp 0 1 (by decide), pow_zero] at h
  · have h := hε (pt t r u s) 0 2 (by decide)
    unfold defect at h
    rwa [pt_step0, pt_step2, zero_exp 0 2 (by decide), pow_zero] at h
  · have h := hε (pt t r u s) 0 3 (by decide)
    unfold defect at h
    rwa [pt_step0, pt_step3, zero_exp 0 3 (by decide), pow_zero] at h
  · have h := hε (pt t r u s) 1 2 (by decide)
    unfold defect at h
    rw [pt_step1, pt_step2] at h
    have he : (ω : Q) ^ twistExp (N := N) 1 2 (pt t r u s) = if r = 0 ∧ u = 0 then ω else 1 := by
      unfold twistExp
      by_cases hc : r = 0 ∧ u = 0
      · rw [if_pos ⟨rfl, rfl, hc.1, hc.2⟩, if_pos hc, pow_one]
      · rw [if_neg (fun h => hc ⟨h.2.2.1, h.2.2.2⟩), if_neg hc, pow_zero]
    rwa [he] at h
  · have h := hε (pt t r u s) 1 3 (by decide)
    unfold defect at h
    rwa [pt_step1, pt_step3, zero_exp 1 3 (by decide), pow_zero] at h
  · have h := hε (pt t r u s) 2 3 (by decide)
    unfold defect at h
    rwa [pt_step2, pt_step3, zero_exp 2 3 (by decide), pow_zero] at h

/-! ### Center shifts -/

/-- The sign of the center shift on a link. -/
def sgn (c₃ c₀ : Q) (x : Vertex N) (μ : Fin 4) : Q :=
  if μ = 3 ∧ x 3 = 0 then c₃ else if μ = 0 ∧ x 0 = 0 then c₀ else 1

/-- The center-shifted field. -/
def shift (c₃ c₀ : Q) (L : Vertex N → Fin 4 → Q) : Vertex N → Fin 4 → Q :=
  fun x μ => sgn c₃ c₀ x μ * L x μ

theorem sgn_cases (c₃ c₀ : Q) (h₃ : c₃ = 1 ∨ c₃ = ω) (h₀ : c₀ = 1 ∨ c₀ = ω) (x : Vertex N)
    (μ : Fin 4) : sgn c₃ c₀ x μ = 1 ∨ sgn c₃ c₀ x μ = ω := by
  unfold sgn
  split_ifs
  · exact h₃
  · exact h₀
  · exact Or.inl rfl

theorem sgn_step (c₃ c₀ : Q) (x : Vertex N) (μ ν : Fin 4) (h : ν ≠ μ) :
    sgn c₃ c₀ (step N x ν) μ = sgn c₃ c₀ x μ := by
  unfold sgn
  by_cases h3 : μ = 3
  · subst h3
    simp [step_other x ν 3 h.symm]
  · by_cases h0 : μ = 0
    · subst h0
      simp [step_other x ν 0 h.symm]
    · simp [h3, h0]

theorem defect_shift (c₃ c₀ : Q) (h₃ : c₃ = 1 ∨ c₃ = ω) (h₀ : c₀ = 1 ∨ c₀ = ω)
    (L : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (hμν : μ ≠ ν) (x : Vertex N) :
    defect (shift c₃ c₀ L) μ ν x = defect L μ ν x := by
  unfold defect shift
  rw [sgn_step c₃ c₀ x μ ν hμν.symm, sgn_step c₃ c₀ x ν μ hμν]
  rw [TwistedTransfer.sign_cancel _ _ (sgn_cases c₃ c₀ h₃ h₀ x μ) (sgn_cases c₃ c₀ h₃ h₀ x ν)]

theorem actionL_shift (c₃ c₀ : Q) (h₃ : c₃ = 1 ∨ c₃ = ω) (h₀ : c₀ = 1 ∨ c₀ = ω)
    (L : Vertex N → Fin 4 → Q) : actionL (shift c₃ c₀ L) = actionL L := by
  unfold actionL
  refine Finset.sum_congr rfl ?_
  rintro ⟨x, ⟨⟨μ, ν⟩, h⟩⟩ _
  simp only
  rw [defect_shift c₃ c₀ h₃ h₀ L μ ν (ne_of_lt h) x]

theorem shift_act (c₃ c₀ : Q) (h₃ : c₃ = 1 ∨ c₃ = ω) (h₀ : c₀ = 1 ∨ c₀ = ω) (h : Vertex N → Q)
    (L : Vertex N → Fin 4 → Q) : shift c₃ c₀ (act h L) = act h (shift c₃ c₀ L) := by
  funext x μ
  unfold shift act
  have hc : ∀ g : Q, Commute (sgn c₃ c₀ x μ) g := by
    intro g
    rcases sgn_cases c₃ c₀ h₃ h₀ x μ with hs | hs
    · rw [hs]
      exact Commute.one_left g
    · rw [hs]
      exact ω_commute g
  rw [← mul_assoc (h x), ← (hc (h x)).eq]
  simp only [mul_assoc]

/-! ### The competitor -/

theorem d_conj (R a b : Q) : d (R * a * R⁻¹) (R * b * R⁻¹) = d a b := by
  rw [d_mul_right, d_mul_left]

/-- Field `A` in axial gauge with small defects is near a center-shifted flat field after one
rotation. All link distances are at most `11 K`, with `K = N (ε + N ε)`. -/
theorem axial_near_flat (hN : 1 ≤ N) (A : Vertex N → Fin 4 → Q) (hA : Axial A) (ε : ℝ) (h0 : 0 ≤ ε)
    (hε : ∀ x μ ν, μ < ν → defect A μ ν x ≤ ε) (hsmall : 3 * scale N ε ≤ 1 / 2) :
    ∃ (R c₃ c₀ : Q), (c₃ = 1 ∨ c₃ = ω) ∧ (c₀ = 1 ∨ c₀ = ω) ∧
      ∀ x μ, d (sgn c₃ c₀ x μ * (R * A x μ * R⁻¹)) (flatLink x μ) ≤ 11 * scale N ε := by
  have C := cells_of_axial A hA ε h0 hε
  set K := scale N ε with hK
  have hKpos : 0 ≤ K := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [hK]
    unfold scale
    positivity
  set A₀ := coordOf A 0 with hA₀
  set A₁ := coordOf A 1 with hA₁
  set A₂ := coordOf A 2 with hA₂
  set A₃ := coordOf A 3 with hA₃
  have r12 := rel12 C hN
  have r13 := rel13 C hN
  have r23 := rel23 C hN
  have r01 := rel01 C hN
  have r02 := rel02 C hN
  obtain ⟨R, hRI, hRJ⟩ := align (G₁ A₁) (G₂ A₂) (3 * K) (by positivity) hsmall r12
  have hle1 : 3 * K ≤ 1 := by linarith only [hsmall]
  have hcent3 := near_central (G₁ A₁) (G₂ A₂) (G₃ A₃) (3 * K) (by positivity) hle1 r12
    (by rw [d_comm]; exact r13) (by rw [d_comm]; exact r23)
  have hcent0 := near_central (G₁ A₁) (G₂ A₂) (G₀ A₀) (3 * K) (by positivity) hle1 r12 r01 r02
  have hc3 : ∃ c₃ : Q, (c₃ = 1 ∨ c₃ = ω) ∧ d (G₃ A₃) c₃ ≤ 8 * K := by
    rcases hcent3 with h | h
    · exact ⟨1, Or.inl rfl, by linarith only [h]⟩
    · exact ⟨ω, Or.inr rfl, by linarith only [h]⟩
  have hc0 : ∃ c₀ : Q, (c₀ = 1 ∨ c₀ = ω) ∧ d (G₀ A₀) c₀ ≤ 8 * K := by
    rcases hcent0 with h | h
    · exact ⟨1, Or.inl rfl, by linarith only [h]⟩
    · exact ⟨ω, Or.inr rfl, by linarith only [h]⟩
  obtain ⟨c₃, hc₃, hG3⟩ := hc3
  obtain ⟨c₀, hc₀, hG0⟩ := hc0
  refine ⟨R, c₃, c₀, hc₃, hc₀, ?_⟩
  have hlink (x : Vertex N) (μ : Fin 4) : A x μ = coordOf A μ (x 0) (x 1) (x 2) (x 3) := by
    unfold coordOf
    rw [pt_eta]
  have hconj1 (a : Q) (ha : d a 1 ≤ 11 * K) : d (R * a * R⁻¹) 1 ≤ 11 * K := by
    have := d_conj R a 1
    rw [mul_one, mul_inv_cancel] at this
    rw [this]
    exact ha
  -- central shifts commute through the rotation
  have hshift (c a : Q) (hc : c = 1 ∨ c = ω) : d (c * (R * a * R⁻¹)) 1 = d a c := by
    have hinv : c * c = 1 := by
      rcases hc with rfl | rfl
      · simp
      · exact TwistedTransfer.ω_mul_ω
    have hcom : Commute c R := by
      rcases hc with rfl | rfl
      · exact Commute.one_left R
      · exact ω_commute R
    have e : c * (R * a * R⁻¹) = R * (c * a) * R⁻¹ := by
      rw [← mul_assoc c, ← mul_assoc c, hcom.eq]
      simp only [mul_assoc]
    rw [e]
    have := d_conj R (c * a) 1
    rw [mul_one, mul_inv_cancel] at this
    rw [this, ← d_mul_left c a c, hinv]
  intro x μ
  fin_cases μ
  · -- direction 0
    change d (sgn c₃ c₀ x 0 * (R * A x 0 * R⁻¹)) (flatLink x 0) ≤ _
    have hF : flatLink x 0 = 1 := by simp [flatLink]
    rw [hF, hlink]
    by_cases h0x : x 0 = 0
    · have hs : sgn c₃ c₀ x 0 = c₀ := by simp [sgn, h0x]
      rw [hs, hshift c₀ _ hc₀]
      have h := reduce0 C hN (x 0) (x 1) (x 2) (x 3)
      rw [h0x] at h ⊢
      have t := d_triangle (A₀ 0 (x 1) (x 2) (x 3)) (G₀ A₀) c₀
      have hG : G₀ A₀ = A₀ 0 1 1 1 := rfl
      rw [← hG] at h
      linarith only [h, t, hG0]
    · have hs : sgn c₃ c₀ x 0 = 1 := by simp [sgn, h0x]
      rw [hs, one_mul]
      apply hconj1
      have h := reduce0 C hN (x 0) (x 1) (x 2) (x 3)
      rw [C.a0 _ h0x] at h
      linarith only [h, hKpos]
  · -- direction 1
    change d (sgn c₃ c₀ x 1 * (R * A x 1 * R⁻¹)) (flatLink x 1) ≤ _
    have hs : sgn c₃ c₀ x 1 = 1 := by simp [sgn]
    rw [hs, one_mul, hlink]
    by_cases h1x : x 1 = 0
    · have hF : flatLink x 1 = qI := by simp [flatLink, h1x]
      rw [hF]
      have h := seam1 C hN (x 0) (x 2) (x 3)
      have hc := d_conj R (coordOf A 1 (x 0) (x 1) (x 2) (x 3)) (G₁ A₁)
      have t := d_triangle (R * coordOf A 1 (x 0) (x 1) (x 2) (x 3) * R⁻¹) (R * G₁ A₁ * R⁻¹) qI
      rw [h1x] at hc t ⊢
      linarith only [h, hc, t, hRI, hKpos]
    · have hF : flatLink x 1 = 1 := by simp [flatLink, h1x]
      rw [hF]
      apply hconj1
      have := off1 C hN (x 0) (x 1) (x 2) (x 3) h1x
      linarith only [this, hKpos]
  · -- direction 2
    change d (sgn c₃ c₀ x 2 * (R * A x 2 * R⁻¹)) (flatLink x 2) ≤ _
    have hs : sgn c₃ c₀ x 2 = 1 := by simp [sgn]
    rw [hs, one_mul, hlink]
    by_cases h2x : x 2 = 0
    · have hF : flatLink x 2 = qJ := by simp [flatLink, h2x]
      rw [hF]
      have h := seam2 C (x 0) (x 1) (x 3)
      have hc := d_conj R (coordOf A 2 (x 0) (x 1) (x 2) (x 3)) (G₂ A₂)
      have t := d_triangle (R * coordOf A 2 (x 0) (x 1) (x 2) (x 3) * R⁻¹) (R * G₂ A₂ * R⁻¹) qJ
      rw [h2x] at hc t ⊢
      linarith only [h, hc, t, hRJ, hKpos]
    · have hF : flatLink x 2 = 1 := by simp [flatLink, h2x]
      rw [hF]
      apply hconj1
      have h1 : coordOf A 2 (x 0) (x 1) (x 2) (x 3) = 1 := C.a2 (x 0) (x 1) (x 2) (x 3) h2x
      rw [h1, d_self]
      positivity
  · -- direction 3
    change d (sgn c₃ c₀ x 3 * (R * A x 3 * R⁻¹)) (flatLink x 3) ≤ _
    have hF : flatLink x 3 = 1 := by simp [flatLink]
    rw [hF, hlink]
    by_cases h3x : x 3 = 0
    · have hs : sgn c₃ c₀ x 3 = c₃ := by simp [sgn, h3x]
      rw [hs, hshift c₃ _ hc₃]
      have h := seam3 C hN (x 0) (x 1) (x 2)
      rw [h3x]
      have t := d_triangle (A₃ (x 0) (x 1) (x 2) 0) (G₃ A₃) c₃
      linarith only [h, t, hG3]
    · have hs : sgn c₃ c₀ x 3 = 1 := by simp [sgn, h3x]
      rw [hs, one_mul]
      apply hconj1
      have := off3 C hN (x 0) (x 1) (x 2) (x 3) h3x
      linarith only [this, hKpos]

/-! ### The theorem -/

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

theorem defect_le_sqrt (L : V' → Fin 4 → Q) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    defect L μ ν x ≤ Real.sqrt (actionL L) := by
  apply Real.le_sqrt_of_sq_le
  have hp := Finset.single_le_sum
    (f := fun p : PlaquetteIndex (2 * n) => defect L p.2.1.1 p.2.1.2 p.1 ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ ((x, ⟨(μ, ν), h⟩) : PlaquetteIndex (2 * n)))
  dsimp only at hp
  unfold actionL
  exact hp

/-- **Small twisted action puts a field near a center-shifted flat field.** With `N = 2n`,
if `S(L) ≤ (1/(1408 N⁵))²` there is a center class and a gauge with squared distance to the flat
field at most `N² S(L)`. -/
theorem near_flat (L : V' → Fin 4 → Q)
    (hS : actionL L ≤ (1 / (1408 * ((2 * n : ℕ) : ℝ) ^ 5)) ^ 2) :
    ∃ (c₃ c₀ : Q) (g : V' → Q), (c₃ = 1 ∨ c₃ = ω) ∧ (c₀ = 1 ∨ c₀ = ω) ∧
      D (act g (shift c₃ c₀ L)) ≤ ((2 * n : ℕ) : ℝ) ^ 2 * actionL L := by
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hNd
  have hN1nat : 1 ≤ 2 * n := NeZero.pos (2 * n)
  have hN : (1 : ℝ) ≤ N := by
    rw [hNd]
    exact_mod_cast hN1nat
  have hNpos : 0 < N := by linarith only [hN]
  set ε := Real.sqrt (actionL L) with hε
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  have hεle : ε ≤ 1 / (1408 * N ^ 5) := by
    rw [hε]
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hS⟩
  obtain ⟨g₀, hax⟩ := exists_axial L
  set A := act g₀ L with hA
  have hdef : ∀ x μ ν, μ < ν → defect A μ ν x ≤ ε := by
    intro x μ ν h
    rw [hA, defect_act]
    exact defect_le_sqrt n L x μ ν h
  have hscale : scale (2 * n) ε = N * (ε + N * ε) := rfl
  set K := scale (2 * n) ε with hK
  -- the product `N⁵ ε` is small
  have hN5 : N ^ 5 * ε ≤ 1 / 1408 := by
    have hp : 0 < N ^ 5 := by positivity
    calc N ^ 5 * ε ≤ N ^ 5 * (1 / (1408 * N ^ 5)) := mul_le_mul_of_nonneg_left hεle hp.le
      _ = 1 / 1408 := by field_simp
  have hKle : K ≤ 2 * N ^ 2 * ε := by
    rw [hscale]
    have : N * ε ≤ N * N * ε := by
      have hm : 0 ≤ N * ε := by positivity
      nlinarith only [hN, hm]
    nlinarith only [this]
  have hN2N5 : N ^ 2 * ε ≤ N ^ 5 * ε := by
    apply mul_le_mul_of_nonneg_right _ hε0
    exact pow_le_pow_right₀ hN (by norm_num)
  have hKpos : 0 ≤ K := by
    rw [hscale]
    positivity
  have hsmall : 3 * K ≤ 1 / 2 := by linarith only [hKle, hN2N5, hN5]
  obtain ⟨R, c₃, c₀, h₃, h₀, hb⟩ := axial_near_flat (N := 2 * n) hN1nat A hax ε hε0 hdef hsmall
  let L' := shift c₃ c₀ L
  let g₁ : V' → Q := fun x => R * g₀ x
  have hBeq : act g₁ L' = shift c₃ c₀ (act (fun _ => R) A) := by
    rw [hA, act_act, shift_act c₃ c₀ h₃ h₀]
  have hbB : ∀ x μ, d (act g₁ L' x μ) (flatLink x μ) ≤ 11 * K := by
    intro x μ
    rw [hBeq]
    have h := hb x μ
    have e : shift c₃ c₀ (act (fun _ => R) A) x μ = sgn c₃ c₀ x μ * (R * A x μ * R⁻¹) := rfl
    rw [e]
    exact h
  have hDle : D (act g₁ L') ≤ (1 / (32 * N)) ^ 2 := by
    have hsum : D (act g₁ L') ≤ ∑ _μ : Fin 4, ∑ _x : V', (11 * K) ^ 2 :=
      Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun x _ =>
        pow_le_pow_left₀ (d_nonneg _ _) (hbB x μ) 2
    have hcard : ∑ _μ : Fin 4, ∑ _x : V', (11 * K) ^ 2 = 4 * N ^ 4 * (11 * K) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
      have hc : (Fintype.card V' : ℝ) = N ^ 4 := by
        rw [hNd]
        simp [ZMod.card]
      rw [hc]
      push_cast
      ring
    rw [hcard] at hsum
    refine hsum.trans ?_
    have hmain : 22 * N ^ 2 * K ≤ 1 / (32 * N) := by
      have h1 : 22 * N ^ 2 * K ≤ 44 * N ^ 4 * ε := by
        have : N ^ 2 * K ≤ N ^ 2 * (2 * N ^ 2 * ε) :=
          mul_le_mul_of_nonneg_left hKle (by positivity)
        nlinarith only [this]
      have h2 : 44 * N ^ 4 * ε ≤ 1 / (32 * N) := by
        rw [le_div_iff₀ (by positivity)]
        have e : 44 * N ^ 4 * ε * (32 * N) = 1408 * (N ^ 5 * ε) := by ring
        rw [e]
        linarith only [hN5]
      linarith only [h1, h2]
    have hsq := pow_le_pow_left₀ (by positivity) hmain 2
    have e : (22 * N ^ 2 * K) ^ 2 = 4 * N ^ 4 * (11 * K) ^ 2 := by ring
    rw [e] at hsq
    exact hsq
  obtain ⟨g', hg', -, -⟩ := orbit_quadratic L' g₁ hDle
  refine ⟨c₃, c₀, g', h₃, h₀, ?_⟩
  have hact : actionL L' = actionL L := actionL_shift c₃ c₀ h₃ h₀ L
  rw [hact] at hg'
  exact hg'

/-! ### The quantum measure -/

open TwistedReflection PeriodicTimeReflection RegulatedGauge

theorem actionOne_eq (U : Configuration V' Q) :
    actionOne n U = actionL (linkValue (2 * n) Q U) := by
  unfold actionOne action actionL
  rw [one_mul]
  refine Finset.sum_congr rfl ?_
  rintro ⟨x, ⟨⟨μ, ν⟩, h⟩⟩ _
  exact term_eq_defect_sq n U x μ ν h

/-- The event that a configuration is within squared distance `N² σ` of a center-shifted flat field,
in some gauge. -/
def NearFlat (σ : ℝ) (U : Configuration V' Q) : Prop :=
  ∃ (c₃ c₀ : Q) (g : V' → Q), (c₃ = 1 ∨ c₃ = ω) ∧ (c₀ = 1 ∨ c₀ = ω) ∧
    D (act g (shift c₃ c₀ (linkValue (2 * n) Q U))) ≤ ((2 * n : ℕ) : ℝ) ^ 2 * σ

/-- **The twisted quantum measure concentrates near the flat classes.** For `0 ≤ σ` below the
threshold, the probability of leaving the `N² σ` neighbourhood is at most
`exp(-β σ) · cap(24β)^links`, for `β ≥ 1/32`. -/
theorem measure_near_flat (β σ : ℝ) (hβ : 1 / 32 ≤ β) (hσ : σ ≤ (1 / (1408 * ((2 * n : ℕ) : ℝ) ^ 5)) ^ 2) :
    twistedLaw n β {U | ¬ NearFlat n σ U} ≤
      ENNReal.ofReal (Real.exp (-β * σ) * SU2GaussianMass.cap (24 * β) ^ linkCount n) := by
  refine (MeasureTheory.measure_mono fun U hU => ?_).trans (action_tail n β σ hβ)
  change σ ≤ actionOne n U
  by_contra hlt
  push_neg at hlt
  apply hU
  rw [actionOne_eq] at hlt
  obtain ⟨c₃, c₀, g, h₃, h₀, hD⟩ := near_flat n (linkValue (2 * n) Q U) (hlt.le.trans hσ)
  refine ⟨c₃, c₀, g, h₃, h₀, hD.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hlt.le (by positivity)

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedNearFlat
