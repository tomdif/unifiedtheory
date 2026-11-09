/- Stokes estimates in axial gauge, in coordinates. Given the axial conditions and a uniform bound
on the plaquette defects, off-seam links are near the identity and the seam links are near four
constants, which nearly satisfy the twisted relations. Purely group-theoretic. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedStability
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedSeams
noncomputable section
open TwistedFlat TwistedStability
open WilsonSingleLinkStaples (Q)

/-- Comparison of two four-link products. -/
theorem four (a b c e a' b' c' e' : Q) :
    d (a * b * c⁻¹ * e⁻¹) (a' * b' * c'⁻¹ * e'⁻¹) ≤ d a a' + d b b' + d c c' + d e e' := by
  have dinv (g h : Q) : d g⁻¹ h⁻¹ = d g h := by
    have h1 := d_mul_left g g⁻¹ h⁻¹
    have h2 := d_mul_right h (g * g⁻¹) (g * h⁻¹)
    rw [mul_inv_cancel, one_mul, mul_assoc, inv_mul_cancel, mul_one] at h2
    rw [← h1, mul_inv_cancel, ← h2]
    exact d_comm _ _
  have s1 : d (a * b * c⁻¹ * e⁻¹) (a' * b * c⁻¹ * e⁻¹) = d a a' := by
    simp only [mul_assoc]
    rw [d_mul_right]
  have s2 : d (a' * b * c⁻¹ * e⁻¹) (a' * b' * c⁻¹ * e⁻¹) = d b b' := by
    simp only [mul_assoc]
    rw [d_mul_left, d_mul_right]
  have s3 : d (a' * b' * c⁻¹ * e⁻¹) (a' * b' * c'⁻¹ * e⁻¹) = d c c' := by
    simp only [mul_assoc]
    rw [d_mul_left, d_mul_left, d_mul_right, dinv]
  have s4 : d (a' * b' * c'⁻¹ * e⁻¹) (a' * b' * c'⁻¹ * e'⁻¹) = d e e' := by
    rw [d_mul_left, dinv]
  have t1 := d_triangle (a * b * c⁻¹ * e⁻¹) (a' * b * c⁻¹ * e⁻¹) (a' * b' * c'⁻¹ * e'⁻¹)
  have t2 := d_triangle (a' * b * c⁻¹ * e⁻¹) (a' * b' * c⁻¹ * e⁻¹) (a' * b' * c'⁻¹ * e'⁻¹)
  have t3 := d_triangle (a' * b' * c⁻¹ * e⁻¹) (a' * b' * c'⁻¹ * e⁻¹) (a' * b' * c'⁻¹ * e'⁻¹)
  linarith only [t1, t2, t3, s1, s2, s3, s4]

/-- Transfer a plaquette estimate to approximate links. -/
theorem transfer (a b c e a' b' c' e' w : Q) (ε : ℝ) (h : d (a * b * c⁻¹ * e⁻¹) w ≤ ε) :
    d (a' * b' * c'⁻¹ * e'⁻¹) w ≤ ε + d a a' + d b b' + d c c' + d e e' := by
  have h1 := four a b c e a' b' c' e'
  have h2 := d_triangle (a' * b' * c'⁻¹ * e'⁻¹) (a * b * c⁻¹ * e⁻¹) w
  have h3 := d_comm (a' * b' * c'⁻¹ * e'⁻¹) (a * b * c⁻¹ * e⁻¹)
  linarith only [h, h1, h2, h3]

theorem d_self (g : Q) : d g g = 0 := by
  unfold d
  simp

/-- Reduction when the first and third links are the identity. -/
theorem reduce_be (b e : Q) (δ : ℝ) (h : d (1 * b * (1 : Q)⁻¹ * e⁻¹) 1 ≤ δ) : d b e ≤ δ := by
  have e1 : (1 : Q) * b * (1 : Q)⁻¹ * e⁻¹ = b * e⁻¹ := by group
  rw [e1] at h
  have h2 := d_mul_right e (b * e⁻¹) 1
  rw [inv_mul_cancel_right, one_mul] at h2
  rw [h2]
  exact h

/-- Reduction when the second and fourth links are the identity. -/
theorem reduce_ac (a c : Q) (δ : ℝ) (h : d (a * 1 * c⁻¹ * (1 : Q)⁻¹) 1 ≤ δ) : d a c ≤ δ := by
  have e1 : a * 1 * c⁻¹ * (1 : Q)⁻¹ = a * c⁻¹ := by group
  rw [e1] at h
  have h2 := d_mul_right c (a * c⁻¹) 1
  rw [inv_mul_cancel_right, one_mul] at h2
  rw [h2]
  exact h

/-- A step with a nearly trivial first link and exactly trivial third link. -/
theorem step_be (b e a c w : Q) (δ η : ℝ) (h : d (a * b * c⁻¹ * e⁻¹) w ≤ δ) (hw : w = 1)
    (ha : d a 1 ≤ η) (hc : c = 1) : d b e ≤ δ + η := by
  subst hw hc
  refine reduce_be _ _ _ ?_
  have := transfer a b 1 e 1 b 1 e 1 δ h
  simp only [d_self, add_zero] at this
  linarith only [this, ha]

/-- A step with an exact trivial second link and a nearly trivial fourth link. -/
theorem step_ac (a c b e w : Q) (δ η : ℝ) (h : d (a * b * c⁻¹ * e⁻¹) w ≤ δ) (hw : w = 1)
    (he : d e 1 ≤ η) (hb : b = 1) : d a c ≤ δ + η := by
  subst hw hb
  refine reduce_ac _ _ _ ?_
  have := transfer a 1 c e a 1 c 1 1 δ h
  simp only [d_self, add_zero] at this
  linarith only [this, he]

variable {N : ℕ} [NeZero N]

/-- The line lemma: small increments off `z = 0` give near constancy along a period. -/
theorem line (g : ZMod N → Q) (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ z, z ≠ 0 → d (g (z + 1)) (g z) ≤ δ)
    (z : ZMod N) : d (g z) (g 1) ≤ N * δ := by
  have hk : ∀ k : ℕ, k < N → d (g (1 + k)) (g 1) ≤ k * δ := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [d_self]
    | succ k ih =>
      intro hlt
      have hne : (1 + (k : ZMod N)) ≠ 0 := by
        intro h0
        have hc : ((k + 1 : ℕ) : ZMod N) = 0 := by
          push_cast
          rw [add_comm]
          exact h0
        rw [ZMod.natCast_eq_zero_iff] at hc
        have := Nat.le_of_dvd (Nat.succ_pos k) hc
        omega
      have h1 := h _ hne
      have h2 := ih (by omega)
      have e : (1 + ((k + 1 : ℕ) : ZMod N)) = 1 + (k : ZMod N) + 1 := by
        push_cast
        ring
      rw [e]
      have t := d_triangle (g (1 + (k : ZMod N) + 1)) (g (1 + (k : ZMod N))) (g 1)
      push_cast
      linarith only [t, h1, h2]
  have hval : (z - 1).val < N := ZMod.val_lt _
  have hz : z = 1 + (((z - 1).val : ℕ) : ZMod N) := by
    rw [ZMod.natCast_zmod_val]
    ring
  rw [hz]
  refine (hk _ hval).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hval.le) hδ

/-- Links as functions of the coordinates `(t, r, u, s) = (x₀, x₁, x₂, x₃)`, with the six plaquette
estimates at uniform size `ε`, and the axial conditions. -/
structure Cells (A₀ A₁ A₂ A₃ : ZMod N → ZMod N → ZMod N → ZMod N → Q) (ε : ℝ) : Prop where
  nonneg : 0 ≤ ε
  p01 : ∀ t r u s, d (A₀ t r u s * A₁ (t + 1) r u s * (A₀ t (r + 1) u s)⁻¹ * (A₁ t r u s)⁻¹) 1 ≤ ε
  p02 : ∀ t r u s, d (A₀ t r u s * A₂ (t + 1) r u s * (A₀ t r (u + 1) s)⁻¹ * (A₂ t r u s)⁻¹) 1 ≤ ε
  p03 : ∀ t r u s, d (A₀ t r u s * A₃ (t + 1) r u s * (A₀ t r u (s + 1))⁻¹ * (A₃ t r u s)⁻¹) 1 ≤ ε
  p12 : ∀ t r u s, d (A₁ t r u s * A₂ t (r + 1) u s * (A₁ t r (u + 1) s)⁻¹ * (A₂ t r u s)⁻¹)
    (if r = 0 ∧ u = 0 then ω else 1) ≤ ε
  p13 : ∀ t r u s, d (A₁ t r u s * A₃ t (r + 1) u s * (A₁ t r u (s + 1))⁻¹ * (A₃ t r u s)⁻¹) 1 ≤ ε
  p23 : ∀ t r u s, d (A₂ t r u s * A₃ t r (u + 1) s * (A₂ t r u (s + 1))⁻¹ * (A₃ t r u s)⁻¹) 1 ≤ ε
  a2 : ∀ t r u s, u ≠ 0 → A₂ t r u s = 1
  a1 : ∀ t r s, r ≠ 0 → A₁ t r 1 s = 1
  a3 : ∀ t s, s ≠ 0 → A₃ t 1 1 s = 1
  a0 : ∀ t, t ≠ 0 → A₀ t 1 1 1 = 1

variable {A₀ A₁ A₂ A₃ : ZMod N → ZMod N → ZMod N → ZMod N → Q} {ε : ℝ}
  (C : Cells A₀ A₁ A₂ A₃ ε)

include C

/-- Reductions off the `u = 1` slab and within it. -/
theorem f1 (t r u s : ZMod N) : d (A₁ t r u s) (A₁ t r 1 s) ≤ N * ε := by
  refine line (fun v => A₁ t r v s) ε C.nonneg (fun v hv => ?_) u
  have h := C.p12 t r v s
  rw [if_neg (fun hc => hv hc.2), C.a2 _ _ _ _ hv, C.a2 _ _ _ _ hv] at h
  rw [d_comm]
  exact reduce_ac _ _ _ h

theorem f0 (t r u s : ZMod N) : d (A₀ t r u s) (A₀ t r 1 s) ≤ N * ε := by
  refine line (fun v => A₀ t r v s) ε C.nonneg (fun v hv => ?_) u
  have h := C.p02 t r v s
  rw [C.a2 _ _ _ _ hv, C.a2 _ _ _ _ hv] at h
  rw [d_comm]
  exact reduce_ac _ _ _ h

theorem f3 (t r u s : ZMod N) : d (A₃ t r u s) (A₃ t r 1 s) ≤ N * ε := by
  refine line (fun v => A₃ t r v s) ε C.nonneg (fun v hv => ?_) u
  have h := C.p23 t r v s
  rw [C.a2 _ _ _ _ hv, C.a2 _ _ _ _ hv] at h
  exact reduce_be _ _ _ h

theorem g3 (t r s : ZMod N) : d (A₃ t r 1 s) (A₃ t 1 1 s) ≤ N * ε := by
  refine line (fun v => A₃ t v 1 s) ε C.nonneg (fun v hv => ?_) r
  have h := C.p13 t v 1 s
  rw [C.a1 _ _ _ hv, C.a1 _ _ _ hv] at h
  exact reduce_be _ _ _ h

theorem g0 (t r s : ZMod N) : d (A₀ t r 1 s) (A₀ t 1 1 s) ≤ N * ε := by
  refine line (fun v => A₀ t v 1 s) ε C.nonneg (fun v hv => ?_) r
  have h := C.p01 t v 1 s
  rw [C.a1 _ _ _ hv, C.a1 _ _ _ hv] at h
  rw [d_comm]
  exact reduce_ac _ _ _ h

theorem h0 (t s : ZMod N) : d (A₀ t 1 1 s) (A₀ t 1 1 1) ≤ N * ε := by
  refine line (fun v => A₀ t 1 1 v) ε C.nonneg (fun v hv => ?_) s
  have h := C.p03 t 1 1 v
  rw [C.a3 _ _ hv, C.a3 _ _ hv] at h
  rw [d_comm]
  exact reduce_ac _ _ _ h

/-- Scale of the seam estimates. -/
def scale (N : ℕ) (ε : ℝ) : ℝ := N * (ε + N * ε)

theorem c3 (t : ZMod N) : d (A₃ t 1 1 0) (A₃ 1 1 1 0) ≤ scale N ε := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine line (fun v => A₃ v 1 1 0) (ε + N * ε) (add_nonneg C.nonneg (mul_nonneg hN C.nonneg))
    (fun v hv => ?_) t
  refine step_be _ _ (A₀ v 1 1 0) (A₀ v 1 1 (0 + 1)) 1 _ _ (C.p03 v 1 1 0) rfl ?_ ?_
  · have := h0 C v 0
    rwa [C.a0 v hv] at this
  · rw [zero_add]
    exact C.a0 v hv

theorem c1a (t s : ZMod N) : d (A₁ t 0 1 s) (A₁ t 0 1 1) ≤ scale N ε := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine line (fun v => A₁ t 0 1 v) (ε + N * ε) (add_nonneg C.nonneg (mul_nonneg hN C.nonneg))
    (fun v hv => ?_) s
  have hq := step_ac (A₁ t 0 1 v) (A₁ t 0 1 (v + 1)) (A₃ t (0 + 1) 1 v) (A₃ t 0 1 v) 1 ε (N * ε)
    (C.p13 t 0 1 v) rfl (by
      have := g3 C t 0 v
      rwa [C.a3 t v hv] at this) (by
      rw [zero_add]
      exact C.a3 t v hv)
  rw [d_comm]
  exact hq

theorem c1b (t : ZMod N) : d (A₁ t 0 1 1) (A₁ 1 0 1 1) ≤ scale N ε := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine line (fun v => A₁ v 0 1 1) (ε + N * ε) (add_nonneg C.nonneg (mul_nonneg hN C.nonneg))
    (fun v hv => ?_) t
  refine step_be _ _ (A₀ v 0 1 1) (A₀ v (0 + 1) 1 1) 1 _ _ (C.p01 v 0 1 1) rfl ?_ ?_
  · have := g0 C v 0 1
    rwa [C.a0 v hv] at this
  · rw [zero_add]
    exact C.a0 v hv

theorem c2a (t r s : ZMod N) : d (A₂ t r 0 s) (A₂ t 1 0 s) ≤ scale N ε := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine line (fun v => A₂ t v 0 s) (ε + N * ε) (add_nonneg C.nonneg (mul_nonneg hN C.nonneg))
    (fun v hv => ?_) r
  have hp := C.p12 t v 0 s
  rw [if_neg (fun hc => hv hc.1)] at hp
  refine step_be _ _ (A₁ t v 0 s) (A₁ t v (0 + 1) s) 1 _ _ hp rfl ?_ ?_
  · have := f1 C t v 0 s
    rwa [C.a1 t v s hv] at this
  · rw [zero_add]
    exact C.a1 t v s hv

theorem c2b (t s : ZMod N) : d (A₂ t 1 0 s) (A₂ t 1 0 1) ≤ scale N ε := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine line (fun v => A₂ t 1 0 v) (ε + N * ε) (add_nonneg C.nonneg (mul_nonneg hN C.nonneg))
    (fun v hv => ?_) s
  have hq := step_ac (A₂ t 1 0 v) (A₂ t 1 0 (v + 1)) (A₃ t 1 (0 + 1) v) (A₃ t 1 0 v) 1 ε (N * ε)
    (C.p23 t 1 0 v) rfl (by
      have := f3 C t 1 0 v
      rwa [C.a3 t v hv] at this) (by
      rw [zero_add]
      exact C.a3 t v hv)
  rw [d_comm]
  exact hq

theorem c2c (t : ZMod N) : d (A₂ t 1 0 1) (A₂ 1 1 0 1) ≤ scale N ε := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine line (fun v => A₂ v 1 0 1) (ε + N * ε) (add_nonneg C.nonneg (mul_nonneg hN C.nonneg))
    (fun v hv => ?_) t
  refine step_be _ _ (A₀ v 1 0 1) (A₀ v 1 (0 + 1) 1) 1 _ _ (C.p02 v 1 0 1) rfl ?_ ?_
  · have := f0 C v 1 0 1
    rwa [C.a0 v hv] at this
  · rw [zero_add]
    exact C.a0 v hv

/-! ### Constants and relations -/

theorem eps_le_scale (hN : 1 ≤ N) : ε ≤ scale N ε := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 := C.nonneg
  unfold scale
  nlinarith only [hN', h0, mul_nonneg (by linarith only [hN'] : (0 : ℝ) ≤ N) h0,
    mul_le_mul_of_nonneg_right hN' h0, mul_nonneg h0 (by linarith only [hN'] : (0 : ℝ) ≤ N)]

theorem Nε_le_scale (hN : 1 ≤ N) : (N : ℝ) * ε ≤ scale N ε := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 := C.nonneg
  have hm : 0 ≤ (N : ℝ) * ε := mul_nonneg (by linarith only [hN']) h0
  have h2 : (N : ℝ) * ε ≤ N * (N * ε) := by nlinarith only [hN', hm]
  unfold scale
  nlinarith only [h2, hm, hN', h0, mul_nonneg (by linarith only [hN'] : (0 : ℝ) ≤ N) h0]

/-- Seam values. -/
def G₁ (A₁ : ZMod N → ZMod N → ZMod N → ZMod N → Q) : Q := A₁ 1 0 1 1
def G₂ (A₂ : ZMod N → ZMod N → ZMod N → ZMod N → Q) : Q := A₂ 1 1 0 1
def G₃ (A₃ : ZMod N → ZMod N → ZMod N → ZMod N → Q) : Q := A₃ 1 1 1 0
def G₀ (A₀ : ZMod N → ZMod N → ZMod N → ZMod N → Q) : Q := A₀ 0 1 1 1

/-- The twisted relation of the seam values. -/
theorem rel12 (hN : 1 ≤ N) : d (G₁ A₁ * G₂ A₂) (ω * (G₂ A₂ * G₁ A₁)) ≤ 3 * scale N ε := by
  have hK₁ := eps_le_scale C hN
  have hK₂ := Nε_le_scale C hN
  have h := C.p12 1 0 0 1
  rw [if_pos ⟨rfl, rfl⟩] at h
  have ht := transfer _ _ _ _ (G₁ A₁) (G₂ A₂) (G₁ A₁) (G₂ A₂) _ _ h
  have e1 : d (A₁ 1 0 0 1) (G₁ A₁) ≤ N * ε := f1 C 1 0 0 1
  have e2 : d (A₂ 1 (0 + 1) 0 1) (G₂ A₂) = 0 := by
    rw [zero_add]
    exact d_self _
  have e3 : d (A₁ 1 0 (0 + 1) 1) (G₁ A₁) = 0 := by
    rw [zero_add]
    exact d_self _
  have e4 : d (A₂ 1 0 0 1) (G₂ A₂) ≤ scale N ε := c2a C 1 0 1
  have hrel := cell_of_defect (G₁ A₁) (G₂ A₂) (G₁ A₁) (G₂ A₂) ω (3 * scale N ε)
    (ht.trans (by rw [e2, e3]; linarith only [e1, e4, hK₁, hK₂]))
  exact hrel

theorem rel13 (hN : 1 ≤ N) : d (G₁ A₁ * G₃ A₃) (G₃ A₃ * G₁ A₁) ≤ 3 * scale N ε := by
  have hK₁ := eps_le_scale C hN
  have hK₂ := Nε_le_scale C hN
  have h := C.p13 1 0 1 0
  have ht := transfer _ _ _ _ (G₁ A₁) (G₃ A₃) (G₁ A₁) (G₃ A₃) _ _ h
  have e1 : d (A₁ 1 0 1 0) (G₁ A₁) ≤ scale N ε := (c1a C 1 0).trans_eq rfl
  have e2 : d (A₃ 1 (0 + 1) 1 0) (G₃ A₃) = 0 := by
    rw [zero_add]
    exact d_self _
  have e3 : d (A₁ 1 0 1 (0 + 1)) (G₁ A₁) = 0 := by
    rw [zero_add]
    exact d_self _
  have e4 : d (A₃ 1 0 1 0) (G₃ A₃) ≤ N * ε := g3 C 1 0 0
  have hrel := cell_of_defect (G₁ A₁) (G₃ A₃) (G₁ A₁) (G₃ A₃) 1 (3 * scale N ε)
    (ht.trans (by rw [e2, e3]; linarith only [e1, e4, hK₁, hK₂]))
  rwa [one_mul] at hrel

theorem rel23 (hN : 1 ≤ N) : d (G₂ A₂ * G₃ A₃) (G₃ A₃ * G₂ A₂) ≤ 3 * scale N ε := by
  have hK₁ := eps_le_scale C hN
  have hK₂ := Nε_le_scale C hN
  have h := C.p23 1 1 0 0
  have ht := transfer _ _ _ _ (G₂ A₂) (G₃ A₃) (G₂ A₂) (G₃ A₃) _ _ h
  have e1 : d (A₂ 1 1 0 0) (G₂ A₂) ≤ scale N ε := (c2b C 1 0).trans_eq rfl
  have e2 : d (A₃ 1 1 (0 + 1) 0) (G₃ A₃) = 0 := by
    rw [zero_add]
    exact d_self _
  have e3 : d (A₂ 1 1 0 (0 + 1)) (G₂ A₂) = 0 := by
    rw [zero_add]
    exact d_self _
  have e4 : d (A₃ 1 1 0 0) (G₃ A₃) ≤ N * ε := f3 C 1 1 0 0
  have hrel := cell_of_defect (G₂ A₂) (G₃ A₃) (G₂ A₂) (G₃ A₃) 1 (3 * scale N ε)
    (ht.trans (by rw [e2, e3]; linarith only [e1, e4, hK₁, hK₂]))
  rwa [one_mul] at hrel

theorem rel01 (hN : 1 ≤ N) : d (G₀ A₀ * G₁ A₁) (G₁ A₁ * G₀ A₀) ≤ 3 * scale N ε := by
  have hK₁ := eps_le_scale C hN
  have hK₂ := Nε_le_scale C hN
  have h := C.p01 0 0 1 1
  have ht := transfer _ _ _ _ (G₀ A₀) (G₁ A₁) (G₀ A₀) (G₁ A₁) _ _ h
  have e1 : d (A₀ 0 0 1 1) (G₀ A₀) ≤ N * ε := g0 C 0 0 1
  have e2 : d (A₁ (0 + 1) 0 1 1) (G₁ A₁) = 0 := by
    rw [zero_add]
    exact d_self _
  have e3 : d (A₀ 0 (0 + 1) 1 1) (G₀ A₀) = 0 := by
    rw [zero_add]
    exact d_self _
  have e4 : d (A₁ 0 0 1 1) (G₁ A₁) ≤ scale N ε := c1b C 0
  have hrel := cell_of_defect (G₀ A₀) (G₁ A₁) (G₀ A₀) (G₁ A₁) 1 (3 * scale N ε)
    (ht.trans (by rw [e2, e3]; linarith only [e1, e4, hK₁, hK₂]))
  rwa [one_mul] at hrel

theorem rel02 (hN : 1 ≤ N) : d (G₀ A₀ * G₂ A₂) (G₂ A₂ * G₀ A₀) ≤ 3 * scale N ε := by
  have hK₁ := eps_le_scale C hN
  have hK₂ := Nε_le_scale C hN
  have h := C.p02 0 1 0 1
  have ht := transfer _ _ _ _ (G₀ A₀) (G₂ A₂) (G₀ A₀) (G₂ A₂) _ _ h
  have e1 : d (A₀ 0 1 0 1) (G₀ A₀) ≤ N * ε := f0 C 0 1 0 1
  have e2 : d (A₂ (0 + 1) 1 0 1) (G₂ A₂) = 0 := by
    rw [zero_add]
    exact d_self _
  have e3 : d (A₀ 0 1 (0 + 1) 1) (G₀ A₀) = 0 := by
    rw [zero_add]
    exact d_self _
  have e4 : d (A₂ 0 1 0 1) (G₂ A₂) ≤ scale N ε := c2c C 0
  have hrel := cell_of_defect (G₀ A₀) (G₂ A₂) (G₀ A₀) (G₂ A₂) 1 (3 * scale N ε)
    (ht.trans (by rw [e2, e3]; linarith only [e1, e4, hK₁, hK₂]))
  rwa [one_mul] at hrel

/-! ### Every link near its target -/

theorem seam2 (t r s : ZMod N) : d (A₂ t r 0 s) (G₂ A₂) ≤ 3 * scale N ε := by
  have h1 := c2a C t r s
  have h2 := c2b C t s
  have h3 := c2c C t
  have t1 := d_triangle (A₂ t r 0 s) (A₂ t 1 0 s) (G₂ A₂)
  have t2 := d_triangle (A₂ t 1 0 s) (A₂ t 1 0 1) (G₂ A₂)
  change d (A₂ t 1 0 1) (A₂ 1 1 0 1) ≤ _ at h3
  have hG : G₂ A₂ = A₂ 1 1 0 1 := rfl
  rw [hG] at t1 t2 ⊢
  linarith only [h1, h2, h3, t1, t2]

theorem off1 (hN : 1 ≤ N) (t r u s : ZMod N) (hr : r ≠ 0) : d (A₁ t r u s) 1 ≤ scale N ε := by
  have h := f1 C t r u s
  rw [C.a1 t r s hr] at h
  exact h.trans (Nε_le_scale C hN)

theorem seam1 (hN : 1 ≤ N) (t u s : ZMod N) : d (A₁ t 0 u s) (G₁ A₁) ≤ 3 * scale N ε := by
  have h0 := f1 C t 0 u s
  have h1 := c1a C t s
  have h2 := c1b C t
  have hK₂ := Nε_le_scale C hN
  have t1 := d_triangle (A₁ t 0 u s) (A₁ t 0 1 s) (G₁ A₁)
  have t2 := d_triangle (A₁ t 0 1 s) (A₁ t 0 1 1) (G₁ A₁)
  have hG : G₁ A₁ = A₁ 1 0 1 1 := rfl
  rw [hG] at t1 t2 ⊢
  linarith only [h0, h1, h2, t1, t2, hK₂]

theorem off3 (hN : 1 ≤ N) (t r u s : ZMod N) (hs : s ≠ 0) : d (A₃ t r u s) 1 ≤ 2 * scale N ε := by
  have h0 := f3 C t r u s
  have h1 := g3 C t r s
  rw [C.a3 t s hs] at h1
  have hK₂ := Nε_le_scale C hN
  have t1 := d_triangle (A₃ t r u s) (A₃ t r 1 s) 1
  linarith only [h0, h1, t1, hK₂]

theorem seam3 (hN : 1 ≤ N) (t r u : ZMod N) : d (A₃ t r u 0) (G₃ A₃) ≤ 3 * scale N ε := by
  have h0 := f3 C t r u 0
  have h1 := g3 C t r 0
  have h2 := c3 C t
  have hK₂ := Nε_le_scale C hN
  have t1 := d_triangle (A₃ t r u 0) (A₃ t r 1 0) (G₃ A₃)
  have t2 := d_triangle (A₃ t r 1 0) (A₃ t 1 1 0) (G₃ A₃)
  have hG : G₃ A₃ = A₃ 1 1 1 0 := rfl
  rw [hG] at t1 t2 ⊢
  linarith only [h0, h1, h2, t1, t2, hK₂]

/-- All four reductions for direction `0`. -/
theorem reduce0 (hN : 1 ≤ N) (t r u s : ZMod N) : d (A₀ t r u s) (A₀ t 1 1 1) ≤ 3 * scale N ε := by
  have h00 := f0 C t r u s
  have h1 := g0 C t r s
  have h2 := TwistedSeams.h0 C t s
  have hK₂ := Nε_le_scale C hN
  have t1 := d_triangle (A₀ t r u s) (A₀ t r 1 s) (A₀ t 1 1 1)
  have t2 := d_triangle (A₀ t r 1 s) (A₀ t 1 1 s) (A₀ t 1 1 1)
  linarith only [h00, h1, h2, t1, t2, hK₂]

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedSeams
