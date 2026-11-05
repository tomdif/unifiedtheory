/- An exact axial gauge on the periodic lattice. Links are set to the identity successively in
directions 2, 1, 3, 0, on the slabs where the later coordinates vanish in the shifted sense, away
from one seam per direction. No smallness of the field is used. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedLandau

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedAxial
noncomputable section
open PeriodicLattice4 TwistedRectangle TwistedFlat TwistedLandau TwistedHessian
open WilsonSingleLinkStaples (Q)

variable {N : ℕ} [NeZero N]

/-- Reset the coordinates in `S` to `1`. -/
def resetSet (S : Finset (Fin 4)) (x : Vertex N) : Vertex N := fun i => if i ∈ S then 1 else x i

/-- Number of steps from the slab `x κ = 1` to `x`. -/
def steps (κ : Fin 4) (x : Vertex N) : ℕ := (x κ - 1).val

/-- The line origin of `x`. -/
def origin (S : Finset (Fin 4)) (κ : Fin 4) (x : Vertex N) : Vertex N :=
  Function.update (resetSet S x) κ 1

/-- Path product along direction `κ`, read on the slab where `S` is reset. -/
def lineGauge (L : Vertex N → Fin 4 → Q) (S : Finset (Fin 4)) (κ : Fin 4) (x : Vertex N) : Q :=
  run L κ (origin S κ x) (steps κ x)

theorem step_apply_same (x : Vertex N) (μ : Fin 4) : step N x μ μ = x μ + 1 := by
  simp [step]

theorem step_apply_other (x : Vertex N) (μ i : Fin 4) (h : i ≠ μ) : step N x μ i = x i :=
  step_other x μ i h

theorem resetSet_step_mem (S : Finset (Fin 4)) (x : Vertex N) (μ : Fin 4) (hμ : μ ∈ S) :
    resetSet S (step N x μ) = resetSet S x := by
  funext i
  unfold resetSet
  by_cases hi : i ∈ S
  · simp [hi]
  · have : i ≠ μ := fun h => hi (h ▸ hμ)
    simp [hi, step_apply_other x μ i this]

theorem origin_step_mem (S : Finset (Fin 4)) (κ : Fin 4) (x : Vertex N) (μ : Fin 4) (hμ : μ ∈ S) :
    origin S κ (step N x μ) = origin S κ x := by
  unfold origin
  rw [resetSet_step_mem S x μ hμ]

theorem steps_step_other (κ : Fin 4) (x : Vertex N) (μ : Fin 4) (h : κ ≠ μ) :
    steps κ (step N x μ) = steps κ x := by
  unfold steps
  rw [step_apply_other x μ κ h]

/-- The gauge does not depend on the coordinates in `S`. -/
theorem lineGauge_step_mem (L : Vertex N → Fin 4 → Q) (S : Finset (Fin 4)) (κ : Fin 4)
    (hκ : κ ∉ S) (x : Vertex N) (μ : Fin 4) (hμ : μ ∈ S) :
    lineGauge L S κ (step N x μ) = lineGauge L S κ x := by
  unfold lineGauge
  have hne : κ ≠ μ := fun h => hκ (h ▸ hμ)
  rw [origin_step_mem S κ x μ hμ, steps_step_other κ x μ hne]

/-- Links equal to one in a reset direction stay equal to one. -/
theorem act_one_of_mem (L : Vertex N → Fin 4 → Q) (S : Finset (Fin 4)) (κ : Fin 4)
    (hκ : κ ∉ S) (x : Vertex N) (μ : Fin 4) (hμ : μ ∈ S) (h1 : L x μ = 1) :
    act (lineGauge L S κ) L x μ = 1 := by
  unfold act
  rw [lineGauge_step_mem L S κ hκ x μ hμ, h1, mul_one, mul_inv_cancel]

theorem steps_succ (κ : Fin 4) (x : Vertex N) (h : x κ ≠ 0) :
    steps κ (step N x κ) = steps κ x + 1 := by
  unfold steps
  rw [step_apply_same]
  set z := x κ - 1 with hz
  have hz1 : z + 1 = x κ := by rw [hz]; ring
  have hx : x κ + 1 - 1 = z + 1 := by rw [hz1]; ring
  rw [hx]
  have hlt : z.val + 1 < N := by
    have hb := ZMod.val_lt z
    by_contra hge
    have heq : z.val + 1 = N := by omega
    apply h
    rw [← hz1, ← ZMod.natCast_zmod_val z]
    have : ((z.val + 1 : ℕ) : ZMod N) = 0 := by
      rw [heq]
      exact ZMod.natCast_self N
    exact_mod_cast this
  have h1 : (1 : ZMod N).val + z.val < N ∨ True := Or.inr trivial
  by_cases hN : N = 1
  · omega
  · have hone : (1 : ZMod N).val = 1 := by
      haveI : Fact (1 < N) := ⟨by have := NeZero.pos N; omega⟩
      exact ZMod.val_one N
    rw [ZMod.val_add_of_lt (by rw [hone]; exact hlt), hone]

/-- A point on its own reset slab is reached from its origin by `steps`. -/
theorem walk_origin (S : Finset (Fin 4)) (κ : Fin 4) (hκ : κ ∉ S) (x : Vertex N)
    (hx : ∀ i ∈ S, x i = 1) : walk κ (origin S κ x) (steps κ x) = x := by
  funext i
  unfold walk origin steps resetSet
  by_cases hi : i = κ
  · subst hi
    have hk : ((x i - 1).val • (Pi.single i (1 : ZMod N) : Vertex N)) i = x i - 1 := by
      rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    simp only [Pi.add_apply, Function.update_self]
    rw [hk]
    ring
  · have hs : ((steps κ x) • (Pi.single κ 1 : Vertex N)) i = 0 := by simp [hi]
    simp only [Pi.add_apply, Function.update_of_ne hi, Pi.smul_apply, Pi.single_eq_of_ne hi,
      smul_zero, add_zero]
    by_cases hm : i ∈ S
    · simp [hm, hx i hm]
    · simp [hm]

theorem origin_step_self (S : Finset (Fin 4)) (κ : Fin 4) (hκ : κ ∉ S) (x : Vertex N) :
    origin S κ (step N x κ) = origin S κ x := by
  funext i
  unfold origin resetSet
  by_cases hi : i = κ
  · subst hi
    simp
  · simp only [Function.update_of_ne hi]
    by_cases hm : i ∈ S
    · simp [hm]
    · simp [hm, step_apply_other x κ i hi]

/-- On the reset slab and off the seam, the new link in direction `κ` is the identity. -/
theorem act_one_on_slab (L : Vertex N → Fin 4 → Q) (S : Finset (Fin 4)) (κ : Fin 4) (hκ : κ ∉ S)
    (x : Vertex N) (hx : ∀ i ∈ S, x i = 1) (h0 : x κ ≠ 0) :
    act (lineGauge L S κ) L x κ = 1 := by
  unfold act lineGauge
  rw [origin_step_self S κ hκ x, steps_succ κ x h0]
  simp only [run]
  rw [walk_origin S κ hκ x hx]
  group

/-- The final gauge field of the four-stage construction. -/
structure Axial (A : Vertex N → Fin 4 → Q) : Prop where
  p2 : ∀ x, x 2 ≠ 0 → A x 2 = 1
  p1 : ∀ x, x 2 = 1 → x 1 ≠ 0 → A x 1 = 1
  p3 : ∀ x, x 2 = 1 → x 1 = 1 → x 3 ≠ 0 → A x 3 = 1
  p0 : ∀ x, x 2 = 1 → x 1 = 1 → x 3 = 1 → x 0 ≠ 0 → A x 0 = 1

/-- Every link field is gauge equivalent to an axial one. -/
theorem exists_axial (L : Vertex N → Fin 4 → Q) :
    ∃ g : Vertex N → Q, Axial (act g L) := by
  let g₁ := lineGauge L ∅ 2
  let L₁ := act g₁ L
  have h₁ : ∀ x, x 2 ≠ 0 → L₁ x 2 = 1 := fun x hx =>
    act_one_on_slab L ∅ 2 (by simp) x (by simp) hx
  let S₂ : Finset (Fin 4) := {2}
  let g₂ := lineGauge L₁ S₂ 1
  let L₂ := act g₂ L₁
  have h₂₂ : ∀ x, x 2 ≠ 0 → L₂ x 2 = 1 := fun x hx =>
    act_one_of_mem L₁ S₂ 1 (by decide) x 2 (by decide) (h₁ x hx)
  have h₂₁ : ∀ x, x 2 = 1 → x 1 ≠ 0 → L₂ x 1 = 1 := fun x h2 hx =>
    act_one_on_slab L₁ S₂ 1 (by decide) x (by
      intro i hi
      have : i = 2 := by simpa [S₂] using hi
      rw [this]
      exact h2) hx
  let S₃ : Finset (Fin 4) := {2, 1}
  let g₃ := lineGauge L₂ S₃ 3
  let L₃ := act g₃ L₂
  have h₃₂ : ∀ x, x 2 ≠ 0 → L₃ x 2 = 1 := fun x hx =>
    act_one_of_mem L₂ S₃ 3 (by decide) x 2 (by decide) (h₂₂ x hx)
  have h₃₁ : ∀ x, x 2 = 1 → x 1 ≠ 0 → L₃ x 1 = 1 := fun x h2 hx =>
    act_one_of_mem L₂ S₃ 3 (by decide) x 1 (by decide) (h₂₁ x h2 hx)
  have h₃₃ : ∀ x, x 2 = 1 → x 1 = 1 → x 3 ≠ 0 → L₃ x 3 = 1 := fun x h2 h1 hx =>
    act_one_on_slab L₂ S₃ 3 (by decide) x (by
      intro i hi
      have : i = 2 ∨ i = 1 := by simpa [S₃] using hi
      rcases this with rfl | rfl
      · exact h2
      · exact h1) hx
  let S₄ : Finset (Fin 4) := {2, 1, 3}
  let g₄ := lineGauge L₃ S₄ 0
  refine ⟨fun x => g₄ x * (g₃ x * (g₂ x * g₁ x)), ?_⟩
  have hact : act (fun x => g₄ x * (g₃ x * (g₂ x * g₁ x))) L = act g₄ L₃ := by
    change _ = act g₄ (act g₃ (act g₂ (act g₁ L)))
    rw [act_act, act_act, act_act]
    congr 1
    funext x
    simp only [mul_assoc]
  rw [hact]
  exact
    { p2 := fun x hx => act_one_of_mem L₃ S₄ 0 (by decide) x 2 (by decide) (h₃₂ x hx)
      p1 := fun x h2 hx => act_one_of_mem L₃ S₄ 0 (by decide) x 1 (by decide) (h₃₁ x h2 hx)
      p3 := fun x h2 h1 hx => act_one_of_mem L₃ S₄ 0 (by decide) x 3 (by decide) (h₃₃ x h2 h1 hx)
      p0 := fun x h2 h1 h3 hx => act_one_on_slab L₃ S₄ 0 (by decide) x (by
        intro i hi
        have : i = 2 ∨ i = 1 ∨ i = 3 := by simpa [S₄] using hi
        rcases this with rfl | rfl | rfl
        · exact h2
        · exact h1
        · exact h3) hx }

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedAxial
