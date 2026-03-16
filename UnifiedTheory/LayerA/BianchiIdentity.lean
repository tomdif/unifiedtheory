/-
  LayerA/BianchiIdentity.lean — Contracted Bianchi identity

  Derives ∇^a R_{ab} = (1/2) ∇_b R from the second Bianchi identity
  via two index contractions using Riemann tensor symmetries.
-/
import Mathlib.Analysis.Normed.Field.Basic

namespace UnifiedTheory.LayerA.Bianchi

variable {n : ℕ}

/-! ### Abstract Riemann curvature data -/

structure RiemannData (n : ℕ) where
  R : Fin n → Fin n → Fin n → Fin n → ℝ
  antisym1 : ∀ a b c d, R a b c d = -R b a c d
  antisym2 : ∀ a b c d, R a b c d = -R a b d c
  dR : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ
  d_antisym1 : ∀ e a b c d, dR e a b c d = -dR e b a c d
  d_antisym2 : ∀ e a b c d, dR e a b c d = -dR e a b d c
  bianchi2 : ∀ e a b c d,
    dR e a b c d + dR a b e c d + dR b e a c d = 0

variable (rd : RiemannData n)

/-! ### Definitions -/

def dRic (e b d : Fin n) : ℝ := ∑ a : Fin n, rd.dR e a b a d
def divRic (b : Fin n) : ℝ := ∑ e : Fin n, dRic rd e b e
def dScalar (b : Fin n) : ℝ := ∑ a : Fin n, dRic rd b a a

/-! ### Contraction lemma -/

lemma d_swap_23 (e b d : Fin n) :
    ∑ c : Fin n, rd.dR e b c c d = -(∑ c : Fin n, rd.dR e c b c d) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  exact rd.d_antisym1 e b c c d

/-! ### Once-contracted Bianchi -/

theorem once_contracted (a b d : Fin n) :
    (∑ c : Fin n, rd.dR c a b c d) -
    (dRic rd a b d) +
    (dRic rd b a d) = 0 := by
  -- Sum bianchi2 over c (with e = c)
  have key : (∑ c : Fin n, (rd.dR c a b c d + rd.dR a b c c d + rd.dR b c a c d)) = 0 :=
    Finset.sum_eq_zero (fun c _ => rd.bianchi2 c a b c d)
  simp only [Finset.sum_add_distrib] at key
  -- 2nd sum: Σ_c dR(a,b,c,c,d) = -dRic(a,b,d)
  have h2 : ∑ c : Fin n, rd.dR a b c c d = -(dRic rd a b d) := by
    simp only [dRic]
    have : (fun c : Fin n => rd.dR a b c c d) = (fun c => -(rd.dR a c b c d)) :=
      funext (fun c => rd.d_antisym1 a b c c d)
    rw [this, Finset.sum_neg_distrib]
  -- 3rd sum = dRic(b,a,d) by definition
  have h3 : ∑ c : Fin n, rd.dR b c a c d = dRic rd b a d := rfl
  rw [h2, h3] at key
  linarith

/-! ### Twice-contracted: the main theorem -/

lemma term1_eq (b : Fin n) :
    (∑ a : Fin n, ∑ c : Fin n, rd.dR c a b c a) = -(divRic rd b) := by
  -- Swap summation: Σ_a Σ_c f(c,a) = Σ_c Σ_a f(c,a)
  rw [Finset.sum_comm]
  -- Now: Σ_c Σ_a dR(c,a,b,c,a)
  -- Use d_antisym2: dR(c,a,b,c,a) = -dR(c,a,b,a,c)
  simp only [divRic, dRic]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact rd.d_antisym2 c a b c a

lemma term2_eq (b : Fin n) :
    (∑ a : Fin n, dRic rd a b a) = divRic rd b := by
  simp only [divRic, dRic]

/-- **Contracted Bianchi Identity.**
    2 · (∇^a R_{ab}) = ∇_b R -/
theorem contracted_bianchi (b : Fin n) :
    2 * divRic rd b = dScalar rd b := by
  have h_once : ∀ a : Fin n,
      (∑ c : Fin n, rd.dR c a b c a) - (dRic rd a b a) + (dRic rd b a a) = 0 :=
    fun a => once_contracted rd a b a
  have hsum : (∑ a : Fin n,
      ((∑ c : Fin n, rd.dR c a b c a) - (dRic rd a b a) + (dRic rd b a a))) = 0 :=
    Finset.sum_eq_zero (fun a _ => h_once a)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [term1_eq rd b, term2_eq rd b] at hsum
  simp only [dScalar] at hsum ⊢
  linarith

/-- **Einstein tensor is divergence-free.** -/
theorem einstein_div_free (b : Fin n) :
    divRic rd b - dScalar rd b / 2 = 0 := by
  have := contracted_bianchi rd b; linarith

end UnifiedTheory.LayerA.Bianchi
