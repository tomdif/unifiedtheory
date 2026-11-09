/- Discrete Stokes theorem on a periodic 4D lattice: if each plaquette in a plane
equals a power of a central involution, the two winding holonomies through a
point commute up to the total power over the 2-torus. Purely algebraic. -/
import UnifiedTheory.Clay.YangMills.PeriodicLattice4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedRectangle
open PeriodicLattice4

variable {N : ℕ} {G : Type*} [Group G]

/-- The point reached by `k` steps in direction `μ`. -/
def walk (μ : Fin 4) (x : Vertex N) (k : ℕ) : Vertex N :=
  x + k • (Pi.single μ 1 : Vertex N)

theorem walk_zero (μ : Fin 4) (x : Vertex N) : walk μ x 0 = x := by simp [walk]

theorem walk_succ (μ : Fin 4) (x : Vertex N) (k : ℕ) :
    walk μ x (k + 1) = step N (walk μ x k) μ := by
  simp [walk, step, add_smul, add_assoc]

theorem walk_comm (μ ν : Fin 4) (x : Vertex N) (a b : ℕ) :
    walk ν (walk μ x a) b = walk μ (walk ν x b) a := by
  simp only [walk]
  abel

theorem walk_card (μ : Fin 4) (x : Vertex N) : walk μ x N = x := by
  funext k
  simp [walk]

/-- Ordered product of links along a straight run. -/
def run (L : Vertex N → Fin 4 → G) (μ : Fin 4) (x : Vertex N) : ℕ → G
  | 0 => 1
  | a + 1 => run L μ x a * L (walk μ x a) μ

variable (L : Vertex N → Fin 4 → G) (ω : G) (hω : ∀ g : G, Commute ω g)
  (μ ν : Fin 4) (ε : Vertex N → ℕ)
  (hcell : ∀ y, L y μ * L (step N y μ) ν = ω ^ ε y * (L y ν * L (step N y ν) μ))

include hω hcell

theorem strip (x : Vertex N) (a : ℕ) :
    run L μ x a * L (walk μ x a) ν =
      ω ^ (∑ i ∈ Finset.range a, ε (walk μ x i)) * (L x ν * run L μ (step N x ν) a) := by
  have hpow (k : ℕ) (g : G) : Commute (ω ^ k) g := (hω g).pow_left k
  induction a with
  | zero => simp [run, walk_zero]
  | succ a ih =>
    have hw : walk μ (step N x ν) a = step N (walk μ x a) ν := by
      simp only [walk, step]
      abel
    rw [walk_succ μ x a, Finset.sum_range_succ, pow_add]
    simp only [run]
    rw [hw]
    calc
      run L μ x a * L (walk μ x a) μ * L (step N (walk μ x a) μ) ν
          = run L μ x a * (L (walk μ x a) μ * L (step N (walk μ x a) μ) ν) := mul_assoc _ _ _
      _ = run L μ x a * (ω ^ ε (walk μ x a) *
            (L (walk μ x a) ν * L (step N (walk μ x a) ν) μ)) := by rw [hcell]
      _ = ω ^ ε (walk μ x a) * ((run L μ x a * L (walk μ x a) ν) *
            L (step N (walk μ x a) ν) μ) := by
          rw [← mul_assoc (run L μ x a), ← (hpow _ _).eq]
          simp only [mul_assoc]
      _ = ω ^ ε (walk μ x a) * ((ω ^ (∑ i ∈ Finset.range a, ε (walk μ x i)) *
            (L x ν * run L μ (step N x ν) a)) * L (step N (walk μ x a) ν) μ) := by rw [ih]
      _ = _ := by
          simp only [mul_assoc]
          rw [← mul_assoc, (hpow _ _).eq, mul_assoc]

theorem rectangle (x : Vertex N) (a b : ℕ) :
    run L μ x a * run L ν (walk μ x a) b =
      ω ^ (∑ j ∈ Finset.range b, ∑ i ∈ Finset.range a, ε (walk μ (walk ν x j) i)) *
        (run L ν x b * run L μ (walk ν x b) a) := by
  have hpow (k : ℕ) (g : G) : Commute (ω ^ k) g := (hω g).pow_left k
  induction b with
  | zero => simp [run, walk_zero]
  | succ b ih =>
    have hs := strip L ω hω μ ν ε hcell (walk ν x b) a
    rw [Finset.sum_range_succ, pow_add, walk_succ ν x b]
    simp only [run]
    rw [walk_comm μ ν x a b]
    calc
      run L μ x a * (run L ν (walk μ x a) b * L (walk μ (walk ν x b) a) ν)
          = (run L μ x a * run L ν (walk μ x a) b) * L (walk μ (walk ν x b) a) ν :=
        (mul_assoc _ _ _).symm
      _ = (ω ^ (∑ j ∈ Finset.range b, ∑ i ∈ Finset.range a, ε (walk μ (walk ν x j) i)) *
            (run L ν x b * run L μ (walk ν x b) a)) * L (walk μ (walk ν x b) a) ν := by rw [ih]
      _ = ω ^ (∑ j ∈ Finset.range b, ∑ i ∈ Finset.range a, ε (walk μ (walk ν x j) i)) *
            (run L ν x b * (run L μ (walk ν x b) a * L (walk μ (walk ν x b) a) ν)) := by
          simp only [mul_assoc]
      _ = _ := by
          rw [hs, ← mul_assoc (run L ν x b), ← (hpow _ _).eq]
          simp only [mul_assoc]

/-- Winding holonomies commute up to the total central power over the 2-torus. -/
theorem winding (x : Vertex N) :
    run L μ x N * run L ν x N =
      ω ^ (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, ε (walk μ (walk ν x j) i)) *
        (run L ν x N * run L μ x N) := by
  have h := rectangle L ω hω μ ν ε hcell x N N
  rwa [walk_card, walk_card] at h

end UnifiedTheory.Clay.YangMills.Twisted.TwistedRectangle
