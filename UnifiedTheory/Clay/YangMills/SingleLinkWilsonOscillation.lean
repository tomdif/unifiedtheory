/- Exact single-link locality for the actual four-dimensional periodic Wilson action.
Only six plaquettes can depend on one positive link. The resulting oscillation
bound is independent of volume. It is still linear in the action coefficient;
no polynomial weak-coupling variance estimate or smeared lower bound is asserted. -/
import UnifiedTheory.Clay.YangMills.WilsonUniformVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SingleLinkWilsonOscillation
noncomputable section
open RegulatedGauge PeriodicLattice4 WilsonMomentBounds WilsonUniformVariance

variable (n : ℕ) [NeZero n]

def planes (μ : Fin 4) : Finset Plane := by
  classical
  exact Finset.univ.filter (fun p => p.1.1 = μ ∨ p.1.2 = μ)

theorem planes_card (μ : Fin 4) : (planes μ).card = 3 := by
  fin_cases μ <;> decide

def transverse (μ : Fin 4) (p : Plane) : Fin 4 :=
  if p.1.1 = μ then p.1.2 else p.1.1

def affected (x : Vertex n) (μ : Fin 4) : Finset (PlaquetteIndex n) := by
  classical
  exact (planes μ).biUnion (fun p => {(x, p), (x - Pi.single (transverse μ p) 1, p)})

theorem affected_card (x : Vertex n) (μ : Fin 4) : (affected n x μ).card ≤ 6 := by
  classical
  calc
    (affected n x μ).card ≤ ∑ p ∈ planes μ,
        ({(x, p), (x - Pi.single (transverse μ p) 1, p)} : Finset _).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ planes μ, 2 := by
      apply Finset.sum_le_sum
      intro p _
      exact Finset.card_insert_le _ _ |>.trans (by simp)
    _ = 6 := by simp [planes_card]

theorem base_mem (x : Vertex n) (μ : Fin 4) (p : Plane)
    (hp : p.1.1 = μ ∨ p.1.2 = μ) : (x, p) ∈ affected n x μ := by
  classical
  simp only [affected, Finset.mem_biUnion]
  exact ⟨p, by simpa [planes] using hp, by simp⟩

theorem shifted_mem (x : Vertex n) (μ : Fin 4) (p : Plane)
    (hp : p.1.1 = μ ∨ p.1.2 = μ) :
    (x - Pi.single (transverse μ p) 1, p) ∈ affected n x μ := by
  classical
  simp only [affected, Finset.mem_biUnion]
  exact ⟨p, by simpa [planes] using hp, by simp⟩

variable (G : Type*) [Group G]

theorem plaquette_unchanged (x : Vertex n) (μ : Fin 4) (p : PlaquetteIndex n)
    (hp : p ∉ affected n x μ) (U W : Configuration (Vertex n) G)
    (hUW : ∀ e : Edge (Vertex n), e ≠ selectedLink n x μ → U e = W e) :
    holonomy (Quiver.Symmetrify (Vertex n)) G (orientedExtension (Vertex n) G U) (loops n p) =
      holonomy (Quiver.Symmetrify (Vertex n)) G (orientedExtension (Vertex n) G W) (loops n p) := by
  have h1 : (⟨p.1, step n p.1 p.2.1.1, forward n p.1 p.2.1.1⟩ : Edge (Vertex n)) ≠
      selectedLink n x μ := by
    intro he
    have hd : p.2.1.1 = μ := congrArg (fun e : Edge (Vertex n) => e.2.2.val) he
    have hs : p.1 = x := congrArg Sigma.fst he
    exact hp (hs ▸ base_mem n x μ p.2 (Or.inl hd))
  have h2 : (⟨step n p.1 p.2.1.1, step n (step n p.1 p.2.1.1) p.2.1.2,
      forward n (step n p.1 p.2.1.1) p.2.1.2⟩ : Edge (Vertex n)) ≠ selectedLink n x μ := by
    intro he
    have hd : p.2.1.2 = μ := congrArg (fun e : Edge (Vertex n) => e.2.2.val) he
    have hs : p.1 = x - Pi.single p.2.1.1 1 := eq_sub_iff_add_eq.mpr (congrArg Sigma.fst he)
    have hn : p.2.1.1 ≠ μ := by rw [← hd]; exact ne_of_lt p.2.2
    have ht : transverse μ p.2 = p.2.1.1 := by simp [transverse, hn]
    have hm := shifted_mem n x μ p.2 (Or.inr hd)
    rw [ht, ← hs] at hm
    exact hp hm
  have h3 : (⟨step n p.1 p.2.1.2, step n (step n p.1 p.2.1.1) p.2.1.2,
      ⟨p.2.1.1, step_comm n p.1 p.2.1.2 p.2.1.1⟩⟩ : Edge (Vertex n)) ≠ selectedLink n x μ := by
    intro he
    have hd : p.2.1.1 = μ := congrArg (fun e : Edge (Vertex n) => e.2.2.val) he
    have hs : p.1 = x - Pi.single p.2.1.2 1 := eq_sub_iff_add_eq.mpr (congrArg Sigma.fst he)
    have ht : transverse μ p.2 = p.2.1.2 := by simp [transverse, hd]
    have hm := shifted_mem n x μ p.2 (Or.inl hd)
    rw [ht, ← hs] at hm
    exact hp hm
  have h4 : (⟨p.1, step n p.1 p.2.1.2, forward n p.1 p.2.1.2⟩ : Edge (Vertex n)) ≠
      selectedLink n x μ := by
    intro he
    have hd : p.2.1.2 = μ := congrArg (fun e : Edge (Vertex n) => e.2.2.val) he
    have hs : p.1 = x := congrArg Sigma.fst he
    exact hp (hs ▸ base_mem n x μ p.2 (Or.inr hd))
  simp only [loops, plaquette, holonomy, link, orientedExtension, base]
  rw [hUW _ h1, hUW _ h2, hUW _ h3, hUW _ h4]

theorem action_oscillation (χ : G → ℂ) (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (x : Vertex n) (μ : Fin 4) (U W : Configuration (Vertex n) G)
    (hUW : ∀ e : Edge (Vertex n), e ≠ selectedLink n x μ → U e = W e) :
    |orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c U -
      orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c W| ≤ 12 * |β| * B := by
  classical
  let d : PlaquetteIndex n → ℝ := fun p =>
    (loopObservable (Vertex n) G χ (loops n p) W).re -
      (loopObservable (Vertex n) G χ (loops n p) U).re
  have he : orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c U -
      orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c W = β * ∑ p, d p := by
    unfold orientedWilsonAction wilsonAction
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    change (c - _) - (c - _) = _ - _
    dsimp only [loopObservable]
    ring
  have hd0 (p : PlaquetteIndex n) (hp : p ∉ affected n x μ) : d p = 0 := by
    have hh := plaquette_unchanged n G x μ p hp U W hUW
    change (χ _).re - (χ _).re = 0
    rw [← hh]
    exact sub_self _
  have hs : (∑ p, d p) = ∑ p ∈ affected n x μ, d p := by
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => hd0 p hp)
  have hd (p : PlaquetteIndex n) : |d p| ≤ 2 * B := by
    have hu : |(loopObservable (Vertex n) G χ (loops n p) U).re| ≤ B :=
      (Complex.abs_re_le_norm _).trans (loopObservable_bound _ G χ B hχ _ _)
    have hw : |(loopObservable (Vertex n) G χ (loops n p) W).re| ≤ B :=
      (Complex.abs_re_le_norm _).trans (loopObservable_bound _ G χ B hχ _ _)
    exact (abs_sub _ _).trans (by linarith)
  have hsum : |∑ p ∈ affected n x μ, d p| ≤ 12 * B := by
    calc
      |∑ p ∈ affected n x μ, d p| ≤ ∑ p ∈ affected n x μ, |d p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ affected n x μ, 2 * B := Finset.sum_le_sum (fun p _ => hd p)
      _ = ((affected n x μ).card : ℝ) * (2 * B) := by simp
      _ ≤ 12 * B := by
        have hc : ((affected n x μ).card : ℝ) ≤ 6 := by exact_mod_cast affected_card n x μ
        nlinarith
  rw [he, abs_mul, hs]
  have hm := mul_le_mul_of_nonneg_left hsum (abs_nonneg β)
  nlinarith

end
end UnifiedTheory.Clay.YangMills.SingleLinkWilsonOscillation
