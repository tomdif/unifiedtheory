/- A conservative local oscillation estimate for the genuine periodic
Wilson action. Changing all outgoing links at one vertex affects at most
30 plaquettes (five possible base vertices and six planes), independently
of lattice volume. The bound is deliberately not the sharp six-plaquette
count for a single link. -/
import UnifiedTheory.Clay.YangMills.UnitaryCharacterObservables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonLocalOscillation
noncomputable section
open RegulatedGauge PeriodicLattice4 WilsonMomentBounds

variable (n : ℕ) [NeZero n]

def nearbyBases (x : Vertex n) : Finset (Vertex n) := by
  classical
  exact insert x (Finset.univ.image (fun μ : Fin 4 => x - Pi.single μ 1))

theorem nearbyBases_card (x : Vertex n) : (nearbyBases n x).card ≤ 5 := by
  classical
  apply (Finset.card_insert_le _ _).trans
  have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin 4)))
    (f := fun μ => x - Pi.single μ (1 : ZMod n))
  simpa using Nat.add_le_add_right h 1

theorem source_ne_of_not_near (x y : Vertex n) (hy : y ∉ nearbyBases n x) : y ≠ x := by
  intro he
  subst y
  classical
  exact hy (Finset.mem_insert_self _ _)

theorem step_ne_of_not_near (x y : Vertex n) (hy : y ∉ nearbyBases n x) (μ : Fin 4) :
    step n y μ ≠ x := by
  intro he
  have hyx : y = x - Pi.single μ 1 := eq_sub_iff_add_eq.mpr he
  classical
  apply hy
  rw [hyx]
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨μ, Finset.mem_univ _, rfl⟩)

def affected (x : Vertex n) : Finset (PlaquetteIndex n) :=
  (nearbyBases n x) ×ˢ (Finset.univ : Finset Plane)

theorem plane_card : Fintype.card Plane = 6 := by decide

theorem affected_card (x : Vertex n) : (affected n x).card ≤ 30 := by
  rw [affected, Finset.card_product, Finset.card_univ, plane_card]
  exact Nat.mul_le_mul_right 6 (nearbyBases_card n x)

variable (G : Type*) [Group G]

theorem plaquette_unchanged (x y : Vertex n) (hy : y ∉ nearbyBases n x)
    (U W : Configuration (Vertex n) G)
    (hUW : ∀ e : Edge (Vertex n), e.1 ≠ x → U e = W e) (μ ν : Fin 4) :
    holonomy (Quiver.Symmetrify (Vertex n)) G (orientedExtension (Vertex n) G U) (plaquette n y μ ν) =
      holonomy (Quiver.Symmetrify (Vertex n)) G (orientedExtension (Vertex n) G W) (plaquette n y μ ν) := by
  have hy0 := source_ne_of_not_near n x y hy
  have hμ := step_ne_of_not_near n x y hy μ
  have hν := step_ne_of_not_near n x y hy ν
  simp only [plaquette, holonomy, link, orientedExtension]
  rw [hUW _ hy0, hUW _ hμ, hUW _ hν, hUW _ hy0]

theorem action_oscillation (χ : G → ℂ) (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (x : Vertex n) (U W : Configuration (Vertex n) G)
    (hUW : ∀ e : Edge (Vertex n), e.1 ≠ x → U e = W e) :
    |orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c U -
      orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c W| ≤ 60 * |β| * B := by
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
  have hd0 (p : PlaquetteIndex n) (hp : p ∉ affected n x) : d p = 0 := by
    have hbase : p.1 ∉ nearbyBases n x := by
      simpa only [affected, Finset.mem_product, Finset.mem_univ, and_true] using hp
    have hh := plaquette_unchanged n G x p.1 hbase U W hUW p.2.1.1 p.2.1.2
    change (χ _).re - (χ _).re = 0
    dsimp only [loops]
    rw [← hh]
    exact sub_self _
  have hs : (∑ p, d p) = ∑ p ∈ affected n x, d p := by
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => hd0 p hp)
  have hd (p : PlaquetteIndex n) : |d p| ≤ 2 * B := by
    have hu : |(loopObservable (Vertex n) G χ (loops n p) U).re| ≤ B :=
      (Complex.abs_re_le_norm _).trans (loopObservable_bound _ G χ B hχ _ _)
    have hw : |(loopObservable (Vertex n) G χ (loops n p) W).re| ≤ B :=
      (Complex.abs_re_le_norm _).trans (loopObservable_bound _ G χ B hχ _ _)
    exact (abs_sub _ _).trans (by linarith)
  have hsum : |∑ p ∈ affected n x, d p| ≤ 60 * B := by
    calc
      |∑ p ∈ affected n x, d p| ≤ ∑ p ∈ affected n x, |d p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ affected n x, 2 * B := Finset.sum_le_sum (fun p _ => hd p)
      _ = ((affected n x).card : ℝ) * (2 * B) := by simp
      _ ≤ 60 * B := by
        have hc : ((affected n x).card : ℝ) ≤ 30 := by exact_mod_cast affected_card n x
        nlinarith
  rw [he, abs_mul, hs]
  have hm := mul_le_mul_of_nonneg_left hsum (abs_nonneg β)
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonLocalOscillation
