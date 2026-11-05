/- Eight actual independent colors on an open Wilson time cylinder.
Spatial parity is periodic; temporal parity uses the ordinary finite time
coordinate. No temporal-period or long-cylinder bound is assumed. -/
import UnifiedTheory.Clay.YangMills.WilsonCylinderGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCylinderColors
noncomputable section
open WilsonTimeSlab WilsonCylinderGeometry

abbrev Color := Fin 4 × ZMod 2

variable (n L : ℕ)

/-- Bipartite parity of the three periodic spatial coordinates. -/
def spatialParity (heven : 2 ∣ n) (x : SpatialVertex n) : ZMod 2 :=
  ∑ i, ZMod.castHom heven (ZMod 2) (x i)

theorem spatialParity_step (heven : 2 ∣ n) (x : SpatialVertex n) (i : Fin 3) :
    spatialParity n heven (spatialStep n x i) = spatialParity n heven x + 1 := by
  classical
  change (∑ j, ZMod.castHom heven (ZMod 2)
    (x j + (Pi.single i (1 : ZMod n) : SpatialVertex n) j)) = _
  simp only [map_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, map_one]
  · intro j _ hji
    simp only [Pi.single_eq_of_ne hji, map_zero]
  · simp

/-- Direction plus time-and-space parity, with no temporal wraparound. -/
def color (heven : 2 ∣ n) : Link n L → Color
  | Sum.inl a => (a.2.2.succ, (a.1.val : ZMod 2) + spatialParity n heven a.2.1)
  | Sum.inr a => (0, (a.1.val : ZMod 2) + spatialParity n heven a.2)

/-- The four slots of every spatial square have distinct actual colors. -/
theorem spatialBoundary_color_injective (heven : 2 ∣ n) (p : SpatialPlaquette n L) :
    Function.Injective (fun k => color n L heven (spatialBoundary n L p k)) := by
  intro i j h
  have hdir : p.2.2.1.1 ≠ p.2.2.1.2 := ne_of_lt p.2.2.2
  fin_cases i <;> fin_cases j <;>
    simp_all [spatialBoundary, color, spatialParity_step, Ne.symm hdir]

/-- Temporal squares also have four distinct colors, including both endpoint slices. -/
theorem temporalBoundary_color_injective (heven : 2 ∣ n) (p : TemporalPlaquette n L) :
    Function.Injective (fun k => color n L heven (temporalBoundary n L p k)) := by
  intro i j h
  have hdir : p.2.2.succ ≠ (0 : Fin 4) := Fin.succ_ne_zero _
  fin_cases i <;> fin_cases j <;>
    simp_all [temporalBoundary, color, spatialParity_step, add_assoc, add_comm, Ne.symm hdir]

/-- Every actual open-cylinder plaquette has four different direction/parity colors. -/
theorem boundary_color_injective (heven : 2 ∣ n) (p : Plaquette n L) :
    Function.Injective (fun k => color n L heven (boundary n L p k)) := by
  rcases p with p | p
  · exact spatialBoundary_color_injective n L heven p
  · exact temporalBoundary_color_injective n L heven p

/-- Consequently the four positive-link occurrences in each square are genuinely distinct. -/
theorem boundary_injective (heven : 2 ∣ n) (p : Plaquette n L) :
    Function.Injective (boundary n L p) := by
  intro i j h
  exact boundary_color_injective n L heven p (congrArg (color n L heven) h)

theorem incidentLinks_card (heven : 2 ∣ n) (p : Plaquette n L) :
    (incidentLinks n L p).card = 4 := by
  letI : DecidableEq (Link n L) := WilsonCylinderGeometry.linkDecidableEq n L
  simpa only [incidentLinks, Finset.card_univ, Fintype.card_fin] using
    Finset.card_image_of_injective (Finset.univ : Finset (Fin 4))
      (boundary_injective n L heven p)

variable [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n L) := Classical.decEq _
local instance colorDecidableEq : DecidableEq Color := Classical.decEq _

/-- No actual plaquette contains two distinct selected coordinates. -/
def Independent (S : Finset (Link n L)) : Prop :=
  ∀ p : Plaquette n L, ∀ a ∈ S, ∀ b ∈ S,
    incident n L p a → incident n L p b → a = b

def colorBlock (heven : 2 ∣ n) (c : Color) : Finset (Link n L) :=
  Finset.univ.filter (fun a => color n L heven a = c)

theorem mem_colorBlock (heven : 2 ∣ n) (c : Color) (a : Link n L) :
    a ∈ colorBlock n L heven c ↔ color n L heven a = c := by simp [colorBlock]

/-- Eight independent product-update blocks for every cylinder length L. -/
theorem colorBlock_independent (heven : 2 ∣ n) (c : Color) :
    Independent n L (colorBlock n L heven c) := by
  intro p a ha b hb hpa hpb
  obtain ⟨i, rfl⟩ := (incident_iff n L p a).mp hpa
  obtain ⟨j, rfl⟩ := (incident_iff n L p b).mp hpb
  have hc := ((mem_colorBlock n L heven c _).mp ha).trans
    ((mem_colorBlock n L heven c _).mp hb).symm
  exact congrArg (boundary n L p) (boundary_color_injective n L heven p hc)

theorem colorBlock_disjoint (heven : 2 ∣ n) (c d : Color) (hcd : c ≠ d) :
    Disjoint (colorBlock n L heven c) (colorBlock n L heven d) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  exact hcd (((mem_colorBlock n L heven c a).mp ha).symm.trans
    ((mem_colorBlock n L heven d a).mp hb))

theorem mem_own_colorBlock (heven : 2 ∣ n) (a : Link n L) :
    a ∈ colorBlock n L heven (color n L heven a) :=
  (mem_colorBlock n L heven _ a).mpr rfl

omit [NeZero n] in
theorem color_card : Fintype.card Color = 8 := by decide

/-- Coverage remains exactly one eighth, including arbitrarily long cylinders and endpoints. -/
theorem uniform_color_coverage (heven : 2 ∣ n) (a : Link n L) :
    (∑ c : Color, if a ∈ colorBlock n L heven c then (1 / 8 : ℝ) else 0) = 1 / 8 := by
  simp_rw [mem_colorBlock]
  simp

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderColors
