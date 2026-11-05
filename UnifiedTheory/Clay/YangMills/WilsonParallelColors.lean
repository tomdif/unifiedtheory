/- Eight geometric parallel update classes for the actual periodic 4D Wilson
action. The period is even. This is an exact finite-volume decomposition;
it does not identify Euclidean heat-bath time with physical transfer time. -/
import UnifiedTheory.Clay.YangMills.WilsonIndependentBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonParallelColors
noncomputable section
open PeriodicLattice4 WilsonIndependentBlocks

variable (n : ℕ) [NeZero n]

abbrev Color := Fin 4 × ZMod 2

/-- Bipartite parity of the actual four-dimensional periodic vertex. -/
def parity (heven : 2 ∣ n) (x : Vertex n) : ZMod 2 :=
  ∑ μ, ZMod.castHom heven (ZMod 2) (x μ)

omit [NeZero n] in
theorem parity_step (heven : 2 ∣ n) (x : Vertex n) (μ : Fin 4) :
    parity n heven (step n x μ) = parity n heven x + 1 := by
  classical
  change (∑ ν, ZMod.castHom heven (ZMod 2)
    (x ν + (Pi.single μ (1 : ZMod n) : Vertex n) ν)) = _
  simp only [map_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single μ]
  · simp only [Pi.single_eq_same, map_one]
  · intro ν _ hν
    simp only [Pi.single_eq_of_ne hν, map_zero]
  · simp

/-- Direction and vertex parity give eight colors, independent of volume. -/
def color (heven : 2 ∣ n) (a : Link n) : Color := (a.2, parity n heven a.1)

def colorBlock (heven : 2 ∣ n) (c : Color) : Finset (Link n) := by
  classical
  exact Finset.univ.filter (fun a => color n heven a = c)

theorem mem_colorBlock (heven : 2 ∣ n) (c : Color) (a : Link n) :
    a ∈ colorBlock n heven c ↔ color n heven a = c := by
  classical
  simp [colorBlock]

theorem colorBlock_independent (heven : 2 ∣ n) (c : Color) :
    Independent n (colorBlock n heven c) := by
  classical
  apply independent_of_transverse_separation n _ c.1
  · intro a ha
    exact congrArg Prod.fst ((mem_colorBlock n heven c a).mp ha)
  · intro a ha b hb _ ν _ hab
    have hca := congrArg Prod.snd ((mem_colorBlock n heven c a).mp ha)
    have hcb := congrArg Prod.snd ((mem_colorBlock n heven c b).mp hb)
    change parity n heven a.1 = c.2 at hca
    change parity n heven b.1 = c.2 at hcb
    rw [hab, parity_step, hcb] at hca
    have hz : (1 : ZMod 2) = 0 := add_left_cancel (hca.trans (add_zero c.2).symm)
    norm_num at hz

theorem colorBlock_disjoint (heven : 2 ∣ n) (c d : Color) (hcd : c ≠ d) :
    Disjoint (colorBlock n heven c) (colorBlock n heven d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  exact hcd (((mem_colorBlock n heven c a).mp ha).symm.trans
    ((mem_colorBlock n heven d a).mp hb))

theorem mem_own_colorBlock (heven : 2 ∣ n) (a : Link n) :
    a ∈ colorBlock n heven (color n heven a) :=
  (mem_colorBlock n heven _ a).mpr rfl

theorem color_card : Fintype.card Color = 8 := by decide

/-- Every link is selected with probability 1/8 by a uniform color choice,
with no inverse-volume factor. This states update coverage, not a gap. -/
theorem uniform_color_coverage (heven : 2 ∣ n) (a : Link n) :
    (∑ c : Color, if a ∈ colorBlock n heven c then (1 / 8 : ℝ) else 0) = 1 / 8 := by
  classical
  simp_rw [mem_colorBlock]
  simp

end
end UnifiedTheory.Clay.YangMills.WilsonParallelColors
