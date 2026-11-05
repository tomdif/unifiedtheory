/- Exact seam area and kinetic tilt for the actual center symmetry.
The seam has n squared links, including the positive-period degeneracies. -/
import UnifiedTheory.Clay.YangMills.WilsonCenterCoercivity
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCenterSeamGeometry
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonCenterTwist
open WilsonSingleLinkStaples (character character_re)

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def vertices (i : Fin 3) : Finset (SpatialVertex n) :=
  Finset.univ.filter (fun x => x i = 0)

def links (i : Fin 3) : Finset (SpatialVertex n × Fin 3) :=
  (vertices n i).image (fun x => (x, i))

theorem mem_links (i : Fin 3) (e : SpatialVertex n × Fin 3) :
    e ∈ links n i ↔ e.2 = i ∧ e.1 i = 0 := by
  classical
  rcases e with ⟨x,j⟩
  simp [links, vertices, eq_comm, and_comm]

theorem vertices_card (i : Fin 3) : (vertices n i).card = n^2 := by
  classical
  have hh := Fintype.card_filter_piFinset_const_eq_of_mem
    (Finset.univ : Finset (ZMod n)) i (Finset.mem_univ (0 : ZMod n))
  simpa [vertices] using hh

theorem links_card (i : Fin 3) : (links n i).card = n^2 := by
  rw [links, Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h), vertices_card]

theorem twist_away (i : Fin 3) (u : Slice n) (e : SpatialVertex n × Fin 3)
    (he : e ∉ links n i) : twist n i u e = u e := by
  rw [mem_links] at he
  simp only [twist_apply, if_neg he]

theorem twist_on (i : Fin 3) (u : Slice n) (e : SpatialVertex n × Fin 3)
    (he : e ∈ links n i) : twist n i u e = -u e := by
  rw [mem_links] at he
  simp only [twist_apply, if_pos he]

theorem tilt_formula (i : Fin 3) (β : ℝ) (u v : Slice n) :
    WilsonTemporalInfluence.tilt n β (links n i) (twist n i u) u v =
      Real.exp (-2 * β * ∑ e ∈ links n i, (character ((u e)⁻¹ * v e)).re) := by
  unfold WilsonTemporalInfluence.tilt
  have hh (e : SpatialVertex n × Fin 3) (he : e ∈ links n i) :
      (character ((twist n i u e)⁻¹ * v e)).re - (character ((u e)⁻¹ * v e)).re =
        -2 * (character ((u e)⁻¹ * v e)).re := by
    rw [twist_on n i u e he]
    simp [character_re, Unitary.coe_neg]
    ring
  rw [Finset.sum_congr rfl hh, ← Finset.mul_sum]
  congr 1
  ring

theorem tilt_identity (i : Fin 3) (β : ℝ) :
    WilsonTemporalInfluence.tilt n β (links n i) (twist n i 1) 1 1 =
      Real.exp (-(4 * β * (n : ℝ)^2)) := by
  rw [tilt_formula]
  simp only [Pi.one_apply, inv_one, one_mul]
  norm_num [character_re, links_card]
  ring

theorem tilt_opposite (i : Fin 3) (β : ℝ) :
    WilsonTemporalInfluence.tilt n β (links n i) (twist n i 1) 1 (twist n i 1) =
      Real.exp (4 * β * (n : ℝ)^2) := by
  rw [tilt_formula]
  have hh (e : SpatialVertex n × Fin 3) (he : e ∈ links n i) :
      (character (((1 : Slice n) e)⁻¹ * twist n i 1 e)).re = -2 := by
    rw [twist_on n i 1 e he]
    norm_num [character_re, Unitary.coe_neg]
  rw [Finset.sum_congr rfl hh]
  simp only [Finset.sum_const, nsmul_eq_mul, links_card, Nat.cast_pow]
  congr 1
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonCenterSeamGeometry
