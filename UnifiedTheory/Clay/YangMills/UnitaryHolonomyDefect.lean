/- Exact unitary holonomy defect and a uniform open identity neighborhood
making every four-link plaquette defect small. This is a lattice statement;
no holonomy-to-continuum-curvature expansion is assumed. -/
import UnifiedTheory.Clay.YangMills.UnitaryCharacterObservables

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Clay.YangMills.UnitaryHolonomyDefect
noncomputable section
open Matrix WilsonCrossingKernel UnitaryCharacterObservables
open scoped Topology

variable {d G : Type*} [Fintype d] [DecidableEq d] [Group G]

def defect (ρ : G →* Matrix.unitaryGroup d ℂ) (g : G) : ℝ :=
  (Fintype.card d : ℝ) - (unitaryCharacter ρ g).re

@[simp] theorem defect_one (ρ : G →* Matrix.unitaryGroup d ℂ) : defect ρ 1 = 0 := by
  simp only [defect, unitaryCharacter_one, Complex.natCast_re, sub_self]

theorem defect_nonneg (ρ : G →* Matrix.unitaryGroup d ℂ) (g : G) : 0 ≤ defect ρ g := by
  exact sub_nonneg.mpr ((Complex.re_le_norm _).trans (unitary_trace_bound (ρ g)))

theorem defect_le (ρ : G →* Matrix.unitaryGroup d ℂ) (g : G) :
    defect ρ g ≤ 2 * (Fintype.card d : ℝ) := by
  have h := (neg_abs_le (unitaryCharacter ρ g).re).trans
    (le_refl _)
  have hr := Complex.abs_re_le_norm (unitaryCharacter ρ g)
  have hb : ‖unitaryCharacter ρ g‖ ≤ (Fintype.card d : ℝ) := unitary_trace_bound (ρ g)
  dsimp [defect]
  linarith

/-- Twice the character defect is the trace of the positive matrix square,
the squared Hilbert--Schmidt distance from the identity. -/
theorem matrix_square_trace (A : Matrix.unitaryGroup d ℂ) :
    (Matrix.trace (((1 : Matrix d d ℂ) - (A : Matrix d d ℂ))ᴴ *
      ((1 : Matrix d d ℂ) - (A : Matrix d d ℂ)))).re =
      2 * ((Fintype.card d : ℝ) - (Matrix.trace (A : Matrix d d ℂ)).re) := by
  have hA : (A : Matrix d d ℂ)ᴴ * (A : Matrix d d ℂ) = 1 := A.2.1
  simp only [conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, hA,
    one_mul, mul_one, trace_sub, trace_one, trace_conjTranspose,
    Complex.sub_re, Complex.natCast_re, Complex.star_def, Complex.conj_re]
  ring

theorem defect_matrix_square (ρ : G →* Matrix.unitaryGroup d ℂ) (g : G) :
    defect ρ g = (Matrix.trace (((1 : Matrix d d ℂ) - (ρ g : Matrix d d ℂ))ᴴ *
      ((1 : Matrix d d ℂ) - (ρ g : Matrix d d ℂ)))).re / 2 := by
  rw [matrix_square_trace]
  dsimp [defect, unitaryCharacter]
  ring

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem defect_continuous (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ) :
    Continuous (defect ρ) :=
  continuous_const.sub (Complex.continuous_re.comp (unitaryCharacter_continuous ρ hρ))

/-- The same neighborhood works for every plaquette in every period. -/
theorem exists_identity_neighborhood (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
      ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, ∀ d ∈ V, defect ρ (a * b * c⁻¹ * d⁻¹) ≤ eps := by
  let f (p : (G × G) × (G × G)) := defect ρ (p.1.1 * p.1.2 * p.2.1⁻¹ * p.2.2⁻¹)
  have hf : Continuous f := (defect_continuous ρ hρ).comp
    (((continuous_fst.fst.mul continuous_fst.snd).mul continuous_snd.fst.inv).mul
      continuous_snd.snd.inv)
  have hm : {p | f p < eps} ∈ 𝓝 (((1 : G), 1), (1, 1)) :=
    (isOpen_lt hf continuous_const).mem_nhds (by
      change defect ρ (1 * 1 * 1⁻¹ * 1⁻¹) < eps
      simpa using heps)
  obtain ⟨W, hWo, hW1, hWW⟩ := exists_nhds_square hm
  obtain ⟨V, hVo, hV1, hVV⟩ := exists_nhds_square (hWo.mem_nhds hW1)
  refine ⟨V, hVo, hV1, ?_⟩
  intro a ha b hb c hc d hd
  have hab : (a, b) ∈ W := hVV (show (a,b) ∈ V ×ˢ V from ⟨ha,hb⟩)
  have hcd : (c, d) ∈ W := hVV (show (c,d) ∈ V ×ˢ V from ⟨hc,hd⟩)
  have hh : f ((a,b),(c,d)) < eps :=
    hWW (show ((a,b),(c,d)) ∈ W ×ˢ W from ⟨hab,hcd⟩)
  exact hh.le

end
end UnifiedTheory.Clay.YangMills.UnitaryHolonomyDefect
