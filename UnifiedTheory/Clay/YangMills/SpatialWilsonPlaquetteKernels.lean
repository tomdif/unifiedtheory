/- The actual spatial plaquette factors in midpoint coordinates. Crossing
plaquettes give SU(2) kernels; the symmetrized interior factors are rank one.
The symmetrization becomes the original weight only after the whole action
has been proved reflection invariant. -/
import UnifiedTheory.Clay.YangMills.SpatialHalfEdgeLocality
import UnifiedTheory.Clay.YangMills.SU2ReflectionInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonPlaquetteKernels
noncomputable section
open WilsonTimeSlab SpatialHalfEdgeGeometry SpatialHalfEdgeSplit
open SpatialPlaquetteCutGeometry SpatialPlaquetteHalfPaths SpatialHalfEdgeLocality
open WilsonSingleLinkStaples PositiveKernelForm PositiveKernelInsertion

variable (n : ℕ) [NeZero n]

def defect (p : Plaquette n) (u : SpatialLinks (2 * n) Q) : ℝ :=
  2 - (character (spatialHolonomy u p.1 p.2.val.1 p.2.val.2)).re

def Crossing (p : Plaquette n) : Prop := p.2.val.1 = 0 ∧
  reflectVertex (2 * n) p.1 = spatialStep (2 * n) p.1 0

omit [NeZero n] in
theorem defect_continuous (p : Plaquette n) : Continuous (defect n p) := by
  unfold defect
  apply continuous_const.sub
  apply Complex.continuous_re.comp
  apply character_continuous.comp
  unfold spatialHolonomy
  fun_prop

theorem noncrossing_side (p : Plaquette n) (hp : ¬ Crossing n p) :
    VertexPositive n (spatialStep (2 * n) p.1 p.2.val.1) ↔ VertexPositive n p.1 := by
  by_cases hi : p.2.val.1 = 0
  · rw [hi]
    rcases normal_partition n p.1 with h | h
    · exact h.symm
    · exact False.elim (hp ⟨hi,h⟩)
  · exact tangent_side n p.1 p.2.val.1 hi

theorem interior_defect (p : Plaquette n) (hp : ¬ Crossing n p) (a b : Half n Q) :
    defect n p (assemble n Q (a,b)) =
      defect n p (assemble n Q (sideHalf n Q a b p.1,sideHalf n Q a b p.1)) := by
  have hj : p.2.val.2 ≠ 0 := by
    intro h
    have hl := p.2.property
    rw [h] at hl
    exact (not_lt_of_ge (Fin.zero_le _)) hl
  unfold defect
  rw [holonomy_on_side n Q a b p.1 p.2.val.1 p.2.val.2 hj (noncrossing_side n p hp)]

theorem crossing_defect (p : Plaquette n) (hp : Crossing n p) (a b : Half n Q) :
    defect n p (assemble n Q (a,b)) =
      2 - (character ((halfPath Q n p.1 p.2.val.2 a)⁻¹ *
        halfPath Q n p.1 p.2.val.2 b)).re := by
  have hj : p.2.val.2 ≠ 0 := by
    intro h
    have hl := p.2.property
    rw [h] at hl
    exact (not_lt_of_ge (Fin.zero_le _)) hl
  unfold defect
  rw [hp.1]
  change 2 - (character (spatialHolonomy (HaarHalfEdges.coarsen Q (join n Q (a,b)))
    p.1 0 p.2.val.2)).re = _
  rw [← path_character (2 * n) Q character character_classFunction,
    startPath_on_side n Q a b p.1 p.2.val.2 hj,
    endPath_on_side n Q a b p.1 p.2.val.2 hj hp.2]
  classical
  by_cases hx : VertexPositive n p.1
  · simp only [sideHalf, if_pos hx]
  · simp only [sideHalf, if_neg hx]
    have he : (halfPath Q n p.1 p.2.val.2 b)⁻¹ * halfPath Q n p.1 p.2.val.2 a =
        ((halfPath Q n p.1 p.2.val.2 a)⁻¹ * halfPath Q n p.1 p.2.val.2 b)⁻¹ := by group
    rw [he, character_inverse_re]

theorem crossing_defect_swap (p : Plaquette n) (hp : Crossing n p) (a b : Half n Q) :
    defect n p (assemble n Q (b,a)) = defect n p (assemble n Q (a,b)) := by
  rw [crossing_defect n p hp b a, crossing_defect n p hp a b]
  have he : (halfPath Q n p.1 p.2.val.2 b)⁻¹ * halfPath Q n p.1 p.2.val.2 a =
      ((halfPath Q n p.1 p.2.val.2 a)⁻¹ * halfPath Q n p.1 p.2.val.2 b)⁻¹ := by group
  rw [he, character_inverse_re]

theorem crossing_factor (p : Plaquette n) (hp : Crossing n p) (s : ℝ) (a b : Half n Q) :
    Real.exp (-s * defect n p (assemble n Q (a,b))) =
      SU2CrossingHaarFloor.kernel s (halfPath Q n p.1 p.2.val.2 a)
        (halfPath Q n p.1 p.2.val.2 b) := by
  rw [crossing_defect n p hp a b]
  unfold SU2CrossingHaarFloor.kernel SU2GaussianMass.weight
  rw [SU2GaussianMass.chord_square, character_re]
  congr 1
  ring

def diagonalDefect (p : Plaquette n) (a : Half n Q) : ℝ :=
  defect n p (assemble n Q (a,a))

def plaquetteKernel (p : Plaquette n) (s : ℝ) (hs : 0 ≤ s) : PositiveKernel (Half n Q) := by
  classical
  exact if Crossing n p then
    pullback (SU2CrossingHaarFloor.positiveKernel s hs) (halfPath Q n p.1 p.2.val.2)
  else KernelHilbertRealization.vectorKernel
    (fun a : Half n Q => (Real.exp (-(s / 2) * diagonalDefect n p a) : ℂ))

theorem plaquetteKernel_value (p : Plaquette n) (s : ℝ) (hs : 0 ≤ s) (a b : Half n Q) :
    (plaquetteKernel n p s hs).value (a,b) =
      (Real.exp (-(s / 2) * (defect n p (assemble n Q (a,b)) +
        defect n p (assemble n Q (b,a)))) : ℂ) := by
  classical
  by_cases hp : Crossing n p
  · simp only [plaquetteKernel, if_pos hp, pullback, SU2CrossingHaarFloor.positiveKernel]
    rw [crossing_defect_swap n p hp a b]
    have he : -(s / 2) * (defect n p (assemble n Q (a,b)) +
        defect n p (assemble n Q (a,b))) = -s * defect n p (assemble n Q (a,b)) := by ring
    rw [he, crossing_factor n p hp s a b]
  · simp only [plaquetteKernel, if_neg hp, KernelHilbertRealization.vectorKernel,
      RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    rw [interior_defect n p hp a b, interior_defect n p hp b a]
    by_cases hx : VertexPositive n p.1 <;>
      simp only [sideHalf, hx, ↓reduceIte, diagonalDefect] <;> ring

theorem plaquetteKernel_continuous (p : Plaquette n) (s : ℝ) (hs : 0 ≤ s) :
    Continuous (plaquetteKernel n p s hs).value := by
  have hd := defect_continuous n p
  have ha := assemble_continuous n Q
  have hr : Continuous (fun z : Half n Q × Half n Q =>
      (Real.exp (-(s / 2) * (defect n p (assemble n Q z) +
        defect n p (assemble n Q (z.2,z.1)))) : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    exact Real.continuous_exp.comp (continuous_const.mul
      ((hd.comp ha).add (hd.comp (ha.comp continuous_swap))))
  exact hr.congr (fun z => (plaquetteKernel_value n p s hs z.1 z.2).symm)

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonPlaquetteKernels
