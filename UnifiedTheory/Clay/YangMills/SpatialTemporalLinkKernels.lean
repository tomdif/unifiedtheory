/- Exact temporal-link factors across the proved spatial midpoint split.
The time slices are paired inside each half; positivity is spatial reflection
positivity of the actual temporal interaction, not a change of time direction. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialTemporalLinkKernels
noncomputable section
open WilsonTimeSlab SpatialHalfEdgeGeometry SpatialHalfEdgeSplit SpatialHalfEdgeLocality
open SpatialPlaquetteCutGeometry SpatialPlaquetteHalfPaths WilsonSingleLinkStaples
open PositiveKernelForm PositiveKernelInsertion

variable (n : ℕ) [NeZero n]
abbrev PairHalf := Half n Q × Half n Q

def pairAssemble (a b : PairHalf n) : SpatialLinks (2 * n) Q × SpatialLinks (2 * n) Q :=
  (assemble n Q (a.1,b.1),assemble n Q (a.2,b.2))

def defect (e : Link (2 * n)) (uv : SpatialLinks (2 * n) Q × SpatialLinks (2 * n) Q) : ℝ :=
  2 - (character ((uv.1 e)⁻¹ * uv.2 e)).re

def Crossing (e : Link (2 * n)) : Prop := e.2 = 0 ∧
  reflectVertex (2 * n) e.1 = spatialStep (2 * n) e.1 0

def startPath (U V : HalfEdge (2 * n) → Q) (e : Link (2 * n)) : Q :=
  (V (Sum.inl e))⁻¹ * U (Sum.inl e)

def endPath (U V : HalfEdge (2 * n) → Q) (e : Link (2 * n)) : Q :=
  (V (Sum.inr e))⁻¹ * U (Sum.inr e)

omit [NeZero n] in
theorem path_character (U V : HalfEdge (2 * n) → Q) (e : Link (2 * n)) :
    character ((HaarHalfEdges.coarsen Q U e)⁻¹ * HaarHalfEdges.coarsen Q V e) =
      character ((startPath n U V e)⁻¹ * endPath n U V e) := by
  have he : (HaarHalfEdges.coarsen Q U e)⁻¹ * HaarHalfEdges.coarsen Q V e =
      U (Sum.inr e) * ((startPath n U V e)⁻¹ * endPath n U V e) * (U (Sum.inr e))⁻¹ := by
    unfold HaarHalfEdges.coarsen startPath endPath
    group
  rw [he, character_classFunction]

def timePath (e : Link (2 * n)) (a : PairHalf n) : Q :=
  startPath n (join n Q (a.1,a.1)) (join n Q (a.2,a.2)) e

def pairSide (a b : PairHalf n) (x : SpatialVertex (2 * n)) : PairHalf n :=
  (sideHalf n Q a.1 b.1 x,sideHalf n Q a.2 b.2 x)

theorem startPath_side (a b : PairHalf n) (e : Link (2 * n)) :
    startPath n (join n Q (a.1,b.1)) (join n Q (a.2,b.2)) e =
      timePath n e (pairSide n a b e.1) := by
  unfold startPath timePath pairSide
  rw [join_on_side n Q a.1 b.1 e.1 (Sum.inl e) Iff.rfl,
    join_on_side n Q a.2 b.2 e.1 (Sum.inl e) Iff.rfl]
  rfl

theorem endPath_side (a b : PairHalf n) (e : Link (2 * n)) (he : Crossing n e) :
    endPath n (join n Q (a.1,b.1)) (join n Q (a.2,b.2)) e =
      timePath n e (pairSide n b a e.1) := by
  have hf : reflectLink (2 * n) e = e := by
    rcases e with ⟨x,k⟩
    rcases he with ⟨rfl,hx⟩
    exact boundary_link_fixed (2 * n) x hx
  have hr : reflectHalf (2 * n) (Sum.inl e) = Sum.inr e := by
    simp [reflectHalf, he.1, hf]
  have hu := join_swap n Q (a.1,b.1) (Sum.inl e)
  have hv := join_swap n Q (a.2,b.2) (Sum.inl e)
  rw [hr] at hu hv
  unfold endPath
  rw [← hu, ← hv]
  exact startPath_side n b a e

theorem crossing_defect (e : Link (2 * n)) (he : Crossing n e) (a b : PairHalf n) :
    defect n e (pairAssemble n a b) =
      2 - (character ((timePath n e a)⁻¹ * timePath n e b)).re := by
  unfold defect pairAssemble assemble
  rw [path_character, startPath_side, endPath_side n a b e he]
  classical
  by_cases hx : VertexPositive n e.1
  · simp only [pairSide, sideHalf, if_pos hx, Prod.eta]
  · simp only [pairSide, sideHalf, if_neg hx, Prod.eta]
    have hi : (timePath n e b)⁻¹ * timePath n e a =
        ((timePath n e a)⁻¹ * timePath n e b)⁻¹ := by group
    rw [hi, character_inverse_re]

theorem crossing_defect_swap (e : Link (2 * n)) (he : Crossing n e) (a b : PairHalf n) :
    defect n e (pairAssemble n b a) = defect n e (pairAssemble n a b) := by
  rw [crossing_defect n e he b a, crossing_defect n e he a b]
  have hi : (timePath n e b)⁻¹ * timePath n e a =
      ((timePath n e a)⁻¹ * timePath n e b)⁻¹ := by group
  rw [hi, character_inverse_re]

theorem crossing_factor (e : Link (2 * n)) (he : Crossing n e) (s : ℝ) (a b : PairHalf n) :
    Real.exp (-s * defect n e (pairAssemble n a b)) =
      SU2CrossingHaarFloor.kernel s (timePath n e a) (timePath n e b) := by
  rw [crossing_defect n e he a b]
  unfold SU2CrossingHaarFloor.kernel SU2GaussianMass.weight
  rw [SU2GaussianMass.chord_square, character_re]
  congr 1
  ring

theorem noncrossing_side (e : Link (2 * n)) (he : ¬ Crossing n e) :
    VertexPositive n (spatialStep (2 * n) e.1 e.2) ↔ VertexPositive n e.1 := by
  by_cases hi : e.2 = 0
  · rw [hi]
    rcases normal_partition n e.1 with h | h
    · exact h.symm
    · exact False.elim (he ⟨hi,h⟩)
  · exact tangent_side n e.1 e.2 hi

theorem interior_defect (e : Link (2 * n)) (he : ¬ Crossing n e) (a b : PairHalf n) :
    defect n e (pairAssemble n a b) =
      defect n e (pairAssemble n (pairSide n a b e.1) (pairSide n a b e.1)) := by
  exact congrArg₂ (fun u v : Q => 2 - (character (u⁻¹ * v)).re)
    (link_on_side n Q a.1 b.1 e.1 e.1 e.2 Iff.rfl (noncrossing_side n e he))
    (link_on_side n Q a.2 b.2 e.1 e.1 e.2 Iff.rfl (noncrossing_side n e he))

theorem timePath_continuous (e : Link (2 * n)) : Continuous (timePath n e) := by
  have hj := join_continuous n Q
  unfold timePath startPath
  exact (((continuous_apply (Sum.inl e)).comp
    (hj.comp (continuous_snd.prodMk continuous_snd))).inv).mul
    ((continuous_apply (Sum.inl e)).comp (hj.comp (continuous_fst.prodMk continuous_fst)))

theorem pairAssemble_continuous :
    Continuous (fun z : PairHalf n × PairHalf n => pairAssemble n z.1 z.2) := by
  exact ((assemble_continuous n Q).comp
    ((continuous_fst.fst).prodMk continuous_snd.fst)).prodMk
    ((assemble_continuous n Q).comp (continuous_fst.snd.prodMk continuous_snd.snd))

omit [NeZero n] in
theorem defect_continuous (e : Link (2 * n)) : Continuous (defect n e) := by
  unfold defect
  exact continuous_const.sub (Complex.continuous_re.comp (character_continuous.comp
    (((continuous_apply e).comp continuous_fst).inv.mul
      ((continuous_apply e).comp continuous_snd))))

def linkKernel (e : Link (2 * n)) (s : ℝ) (hs : 0 ≤ s) : PositiveKernel (PairHalf n) := by
  classical
  exact if Crossing n e then
    pullback (SU2CrossingHaarFloor.positiveKernel s hs) (timePath n e)
  else KernelHilbertRealization.vectorKernel (fun a : PairHalf n =>
    (Real.exp (-(s / 2) * defect n e (pairAssemble n a a)) : ℂ))

theorem linkKernel_value (e : Link (2 * n)) (s : ℝ) (hs : 0 ≤ s) (a b : PairHalf n) :
    (linkKernel n e s hs).value (a,b) =
      (Real.exp (-(s / 2) * (defect n e (pairAssemble n a b) +
        defect n e (pairAssemble n b a))) : ℂ) := by
  classical
  by_cases he : Crossing n e
  · simp only [linkKernel, if_pos he, pullback, SU2CrossingHaarFloor.positiveKernel]
    rw [crossing_defect_swap n e he a b]
    have hr : -(s / 2) * (defect n e (pairAssemble n a b) +
        defect n e (pairAssemble n a b)) = -s * defect n e (pairAssemble n a b) := by ring
    rw [hr, crossing_factor n e he s a b]
  · simp only [linkKernel, if_neg he, KernelHilbertRealization.vectorKernel,
      RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    rw [interior_defect n e he a b, interior_defect n e he b a]
    by_cases hx : VertexPositive n e.1 <;>
      simp only [pairSide, sideHalf, hx, ↓reduceIte, Prod.eta] <;> ring

end
end UnifiedTheory.Clay.YangMills.SpatialTemporalLinkKernels
