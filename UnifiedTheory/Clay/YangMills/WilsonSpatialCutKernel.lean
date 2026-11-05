/- Block/exterior coordinates for the actual raw Wilson kernel. The original
full-transfer eigenvalue controls the cut kernel at a boundary-only cost. -/
import UnifiedTheory.Clay.YangMills.WilsonSpatialCutEnergy
import UnifiedTheory.Clay.YangMills.CompactKernelProductComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSpatialCutKernel
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalGauge WilsonTemporalInfluence
open WilsonGroundLocalComparison WilsonGroundHeatBath WilsonSpatialCutEnergy
open CompactKernelOperator CompactKernelProductComparison WilsonPositiveGroundState
open WilsonSingleLinkStaples (character character_continuous)

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

abbrev Coordinates (S : Finset (SpatialVertex n × Fin 3)) := Outside n S × Inside n S

def outsideField (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) : Slice n :=
  WilsonBlockMarginal.assemble S (r,1)

def insideField (S : Finset (SpatialVertex n × Fin 3)) (a : Inside n S) : Slice n :=
  WilsonBlockMarginal.assemble S (1,a)

omit [NeZero n] in
theorem outsideField_continuous (S : Finset (SpatialVertex n × Fin 3)) :
    Continuous (outsideField n S) :=
  (WilsonBlockMarginal.assemble_continuous S).comp
    (f := fun r : Outside n S => (r,1)) (continuous_id.prodMk continuous_const)

omit [NeZero n] in
theorem insideField_continuous (S : Finset (SpatialVertex n × Fin 3)) :
    Continuous (insideField n S) :=
  (WilsonBlockMarginal.assemble_continuous S).comp
    (f := fun a : Inside n S => (1,a)) (continuous_const.prodMk continuous_id)

def exterior (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) :
    C(Outside n S × Outside n S, ℝ) :=
  ⟨fun z => piece n β Sᶜ (outsideField n S z.1) (outsideField n S z.2),
    (piece_continuous n β Sᶜ).comp
      (f := fun z : Outside n S × Outside n S => (outsideField n S z.1,outsideField n S z.2))
      (((outsideField_continuous n S).comp continuous_fst).prodMk
        ((outsideField_continuous n S).comp continuous_snd))⟩

def interior (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) :
    C(Inside n S × Inside n S, ℝ) :=
  ⟨fun z => piece n β S (insideField n S z.1) (insideField n S z.2),
    (piece_continuous n β S).comp
      (f := fun z : Inside n S × Inside n S => (insideField n S z.1,insideField n S z.2))
      (((insideField_continuous n S).comp continuous_fst).prodMk
        ((insideField_continuous n S).comp continuous_snd))⟩

def full (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) :
    C(Coordinates n S × Coordinates n S, ℝ) :=
  ⟨fun z => rawKernel character β 2 (WilsonBlockMarginal.assemble S z.1)
    (WilsonBlockMarginal.assemble S z.2),
    (rawKernel_continuous character character_continuous β 2).comp
      (f := fun z : Coordinates n S × Coordinates n S =>
        (WilsonBlockMarginal.assemble S z.1,WilsonBlockMarginal.assemble S z.2))
      (((WilsonBlockMarginal.assemble_continuous S).comp continuous_fst).prodMk
        ((WilsonBlockMarginal.assemble_continuous S).comp continuous_snd))⟩

def cut (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) :
    C(Coordinates n S × Coordinates n S, ℝ) := productKernel (exterior n β S) (interior n β S)

theorem exterior_piece (β : ℝ) (S : Finset (SpatialVertex n × Fin 3))
    (z w : Coordinates n S) :
    piece n β Sᶜ (WilsonBlockMarginal.assemble S z) (WilsonBlockMarginal.assemble S w) =
      exterior n β S (z.1,w.1) := by
  apply piece_congr
  · intro e he
    simp only [Finset.mem_compl] at he
    simp only [outsideField, WilsonBlockMarginal.assemble_outside S _ e he]
  · intro e he
    simp only [Finset.mem_compl] at he
    simp only [outsideField, WilsonBlockMarginal.assemble_outside S _ e he]

theorem interior_piece (β : ℝ) (S : Finset (SpatialVertex n × Fin 3))
    (z w : Coordinates n S) :
    piece n β S (WilsonBlockMarginal.assemble S z) (WilsonBlockMarginal.assemble S w) =
      interior n β S (z.2,w.2) := by
  apply piece_congr
  · intro e he
    simp only [insideField, WilsonBlockMarginal.assemble_inside S _ e he]
  · intro e he
    simp only [insideField, WilsonBlockMarginal.assemble_inside S _ e he]

theorem cut_lower (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (z w : Coordinates n S) :
    Real.exp (-4*β*(boundary n S).card)*cut n β S (z,w) ≤ full n β S (z,w) := by
  have h := raw_cut_lower n β hβ S (WilsonBlockMarginal.assemble S z)
    (WilsonBlockMarginal.assemble S w)
  rw [exterior_piece, interior_piece] at h
  simpa only [cut, productKernel, ContinuousMap.coe_mk, mul_comm] using h

theorem cut_upper (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (z w : Coordinates n S) : full n β S (z,w) ≤ cut n β S (z,w) := by
  have h := raw_cut_upper n β hβ S (WilsonBlockMarginal.assemble S z)
    (WilsonBlockMarginal.assemble S w)
  rw [exterior_piece, interior_piece] at h
  simpa only [cut, productKernel, ContinuousMap.coe_mk, mul_comm] using h

/-- The full kernel in product coordinates has the actual original eigenvalue
as its norm upper bound; no exterior eigenfunction is assumed. -/
theorem full_norm_le (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3)) :
    ‖operator ((outsideHaar n S).prod (insideHaar n S)) (full n β S)‖ ≤ ‖transfer n β‖ := by
  let g : C(Coordinates n S, ℝ) :=
    ⟨fun z => ground n β hβ (WilsonBlockMarginal.assemble S z),
      (ground n β hβ).continuous.comp (WilsonBlockMarginal.assemble_continuous S)⟩
  apply CompactKernelWeightedSchur.norm_le _ (full n β S)
    (fun _ _ => (rawKernel_pos _ _ _ _ _).le)
    (fun z w => rawKernel_symm n β _ _) g
    (fun z => ground_pos n β hβ _) _ (norm_nonneg _)
  intro z
  have hp := WilsonBlockMarginal.assemble_preserving S (RegulatedGauge.compactHaar Q)
  have hi := hp.integral_comp (WilsonBlockMarginal.assemble S).measurableEmbedding
    (fun v => rawKernel character β 2 (WilsonBlockMarginal.assemble S z) v*ground n β hβ v)
  exact hi.trans (ground_raw_equation n β hβ _)

/-- Cutting only the crossing spatial plaquettes costs at most exp(4 beta b),
where b is their actual count, independently of exterior volume. -/
theorem cut_norm_le (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3)) :
    ‖operator ((outsideHaar n S).prod (insideHaar n S)) (cut n β S)‖ ≤
      Real.exp (4*β*(boundary n S).card)*‖transfer n β‖ := by
  have h := CompactKernelDomination.norm_domination
    ((outsideHaar n S).prod (insideHaar n S)) (cut n β S) (full n β S)
    (Real.exp (4*β*(boundary n S).card)) (Real.exp_pos _).le (fun z w => by
      have hh := mul_le_mul_of_nonneg_left (cut_lower n β hβ S z w)
        (Real.exp_pos (4*β*(boundary n S).card)).le
      have he : Real.exp (4*β*(boundary n S).card)*Real.exp (-4*β*(boundary n S).card) = 1 := by
        rw [← Real.exp_add, show 4*β*(boundary n S).card+ -4*β*(boundary n S).card = 0 by ring,
          Real.exp_zero]
      rw [← mul_assoc, he, one_mul] at hh
      rw [abs_of_pos (show 0 < cut n β S (z,w) from
        mul_pos (piece_pos n β Sᶜ _ _) (piece_pos n β S _ _))]
      exact hh)
  exact h.trans (mul_le_mul_of_nonneg_left (full_norm_le n β hβ S) (Real.exp_pos _).le)

def insideMass (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) : ℝ :=
  ∫ z, interior n β S z ∂(insideHaar n S).prod (insideHaar n S)

theorem insideMass_pos (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) :
    0 < insideMass n β S := by
  apply (integral_pos_iff_support_of_nonneg
    (fun z => (piece_pos n β S _ _).le)
    (CompactDensityEntropy.continuous_integrable _ _ (interior n β S).continuous)).mpr
  have hs : Function.support (interior n β S) = Set.univ := by
    ext z
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (piece_pos n β S _ _).ne'
  change 0 < ((insideHaar n S).prod (insideHaar n S)) (Function.support (interior n β S))
  rw [hs, measure_univ]
  exact zero_lt_one

theorem insideMass_row (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) :
    insideMass n β S =
      ∫ a, realSmoothing (insideHaar n S) (interior n β S) 1 a ∂insideHaar n S := by
  rw [insideMass, integral_prod _
    (CompactDensityEntropy.continuous_integrable _ _ (interior n β S).continuous)]
  simp only [realSmoothing_integral, ContinuousMap.one_apply, mul_one]

/-- The exterior norm cancels against the original normalization after paying
only the block's explicit kernel mass and the crossing-plaquette cost. -/
theorem exterior_normalization (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3)) :
    insideMass n β S*‖operator (outsideHaar n S) (exterior n β S)‖ ≤
      Real.exp (4*β*(boundary n S).card)*‖transfer n β‖ := by
  rw [insideMass_row]
  exact (mean_mul_norm_le (outsideHaar n S) (insideHaar n S) (exterior n β S)
    (fun _ _ => (piece_pos n β Sᶜ _ _).le) (interior n β S)
    (by rw [← insideMass_row]; exact insideMass_pos n β S)).trans (cut_norm_le n β hβ S)

end
end UnifiedTheory.Clay.YangMills.WilsonSpatialCutKernel
