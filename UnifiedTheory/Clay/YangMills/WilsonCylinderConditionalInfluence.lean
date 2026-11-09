/- Actual one-link conditional influences of the full open Wilson cylinder. -/
import UnifiedTheory.Clay.YangMills.WilsonCylinderCoordinates
import UnifiedTheory.Clay.YangMills.WilsonCylinderInfluenceGeometry
import UnifiedTheory.Clay.YangMills.WilsonSlabBounds
import UnifiedTheory.Clay.YangMills.CompactGibbsOscillation
import UnifiedTheory.Clay.YangMills.GibbsConstantShift
import UnifiedTheory.Clay.YangMills.ParallelOscillation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCylinderConditionalInfluence
noncomputable section
open MeasureTheory RegulatedGauge WilsonCylinderGeometry WilsonSingleLinkStaples
open FiniteIncidenceInfluence

abbrev State (n L : ℕ) := Link n L → Q

variable (n L : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n L) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (Plaquette n L) := Classical.decEq _

/-- The original full plaquette action, including both endpoint spatial potentials. -/
def stateAction (β : ℝ) : C(State n L, ℝ) :=
  ⟨WilsonCylinderCoordinates.flatAction n L Q character β 2,
    WilsonCylinderCoordinates.flatAction_continuous n L Q character character_continuous β 2⟩

/-- The actual full action with one link replaced by its integration variable. -/
def conditionalAction (β : ℝ) (U : State n L) (a : Link n L) : C(Q, ℝ) :=
  ⟨fun q => stateAction n L β (Function.update U a q),
    (stateAction n L β).continuous.comp (continuous_const.update a continuous_id)⟩

def coordinateLaw (β : ℝ) (U : State n L) (a : Link n L) : Measure Q :=
  CompactGibbsContinuity.law (compactHaar Q) (conditionalAction n L β U a)

theorem coordinateLaw_probability (β : ℝ) (U : State n L) (a : Link n L) :
    IsProbabilityMeasure (coordinateLaw n L β U a) :=
  CompactGibbsContinuity.law_probability _ _ (conditionalAction n L β U a).continuous

/-- Actual fundamental-character defect of a cylinder face. -/
def plaquetteTerm (U : State n L) (p : Plaquette n L) : ℝ :=
  2 - (character (plaquetteProduct n L U p)).re

omit [NeZero n] in
theorem plaquetteTerm_continuous (p : Plaquette n L) :
    Continuous (fun U : State n L => plaquetteTerm n L U p) := by
  have h (k : Fin 4) : Continuous (fun U : State n L => U (boundary n L p k)) :=
    continuous_apply _
  have hc : Continuous (fun U : State n L => plaquetteProduct n L U p) :=
    ((h 0 |>.mul (h 1)).mul (h 2).inv).mul (h 3).inv
  exact continuous_const.sub (Complex.continuous_re.comp (character_continuous.comp hc))

omit [NeZero n] in
theorem plaquetteTerm_bounds (U : State n L) (p : Plaquette n L) :
    0 ≤ plaquetteTerm n L U p ∧ plaquetteTerm n L U p ≤ 4 :=
  WilsonSlabBounds.characterDefect_bounds _

omit [NeZero n] in
/-- A face depends only on its actual four positive boundary links. -/
theorem plaquetteTerm_congr (U V : State n L) (p : Plaquette n L)
    (hUV : ∀ e ∈ incidentLinks n L p, U e = V e) :
    plaquetteTerm n L U p = plaquetteTerm n L V p := by
  have h (k : Fin 4) : U (boundary n L p k) = V (boundary n L p k) :=
    hUV _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  simp only [plaquetteTerm, plaquetteProduct, h]

omit [NeZero n] in
/-- Replacing a coordinate outside a face leaves that face unchanged. -/
theorem plaquetteTerm_update_of_not_mem (U : State n L) (a : Link n L) (q : Q)
    (p : Plaquette n L) (ha : a ∉ incidentLinks n L p) :
    plaquetteTerm n L (Function.update U a q) p = plaquetteTerm n L U p := by
  apply plaquetteTerm_congr
  intro e he
  rw [Function.update_of_ne (show e ≠ a from fun h => ha (h ▸ he))]

/-- Only the incident faces enter the normalized one-link law. -/
def localAction (β : ℝ) (U : State n L) (a : Link n L) : C(Q, ℝ) :=
  ⟨fun q => β * ∑ p ∈ incidentFaces (incidentLinks n L) a,
      plaquetteTerm n L (Function.update U a q) p,
    continuous_const.mul (continuous_finset_sum _ (fun p _ =>
      (plaquetteTerm_continuous n L p).comp (continuous_const.update a continuous_id)))⟩

def exteriorAction (β : ℝ) (U : State n L) (a : Link n L) : ℝ :=
  β * ∑ p ∈ Finset.univ \ incidentFaces (incidentLinks n L) a, plaquetteTerm n L U p

theorem conditionalAction_eq (β : ℝ) (U : State n L) (a : Link n L) (q : Q) :
    conditionalAction n L β U a q = exteriorAction n L β U a + localAction n L β U a q := by
  change β * ∑ p, plaquetteTerm n L (Function.update U a q) p = _
  have h : ∑ p ∈ Finset.univ \ incidentFaces (incidentLinks n L) a,
      plaquetteTerm n L (Function.update U a q) p =
      ∑ p ∈ Finset.univ \ incidentFaces (incidentLinks n L) a, plaquetteTerm n L U p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact plaquetteTerm_update_of_not_mem n L U a q p
      (by simpa only [mem_incidentFaces] using (Finset.mem_sdiff.mp hp).2)
  rw [← Finset.sum_sdiff (Finset.subset_univ (incidentFaces (incidentLinks n L) a)), h]
  simp only [exteriorAction, localAction, ContinuousMap.coe_mk]
  ring

theorem coordinateLaw_eq_local (β : ℝ) (U : State n L) (a : Link n L) :
    coordinateLaw n L β U a =
      CompactGibbsContinuity.law (compactHaar Q) (localAction n L β U a) := by
  unfold coordinateLaw
  have he : (conditionalAction n L β U a : Q → ℝ) =
      fun q => exteriorAction n L β U a + localAction n L β U a q :=
    funext (conditionalAction_eq n L β U a)
  rw [he]
  exact GibbsConstantShift.law_const_add _ _ (localAction n L β U a).continuous _


/-- The replacement erases every dependence on the old selected-link value. -/
theorem coordinateLaw_self (β : ℝ) (a : Link n L) (U V : State n L)
    (hUV : ∀ e, e ≠ a → U e = V e) :
    coordinateLaw n L β U a = coordinateLaw n L β V a := by
  have hu (q : Q) : Function.update U a q = Function.update V a q := by
    funext e
    by_cases h : e = a
    · subst e; simp
    · simp only [Function.update_of_ne h, hUV e h]
  unfold coordinateLaw
  congr 1
  ext q
  exact congrArg (stateAction n L β) (hu q)

/-- Faces not containing the changed exterior coordinate cancel exactly. -/
theorem localAction_difference (β : ℝ) (a b : Link n L) (hab : a ≠ b)
    (U V : State n L) (hUV : ∀ e, e ≠ b → U e = V e) (q : Q) :
    localAction n L β U a q - localAction n L β V a q =
      β * ∑ p ∈ sharedFaces (incidentLinks n L) a b,
        (plaquetteTerm n L (Function.update U a q) p -
          plaquetteTerm n L (Function.update V a q) p) := by
  simp only [localAction, ContinuousMap.coe_mk, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  symm
  unfold sharedFaces
  rw [if_neg hab]
  apply Finset.sum_subset Finset.inter_subset_left
  intro p hp hnot
  have hb : b ∉ incidentLinks n L p := by
    intro hb
    exact hnot (Finset.mem_inter.mpr ⟨hp, (mem_incidentFaces _ _ _).mpr hb⟩)
  apply sub_eq_zero.mpr
  apply plaquetteTerm_congr
  intro e he
  by_cases h : e = a
  · subst e; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]
    exact hUV e (fun hh => hb (hh ▸ he))

/-- The full, normalized conditional action perturbation has no cylinder-volume factor. -/
theorem localAction_difference_bound (β : ℝ) (hβ : 0 ≤ β)
    (a b : Link n L) (hab : a ≠ b) (U V : State n L)
    (hUV : ∀ e, e ≠ b → U e = V e) (q : Q) :
    |localAction n L β U a q - localAction n L β V a q| ≤
      4 * β * (multiplicity (incidentLinks n L) a b : ℝ) := by
  rw [localAction_difference n L β a b hab U V hUV q, abs_mul, abs_of_nonneg hβ]
  calc
    _ ≤ β * ∑ p ∈ sharedFaces (incidentLinks n L) a b,
        |plaquetteTerm n L (Function.update U a q) p -
          plaquetteTerm n L (Function.update V a q) p| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hβ
    _ ≤ β * ∑ _p ∈ sharedFaces (incidentLinks n L) a b, (4 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hβ
      apply Finset.sum_le_sum
      intro p _
      apply abs_le.mpr
      have hu := plaquetteTerm_bounds n L (Function.update U a q) p
      have hv := plaquetteTerm_bounds n L (Function.update V a q) p
      constructor <;> linarith
    _ = _ := by simp [FiniteIncidenceInfluence.multiplicity]; ring

/-- Actual bounded-test influence: each shared Wilson plaquette contributes at most 2 beta. -/
theorem coordinateLaw_influence (β : ℝ) (hβ : 0 ≤ β)
    (a b : Link n L) (U V : State n L) (hUV : ∀ e, e ≠ b → U e = V e)
    (G : Q → ℝ) (hG : Continuous G) (c d : ℝ) (hcd : c ≤ d)
    (hGb : ∀ q, G q ∈ Set.Icc c d) :
    |(∫ q, G q ∂coordinateLaw n L β U a) -
      (∫ q, G q ∂coordinateLaw n L β V a)| ≤
        coefficient (incidentLinks n L) β a b * (d - c) := by
  by_cases hab : a = b
  · subst b
    rw [coordinateLaw_self n L β a U V hUV]
    simp [coefficient]
  · rw [coordinateLaw_eq_local, coordinateLaw_eq_local]
    let m : ℝ := multiplicity (incidentLinks n L) a b
    have hm : 0 ≤ m := Nat.cast_nonneg _
    have hbound := CompactGibbsOscillation.action_expectation_difference
      (compactHaar Q) (localAction n L β V a) (localAction n L β U a) G
      (localAction n L β V a).continuous (localAction n L β U a).continuous hG
      (-(4 * β * m)) (4 * β * m) c d (by
        have hp : 0 ≤ 4 * β * m := by positivity
        linarith) hcd
      (fun q => by
        have h := localAction_difference_bound n L β hβ a b hab V U
          (fun e he => (hUV e he).symm) q
        exact abs_le.mp h) hGb
    calc
      _ ≤ (d - c) * (4 * β * m - -(4 * β * m)) / 4 := hbound
      _ = _ := by unfold coefficient; dsimp [m]; ring

/-- The abstract parallel-update influence hypothesis is discharged by actual cylinder laws. -/
theorem localInfluence (β : ℝ) (hβ : 0 ≤ β) :
    ParallelOscillation.LocalInfluence (fun a U => coordinateLaw n L β U a)
      (coefficient (incidentLinks n L) β) := by
  intro a b U V hUV G d hG
  obtain ⟨c, hcd, hb⟩ := ParallelOscillation.interval_of_oscillation G d hG
  have h := coordinateLaw_influence n L β hβ a b U V hUV G G.continuous
    c (c + d) hcd hb
  simpa only [add_sub_cancel_left] using h

/-- The resulting influence rows are uniformly bounded, including temporal endpoints. -/
theorem influence_row_bound (β : ℝ) (hβ : 0 ≤ β) (a : Link n L) :
    ∑ b, coefficient (incidentLinks n L) β a b ≤ 36 * β :=
  WilsonCylinderInfluenceGeometry.coefficient_row_le n L β hβ a

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderConditionalInfluence
