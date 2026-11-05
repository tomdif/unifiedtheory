/- A concrete physical large-plaquette bump rules out loss-only absorption
of the spatial-large-field complement of the axial small-curvature region. -/
import UnifiedTheory.Clay.YangMills.WilsonEndpointSupport
import UnifiedTheory.Clay.YangMills.WilsonAxialSource

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSpatialSourceObstruction
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonPhysicalVariance WilsonGroundHeatBath
open WilsonGroundVarianceBudget WilsonEndpointSupport WilsonAxialRegularity CompactDensityEntropy
open WilsonGaugeSourceTail (source source_continuous source_nonneg)
open scoped Quaternion

variable (n : ℕ) [NeZero n]

/-- Squared chord defect of a fixed actual spatial plaquette. -/
def defect : C(Slice n, ℝ) :=
  ⟨fun u => 2-WilsonPlaquetteTransport.plaquette n 0 0 1 u,
    continuous_const.sub (WilsonPlaquetteTransport.plaquette n 0 0 1).continuous⟩

omit [NeZero n] in
theorem defect_gauge (h : SliceGauge n Q) (u : Slice n) :
    defect n (gaugeSlice h u) = defect n u := by
  exact congrArg (fun x : ℝ => 2-x) (WilsonPlaquetteTransport.plaquette_gauge n 0 0 1 h u)

omit [NeZero n] in
theorem defect_chord (u : Slice n) :
    defect n u = ‖((spatialHolonomy u 0 0 1 : Q) : ℍ)-1‖^2 :=
  QuaternionDefectCurvature.character_chord _

def bad (t : ℝ) : Set (Slice n) := {u | t < defect n u}

theorem bad_measurable (t : ℝ) : MeasurableSet (bad n t) :=
  (isOpen_lt continuous_const (defect n).continuous).measurableSet

def bump (t : ℝ) : C(Slice n, ℝ) :=
  ⟨fun u => max 0 (defect n u-t), continuous_const.max ((defect n).continuous.sub continuous_const)⟩

omit [NeZero n] in
theorem bump_gauge (t : ℝ) (h : SliceGauge n Q) (u : Slice n) :
    bump n t (gaugeSlice h u) = bump n t u := by
  change max 0 (defect n (gaugeSlice h u)-t) = _
  rw [defect_gauge]
  rfl

omit [NeZero n] in
theorem bump_supported (t : ℝ) (u : Slice n) (hu : u ∉ bad n t) : bump n t u = 0 := by
  exact max_eq_left (sub_nonpos.mpr (not_lt.mp hu))

variable [Fact (1 < n)]

omit [NeZero n] in
theorem defect_single (q : Q) : defect n (singleLink n 0 0 q) =
    2-(WilsonSingleLinkStaples.character q).re := by
  change 2-(WilsonSingleLinkStaples.character
    (spatialHolonomy (singleLink n 0 0 q) 0 0 1)).re = _
  rw [singleLink_holonomy n 0 0 1 (by decide)]

omit [NeZero n] in
theorem bump_nonconstant (t : ℝ) (ht : 0 ≤ t) (h4 : t < 4) :
    bump n t (singleLink n 0 0 1) ≠ bump n t (singleLink n 0 0 (-1)) := by
  change max 0 (defect n (singleLink n 0 0 1)-t) ≠
    max 0 (defect n (singleLink n 0 0 (-1))-t)
  rw [defect_single, defect_single]
  norm_num [WilsonSingleLinkStaples.character_re, Unitary.coe_neg,
    max_eq_left (show -t ≤ 0 by linarith), max_eq_right (show 0 ≤ 4-t by linarith)]
  linarith

theorem bump_loss_positive (β : ℝ) (hβ : 0 ≤ β) (t : ℝ) (ht : 0 ≤ t) (h4 : t < 4) :
    0 < loss n β hβ (bump n t) :=
  loss_positive n β hβ (bump n t) _ _ (bump_nonconstant n t ht h4)

/-- Even an arbitrarily rare gauge-invariant plaquette event cannot have a
uniform exceptional-source coefficient below one half for all physical tests. -/
theorem no_uniform_endpoint_tail (β : ℝ) (hβ : 0 ≤ β) (t : ℝ) (ht : 0 ≤ t) (h4 : t < 4)
    (ε : ℝ) (hε : ε < 1 / 2) :
    ¬∀ f : C(Slice n, ℝ), (∀ h u, f (gaugeSlice h u) = f u) →
      meanMass n (bad n t) β hβ f ≤ ε*loss n β hβ f := by
  intro h
  exact no_small_bound n (bad n t) (bad_measurable n t) β hβ (bump n t)
    (bump_supported n t) _ _ (bump_nonconstant n t ht h4) ε hε
    (h (bump n t) (bump_gauge n t))

omit [NeZero n] [Fact (1 < n)] in
theorem bad_outside_flat (L : ℕ) (δ : ℝ) (_hδ : 0 ≤ δ) (u : Slice n)
    (hu : u ∈ bad n (δ ^ 2)) : ¬FlatBox n u (L + 1) δ := by
  intro hf
  have h := hf 0 0 0 (by omega) (by omega) (by omega) 0 1 (by decide)
  have hz : WilsonAxialGauge.vertex n 0 0 0 = 0 := by
    funext i
    fin_cases i <;> simp [WilsonAxialGauge.vertex]
  rw [hz] at h
  change δ ^ 2 < defect n u at hu
  rw [defect_chord] at hu
  have hs := pow_le_pow_left₀ (norm_nonneg (((spatialHolonomy u 0 0 1 : Q) : ℍ)-1)) h 2
  linarith

omit [Fact (1 < n)] in
def excluded (L : ℕ) (δ : ℝ) : Set (Slice n × Slice n) :=
  {z | ¬FlatBox n z.1 (L + 1) δ ∨ ¬FlatBox n z.2 (L + 1) δ}

omit [Fact (1 < n)] in
theorem excluded_measurable (L : ℕ) (δ : ℝ) : MeasurableSet (excluded n L δ) :=
  (((WilsonAxialSource.flat_closed n (L + 1) δ).preimage continuous_fst).measurableSet.compl).union
    (((WilsonAxialSource.flat_closed n (L + 1) δ).preimage continuous_snd).measurableSet.compl)

omit [Fact (1 < n)] in
def excludedRow (L : ℕ) (δ β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (u : Slice n) : ℝ :=
  (∫ v, (excluded n L δ).indicator (source n β hβ f) (u,v) ∂WilsonSlabOperator.measure n)/2

omit [Fact (1 < n)] in
theorem excludedRow_integrable (L : ℕ) (δ β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    Integrable (excludedRow n L δ β hβ f) (groundLaw n β hβ) := by
  letI := groundLaw_probability n β hβ
  exact (((continuous_integrable ((groundLaw n β hβ).prod (WilsonSlabOperator.measure n)) _
    (source_continuous n β hβ f)).indicator
      (excluded_measurable n L δ)).integral_prod_left).div_const 2

omit [Fact (1 < n)] in
theorem row_le_excluded (L : ℕ) (δ β : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (f : C(Slice n, ℝ)) (u : Slice n) :
    rowMass n (bad n (δ ^ 2)) β hβ f u ≤ excludedRow n L δ β hβ f u := by
  let E := {v : Slice n | (u,v) ∈ excluded n L δ}
  have hE : MeasurableSet E := (excluded_measurable n L δ).preimage
    (measurable_const.prodMk measurable_id)
  have hi := continuous_integrable (WilsonSlabOperator.measure n) _
    ((source_continuous n β hβ f).comp
      (f := fun v : Slice n => (u,v)) (continuous_const.prodMk continuous_id))
  have h := integral_mono (hi.indicator (bad_measurable n (δ ^ 2))) (hi.indicator hE) (fun v => by
    by_cases hv : v ∈ bad n (δ ^ 2)
    · have he : v ∈ E := Or.inr (bad_outside_flat n L δ hδ v hv)
      rw [Set.indicator_of_mem hv, Set.indicator_of_mem he]
    · rw [Set.indicator_of_notMem hv]
      exact Set.indicator_nonneg (fun _ _ => source_nonneg n β hβ f _) _)
  exact div_le_div_of_nonneg_right h (by norm_num)

omit [Fact (1 < n)] in
def excludedMass (L : ℕ) (δ β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : ℝ :=
  ∫ u, excludedRow n L δ β hβ f u ∂groundLaw n β hβ

omit [Fact (1 < n)] in
/-- The actual complement proposed after axial alignment retains at least
half the source for the explicit physical bump. -/
theorem excluded_lower (L : ℕ) (δ β : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) :
    loss n β hβ (bump n (δ ^ 2))/2 ≤ excludedMass n L δ β hβ (bump n (δ ^ 2)) := by
  exact (loss_half_le n (bad n (δ ^ 2)) (bad_measurable n (δ ^ 2)) β hβ (bump n (δ ^ 2))
    (bump_supported n (δ ^ 2))).trans
      (integral_mono (rowMass_integrable n (bad n (δ ^ 2)) (bad_measurable n (δ ^ 2)) β hβ _)
        (excludedRow_integrable n L δ β hβ _) (row_le_excluded n L δ β hβ hδ _))

theorem no_uniform_excluded_tail (L : ℕ) (δ β : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (h2 : δ < 2) (ε : ℝ) (hε : ε < 1 / 2) :
    ¬∀ f : C(Slice n, ℝ), (∀ h u, f (gaugeSlice h u) = f u) →
      excludedMass n L δ β hβ f ≤ ε*loss n β hβ f := by
  intro h
  have hl := excluded_lower n L δ β hβ hδ
  have hp := bump_loss_positive n β hβ (δ ^ 2) (sq_nonneg δ) (by nlinarith)
  have hu := h (bump n (δ ^ 2)) (bump_gauge n (δ ^ 2))
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonSpatialSourceObstruction
