/- Exact covariance of the actual floor-cell sampler under site reflection.
Spatial plaquettes require reflection about time a/2; temporal plaquettes
require reflection about zero. Grid-boundary exceptions have zero volume.
The spatial offset tends to zero with the lattice spacing. -/
import UnifiedTheory.Clay.YangMills.WilsonSmearedObservable
import UnifiedTheory.Clay.YangMills.PeriodicPlaquetteReflection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CellReflectionCovariance
noncomputable section
open MeasureTheory Filter LocalFields PeriodicLattice4 PeriodicCellSampling
open PeriodicTimeReflection PeriodicPlaquetteReflection RegulatedGauge WilsonMomentBounds
open scoped Topology

def OffGrid (a : ℝ) (x : Spacetime) : Prop := x 0 / a ≠ (⌊x 0 / a⌋ : ℤ)

theorem floor_neg_offGrid (r : ℝ) (hr : r ≠ (⌊r⌋ : ℤ)) :
    ⌊-r⌋ = -⌊r⌋ - 1 := by
  have hlo := Int.floor_le r
  have hhi := Int.lt_floor_add_one r
  have hstrict : (⌊r⌋ : ℤ) < r := lt_of_le_of_ne hlo (Ne.symm hr)
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor <;> linarith

theorem floor_one_sub_offGrid (r : ℝ) (hr : r ≠ (⌊r⌋ : ℤ)) :
    ⌊1 - r⌋ = -⌊r⌋ := by
  have hlo := Int.floor_le r
  have hhi := Int.lt_floor_add_one r
  have hstrict : (⌊r⌋ : ℤ) < r := lt_of_le_of_ne hlo (Ne.symm hr)
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor <;> linarith

def pointReflection (s : ℝ) (x : Spacetime) : Spacetime :=
  WithLp.toLp 2 (fun μ => if μ = 0 then s - x 0 else x μ)

def cellOffset (a : ℝ) (plane : Plane) : ℝ := if plane.1.1 = 0 then 0 else a

def cellReflection (a : ℝ) (plane : Plane) : Spacetime → Spacetime :=
  pointReflection (cellOffset a plane)

theorem pointReflection_involutive (s : ℝ) : Function.Involutive (pointReflection s) := by
  intro x
  ext μ
  by_cases hμ : μ = 0
  · subst μ
    simp [pointReflection]
  · simp [pointReflection, hμ]

theorem pointReflection_offset_continuous (x : Spacetime) :
    Continuous (fun s => pointReflection s x) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro μ
  by_cases hμ : μ = 0
  · simpa only [hμ, if_true] using (continuous_id.sub continuous_const :
      Continuous (fun s : ℝ => s - x 0))
  · simpa only [hμ, if_false] using (continuous_const : Continuous (fun _ : ℝ => x μ))

theorem cellReflection_tendsto (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (plane : Plane) (x : Spacetime) :
    Tendsto (fun k => cellReflection (a k) plane x) atTop (𝓝 (pointReflection 0 x)) := by
  apply (pointReflection_offset_continuous x).continuousAt.tendsto.comp
  by_cases hp : plane.1.1 = 0
  · simpa only [cellOffset, hp, if_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · simpa only [cellOffset, hp, if_false] using ha

theorem vertexSample_temporal_reflection (N : ℕ) (a : ℝ) (x : Spacetime)
    (hx : OffGrid a x) :
    vertexSample N a (pointReflection 0 x) = reflectVertex N (step N (vertexSample N a x) 0) := by
  funext μ
  by_cases hμ : μ = 0
  · subst μ
    change (⌊(0 - x 0) / a⌋ : ZMod N) = -((⌊x 0 / a⌋ : ZMod N) + 1)
    rw [zero_sub, neg_div, floor_neg_offGrid _ hx]
    push_cast
    ring
  · simp [vertexSample, pointReflection, reflectVertex, step, hμ]

theorem vertexSample_spatial_reflection (N : ℕ) (a : ℝ) (ha : a ≠ 0) (x : Spacetime)
    (hx : OffGrid a x) :
    vertexSample N a (pointReflection a x) = reflectVertex N (vertexSample N a x) := by
  funext μ
  by_cases hμ : μ = 0
  · subst μ
    change (⌊(a - x 0) / a⌋ : ZMod N) = -(⌊x 0 / a⌋ : ZMod N)
    rw [sub_div, div_self ha, floor_one_sub_offGrid _ hx, Int.cast_neg]
  · simp [vertexSample, pointReflection, reflectVertex, hμ]

theorem sample_reflection (N : ℕ) (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (x : Spacetime) (hx : OffGrid a x) :
    sample N a plane (cellReflection a plane x) = reflectPlaquette N (sample N a plane x) := by
  apply Prod.ext
  · by_cases hp : plane.1.1 = 0
    · simpa only [sample, cellReflection, cellOffset, reflectPlaquette, reflectIndex,
        hp, if_true] using vertexSample_temporal_reflection N a x hx
    · simpa only [sample, cellReflection, cellOffset, reflectPlaquette, reflectIndex,
        hp, if_false] using vertexSample_spatial_reflection N a ha x hx
  · rfl

def reflectPoints (m : ℕ) (a : ℝ) (plane : Plane)
    (x : ContinuumControl.Configuration m) : ContinuumControl.Configuration m :=
  WithLp.toLp 2 (fun jμ => if jμ.2 = 0 then cellOffset a plane - x (jμ.1, 0) else x jμ)

theorem point_reflectPoints (m : ℕ) (a : ℝ) (plane : Plane)
    (x : ContinuumControl.Configuration m) (j : Fin m) :
    point m j (reflectPoints m a plane x) = cellReflection a plane (point m j x) := by
  ext μ
  rfl

theorem sampleConfiguration_reflection (m N : ℕ) (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (x : ContinuumControl.Configuration m) (hx : ∀ j, OffGrid a (point m j x)) :
    sampleConfiguration m N a plane (reflectPoints m a plane x) =
      fun j => reflectPlaquette N (sampleConfiguration m N a plane x j) := by
  funext j
  exact (congrArg (sample N a plane) (point_reflectPoints m a plane x j)).trans
    (sample_reflection N a ha plane (point m j x) (hx j))

theorem coordinate_ae_ne {ι : Type*} [Fintype ι] (i : ι) (r : ℝ) :
    ∀ᵐ x : EuclideanSpace ℝ ι, x i ≠ r := by
  have h : ∀ᵐ x : ι → ℝ, x i ≠ r :=
    Measure.ae_eval_ne (fun _ : ι => (volume : Measure ℝ)) i r
  exact (PiLp.volume_preserving_ofLp ι).quasiMeasurePreserving.ae h

theorem offGrid_ae (a : ℝ) (ha : a ≠ 0) : ∀ᵐ x : Spacetime, OffGrid a x := by
  have h : ∀ᵐ x : Spacetime, ∀ k : ℤ, x 0 ≠ a * k :=
    ae_all_iff.mpr (fun k => coordinate_ae_ne 0 (a * k))
  filter_upwards [h] with x hx
  intro he
  apply hx ⌊x 0 / a⌋
  exact (div_eq_iff ha).mp he |>.trans (mul_comm _ _)

theorem offGrid_points_ae (m : ℕ) (a : ℝ) (ha : a ≠ 0) :
    ∀ᵐ x : ContinuumControl.Configuration m, ∀ j, OffGrid a (point m j x) := by
  apply ae_all_iff.mpr
  intro j
  have h : ∀ᵐ x : ContinuumControl.Configuration m, ∀ k : ℤ, x (j, 0) ≠ a * k :=
    ae_all_iff.mpr (fun k => coordinate_ae_ne (j, 0) (a * k))
  filter_upwards [h] with x hx
  intro he
  apply hx ⌊x (j, 0) / a⌋
  exact (div_eq_iff ha).mp he |>.trans (mul_comm _ _)

theorem sampleConfiguration_reflection_ae (m N : ℕ) (a : ℝ) (ha : a ≠ 0) (plane : Plane) :
    (fun x => sampleConfiguration m N a plane (reflectPoints m a plane x)) =ᵐ[volume]
      (fun x j => reflectPlaquette N (sampleConfiguration m N a plane x j)) := by
  filter_upwards [offGrid_points_ae m a ha] with x hx
  exact sampleConfiguration_reflection m N a ha plane x hx

variable (G : Type*) [Group G] (N : ℕ) [NeZero N]

def realPartCharacter (χ : G → ℂ) (g : G) : ℂ := (χ g).re

theorem real_word_reflection (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (m : ℕ) (q : Fin m → PlaquetteIndex N)
    (U : Configuration (Vertex N) G) :
    WilsonSmearedObservable.word G N (realPartCharacter G χ) m q (reflectConfiguration N G U) =
      WilsonSmearedObservable.word G N (realPartCharacter G χ) m
        (fun j => reflectPlaquette N (q j)) U := by
  apply Finset.prod_congr rfl
  intro j _
  change ((χ (holonomy (Quiver.Symmetrify (Vertex N)) G
    (orientedExtension (Vertex N) G (reflectConfiguration N G U))
    (plaquette N (q j).1 (q j).2.1.1 (q j).2.1.2))).re : ℂ) =
    ((χ (holonomy (Quiver.Symmetrify (Vertex N)) G
    (orientedExtension (Vertex N) G U)
    (plaquette N (reflectPlaquette N (q j)).1
      (reflectPlaquette N (q j)).2.1.1 (reflectPlaquette N (q j)).2.1.2))).re : ℂ)
  simp only [plaquette_holonomy_eq_product]
  exact congrArg Complex.ofReal (reflected_plaquette_character N G χ hχ hinv U (q j))

theorem sampled_real_word_reflection (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (χ : G → ℂ) (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (m : ℕ) (x : ContinuumControl.Configuration m) (hx : ∀ j, OffGrid a (point m j x))
    (U : Configuration (Vertex N) G) :
    WilsonSmearedObservable.word G N (realPartCharacter G χ) m
      (sampleConfiguration m N a plane x) (reflectConfiguration N G U) =
    WilsonSmearedObservable.word G N (realPartCharacter G χ) m
      (sampleConfiguration m N a plane (reflectPoints m a plane x)) U := by
  rw [real_word_reflection G N χ hχ hinv,
    sampleConfiguration_reflection m N a ha plane x hx]

theorem sampled_real_word_reflection_ae (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (χ : G → ℂ) (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (m : ℕ) (U : Configuration (Vertex N) G) :
    (fun x => WilsonSmearedObservable.word G N (realPartCharacter G χ) m
      (sampleConfiguration m N a plane x) (reflectConfiguration N G U)) =ᵐ[volume]
    (fun x => WilsonSmearedObservable.word G N (realPartCharacter G χ) m
      (sampleConfiguration m N a plane (reflectPoints m a plane x)) U) := by
  filter_upwards [offGrid_points_ae m a ha] with x hx
  exact sampled_real_word_reflection G N a ha plane χ hχ hinv m x hx U

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Actual reflected smearing, expressed by the reflected cell samples. Turning
this into a test-function pullback requires the affine change-of-variable step. -/
theorem reflected_observable_integral (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (χ : G → ℂ) (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (m : ℕ) (f : ContinuumControl.CorrelationTest m) (U : Configuration (Vertex N) G) :
    WilsonSmearedObservable.observable G N a plane (realPartCharacter G χ) m f
      (reflectConfiguration N G U) =
      ∫ x, WilsonSmearedObservable.word G N (realPartCharacter G χ) m
        (sampleConfiguration m N a plane (reflectPoints m a plane x)) U * f x := by
  rw [WilsonSmearedObservable.observable_integral]
  apply integral_congr_ae
  filter_upwards [sampled_real_word_reflection_ae G N a ha plane χ hχ hinv m U] with x hx
  rw [hx]

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem unitary_reflected_observable_integral (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (m : ℕ) (f : ContinuumControl.CorrelationTest m)
    (U : Configuration (Vertex N) G) :
    WilsonSmearedObservable.observable G N a plane
      (realPartCharacter G (WilsonCrossingKernel.unitaryCharacter ρ)) m f
      (reflectConfiguration N G U) =
      ∫ x, WilsonSmearedObservable.word G N
        (realPartCharacter G (WilsonCrossingKernel.unitaryCharacter ρ)) m
        (sampleConfiguration m N a plane (reflectPoints m a plane x)) U * f x :=
  reflected_observable_integral G N a ha plane _
    (UnitaryCharacterObservables.unitaryCharacter_class ρ)
    (unitaryCharacter_inverse_re G ρ) m f U

end
end UnifiedTheory.Clay.YangMills.CellReflectionCovariance
