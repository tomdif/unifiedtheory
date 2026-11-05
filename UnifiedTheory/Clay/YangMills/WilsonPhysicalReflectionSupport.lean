/- A physical time slab supplies actual reflection-separated Wilson cell weights.
For period 2n, spacing a>0, and circumference L=2na, a test supported between
delta and L/2-delta samples only the lower time half, with no temporal wrapping.
The temporal plaquette reflection is t -> -t-1. The resulting independent
time-line elimination preserves the reflected product exactly and gives zero
removed reflected pairing. No positive norm or continuum lower bound is claimed. -/
import UnifiedTheory.Clay.YangMills.WilsonPhysicalCellWeights
import UnifiedTheory.Clay.YangMills.WilsonBlockReflection
import UnifiedTheory.Clay.YangMills.ClosedHalfSmearing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonPhysicalReflectionSupport
noncomputable section
open MeasureTheory LocalFields RegulatedGauge PeriodicLattice4
open PeriodicHalfGeometry PeriodicHalfAction PeriodicTimeReflection
open PeriodicHalfSplit PeriodicPlaquetteReflection

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex (2 * n))) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (WilsonIndependentBlocks.Link (2 * n)) :=
  Classical.decEq _

def lowerTime : Set (ZMod (2 * n)) := {t | t.val < n}

/-- The actual shifted temporal reflection exchanges the two discrete halves. -/
theorem lowerTime_shift_separated (t : ZMod (2 * n)) (ht : t ∈ lowerTime n) :
    -t - 1 ∉ lowerTime n := by
  have hval := val_neg_add_one (2 * n) t
  have he : -t - 1 = -(t + 1) := by ring
  change ¬ (-t - 1).val < n
  rw [he, hval]
  change t.val < n at ht
  omega

/-- There is no modular wrap for any sampled time strictly in the physical half. -/
theorem sample_time_no_wrap (a : ℝ) (ha : 0 < a) (x : Spacetime)
    (hx0 : 0 ≤ x 0) (hxn : x 0 < (n : ℝ) * a) :
    (((PeriodicCellSampling.vertexSample (2 * n) a x) 0).val : ℤ) =
      Int.floor (x 0 / a) ∧
        ((PeriodicCellSampling.vertexSample (2 * n) a x) 0).val < n := by
  have hk0 : 0 ≤ Int.floor (x 0 / a) := Int.floor_nonneg.mpr (div_nonneg hx0 ha.le)
  have hkn : Int.floor (x 0 / a) < (n : ℤ) := by
    apply Int.floor_lt.mpr
    push_cast
    exact (div_lt_iff₀ ha).mpr hxn
  have hkN : Int.floor (x 0 / a) < ((2 * n : ℕ) : ℤ) := by omega
  have hv := ZMod.val_intCast (n := 2 * n) (Int.floor (x 0 / a))
  rw [Int.emod_eq_of_lt hk0 hkN] at hv
  constructor
  · exact hv
  · change ((Int.floor (x 0 / a) : ZMod (2 * n))).val < n
    have h : (((Int.floor (x 0 / a) : ZMod (2 * n))).val : ℤ) < (n : ℤ) := by
      rw [hv]
      exact hkn
    exact_mod_cast h

omit n [NeZero n] in
/-- A support statement about the actual spacetime test, not its cell coefficients. -/
def SlabSupported (δ L : ℝ) (f : TestFunction) : Prop :=
  ∀ x : Spacetime, f x ≠ 0 → δ ≤ x 0 ∧ x 0 ≤ L / 2 - δ

theorem slab_sample_time (a δ L : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hL : L = (2 * n : ℕ) * a) (f : TestFunction) (hf : SlabSupported δ L f)
    (x : Spacetime) (hx : f x ≠ 0) :
    (PeriodicCellSampling.vertexSample (2 * n) a x) 0 ∈ lowerTime n := by
  obtain ⟨hlo, hhi⟩ := hf x hx
  apply (sample_time_no_wrap n a ha x (hδ.le.trans hlo) _).2
  rw [hL] at hhi
  push_cast at hhi
  nlinarith

/-- The coefficient outside the discrete half vanishes by its actual defining integral. -/
theorem weight_zero_outside (a δ L : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hL : L = (2 * n : ℕ) * a) (plane : Plane) (f : TestFunction)
    (hf : SlabSupported δ L f) (p : PlaquetteIndex (2 * n))
    (hp : p.1 0 ∉ lowerTime n) : WilsonPhysicalCellWeights.weight (2 * n) a plane f p = 0 := by
  have he (x : Spacetime) :
      FiniteCellSmearing.cellFunction (PeriodicCellSampling.sample (2 * n) a plane) p f x = 0 := by
    unfold FiniteCellSmearing.cellFunction
    split_ifs with hs
    · by_contra hx
      have ht := slab_sample_time n a δ L ha hδ hL f hf x hx
      have hs' := congrArg (fun q : PlaquetteIndex (2 * n) => q.1 0) hs
      change (PeriodicCellSampling.vertexSample (2 * n) a x) 0 = p.1 0 at hs'
      rw [hs'] at ht
      exact hp ht
    · rfl
  simp only [WilsonPhysicalCellWeights.weight, FiniteCellSmearing.coefficient, he, integral_zero]
  rfl

theorem weights_separated (a δ L : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hL : L = (2 * n : ℕ) * a) (plane : Plane) (f : TestFunction)
    (hf : SlabSupported δ L f) :
    WilsonSeparatedSources.SeparatedOnBlock (2 * n) (WilsonBlockReflection.timeLine (2 * n))
      (WilsonBlockReflection.reflectedWeights (2 * n)
        (WilsonPhysicalCellWeights.weight (2 * n) a plane f))
      (WilsonPhysicalCellWeights.weight (2 * n) a plane f) :=
  WilsonBlockReflection.timeLine_separated (2 * n) (lowerTime n) _
    (weight_zero_outside n a δ L ha hδ hL plane f hf) (lowerTime_shift_separated n)

/-- A sampled plaquette lies in the closed positive half, including its boundary links. -/
theorem closed_plaquette_of_lower_time (p : PlaquetteIndex (2 * n))
    (hp : p.1 0 ∈ lowerTime n) : BoundaryP n p ∨ PositiveP n p := by
  by_cases ht : p.2.1.1 = 0
  · right
    simpa only [PositiveP, Positive, ht, if_true] using hp
  · exact closed_spatial n p.1 p.2.1.1 ht hp.le

theorem slab_sample_closed (a δ L : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hL : L = (2 * n : ℕ) * a) (plane : Plane) (f : TestFunction)
    (hf : SlabSupported δ L f) (x : Spacetime) (hx : f x ≠ 0) :
    BoundaryP n (PeriodicCellSampling.sample (2 * n) a plane x) ∨
      PositiveP n (PeriodicCellSampling.sample (2 * n) a plane x) :=
  closed_plaquette_of_lower_time n _ (slab_sample_time n a δ L ha hδ hL f hf x hx)

/-- Once the spacing fits inside the fixed margin, even the spatial plaquette
bases avoid the boundary time slice. -/
theorem slab_sample_positive (a δ L : ℝ) (ha : 0 < a) (haδ : a ≤ δ)
    (hL : L = (2 * n : ℕ) * a) (plane : Plane) (f : TestFunction)
    (hf : SlabSupported δ L f) (x : Spacetime) (hx : f x ≠ 0) :
    PositiveP n (PeriodicCellSampling.sample (2 * n) a plane x) := by
  obtain ⟨hlo, hhi⟩ := hf x hx
  have hδ : 0 < δ := ha.trans_le haδ
  have hxn : x 0 < (n : ℝ) * a := by
    rw [hL] at hhi
    push_cast at hhi
    nlinarith
  have hv := sample_time_no_wrap n a ha x (hδ.le.trans hlo) hxn
  have hxdiv : (1 : ℝ) ≤ x 0 / a := (le_div_iff₀ ha).mpr (by simpa using haδ.trans hlo)
  have hk : (1 : ℤ) ≤ Int.floor (x 0 / a) := Int.le_floor.mpr (by simpa using hxdiv)
  have ht : 0 < ((PeriodicCellSampling.vertexSample (2 * n) a x) 0).val := by
    have hi : (0 : ℤ) < (((PeriodicCellSampling.vertexSample (2 * n) a x) 0).val : ℤ) := by
      rw [hv.1]
      omega
    exact_mod_cast hi
  change (if plane.1.1 = 0 then
    ((PeriodicCellSampling.vertexSample (2 * n) a x) 0).val < n else
      0 < ((PeriodicCellSampling.vertexSample (2 * n) a x) 0).val ∧
        ((PeriodicCellSampling.vertexSample (2 * n) a x) 0).val < n)
  split_ifs
  · exact hv.2
  · exact ⟨ht, hv.2⟩

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
/-- The actual cell-weighted source depends only on positive and boundary links. -/
theorem source_independent (a δ L : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hL : L = (2 * n : ℕ) * a) (plane : Plane) (f : TestFunction)
    (hf : SlabSupported δ L f) (χ : G → ℂ) (c : ℝ)
    (b : BoundaryConfiguration n G) (x y z : HalfConfiguration n G) :
    WilsonBlockIntegration.source (2 * n) G χ c (WilsonPhysicalCellWeights.weight (2 * n) a plane f)
      (assemble n G (b, (x, y))) =
    WilsonBlockIntegration.source (2 * n) G χ c (WilsonPhysicalCellWeights.weight (2 * n) a plane f)
      (assemble n G (b, (x, z))) := by
  have hlo (V : Configuration (Vertex (2 * n)) G) (p : PlaquetteIndex (2 * n)) :
      WilsonMomentBounds.loopObservable (Vertex (2 * n)) G χ (loops (2 * n) p) V =
        χ (plaquetteProduct (2 * n) G V p.1 p.2.1.1 p.2.1.2) :=
    congrArg χ (plaquette_holonomy_eq_product (2 * n) G V p.1 p.2.1.1 p.2.1.2)
  unfold WilsonBlockIntegration.source WilsonIndependentBlocks.plaquetteTerm
  simp only [hlo]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.1 0 ∈ lowerTime n
  · rcases closed_plaquette_of_lower_time n p hp with hb | hh
    · rw [boundary_plaquette_independent n G p hb b x y x z]
    · rw [positive_plaquette_independent n G p hh b x y z]
  · rw [weight_zero_outside n a δ L ha hδ hL plane f hf p hp]
    simp only [zero_mul]

def halfSource (a : ℝ) (plane : Plane) (f : TestFunction) (χ : G → ℂ) (c : ℝ)
    (z : BoundaryConfiguration n G × HalfConfiguration n G) : ℂ :=
  WilsonBlockIntegration.source (2 * n) G χ c (WilsonPhysicalCellWeights.weight (2 * n) a plane f)
    (assemble n G (z.1, (z.2, 1)))

omit [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem halfSource_continuous (a : ℝ) (plane : Plane) (f : TestFunction)
    (χ : G → ℂ) (hcχ : Continuous χ) (c : ℝ) :
    Continuous (halfSource n G a plane f χ c) :=
  Complex.continuous_ofReal.comp
    ((WilsonBlockIntegration.source_continuous (2 * n) G χ hcχ c _).comp
      ((continuous_assemble n G).comp
        (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))))

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
/-- Literal identification with the repository positive-half observable domain. -/
theorem source_half_identification (a δ L : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hL : L = (2 * n : ℕ) * a) (plane : Plane) (f : TestFunction)
    (hf : SlabSupported δ L f) (χ : G → ℂ) (c : ℝ)
    (U : Configuration (Vertex (2 * n)) G) :
    (WilsonBlockIntegration.source (2 * n) G χ c
      (WilsonPhysicalCellWeights.weight (2 * n) a plane f) U : ℂ) =
      ReflectedWilsonKernel.positiveObservable n G (halfSource n G a plane f χ c) U := by
  have h := source_independent n G a δ L ha hδ hL plane f hf χ c
    (splitConfiguration n G U).1 (splitConfiguration n G U).2.1
    (splitConfiguration n G U).2.2 1
  rw [show ((splitConfiguration n G U).1,
    ((splitConfiguration n G U).2.1, (splitConfiguration n G U).2.2)) =
      splitConfiguration n G U from rfl, assemble_split] at h
  exact congrArg Complex.ofReal h

/-- Nonnegativity is now instantiated on the physically supported source.
It is not strict positivity or a uniform positive lower bound. -/
theorem reflection_positive (a δ L : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hL : L = (2 * n : ℕ) * a) (plane : Plane) (f : TestFunction)
    (hf : SlabSupported δ L f) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ) :
    0 ≤ (∫ U, star (WilsonBlockIntegration.source (2 * n) G χ c
      (WilsonPhysicalCellWeights.weight (2 * n) a plane f)
        (reflectConfiguration (2 * n) G U) : ℂ) *
      (WilsonBlockIntegration.source (2 * n) G χ c
        (WilsonPhysicalCellWeights.weight (2 * n) a plane f) U : ℂ)
      ∂wilsonLaw (2 * n) G χ β c).re := by
  simp_rw [source_half_identification n G a δ L ha hδ hL plane f hf χ c]
  exact (ReflectedWilsonKernel.positive_reflection_positive n G χ hcχ hχ hinv β c
    (halfSource n G a plane f χ c) (halfSource_continuous n G a plane f χ hcχ c)).1

/-- The actual removed fluctuation has zero reflected pairing for a physical slab test. -/
theorem removed_reflected_zero (a δ L : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hL : L = (2 * n : ℕ) * a) (plane : Plane) (f : TestFunction)
    (hf : SlabSupported δ L f) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ) :
    (∫ U, WilsonCrossCovariance.removedSource (2 * n) G χ β c
      (WilsonBlockReflection.timeLine (2 * n)) (WilsonPhysicalCellWeights.weight (2 * n) a plane f)
      (reflectConfiguration (2 * n) G U) *
      WilsonCrossCovariance.removedSource (2 * n) G χ β c
        (WilsonBlockReflection.timeLine (2 * n))
        (WilsonPhysicalCellWeights.weight (2 * n) a plane f) U
      ∂wilsonLaw (2 * n) G χ β c) = 0 :=
  WilsonBlockReflection.timeLine_removed_reflected_zero (2 * n) G χ hcχ hχ hinv β c
    (lowerTime n) _ (weight_zero_outside n a δ L ha hδ hL plane f hf)
    (lowerTime_shift_separated n)

/-- Exact reflected-product preservation under the original interacting law. -/
theorem reflected_product_preserved (a δ L : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hL : L = (2 * n : ℕ) * a) (plane : Plane) (f : TestFunction)
    (hf : SlabSupported δ L f) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ) :
    (∫ U, WilsonBlockIntegration.source (2 * n) G χ c
      (WilsonPhysicalCellWeights.weight (2 * n) a plane f) (reflectConfiguration (2 * n) G U) *
      WilsonBlockIntegration.source (2 * n) G χ c
        (WilsonPhysicalCellWeights.weight (2 * n) a plane f) U ∂wilsonLaw (2 * n) G χ β c) =
      ∫ b, WilsonCrossCovariance.retainedSource (2 * n) G χ β c
        (WilsonBlockReflection.timeLine (2 * n))
        (WilsonPhysicalCellWeights.weight (2 * n) a plane f)
        (WilsonBlockReflection.outsideReflection (2 * n) G
          (WilsonBlockReflection.timeLine (2 * n))
          (WilsonBlockReflection.timeLine_stable (2 * n)) b) *
        WilsonCrossCovariance.retainedSource (2 * n) G χ β c
          (WilsonBlockReflection.timeLine (2 * n))
          (WilsonPhysicalCellWeights.weight (2 * n) a plane f) b
        ∂WilsonCrossCovariance.retainedLaw (2 * n) G χ β c
          (WilsonBlockReflection.timeLine (2 * n)) :=
  WilsonBlockReflection.reflected_product_preserved (2 * n) G
    (WilsonBlockReflection.timeLine (2 * n)) (WilsonBlockReflection.timeLine_stable (2 * n))
    χ hcχ hχ hinv β c (WilsonBlockReflection.timeLine_independent (2 * n)) _ _
    (weights_separated n a δ L ha hδ hL plane f hf)

end
end UnifiedTheory.Clay.YangMills.WilsonPhysicalReflectionSupport
