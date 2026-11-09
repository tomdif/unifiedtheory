/- Strict positive-time slab tests eventually use only interior positive-half
links. Their actual smeared Wilson observables are independent of all fixed
boundary links and negative-half links. All plaquette planes are included. -/
import UnifiedTheory.Clay.YangMills.PositiveCellSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.InteriorCellSupport
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 PeriodicCellSampling
open PeriodicHalfSplit PeriodicHalfGeometry PeriodicHalfAction PeriodicPlaquetteReflection
open PeriodicTimeReflection LocalFields
open scoped Topology

variable (n : ℕ) [NeZero n]

def InteriorP (p : PlaquetteIndex (2 * n)) : Prop :=
  0 < (p.1 0).val ∧ (p.1 0).val + 1 < n

theorem positive_of_time (x : Vertex (2 * n)) (μ : Fin 4)
    (hzero : 0 < (x 0).val) (hupper : (x 0).val < n) : Positive n (x, μ) := by
  by_cases hμ : μ = 0
  · simpa only [Positive, hμ, if_true] using hupper
  · simpa only [Positive, hμ, if_false] using And.intro hzero hupper

theorem interior_plaquette_support (p : PlaquetteIndex (2 * n)) (hp : InteriorP n p) :
    Positive n (p.1, p.2.1.1) ∧
    Positive n (step (2 * n) p.1 p.2.1.1, p.2.1.2) ∧
    Positive n (step (2 * n) p.1 p.2.1.2, p.2.1.1) ∧
    Positive n (p.1, p.2.1.2) := by
  rcases p with ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩
  have hν : ν ≠ 0 := by intro h; subst ν; exact (not_lt_of_ge (Fin.zero_le μ)) hμν
  change 0 < (x 0).val ∧ (x 0).val + 1 < n at hp
  obtain ⟨hzero, hupper⟩ := hp
  have ht : (x 0).val < n := by omega
  refine ⟨positive_of_time n x μ hzero ht, ?_, ?_, positive_of_time n x ν hzero ht⟩
  · by_cases hμ : μ = 0
    · subst μ
      apply positive_of_time n _ ν
      · rw [next_time_val n x ht]
        omega
      · rwa [next_time_val n x ht]
    · apply positive_of_time n _ ν
      · simpa only [spatial_time n x μ hμ] using hzero
      · simpa only [spatial_time n x μ hμ] using ht
  · apply positive_of_time n _ μ
    · simpa only [spatial_time n x ν hν] using hzero
    · simpa only [spatial_time n x ν hν] using ht

theorem sample_interior (a : ℝ) (ha : 0 < a) (plane : Plane) (x : Spacetime)
    (hlower : a ≤ x 0) (hupper : x 0 + a < (n : ℝ) * a) :
    InteriorP n (sample (2 * n) a plane x) := by
  have hlo : 1 ≤ ⌊x 0 / a⌋ := by
    apply Int.le_floor.mpr
    simp only [Int.cast_one]
    rw [le_div_iff₀ ha, one_mul]
    exact hlower
  have hdiv : x 0 / a + 1 < (n : ℝ) := by
    have h := (div_lt_iff₀ ha).mpr hupper
    simpa only [add_div, div_self (ne_of_gt ha)] using h
  have hhi : ⌊x 0 / a⌋ + 1 < (n : ℤ) := by
    have hfloor : (⌊x 0 / a⌋ : ℤ) ≤ x 0 / a := Int.floor_le (x 0 / a)
    have h : (⌊x 0 / a⌋ : ℝ) + 1 < (n : ℝ) := by linarith
    exact_mod_cast h
  have hnonneg : 0 ≤ ⌊x 0 / a⌋ := by omega
  have hnat : (⌊x 0 / a⌋).toNat + 1 < n := by omega
  change 0 < ((⌊x 0 / a⌋ : ZMod (2 * n))).val ∧
    ((⌊x 0 / a⌋ : ZMod (2 * n))).val + 1 < n
  rw [← ZMod.natCast_toNat (2 * n) hnonneg,
    ZMod.val_natCast_of_lt (by omega : (⌊x 0 / a⌋).toNat < 2*n)]
  constructor <;> omega

def InteriorWord (m : ℕ) (q : Fin m → PlaquetteIndex (2 * n)) : Prop := ∀ j, InteriorP n (q j)

def Supported (a : ℝ) (plane : Plane) (m : ℕ) (f : CorrelationTest m) : Prop :=
  ∀ x, f x ≠ 0 → InteriorWord n m (sampleConfiguration m (2 * n) a plane x)

theorem eventually_supported (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hlarge : Tendsto (fun k => (period k : ℝ) * a k) atTop atTop)
    (plane : Plane) (m : ℕ) (f : CorrelationTest m) (δ R : ℝ) (hδ : 0 < δ)
    (hf : ∀ x, f x ≠ 0 → ∀ j, δ ≤ point m j x 0 ∧ point m j x 0 ≤ R) :
    ∀ᶠ k in atTop, Supported (period k) (a k) plane m f := by
  filter_upwards [ha0.eventually (gt_mem_nhds hδ),
    ha0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hlarge.eventually (eventually_gt_atTop (R+1))] with k hkδ hk1 hkR
  intro x hx j
  apply sample_interior (period k) (a k) (ha k) plane (point m j x)
  · exact hkδ.le.trans (hf x hx j).1
  · exact (add_le_add (hf x hx j).2 hk1.le).trans_lt hkR

theorem coefficient_zero_outside (a : ℝ) (plane : Plane) (m : ℕ) (f : CorrelationTest m)
    (hf : Supported n a plane m f) (q : Fin m → PlaquetteIndex (2 * n))
    (hq : ¬ InteriorWord n m q) :
    WilsonSmearedObservable.cellCoefficient (2 * n) a plane m q f = 0 := by
  unfold WilsonSmearedObservable.cellCoefficient FiniteCellSmearing.coefficient
  have he (x : Configuration m) :
      FiniteCellSmearing.cellFunction (sampleConfiguration m (2 * n) a plane) q f x = 0 := by
    unfold FiniteCellSmearing.cellFunction
    split_ifs with hx
    · by_contra hnonzero
      exact hq (hx ▸ hf x hnonzero)
    · rfl
  simp_rw [he]
  exact integral_zero _ _

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem positive_link_independent (p : Index n) (hp : Positive n p)
    (b c : BoundaryConfiguration n G) (x y z : HalfConfiguration n G) :
    linkAt n G (assemble n G (b,(x,y))) p = linkAt n G (assemble n G (c,(x,z))) p :=
  (assemble_positive n G (b,(x,y)) ⟨p,hp⟩).trans
    (assemble_positive n G (c,(x,z)) ⟨p,hp⟩).symm

theorem plaquette_independent (p : PlaquetteIndex (2 * n)) (hp : InteriorP n p)
    (b c : BoundaryConfiguration n G) (x y z : HalfConfiguration n G) :
    plaquetteProduct (2 * n) G (assemble n G (b,(x,y))) p.1 p.2.1.1 p.2.1.2 =
      plaquetteProduct (2 * n) G (assemble n G (c,(x,z))) p.1 p.2.1.1 p.2.1.2 := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := interior_plaquette_support n p hp
  unfold plaquetteProduct
  change linkAt n G _ (p.1,p.2.1.1) * linkAt n G _ (step (2 * n) p.1 p.2.1.1,p.2.1.2) *
    (linkAt n G _ (step (2 * n) p.1 p.2.1.2,p.2.1.1))⁻¹ * (linkAt n G _ (p.1,p.2.1.2))⁻¹ = _
  rw [positive_link_independent n G _ h₁ b c x y z,
    positive_link_independent n G _ h₂ b c x y z,
    positive_link_independent n G _ h₃ b c x y z,
    positive_link_independent n G _ h₄ b c x y z]
  rfl

theorem word_independent (χ : G → ℂ) (m : ℕ) (q : Fin m → PlaquetteIndex (2 * n))
    (hq : InteriorWord n m q) (b c : BoundaryConfiguration n G) (x y z : HalfConfiguration n G) :
    WilsonSmearedObservable.word G (2 * n) χ m q (assemble n G (b,(x,y))) =
      WilsonSmearedObservable.word G (2 * n) χ m q (assemble n G (c,(x,z))) := by
  apply Finset.prod_congr rfl
  intro j _
  change χ (RegulatedGauge.holonomy _ G _ (plaquette (2 * n) (q j).1 (q j).2.1.1 (q j).2.1.2)) =
    χ (RegulatedGauge.holonomy _ G _ (plaquette (2 * n) (q j).1 (q j).2.1.1 (q j).2.1.2))
  simp only [plaquette_holonomy_eq_product]
  exact congrArg χ (plaquette_independent n G (q j) (hq j) b c x y z)

theorem observable_independent (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (m : ℕ) (f : CorrelationTest m) (hf : Supported n a plane m f)
    (b c : BoundaryConfiguration n G) (x y z : HalfConfiguration n G) :
    WilsonSmearedObservable.observable G (2 * n) a plane χ m f (assemble n G (b,(x,y))) =
      WilsonSmearedObservable.observable G (2 * n) a plane χ m f (assemble n G (c,(x,z))) := by
  classical
  unfold WilsonSmearedObservable.observable FiniteCellSmearing.observable
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : InteriorWord n m q
  · rw [word_independent n G χ m q hq b c x y z]
  · change WilsonSmearedObservable.cellCoefficient (2 * n) a plane m q f * _ =
      WilsonSmearedObservable.cellCoefficient (2 * n) a plane m q f * _
    rw [coefficient_zero_outside n a plane m f hf q hq, zero_mul, zero_mul]

def interiorObservable (a : ℝ) (plane : Plane) (χ : G → ℂ) (m : ℕ) (f : CorrelationTest m)
    (x : HalfConfiguration n G) : ℂ :=
  WilsonSmearedObservable.observable G (2 * n) a plane χ m f (assemble n G (1,(x,1)))

theorem interiorObservable_continuous (a : ℝ) (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (m : ℕ) (f : CorrelationTest m) : Continuous (interiorObservable n G a plane χ m f) :=
  (WilsonSmearedObservable.observable_continuous G (2 * n) a plane χ hcχ m f).comp
    ((continuous_assemble n G).comp (continuous_const.prodMk
      (continuous_id.prodMk continuous_const)))

theorem interior_identification (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (m : ℕ) (f : CorrelationTest m) (hf : Supported n a plane m f)
    (U : RegulatedGauge.Configuration (Vertex (2 * n)) G) :
    WilsonSmearedObservable.observable G (2 * n) a plane χ m f U =
      interiorObservable n G a plane χ m f (splitConfiguration n G U).2.1 := by
  have he := observable_independent n G a plane χ m f hf
    (splitConfiguration n G U).1 1 (splitConfiguration n G U).2.1
    (splitConfiguration n G U).2.2 1
  rw [show ((splitConfiguration n G U).1,
    ((splitConfiguration n G U).2.1,(splitConfiguration n G U).2.2)) =
    splitConfiguration n G U from rfl, assemble_split] at he
  exact he

end
end UnifiedTheory.Clay.YangMills.InteriorCellSupport
