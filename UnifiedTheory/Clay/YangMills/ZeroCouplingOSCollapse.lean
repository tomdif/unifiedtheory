/- An actual zero-coupling obstruction: observables of one open half,
independent of boundary links, have rank-one reflected pairing. Centered bulk
observables are reflection-null despite possible positive ordinary variance.
This does not address the renormalized interacting continuum trajectory. -/
import UnifiedTheory.Clay.YangMills.WilsonBoundaryHilbert
import UnifiedTheory.Clay.YangMills.GibbsFullSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ZeroCouplingOSCollapse
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 PeriodicHalfSplit
open PeriodicTimeReflection PeriodicSiteReflection

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem wilson_zero (χ : G → ℂ) (c : ℝ) :
    wilsonLaw (2*n) G χ 0 c = referenceMeasure G (Vertex (2*n)) := by
  have hd : gibbsDensity (Vertex (2*n)) G
      (orientedWilsonAction (Vertex (2*n)) G χ (base (2*n)) (loops (2*n)) 0 c) =
      fun _ => 1 := by
    funext U
    simp [gibbsDensity, orientedWilsonAction, wilsonAction]
  unfold wilsonLaw orientedWilsonMeasure gibbsMeasure gibbsPartition
  rw [hd]
  simp

def bulkObservable (g : HalfConfiguration n G → ℂ)
    (U : Configuration (Vertex (2*n)) G) : ℂ :=
  observable n G (fun z => g z.2) U

theorem bulk_continuous (g : HalfConfiguration n G → ℂ) (hg : Continuous g) :
    Continuous (bulkObservable n G g) :=
  ReflectedWilsonKernel.continuous_observable n G _ (hg.comp continuous_snd)

theorem bulk_assemble (g : HalfConfiguration n G → ℂ) (b : BoundaryConfiguration n G)
    (x y : HalfConfiguration n G) : bulkObservable n G g (assemble n G (b,(x,y))) = g y := by
  change g ((splitConfiguration n G (assemble n G (b,(x,y)))).2.2) = _
  rw [split_assemble]

/-- The exact reflected pairing is rank one in the boundary-independent sector. -/
theorem bulk_pairing (χ : G → ℂ) (c : ℝ) (g h : HalfConfiguration n G → ℂ)
    (hg : Continuous g) (hh : Continuous h) :
    (∫ U, star (bulkObservable n G g (reflectConfiguration (2*n) G U)) *
      bulkObservable n G h U ∂wilsonLaw (2*n) G χ 0 c) =
      star (∫ x, g x ∂halfMeasure n G) * ∫ x, h x ∂halfMeasure n G := by
  letI : BorelSpace (SplitConfiguration n G) := by
    unfold SplitConfiguration
    exact Prod.borelSpace
  rw [wilson_zero]
  have he (U : Configuration (Vertex (2*n)) G) :
      star (bulkObservable n G g (reflectConfiguration (2*n) G U)) * bulkObservable n G h U =
      star (g ((splitConfiguration n G U).2.1)) * h ((splitConfiguration n G U).2.2) := by
    change star (g ((splitConfiguration n G (reflectConfiguration (2*n) G U)).2.2)) * _ = _
    rw [split_reflection]
    rfl
  simp_rw [he]
  rw [(splitConfiguration_preserves n G).integral_comp (coordinates n G).measurableEmbedding
    (fun z => star (g z.2.1) * h z.2.2)]
  have hc : Continuous (fun z : SplitConfiguration n G => star (g z.2.1) * h z.2.2) :=
    (hg.comp (continuous_fst.comp continuous_snd)).star.mul
      (hh.comp (continuous_snd.comp continuous_snd))
  rw [integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp only [integral_const, probReal_univ, one_smul]
  rw [integral_prod_mul (fun x => star (g x)) h]
  simp only [Complex.star_def, integral_conj]

theorem bulk_mean (χ : G → ℂ) (c : ℝ) (g : HalfConfiguration n G → ℂ) (hg : Continuous g) :
    (∫ U, bulkObservable n G g U ∂wilsonLaw (2*n) G χ 0 c) =
      ∫ x, g x ∂halfMeasure n G := by
  have h := bulk_pairing n G χ c (fun _ => 1) g continuous_const hg
  simpa only [bulkObservable, observable, BoundaryReflectionGluing.halfObservable,
    star_one, one_mul, integral_const, probReal_univ, one_smul] using h

theorem centered_bulk_null (χ : G → ℂ) (c : ℝ)
    (g : HalfConfiguration n G → ℂ) (hg : Continuous g) :
    (∫ U, star (bulkObservable n G g (reflectConfiguration (2*n) G U) -
      ∫ W, bulkObservable n G g W ∂wilsonLaw (2*n) G χ 0 c) *
      (bulkObservable n G g U - ∫ W, bulkObservable n G g W ∂wilsonLaw (2*n) G χ 0 c)
        ∂wilsonLaw (2*n) G χ 0 c) = 0 := by
  rw [bulk_mean n G χ c g hg]
  have h := bulk_pairing n G χ c
    (fun x => g x - ∫ y, g y ∂halfMeasure n G)
    (fun x => g x - ∫ y, g y ∂halfMeasure n G)
    (hg.sub continuous_const) (hg.sub continuous_const)
  have hi := hg.integrable_of_hasCompactSupport (μ := halfMeasure n G)
    (HasCompactSupport.of_compactSpace _)
  simpa only [bulkObservable, observable, BoundaryReflectionGluing.halfObservable,
    integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul,
    sub_self, star_zero, zero_mul] using h

/-- Positive ordinary fluctuations do not ensure a nonzero reflected state,
even for the actual periodic Wilson law. -/
theorem ordinary_variance_positive (χ : G → ℂ) (c : ℝ)
    (g : HalfConfiguration n G → ℂ) (hg : Continuous g)
    (x y : HalfConfiguration n G) (hne : g x ≠ g y) :
    0 < ∫ U, ‖bulkObservable n G g U -
      ∫ W, bulkObservable n G g W ∂wilsonLaw (2*n) G χ 0 c‖ ^ 2
        ∂wilsonLaw (2*n) G χ 0 c := by
  have he : orientedWilsonAction (Vertex (2*n)) G χ (base (2*n)) (loops (2*n)) 0 c =
      fun _ => (0 : ℝ) := by funext U; simp [orientedWilsonAction, wilsonAction]
  change 0 < GibbsFullSupport.variance (Vertex (2*n)) G
    (orientedWilsonAction (Vertex (2*n)) G χ (base (2*n)) (loops (2*n)) 0 c) _
  rw [he]
  apply GibbsFullSupport.variance_pos _ G _ continuous_const _ (bulk_continuous n G g hg)
    (assemble n G (1,(1,x))) (assemble n G (1,(1,y)))
  simpa only [bulk_assemble] using hne

end
end UnifiedTheory.Clay.YangMills.ZeroCouplingOSCollapse
