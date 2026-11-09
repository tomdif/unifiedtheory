/- Actual Wilson marginals inherit the single-link action oscillation after
arbitrary finite elimination. The resulting normalized surviving-link law is
compared to Haar with constants independent of volume and eliminated-set size.
The exponential coupling cost is explicit; no weak-coupling contraction or
approximate tensorization is asserted. -/
import UnifiedTheory.Clay.YangMills.WilsonCrossCovariance
import UnifiedTheory.Clay.YangMills.WilsonEnergyDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonRetainedLawComparison
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonBlockMarginal
open GibbsMarginalTower WilsonIndependentBlocks SingleLinkWilsonOscillation
open scoped ENNReal

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The unnormalized density of the actual retained Wilson coordinates. -/
def integratedWeight (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n))) :
    Outside (G := G) S → ℝ :=
  fiberMass (insideMeasure S (compactHaar G)) (splitAction n G χ β c S)

/-- The exact effective action, without a Wilson-form closure assumption. -/
def evolvedAction (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n))) :
    Outside (G := G) S → ℝ :=
  effectiveAction (insideMeasure S (compactHaar G)) (splitAction n G χ β c S)

theorem integratedWeight_positive (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (b : Outside (G := G) S) :
    0 < integratedWeight n G χ β c S b :=
  fiberMass_positive _ _ (splitAction_continuous n G χ hχ β c S) b

theorem integratedWeight_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) : Continuous (integratedWeight n G χ β c S) :=
  fiberMass_continuous _ _ (splitAction_continuous n G χ hχ β c S)

theorem evolvedAction_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) : Continuous (evolvedAction n G χ β c S) :=
  effectiveAction_continuous _ _ (splitAction_continuous n G χ hχ β c S)

/-- This effective law is the existing actual Wilson marginal. -/
theorem retainedLaw_eq_effective (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) :
    WilsonCrossCovariance.retainedLaw n G χ β c S =
      CompactGibbsContinuity.law (outsideMeasure S (compactHaar G))
        (evolvedAction n G χ β c S) :=
  marginal_eq_effectiveLaw _ _ _ (splitAction_continuous n G χ hχ β c S)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
/-- Original locality holds uniformly over every eliminated configuration. -/
theorem splitAction_oscillation (χ : G → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (e : {e : Edge (Vertex n) // e ∉ S}) (b b' : Outside (G := G) S)
    (hb : ∀ j, j ≠ e → b j = b' j) (z : Inside (G := G) S) :
    |splitAction n G χ β c S (b,z) - splitAction n G χ β c S (b',z)| ≤ 12 * |β| * B := by
  apply action_oscillation n G χ B hB hχ β c (edgeCoord n e.val).1 (edgeCoord n e.val).2
  intro j hj
  rw [selected_edgeCoord] at hj
  by_cases hjs : j ∈ S
  · simp only [assemble_inside S _ j hjs]
  · simp only [assemble_outside S _ j hjs]
    exact hb ⟨j,hjs⟩ (fun he => hj (congrArg Subtype.val he))

/-- Integration does not increase the local Boltzmann-factor comparison. -/
theorem integratedWeight_comparison (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (e : {e : Edge (Vertex n) // e ∉ S})
    (b b' : Outside (G := G) S) (hb : ∀ j, j ≠ e → b j = b' j) :
    integratedWeight n G χ β c S b ≤
      Real.exp (12 * |β| * B) * integratedWeight n G χ β c S b' := by
  have hi (w : Outside (G := G) S) :
      Integrable (fun z => Real.exp (-splitAction n G χ β c S (w,z)))
        (insideMeasure S (compactHaar G)) :=
    (Real.continuous_exp.comp ((splitAction_continuous n G χ hcχ β c S).comp
      (continuous_const.prodMk continuous_id)).neg).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have h := integral_mono (hi b) ((hi b').const_mul (Real.exp (12 * |β| * B))) (fun z => by
    have hs := splitAction_oscillation n G χ B hB hχ β c S e b b' hb z
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl := neg_le_abs (splitAction n G χ β c S (b,z) - splitAction n G χ β c S (b',z))
    linarith)
  rw [integral_const_mul] at h
  exact h

/-- The same local action oscillation survives arbitrary finite elimination. -/
theorem evolvedAction_oscillation (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (e : {e : Edge (Vertex n) // e ∉ S})
    (b b' : Outside (G := G) S) (hb : ∀ j, j ≠ e → b j = b' j) :
    |evolvedAction n G χ β c S b - evolvedAction n G χ β c S b'| ≤ 12 * |β| * B := by
  have h1 := Real.log_le_log (integratedWeight_positive n G χ hcχ β c S b)
    (integratedWeight_comparison n G χ hcχ B hB hχ β c S e b b' hb)
  have h2 := Real.log_le_log (integratedWeight_positive n G χ hcχ β c S b')
    (integratedWeight_comparison n G χ hcχ B hB hχ β c S e b' b (fun j hj => (hb j hj).symm))
  rw [Real.log_mul (Real.exp_ne_zero _) (integratedWeight_positive n G χ hcχ β c S b').ne',
    Real.log_exp] at h1
  rw [Real.log_mul (Real.exp_ne_zero _) (integratedWeight_positive n G χ hcχ β c S b).ne',
    Real.log_exp] at h2
  change |-Real.log (integratedWeight n G χ β c S b) -
    -Real.log (integratedWeight n G χ β c S b')| ≤ _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The surviving link is split from the other retained coordinates. -/
def linkSplitAction (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (e : {e : Edge (Vertex n) // e ∉ S})
    (z : SingleCoordinateProduct.Outside (G := G) e × G) : ℝ :=
  evolvedAction n G χ β c S (SingleCoordinateProduct.assemble e z)

theorem linkSplitAction_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (e : {e : Edge (Vertex n) // e ∉ S}) :
    Continuous (linkSplitAction n G χ β c S e) :=
  (evolvedAction_continuous n G χ hχ β c S).comp (SingleCoordinateProduct.assemble_continuous e)

/-- The true normalized conditional law of one surviving coordinate. -/
def linkLaw (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (e : {e : Edge (Vertex n) // e ∉ S}) (r : SingleCoordinateProduct.Outside (G := G) e) :
    Measure G := CompactGibbsContinuity.law (compactHaar G)
      (fun q => linkSplitAction n G χ β c S e (r,q))

theorem linkLaw_probability (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (e : {e : Edge (Vertex n) // e ∉ S})
    (r : SingleCoordinateProduct.Outside (G := G) e) :
    IsProbabilityMeasure (linkLaw n G χ β c S e r) :=
  CompactGibbsContinuity.law_probability _ _
    ((linkSplitAction_continuous n G χ hχ β c S e).comp (continuous_const.prodMk continuous_id))

theorem linkAction_oscillation (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (e : {e : Edge (Vertex n) // e ∉ S})
    (r : SingleCoordinateProduct.Outside (G := G) e) (q q' : G) :
    |linkSplitAction n G χ β c S e (r,q) - linkSplitAction n G χ β c S e (r,q')| ≤
      12 * |β| * B := by
  apply evolvedAction_oscillation n G χ hcχ B hB hχ β c S e
  intro j hj
  simp only [SingleCoordinateProduct.assemble_other e j hj]

/-- The actual normalized surviving-link density with respect to Haar. -/
def linkDensity (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (e : {e : Edge (Vertex n) // e ∉ S}) (r : SingleCoordinateProduct.Outside (G := G) e)
    (q : G) : ℝ :=
  Real.exp (-linkSplitAction n G χ β c S e (r,q)) /
    (∫ u, Real.exp (-linkSplitAction n G χ β c S e (r,u)) ∂compactHaar G)

/-- Normalization incurs no second oscillation factor. -/
theorem linkDensity_bounds (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (e : {e : Edge (Vertex n) // e ∉ S})
    (r : SingleCoordinateProduct.Outside (G := G) e) (q : G) :
    Real.exp (-(12 * |β| * B)) ≤ linkDensity n G χ β c S e r q ∧
      linkDensity n G χ β c S e r q ≤ Real.exp (12 * |β| * B) := by
  let A := fun u => linkSplitAction n G χ β c S e (r,u)
  let w := fun u => Real.exp (-A u)
  let C := 12 * |β| * B
  have hA : Continuous A :=
    (linkSplitAction_continuous n G χ hcχ β c S e).comp (continuous_const.prodMk continuous_id)
  have hi : Integrable w (compactHaar G) :=
    (Real.continuous_exp.comp hA.neg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz := CompactGibbsContinuity.partition_positive (compactHaar G) A hA
  have hw (u v : G) : w u ≤ Real.exp C * w v := by
    dsimp only [w]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := linkAction_oscillation n G χ hcχ B hB hχ β c S e r u v
    have hl := neg_le_abs (A u - A v)
    change |A u - A v| ≤ C at h
    linarith
  have hupper := integral_mono (integrable_const (w q)) (hi.const_mul (Real.exp C))
    (fun u => hw q u)
  have hlower := integral_mono hi (integrable_const (Real.exp C * w q))
    (fun u => hw u q)
  simp only [integral_const_mul, integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul] at hupper hlower
  constructor
  · apply (le_div_iff₀ hz).mpr
    have h := mul_le_mul_of_nonneg_left hlower (Real.exp_pos (-C)).le
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at h
    exact h
  · exact (div_le_iff₀ hz).mpr hupper

/-- Literal density representation of the evolved conditional probability. -/
theorem linkLaw_eq_withDensity (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (e : {e : Edge (Vertex n) // e ∉ S})
    (r : SingleCoordinateProduct.Outside (G := G) e) :
    linkLaw n G χ β c S e r =
      (compactHaar G).withDensity (fun q => ENNReal.ofReal (linkDensity n G χ β c S e r q)) := by
  let A := fun q => linkSplitAction n G χ β c S e (r,q)
  have hA : Continuous A :=
    (linkSplitAction_continuous n G χ hcχ β c S e).comp (continuous_const.prodMk continuous_id)
  have hz := CompactGibbsContinuity.partition_positive (compactHaar G) A hA
  unfold linkLaw CompactGibbsContinuity.law LocalGibbsComparison.weightedLaw linkDensity
  change (ENNReal.ofReal (∫ q, Real.exp (-A q) ∂compactHaar G))⁻¹ •
    (compactHaar G).withDensity (fun q => ENNReal.ofReal (Real.exp (-A q))) =
    (compactHaar G).withDensity (fun q => ENNReal.ofReal
      (Real.exp (-A q) / (∫ u, Real.exp (-A u) ∂compactHaar G)))
  have hw : Measurable (fun q => ENNReal.ofReal (Real.exp (-A q))) :=
    (Real.continuous_exp.comp hA.neg).measurable.ennreal_ofReal
  rw [← withDensity_smul _ hw]
  congr 1
  funext q
  rw [ENNReal.ofReal_div_of_pos hz]
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Both measure inequalities apply to every measurable retained-link event. -/
theorem linkLaw_comparison (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (e : {e : Edge (Vertex n) // e ∉ S})
    (r : SingleCoordinateProduct.Outside (G := G) e) :
    ENNReal.ofReal (Real.exp (-(12 * |β| * B))) • compactHaar G ≤ linkLaw n G χ β c S e r ∧
      linkLaw n G χ β c S e r ≤ ENNReal.ofReal (Real.exp (12 * |β| * B)) • compactHaar G := by
  rw [linkLaw_eq_withDensity n G χ hcχ β c S e r]
  constructor
  · rw [← withDensity_const]
    exact withDensity_mono (Filter.Eventually.of_forall (fun q =>
      ENNReal.ofReal_le_ofReal (linkDensity_bounds n G χ hcχ B hB hχ β c S e r q).1))
  · rw [← withDensity_const]
    exact withDensity_mono (Filter.Eventually.of_forall (fun q =>
      ENNReal.ofReal_le_ofReal (linkDensity_bounds n G χ hcχ B hB hχ β c S e r q).2))

/-- All nonnegative continuous observables obey the same two-sided comparison. -/
theorem link_expectation_comparison (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (e : {e : Edge (Vertex n) // e ∉ S})
    (r : SingleCoordinateProduct.Outside (G := G) e)
    (F : G → ℝ) (hF : Continuous F) (hFn : ∀ q, 0 ≤ F q) :
    Real.exp (-(12 * |β| * B)) * (∫ q, F q ∂compactHaar G) ≤
      (∫ q, F q ∂linkLaw n G χ β c S e r) ∧
    (∫ q, F q ∂linkLaw n G χ β c S e r) ≤
      Real.exp (12 * |β| * B) * (∫ q, F q ∂compactHaar G) := by
  letI := linkLaw_probability n G χ hcχ β c S e r
  have h := linkLaw_comparison n G χ hcχ B hB hχ β c S e r
  constructor
  · have hm := integral_mono_measure h.1 (Filter.Eventually.of_forall hFn)
      (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    simpa only [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      smul_eq_mul] using hm
  · have hm := integral_mono_measure h.2 (Filter.Eventually.of_forall hFn)
      ((hF.integrable_of_hasCompactSupport (μ := compactHaar G)
        (HasCompactSupport.of_compactSpace _)).smul_measure ENNReal.ofReal_ne_top)
    simpa only [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      smul_eq_mul] using hm

/-- In particular, local centered squares remain quantitatively comparable after elimination. -/
theorem link_centered_square_comparison (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (e : {e : Edge (Vertex n) // e ∉ S})
    (r : SingleCoordinateProduct.Outside (G := G) e) (F : G → ℝ) (hF : Continuous F) (m : ℝ) :
    Real.exp (-(12 * |β| * B)) * (∫ q, (F q - m)^2 ∂compactHaar G) ≤
      (∫ q, (F q - m)^2 ∂linkLaw n G χ β c S e r) ∧
    (∫ q, (F q - m)^2 ∂linkLaw n G χ β c S e r) ≤
      Real.exp (12 * |β| * B) * (∫ q, (F q - m)^2 ∂compactHaar G) :=
  link_expectation_comparison n G χ hcχ B hB hχ β c S e r _
    ((hF.sub continuous_const).pow 2) (fun _ => sq_nonneg _)

/-- Exact coordinate transport of the original interacting Wilson probability. -/
theorem wilson_coordinates_preserving (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) :
    MeasurePreserving (assemble (G := G) S).symm (wilsonLaw n G χ β c)
      (CompactGibbsContinuity.law
        ((outsideMeasure S (compactHaar G)).prod (insideMeasure S (compactHaar G)))
        (splitAction n G χ β c S)) := by
  have h := weightedLaw_preserving _ _ (assemble (G := G) S)
    (assemble_preserving S (compactHaar G))
    (fun U => Real.exp (-WilsonBlockIntegration.action n G χ β c U))
    (Real.continuous_exp.comp
      (continuous_orientedWilsonAction _ G χ hχ (base n) (loops n) β c).neg).measurable
  have hg := GibbsCoordinateTransport.gibbs_eq_weightedLaw (Vertex n) G
    (orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c)
    (continuous_orientedWilsonAction _ G χ hχ (base n) (loops n) β c)
  change wilsonLaw n G χ β c = LocalGibbsComparison.weightedLaw
    (Measure.pi (fun _ : Edge (Vertex n) => compactHaar G))
    (fun U => Real.exp (-WilsonBlockIntegration.action n G χ β c U)) at hg
  rw [← hg] at h
  exact h.symm (assemble S)

/-- The evolved law is literally the original law's retained-coordinate pushforward. -/
theorem retainedLaw_eq_map (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) :
    WilsonCrossCovariance.retainedLaw n G χ β c S =
      (wilsonLaw n G χ β c).map (fun U => ((assemble (G := G) S).symm U).1) := by
  unfold WilsonCrossCovariance.retainedLaw marginal
  rw [← (wilson_coordinates_preserving n G χ hχ β c S).map_eq,
    Measure.map_map measurable_fst (assemble S).symm.measurable]
  rfl

/-- This disintegration identifies linkLaw as the actual conditional law of the evolved measure. -/
theorem retained_link_disintegration (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (e : {e : Edge (Vertex n) // e ∉ S})
    (F : Outside (G := G) S → ℝ) (hF : Continuous F) :
    (∫ b, F b ∂WilsonCrossCovariance.retainedLaw n G χ β c S) =
      ∫ r, (∫ q, F (SingleCoordinateProduct.assemble e (r,q))
        ∂linkLaw n G χ β c S e r)
        ∂marginal (Measure.pi (fun _ : {j : {i : Edge (Vertex n) // i ∉ S} // j ≠ e} =>
          compactHaar G)) (compactHaar G) (linkSplitAction n G χ β c S e) := by
  rw [retainedLaw_eq_effective n G χ hχ β c S]
  have hA := evolvedAction_continuous n G χ hχ β c S
  have ht := GibbsCoordinateTransport.weighted_integral_transport _ _
    (SingleCoordinateProduct.assemble e) (SingleCoordinateProduct.assemble_preserving e
      (compactHaar G))
    (fun b => Real.exp (-evolvedAction n G χ β c S b))
    (Real.continuous_exp.comp hA.neg).measurable (fun b => (Real.exp_pos _).le)
    (CompactGibbsContinuity.partition_positive _ _ hA) F
  change (∫ z, F (SingleCoordinateProduct.assemble e z)
    ∂CompactGibbsContinuity.law _ (linkSplitAction n G χ β c S e)) =
    (∫ b, F b ∂CompactGibbsContinuity.law _ (evolvedAction n G χ β c S)) at ht
  have hr := response_expectation
    (Measure.pi (fun _ : {j : {i : Edge (Vertex n) // i ∉ S} // j ≠ e} => compactHaar G))
    (compactHaar G) (linkSplitAction n G χ β c S e)
    (fun z => F (SingleCoordinateProduct.assemble e z))
    (linkSplitAction_continuous n G χ hχ β c S e)
    (hF.comp (SingleCoordinateProduct.assemble_continuous e))
  rw [← ht, ← hr]
  apply integral_congr_ae
  filter_upwards with r
  exact response_eq_expectation _ _ _ (linkSplitAction_continuous n G χ hχ β c S e) r

/-- Explicit SU(2) specialization for its actual quaternion fundamental character. -/
theorem su2_linkLaw_comparison (β : ℝ) (S : Finset (Edge (Vertex n)))
    (e : {e : Edge (Vertex n) // e ∉ S})
    (r : SingleCoordinateProduct.Outside (G := WilsonSingleLinkStaples.Q) e) :
    ENNReal.ofReal (Real.exp (-(24 * |β|))) • compactHaar WilsonSingleLinkStaples.Q ≤
      linkLaw n WilsonSingleLinkStaples.Q WilsonSingleLinkStaples.character β 2 S e r ∧
    linkLaw n WilsonSingleLinkStaples.Q WilsonSingleLinkStaples.character β 2 S e r ≤
      ENNReal.ofReal (Real.exp (24 * |β|)) • compactHaar WilsonSingleLinkStaples.Q := by
  have hb (q : WilsonSingleLinkStaples.Q) : ‖WilsonSingleLinkStaples.character q‖ ≤ 2 := by
    simpa only [Fintype.card_fin, Nat.cast_ofNat] using
      UnitaryCharacterObservables.unitary_trace_bound (WilsonEnergyDensity.representation q)
  have h := linkLaw_comparison n WilsonSingleLinkStaples.Q WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_continuous 2 (by norm_num) hb β 2 S e r
  simpa only [show 12 * |β| * 2 = 24 * |β| by ring] using h

end
end UnifiedTheory.Clay.YangMills.WilsonRetainedLawComparison
