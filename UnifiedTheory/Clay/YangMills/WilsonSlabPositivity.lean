/- Positive definiteness of the actual full Wilson time-slab kernel.
All spatial-link representation entries first give explicit finite features
for its kinetic factor. The positive kinetic kernel is completed to a Hilbert
space; its continuous canonical features are then genuinely integrated over
temporal product Haar measure. Simultaneous gauge invariance and Haar
translation identify the averaged Gram kernel. Spatial weights finally give
continuous features whose inner products equal the original full slab kernel.
No positive transfer eigenpair, cutoff-uniform spectral estimate, physical
coupling trajectory, or continuum limit is inferred here. -/
import UnifiedTheory.Clay.YangMills.WilsonSlabGauge
import UnifiedTheory.Clay.YangMills.KernelHilbertCompletion
import Mathlib.MeasureTheory.Function.L2Space
import UnifiedTheory.Clay.YangMills.WilsonCrossingKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSlabPositivity
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonCrossingKernel WilsonSlabGauge
open PositiveKernelForm KernelHilbertCompletion CountableCorrelationCompactness

variable {n : ℕ} [NeZero n] {G : Type*} [Group G]
  {d : Type*} [Fintype d] [DecidableEq d]

/-- All real and imaginary representation entries of the actual spatial links. -/
def sliceFeatures (ρ : G →* Matrix.unitaryGroup d ℂ) (u : SpatialLinks n G)
    (p : (SpatialVertex n × Fin 3) × ((d × d) ⊕ (d × d))) : ℝ :=
  matrixFeatures (ρ (u p.1) : Matrix d d ℂ) p.2

theorem sliceFeatures_inner (ρ : G →* Matrix.unitaryGroup d ℂ)
    (u v : SpatialLinks n G) :
    featureKernel (sliceFeatures ρ) u v =
      ∑ e : SpatialVertex n × Fin 3, (unitaryCharacter ρ ((u e)⁻¹ * v e)).re := by
  unfold featureKernel
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  change featureKernel matrixFeatures (ρ (u e) : Matrix d d ℂ)
    (ρ (v e) : Matrix d d ℂ) = _
  simpa only [unitaryCharacter, map_mul, map_inv, Matrix.UnitaryGroup.mul_val,
    Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose] using
      (real_trace_eq_featureKernel (ρ (u e) : Matrix d d ℂ)
        (ρ (v e) : Matrix d d ℂ)).symm

/-- The entire kinetic weight is one character exponential in explicit finite
features, with the Wilson constant retained. -/
theorem kineticWeight_eq_exp_feature (ρ : G →* Matrix.unitaryGroup d ℂ)
    (β c : ℝ) (u v : SpatialLinks n G) :
    kineticWeight (unitaryCharacter ρ) β c u v =
      Real.exp (-β * (Fintype.card (SpatialVertex n × Fin 3) : ℝ) * c) *
        Real.exp (β * featureKernel (sliceFeatures ρ) u v) := by
  rw [← Real.exp_add, sliceFeatures_inner]
  unfold kineticWeight kineticAction
  congr 1
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

variable {ι : Type*} [Fintype ι]

theorem complexQuadratic_scale (K : ι → ι → ℝ) (z : ι → ℂ) (a : ℝ) :
    complexQuadratic (fun i j => a * K i j) z = (a : ℂ) * complexQuadratic K z := by
  unfold complexQuadratic
  simp only [Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positive definiteness of the complete spatial-slice kinetic factor for
arbitrary complex coefficients; no sign condition is imposed on the Wilson offset. -/
theorem kineticWeight_positive (ρ : G →* Matrix.unitaryGroup d ℂ)
    (β c : ℝ) (hβ : 0 ≤ β) (u : ι → SpatialLinks n G) (z : ι → ℂ) :
    0 ≤ (complexQuadratic (fun i j => kineticWeight (unitaryCharacter ρ) β c
      (u i) (u j)) z).re ∧
      (complexQuadratic (fun i j => kineticWeight (unitaryCharacter ρ) β c
        (u i) (u j)) z).im = 0 := by
  simp only [kineticWeight_eq_exp_feature, complexQuadratic_scale,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  have hp := exp_feature_complex_nonneg (fun i => sliceFeatures ρ (u i)) z β hβ
  have him : (complexQuadratic (fun i j => Real.exp
      (β * featureKernel (sliceFeatures ρ) (u i) (u j))) z).im = 0 := hp.2
  exact ⟨mul_nonneg (Real.exp_pos _).le hp.1, by rw [him, mul_zero]⟩

/-- The kinetic Wilson kernel as a constructed positive Gram kernel. -/
def kineticPositiveKernel (ρ : G →* Matrix.unitaryGroup d ℂ)
    (β c : ℝ) (hβ : 0 ≤ β) : PositiveKernel (SpatialLinks n G) where
  value uv := (kineticWeight (unitaryCharacter ρ) β c uv.1 uv.2 : ℂ)
  positive N u z := by
    have hp := kineticWeight_positive ρ β c hβ u z
    simpa only [gramValue, complexQuadratic, mul_right_comm] using And.intro hp.2 hp.1

section Continuity
variable {X : Type*} [TopologicalSpace X]

/-- Continuous kernel entries give continuous canonical Hilbert features. -/
theorem continuous_canonical (K : PositiveKernel X) (hc : Continuous K.value) :
    Continuous (canonical K) := by
  rw [continuous_iff_continuousAt]
  intro y
  have he (x : X) : ‖canonical K x - canonical K y‖ ^ 2 =
      (K.value (x, x) - K.value (x, y) - K.value (y, x) + K.value (y, y)).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    change (inner ℂ (canonical K x - canonical K y)
      (canonical K x - canonical K y)).re = _
    simp only [inner_sub_left, inner_sub_right, canonical_inner,
      Complex.sub_re, Complex.add_re]
    ring
  have hn : Continuous (fun x : X => ‖canonical K x - canonical K y‖) := by
    have hc' : Continuous (fun x : X =>
        K.value (x, x) - K.value (x, y) - K.value (y, x) + K.value (y, y)) := by
      fun_prop
    have h := (Complex.continuous_re.comp hc').sqrt
    convert h using 1
    ext x
    dsimp only [Function.comp_def]
    rw [← he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_self, norm_zero] using hn.tendsto y

end Continuity

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance temporalHaar_left :
    (temporalHaar (n := n) (G := G)).IsMulLeftInvariant := by
  unfold temporalHaar
  infer_instance

omit [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem kineticWeight_continuous (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hc : Continuous (unitaryCharacter ρ)) (β c : ℝ) :
    Continuous (fun uv : SpatialLinks n G × SpatialLinks n G =>
      kineticWeight (unitaryCharacter ρ) β c uv.1 uv.2) := by
  unfold kineticWeight kineticAction
  fun_prop

omit [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem kineticCanonical_continuous (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hc : Continuous (unitaryCharacter ρ)) (β c : ℝ) (hβ : 0 ≤ β) :
    Continuous (canonical (kineticPositiveKernel (n := n) ρ β c hβ)) := by
  apply continuous_canonical
  exact Complex.continuous_ofReal.comp (kineticWeight_continuous ρ hc β c)

/-- An actual Bochner integral of kinetic feature vectors over temporal links. -/
def gaugeFeature (ρ : G →* Matrix.unitaryGroup d ℂ) (β c : ℝ) (hβ : 0 ≤ β)
    (u : SpatialLinks n G) : Hilbert (kineticPositiveKernel (n := n) ρ β c hβ) :=
  ∫ h, canonical (kineticPositiveKernel (n := n) ρ β c hβ) (gaugeSlice h u) ∂temporalHaar

theorem gaugeFeature_integrable (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hc : Continuous (unitaryCharacter ρ)) (β c : ℝ) (hβ : 0 ≤ β)
    (u : SpatialLinks n G) :
    Integrable (fun h => canonical (kineticPositiveKernel (n := n) ρ β c hβ) (gaugeSlice h u))
      temporalHaar := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  apply (kineticCanonical_continuous ρ hc β c hβ).comp
  unfold gaugeSlice
  fun_prop

theorem gaugeFeature_inner (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hc : Continuous (unitaryCharacter ρ)) (β c : ℝ) (hβ : 0 ≤ β)
    (u v : SpatialLinks n G) :
    inner ℂ (gaugeFeature ρ β c hβ u) (gaugeFeature ρ β c hβ v) =
      ∫ h, (kineticWeight (unitaryCharacter ρ) β c u (gaugeSlice h v) : ℂ) ∂temporalHaar := by
  have hi := gaugeFeature_integrable ρ hc β c hβ u
  have hj := gaugeFeature_integrable ρ hc β c hβ v
  have hleft (z : Hilbert (kineticPositiveKernel (n := n) ρ β c hβ)) :
      inner ℂ (gaugeFeature ρ β c hβ u) z =
        ∫ h, inner ℂ (canonical (kineticPositiveKernel (n := n) ρ β c hβ) (gaugeSlice h u)) z
          ∂temporalHaar := by
    calc
      _ = (starRingEnd ℂ) (inner ℂ z (gaugeFeature ρ β c hβ u)) :=
        (inner_conj_symm (𝕜 := ℂ) (gaugeFeature ρ β c hβ u) z).symm
      _ = (starRingEnd ℂ) (∫ h, inner ℂ z
          (canonical (kineticPositiveKernel (n := n) ρ β c hβ) (gaugeSlice h u))
            ∂temporalHaar) := congrArg (starRingEnd ℂ) (integral_inner hi z).symm
      _ = ∫ h, (starRingEnd ℂ) (inner ℂ z
          (canonical (kineticPositiveKernel (n := n) ρ β c hβ) (gaugeSlice h u)))
            ∂temporalHaar := integral_conj.symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun h =>
        inner_conj_symm (𝕜 := ℂ)
          (canonical (kineticPositiveKernel (n := n) ρ β c hβ) (gaugeSlice h u)) z))
  rw [hleft]
  have he (h : SliceGauge n G) :
      inner ℂ (canonical (kineticPositiveKernel (n := n) ρ β c hβ) (gaugeSlice h u))
        (gaugeFeature ρ β c hβ v) =
      ∫ k, (kineticWeight (unitaryCharacter ρ) β c u (gaugeSlice k v) : ℂ) ∂temporalHaar := by
    rw [gaugeFeature, ← integral_inner hj]
    simp only [canonical_inner, kineticPositiveKernel]
    have hr (k : SliceGauge n G) :
        kineticWeight (unitaryCharacter ρ) β c (gaugeSlice h u) (gaugeSlice k v) =
          kineticWeight (unitaryCharacter ρ) β c u (gaugeSlice (h⁻¹ * k) v) := by
      rw [← kineticWeight_gauge _ (unitaryCharacter_class ρ) β c h⁻¹
        (gaugeSlice h u) (gaugeSlice k v), gaugeSlice_inv, ← gaugeSlice_mul]
    simp_rw [hr]
    exact integral_mul_left_eq_self
      (fun k => (kineticWeight (unitaryCharacter ρ) β c u (gaugeSlice k v) : ℂ)) h⁻¹
  simp only [he, integral_const, probReal_univ, one_smul]

theorem gaugeFeature_continuous (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hc : Continuous (unitaryCharacter ρ)) (β c : ℝ) (hβ : 0 ≤ β) :
    Continuous (gaugeFeature (n := n) ρ β c hβ) := by
  have he : Continuous (fun uh : SpatialLinks n G × SliceGauge n G =>
      canonical (kineticPositiveKernel (n := n) ρ β c hβ) (gaugeSlice uh.2 uh.1)) := by
    apply (kineticCanonical_continuous ρ hc β c hβ).comp
    unfold gaugeSlice
    fun_prop
  simpa only [Measure.restrict_univ, gaugeFeature] using
    (continuous_parametric_integral_of_continuous (μ := temporalHaar) he isCompact_univ)

/-- The spatial potential multiplies the genuinely averaged kinetic feature. -/
def slabFeature (ρ : G →* Matrix.unitaryGroup d ℂ) (β c : ℝ) (hβ : 0 ≤ β)
    (u : SpatialLinks n G) : Hilbert (kineticPositiveKernel (n := n) ρ β c hβ) :=
  (spatialWeight (unitaryCharacter ρ) β c u : ℂ) • gaugeFeature ρ β c hβ u

theorem slabFeature_continuous (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hc : Continuous (unitaryCharacter ρ)) (β c : ℝ) (hβ : 0 ≤ β) :
    Continuous (slabFeature (n := n) ρ β c hβ) := by
  have hw : Continuous (fun u : SpatialLinks n G =>
      (spatialWeight (unitaryCharacter ρ) β c u : ℂ)) := by
    unfold spatialWeight potential spatialHolonomy
    fun_prop
  exact hw.smul (gaugeFeature_continuous ρ hc β c hβ)

/-- An exact Hilbert-space Gram representation of the original full slab kernel. -/
theorem slabFeature_inner (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hc : Continuous (unitaryCharacter ρ)) (β c : ℝ) (hβ : 0 ≤ β)
    (u v : SpatialLinks n G) :
    inner ℂ (slabFeature ρ β c hβ u) (slabFeature ρ β c hβ v) =
      (kernel (unitaryCharacter ρ) β c u v : ℂ) := by
  unfold slabFeature
  rw [inner_smul_left (𝕜 := ℂ) (gaugeFeature ρ β c hβ u)
    ((spatialWeight (unitaryCharacter ρ) β c v : ℂ) • gaugeFeature ρ β c hβ v)
    (spatialWeight (unitaryCharacter ρ) β c u : ℂ)]
  rw [inner_smul_right (𝕜 := ℂ) (gaugeFeature ρ β c hβ u)
    (gaugeFeature ρ β c hβ v) (spatialWeight (unitaryCharacter ρ) β c v : ℂ)]
  rw [Complex.conj_ofReal, gaugeFeature_inner ρ hc β c hβ, integral_complex_ofReal]
  rw [kernel_eq_gauge_average _ (unitaryCharacter_class ρ)]
  push_cast
  ring

/-- Full slab positive definiteness, with temporal integration and both spatial
weights included, proved by the constructed averaged Hilbert features. -/
theorem kernel_positiveDefinite (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hc : Continuous (unitaryCharacter ρ)) (β c : ℝ) (hβ : 0 ≤ β)
    (u : ι → SpatialLinks n G) (z : ι → ℂ) :
    0 ≤ (complexQuadratic (fun i j => kernel (unitaryCharacter ρ) β c (u i) (u j)) z).re ∧
      (complexQuadratic (fun i j => kernel (unitaryCharacter ρ) β c (u i) (u j)) z).im = 0 := by
  let v := ∑ i, z i • slabFeature ρ β c hβ (u i)
  have he : complexQuadratic (fun i j => kernel (unitaryCharacter ρ) β c (u i) (u j)) z =
      inner ℂ v v := by
    change _ = inner ℂ (∑ i, z i • slabFeature ρ β c hβ (u i))
      (∑ i, z i • slabFeature ρ β c hβ (u i))
    rw [sum_inner]
    simp only [inner_sum, complexQuadratic]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [inner_smul_left (𝕜 := ℂ) (slabFeature ρ β c hβ (u i))
      (z j • slabFeature ρ β c hβ (u j)) (z i)]
    rw [inner_smul_right (𝕜 := ℂ) (slabFeature ρ β c hβ (u i))
      (slabFeature ρ β c hβ (u j)) (z j)]
    rw [slabFeature_inner ρ hc β c hβ, starRingEnd_apply]
    ring
  rw [he]
  exact ⟨inner_self_nonneg (𝕜 := ℂ) (x := v), inner_self_im (𝕜 := ℂ) v⟩

/-- The original Wilson slab, as a positive Gram kernel rather than merely a
pointwise positive continuous function. -/
def slabPositiveKernel (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hc : Continuous (unitaryCharacter ρ)) (β c : ℝ) (hβ : 0 ≤ β) :
    PositiveKernel (SpatialLinks n G) where
  value uv := (kernel (unitaryCharacter ρ) β c uv.1 uv.2 : ℂ)
  positive N u z := by
    have hp := kernel_positiveDefinite ρ hc β c hβ u z
    simpa only [gramValue, complexQuadratic, mul_right_comm] using And.intro hp.2 hp.1

end
end UnifiedTheory.Clay.YangMills.WilsonSlabPositivity
