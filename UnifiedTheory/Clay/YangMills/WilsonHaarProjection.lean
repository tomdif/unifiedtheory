/- Exact canonical physical projection for continuous mixtures of Haar
responses. Raw, retained and removed forms all use the same actual row law. -/
import UnifiedTheory.Clay.YangMills.WilsonPhysicalHaarFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonHaarProjection
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalInfluence
open WilsonPhysicalVariance WilsonSymmetricLinkChange WilsonHaarLinkResponse
open WilsonPhysicalHaarFrame CompactDensityEntropy

variable (n : ℕ) [NeZero n]

def rawFamily (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (e : SpatialVertex n × Fin 3) (z : Q × Slice n) : ℝ :=
  WilsonRowGram.score n β hβ e z.1 u z.2

theorem rawFamily_continuous (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (e : SpatialVertex n × Fin 3) : Continuous (rawFamily n β hβ u e) := by
  have hs : Continuous (fun z : Q × Slice n => shift n e z.1 u) :=
    (shift_joint_continuous n e).comp (continuous_fst.prodMk continuous_const)
  exact (((WilsonTemporalInfluence.rawTransition_continuous n β hβ).comp
    (hs.prodMk continuous_snd)).div
    ((WilsonStationaryEntropy.row_continuous n β hβ u).comp continuous_snd)
      (fun z => (WilsonTemporalGauge.rawTransition_pos n β hβ u z.2).ne')).sub continuous_const

def rawMixture (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)) : Slice n → ℝ :=
  CompactHaarFrame.mixture (RegulatedGauge.compactHaar Q) (rawFamily n β hβ u) a

theorem rawMixture_continuous (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)) : Continuous (rawMixture n β hβ u a) :=
  CompactHaarFrame.mixture_continuous _ _ (rawFamily_continuous n β hβ u) a

theorem rawMixture_pairing (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)) (f : C(Slice n, ℝ)) :
    (∫ v, rawMixture n β hβ u a v*f v ∂rowLaw n β hβ u) =
      ∑ e, ∫ q, a e q*(step n β hβ f (shift n e q u)-step n β hβ f u)
        ∂RegulatedGauge.compactHaar Q := by
  letI := rowLaw_probability n β hβ u
  rw [rawMixture, CompactHaarFrame.mixture_pairing _ _ _ (rawFamily_continuous n β hβ u)
    a f f.continuous]
  simp only [CompactHaarFrame.pairing, rawFamily, WilsonRowGram.score,
    WilsonPhysicalScore.raw_pairing n β hβ u _ f]

/-- Orthogonality holds after arbitrary continuous mixing over every rotation. -/
theorem removed_orthogonal (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ))
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    (∫ v, (rawMixture n β hβ u a v-mixture n β hβ u a v)*f v ∂rowLaw n β hβ u) = 0 := by
  letI := rowLaw_probability n β hβ u
  simp_rw [sub_mul]
  rw [integral_sub
    (continuous_integrable (rowLaw n β hβ u) (fun v => rawMixture n β hβ u a v*f v)
      ((rawMixture_continuous n β hβ u a).mul f.continuous))
    (continuous_integrable (rowLaw n β hβ u) (fun v => mixture n β hβ u a v*f v)
      ((mixture_continuous n β hβ u a).mul f.continuous)),
    rawMixture_pairing, mixture_pairing n β hβ u a f hinv, sub_self]

/-- The same Pythagorean decomposition holds for the full Haar integral form. -/
theorem form_decomposition (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)) :
    (∫ v, (rawMixture n β hβ u a v)^2 ∂rowLaw n β hβ u) = form n β hβ u a +
      ∫ v, (rawMixture n β hβ u a v-mixture n β hβ u a v)^2 ∂rowLaw n β hβ u := by
  letI := rowLaw_probability n β hβ u
  have h := CompactPhysicalProjection.gram_decomposition (rowLaw n β hβ u)
    (fun _ : Unit => rawMixture n β hβ u a) (fun _ : Unit => mixture n β hβ u a)
    (fun _ => rawMixture_continuous n β hβ u a) (fun _ => mixture_continuous n β hβ u a)
    (fun _ _ => removed_orthogonal n β hβ u a
      ⟨_, mixture_continuous n β hβ u a⟩ (mixture_gauge n β hβ u a)) () ()
  simpa only [CompactGramResponse.gram, form, pow_two] using h

theorem form_le_raw (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)) :
    form n β hβ u a ≤ ∫ v, (rawMixture n β hβ u a v)^2 ∂rowLaw n β hβ u := by
  rw [form_decomposition]
  exact le_add_of_nonneg_right (integral_nonneg (fun v =>
    sq_nonneg (rawMixture n β hβ u a v-mixture n β hβ u a v)))

/-- Every continuous mixture admits an exact kernel formula, not a finite-sample proxy. -/
theorem form_kernel (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)) :
    form n β hβ u a = ∑ e, ∫ q, ∑ d, ∫ r, a e q*a d r*
      CompactHaarFrame.kernel (rowLaw n β hβ u) (family n β hβ u) e q d r
        ∂RegulatedGauge.compactHaar Q ∂RegulatedGauge.compactHaar Q := by
  letI := rowLaw_probability n β hβ u
  exact CompactHaarFrame.mixture_quadratic _ _ _ (family_continuous n β hβ u) a

/-- Each kernel entry is an entry of the previously constructed canonical physical Gram. -/
theorem kernel_finite_entry (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q) :
    CompactHaarFrame.kernel (rowLaw n β hβ u) (family n β hβ u) e q d r =
      WilsonPhysicalGram.matrix n β hβ (fun b : Bool => if b then e else d)
        (fun b : Bool => if b then q else r) (fun _ => 1) u true false := by
  simp only [WilsonPhysicalGram.matrix, CompactGramResponse.gram,
    WilsonPhysicalGram.physicalScore, Bool.false_eq_true, if_false, if_true,
    one_mul, CompactHaarFrame.kernel, family]

/-- Minimality now applies to an arbitrary continuous representation of the
same mixed physical response, rather than only a fixed finite score family. -/
theorem form_minimal (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)) (r : C(Slice n, ℝ))
    (hrep : ∀ f : C(Slice n, ℝ), (∀ h v, f (gaugeSlice h v) = f v) →
      (∫ v, r v*f v ∂rowLaw n β hβ u) =
        ∑ e, ∫ q, a e q*(step n β hβ f (shift n e q u)-step n β hβ f u)
          ∂RegulatedGauge.compactHaar Q) :
    form n β hβ u a ≤ ∫ v, (r v)^2 ∂rowLaw n β hβ u := by
  letI := rowLaw_probability n β hβ u
  let F : C(Slice n, ℝ) := ⟨_, mixture_continuous n β hβ u a⟩
  have hinv : ∀ h v, F (gaugeSlice h v) = F v := mixture_gauge n β hβ u a
  have hp : (∫ v, (r v-F v)*F v ∂rowLaw n β hβ u) = 0 := by
    simp_rw [sub_mul]
    rw [integral_sub
      (continuous_integrable (rowLaw n β hβ u) (fun v => r v*F v) (r.continuous.mul F.continuous))
      (continuous_integrable (rowLaw n β hβ u) (fun v => F v*F v) (F.continuous.mul F.continuous)),
      hrep F hinv]
    have hF := mixture_pairing n β hβ u a F hinv
    change (∫ v, F v*F v ∂rowLaw n β hβ u) = _ at hF
    rw [hF, sub_self]
  have h := CompactPhysicalProjection.gram_le (rowLaw n β hβ u)
    (fun _ : Unit => (r : Slice n → ℝ)) (fun _ : Unit => (F : Slice n → ℝ))
    (fun _ => r.continuous) (fun _ => F.continuous) (fun _ _ => hp) (fun _ => 1)
  simpa only [CompactGramResponse.gram, Finset.univ_unique, Finset.sum_singleton,
    one_mul, form, F, ContinuousMap.coe_mk, pow_two] using h

end
end UnifiedTheory.Clay.YangMills.WilsonHaarProjection
