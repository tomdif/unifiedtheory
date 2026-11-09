/- Strict positivity for a centered actual U(2) plaquette and the four-link
Wilson spatial transfer kernel. The full periodic time-slice/conditional
response identification is not proved here. -/
import UnifiedTheory.Clay.YangMills.WilsonFeatureIntegral
import UnifiedTheory.Clay.YangMills.HaarCenteredFluctuation
import UnifiedTheory.Clay.YangMills.UnitaryUniformVariance
import Mathlib.Topology.Algebra.Star.Unitary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Clay.YangMills.FourLinkWilsonTransfer
noncomputable section
open MeasureTheory Matrix WilsonCrossingKernel WilsonFeatureIntegral RegulatedGauge

abbrev GaugeGroup := Matrix.unitaryGroup (Fin 2) ℂ
abbrev Links := Fin 4 → GaugeGroup
abbrev Feature := Fin 4 × ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2))

instance gaugeGroup_measurable : MeasurableSpace GaugeGroup := borel GaugeGroup
instance gaugeGroup_borel : BorelSpace GaugeGroup := ⟨rfl⟩
instance gaugeGroup_secondCountable : SecondCountableTopology GaugeGroup := by
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  exact TopologicalSpace.Subtype.secondCountableTopology
    (GaugeGroup : Set (Matrix (Fin 2) (Fin 2) ℂ))
instance links_borel : BorelSpace Links := by
  unfold Links
  infer_instance
instance gaugeGroup_compact : CompactSpace GaugeGroup := by
  apply isCompact_iff_compactSpace.mp
  apply ((isCompact_closedBall (0 : ℂ) 1).matrix (m := Fin 2) (n := Fin 2)).of_isClosed_subset
    isClosed_unitary
  intro U hU i j
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    UnitaryCharacterObservables.unitary_entry_bound (⟨U,hU⟩ : GaugeGroup) i j

def haar : Measure Links := Measure.pi (fun _ : Fin 4 => compactHaar GaugeGroup)

instance haar_probability : IsProbabilityMeasure haar := by unfold haar; infer_instance
instance haar_open_positive : Measure.IsOpenPosMeasure haar := by
  unfold haar compactHaar
  infer_instance

def features (U : Links) (d : Feature) : ℝ := matrixFeatures (U d.1 : Matrix (Fin 2) (Fin 2) ℂ) d.2

private theorem entry_continuous (r : Fin 4) (i j : Fin 2) :
    Continuous (fun U : Links => (U r : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp
    (continuous_subtype_val.comp (continuous_apply r)))

theorem features_continuous (d : Feature) : Continuous (fun U => features U d) := by
  rcases d with ⟨r, ij | ij⟩
  · exact Complex.continuous_re.comp ((continuous_apply ij.2).comp
      ((continuous_apply ij.1).comp (continuous_subtype_val.comp (continuous_apply r))))
  · exact Complex.continuous_im.comp ((continuous_apply ij.2).comp
      ((continuous_apply ij.1).comp (continuous_subtype_val.comp (continuous_apply r))))

def holonomy (U : Links) : GaugeGroup := U 0 * U 1 * (U 2)⁻¹ * (U 3)⁻¹
def plaquette (U : Links) : ℝ := (Matrix.trace (holonomy U : Matrix (Fin 2) (Fin 2) ℂ)).re

theorem plaquette_continuous : Continuous plaquette := by
  have hh : Continuous holonomy :=
    (((continuous_apply (0 : Fin 4)).mul (continuous_apply 1)).mul
      (continuous_apply 2).inv).mul (continuous_apply 3).inv
  exact (Complex.continuous_re.comp
    (UnitaryCharacterObservables.unitaryCharacter_continuous (MonoidHom.id GaugeGroup)
      continuous_id)).comp hh

def center : ℝ := ∫ U, plaquette U ∂haar
def centered (U : Links) : ℝ := plaquette U - center

@[fun_prop] theorem centered_continuous : Continuous centered := plaquette_continuous.sub continuous_const

theorem centered_mean_zero : (∫ U, centered U ∂haar) = 0 := by
  unfold centered
  rw [integral_sub
    (plaquette_continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (integrable_const _), integral_const]
  simp [center]

theorem variance_positive : 0 < ∫ U, (centered U)^2 ∂haar := by
  have h := HaarCenteredFluctuation.real_variance_positive haar plaquette plaquette_continuous
    (fun _ => (1 : GaugeGroup)) (fun r : Fin 4 => if r = 0 then (-1 : GaugeGroup) else 1) (by
      have h2 : (2 : Fin 4) ≠ 0 := by decide
      have h3 : (3 : Fin 4) ≠ 0 := by decide
      norm_num [plaquette, holonomy, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
        h2, h3, Unitary.coe_neg])
  simpa only [ProbabilityTheory.variance_eq_integral plaquette_continuous.measurable.aemeasurable,
    center, centered] using h

def kernel (β : ℝ) (U V : Links) : ℝ :=
  Real.exp (β * ∑ r : Fin 4, (Matrix.trace
    (((U r)⁻¹ * V r : GaugeGroup) : Matrix (Fin 2) (Fin 2) ℂ)).re)

theorem kernel_feature (β : ℝ) (U V : Links) :
    kernel β U V = Real.exp (β * featureKernel features U V) := by
  unfold kernel
  congr 2
  simp only [featureKernel, Fintype.sum_prod_type, features]
  apply Finset.sum_congr rfl
  intro r _
  change (Matrix.trace ((U r : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
    (V r : Matrix (Fin 2) (Fin 2) ℂ))).re = _
  exact real_trace_eq_featureKernel _ _

def signal (β : ℝ) : ℝ :=
  ∫ z : Links × Links, centered z.1 * kernel β z.1 z.2 * centered z.2 ∂haar.prod haar

def fourthCoefficient : ℝ := coefficient haar features centered 4

/-- The coefficient is a finite explicit sum of squared Haar moments. -/
theorem signal_lower (β : ℝ) (hβ : 0 ≤ β) :
    β^4 / 24 * fourthCoefficient ≤ signal β := by
  have h := coefficient_lower haar features features_continuous centered centered_continuous β hβ 4
  norm_num only [show (4 : ℕ).factorial = 24 from rfl, Nat.cast_ofNat] at h
  simpa only [fourthCoefficient, signal, kernel_feature, pairing] using h

private def componentIndex (row col : Fin 4 → Fin 2) (r : Fin 4) (b : Bool) : Feature :=
  (r, if b then Sum.inl (row r,col r) else Sum.inr (row r,col r))

private def componentScalar (conjugated : Fin 4 → Bool) (r : Fin 4) (b : Bool) : ℂ :=
  if b then 1 else if conjugated r then -Complex.I else Complex.I

private theorem complex_word_zero (hzero : fourthCoefficient = 0)
    (row col : Fin 4 → Fin 2) (conjugated : Fin 4 → Bool) :
    (∫ U, (centered U : ℂ) * ∏ r : Fin 4,
      (if conjugated r then star ((U r : Matrix (Fin 2) (Fin 2) ℂ) (row r) (col r))
      else (U r : Matrix (Fin 2) (Fin 2) ℂ) (row r) (col r)) ∂haar) = 0 := by
  have hm (p : Fin 4 → Feature) : moment haar features centered 4 p = 0 := by
    change (∑ p : Fin 4 → Feature, moment haar features centered 4 p ^ 2) = 0 at hzero
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => sq_nonneg
      (moment haar features centered 4 p))).mp hzero p (Finset.mem_univ p)
    exact sq_eq_zero_iff.mp hz
  have he (U : Links) (r : Fin 4) :
      (if conjugated r then star ((U r : Matrix (Fin 2) (Fin 2) ℂ) (row r) (col r))
      else (U r : Matrix (Fin 2) (Fin 2) ℂ) (row r) (col r)) =
      ∑ b : Bool, componentScalar conjugated r b * (features U (componentIndex row col r b) : ℂ) := by
    cases h : conjugated r <;>
      apply Complex.ext <;>
      simp [componentScalar, componentIndex, features, matrixFeatures, h]
  simp_rw [he, Fintype.prod_sum, Finset.prod_mul_distrib, ← Complex.ofReal_prod,
    Finset.mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro b _
    have he' : (fun U : Links => (centered U : ℂ) *
        ((∏ r, componentScalar conjugated r (b r)) *
          ((∏ r, features U (componentIndex row col r (b r)) : ℝ) : ℂ))) =
        (fun U : Links => (∏ r, componentScalar conjugated r (b r)) *
          ((centered U * ∏ r, features U (componentIndex row col r (b r)) : ℝ) : ℂ)) := by
      funext U
      simp only [Complex.ofReal_mul]
      ring
    rw [he', integral_const_mul, integral_complex_ofReal,
      show (∫ U, centered U * ∏ r, features U (componentIndex row col r (b r)) ∂haar) = 0 from
        hm (fun r => componentIndex row col r (b r))]
    simp
  · intro b _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (Complex.continuous_ofReal.comp centered_continuous).mul
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_finset_prod _ (fun r _ => features_continuous _))))

private theorem plaquette_moment_zero (hzero : fourthCoefficient = 0) :
    (∫ U, (centered U : ℂ) * Matrix.trace
      (holonomy U : Matrix (Fin 2) (Fin 2) ℂ) ∂haar) = 0 := by
  have ht (i j k l : Fin 2) : Continuous (fun U : Links => (centered U : ℂ) *
      ((U 0 : Matrix (Fin 2) (Fin 2) ℂ) i j * (U 1 : Matrix (Fin 2) (Fin 2) ℂ) j k *
        star ((U 2 : Matrix (Fin 2) (Fin 2) ℂ) l k) *
        star ((U 3 : Matrix (Fin 2) (Fin 2) ℂ) i l))) :=
    (Complex.continuous_ofReal.comp centered_continuous).mul
      ((((entry_continuous 0 i j).mul (entry_continuous 1 j k)).mul
        (entry_continuous 2 l k).star).mul (entry_continuous 3 i l).star)
  have hz (i j k l : Fin 2) :
      (∫ U, (centered U : ℂ) *
        ((U 0 : Matrix (Fin 2) (Fin 2) ℂ) i j * (U 1 : Matrix (Fin 2) (Fin 2) ℂ) j k *
          star ((U 2 : Matrix (Fin 2) (Fin 2) ℂ) l k) *
          star ((U 3 : Matrix (Fin 2) (Fin 2) ℂ) i l)) ∂haar) = 0 := by
    simpa only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Bool.false_eq_true,
      if_false, if_true, mul_assoc] using
      complex_word_zero hzero ![i,j,l,i] ![j,k,k,l] ![false,false,true,true]
  simp only [holonomy, Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.inv_val,
    Matrix.star_eq_conjTranspose, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro l _
      rw [integral_finset_sum]
      · apply Finset.sum_eq_zero
        intro k _
        rw [integral_finset_sum]
        · apply Finset.sum_eq_zero
          intro j _
          exact hz i j k l
        · intro j _
          apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
          exact ht i j k l
      · intro k _
        apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
        exact continuous_finset_sum _ (fun j _ => ht i j k l)
    · intro l _
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      exact continuous_finset_sum _ (fun k _ => continuous_finset_sum _ (fun j _ => ht i j k l))
  · intro i _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_finset_sum _ (fun l _ => continuous_finset_sum _ (fun k _ =>
      continuous_finset_sum _ (fun j _ => ht i j k l)))

/-- No nonzero moment is supplied as a premise: it follows from the actual
nonconstant plaquette, its Haar variance, and its degree-four entry expansion. -/
theorem fourthCoefficient_positive : 0 < fourthCoefficient := by
  have hn := coefficient_nonneg haar features centered 4
  change 0 ≤ fourthCoefficient at hn
  by_contra hp
  have hz : fourthCoefficient = 0 := le_antisymm (le_of_not_gt hp) hn
  have hc : Continuous (fun U : Links => (centered U : ℂ) *
      Matrix.trace (holonomy U : Matrix (Fin 2) (Fin 2) ℂ)) := by
    unfold holonomy Matrix.trace Matrix.diag
    fun_prop
  have hi : Integrable (fun U : Links => (centered U : ℂ) *
      Matrix.trace (holonomy U : Matrix (Fin 2) (Fin 2) ℂ)) haar :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm := (integral_re hi).trans (congrArg Complex.re (plaquette_moment_zero hz))
  change (∫ U, ((centered U : ℂ) *
    Matrix.trace (holonomy U : Matrix (Fin 2) (Fin 2) ℂ)).re ∂haar) = Complex.re 0 at hm
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.zero_re] at hm
  change (∫ U, centered U * plaquette U ∂haar) = 0 at hm
  have he (U : Links) : centered U^2 = centered U * plaquette U - centered U * center := by
    unfold centered
    ring
  have hv : (∫ U, centered U^2 ∂haar) = 0 := by
    simp_rw [he]
    have hi1 : Integrable (fun U => centered U * plaquette U) haar :=
      (centered_continuous.mul plaquette_continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hi2 : Integrable (fun U => centered U * center) haar :=
      (centered_continuous.mul continuous_const).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_sub hi1 hi2, hm, integral_mul_const, centered_mean_zero]
    ring
  exact (ne_of_gt variance_positive) hv

theorem signal_positive (β : ℝ) (hβ : 0 < β) : 0 < signal β :=
  lt_of_lt_of_le (mul_pos (div_pos (pow_pos hβ _) (by norm_num)) fourthCoefficient_positive)
    (signal_lower β hβ.le)

theorem signal_zero : signal 0 = 0 := by
  simp only [signal, kernel, zero_mul, Real.exp_zero, mul_one]
  rw [integral_prod_mul centered centered, centered_mean_zero]
  ring

theorem kernel_continuous (β : ℝ) : Continuous (fun z : Links × Links => kernel β z.1 z.2) := by
  simp only [kernel_feature, featureKernel]
  exact Real.continuous_exp.comp (continuous_const.mul
    (continuous_finset_sum _ (fun d _ =>
      ((features_continuous d).comp continuous_fst).mul
        ((features_continuous d).comp continuous_snd))))

def partition (β : ℝ) : ℝ := ∫ z : Links × Links, kernel β z.1 z.2 ∂haar.prod haar

theorem partition_positive (β : ℝ) : 0 < partition β := by
  apply integral_pos_of_integrable_nonneg_nonzero (kernel_continuous β)
    ((kernel_continuous β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun z => (Real.exp_pos _).le) (x := ((1 : Links),(1 : Links)))
  exact Real.exp_ne_zero _

theorem kernel_bound (β : ℝ) (hβ : 0 ≤ β) (U V : Links) : kernel β U V ≤ Real.exp (8*β) := by
  apply Real.exp_le_exp.mpr
  have hsum : (∑ r : Fin 4, (Matrix.trace
      (((U r)⁻¹ * V r : GaugeGroup) : Matrix (Fin 2) (Fin 2) ℂ)).re) ≤ 8 := by
    calc
      _ ≤ ∑ _ : Fin 4, (2 : ℝ) := Finset.sum_le_sum (fun r _ =>
        (Complex.re_le_norm _).trans (by
          simpa using UnitaryCharacterObservables.unitary_trace_bound ((U r)⁻¹ * V r)))
      _ = _ := by norm_num
  exact (mul_le_mul_of_nonneg_left hsum hβ).trans_eq (mul_comm _ _)

theorem partition_bound (β : ℝ) (hβ : 0 ≤ β) : partition β ≤ Real.exp (8*β) := by
  calc
    _ ≤ ∫ _ : Links × Links, Real.exp (8*β) ∂haar.prod haar :=
      integral_mono
        ((kernel_continuous β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (integrable_const _) (fun z => kernel_bound β hβ z.1 z.2)
    _ = _ := by simp

/-- Normalization is explicit. This is the normalized primitive kinetic
kernel pairing, not a full spatial-potential Wilson transfer matrix. -/
def normalizedSignal (β : ℝ) : ℝ := signal β / partition β

theorem normalizedSignal_lower (β : ℝ) (hβ : 0 ≤ β) :
    Real.exp (-8*β) * (β^4 / 24 * fourthCoefficient) ≤ normalizedSignal β := by
  have hL : 0 ≤ β^4 / 24 * fourthCoefficient :=
    mul_nonneg (by positivity) fourthCoefficient_positive.le
  calc
    _ = (β^4 / 24 * fourthCoefficient) / Real.exp (8*β) := by
      rw [show -8*β = -(8*β) by ring, Real.exp_neg]
      ring
    _ ≤ (β^4 / 24 * fourthCoefficient) / partition β :=
      div_le_div_of_nonneg_left hL (partition_positive β) (partition_bound β hβ)
    _ ≤ normalizedSignal β := div_le_div_of_nonneg_right (signal_lower β hβ)
      (partition_positive β).le

theorem normalizedSignal_positive (β : ℝ) (hβ : 0 < β) : 0 < normalizedSignal β :=
  div_pos (signal_positive β hβ) (partition_positive β)

end
end UnifiedTheory.Clay.YangMills.FourLinkWilsonTransfer
