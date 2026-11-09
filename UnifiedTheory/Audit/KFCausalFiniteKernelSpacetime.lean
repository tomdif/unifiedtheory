/- A finite spacetime measure on each compact time window, constructed
from a measurable kernel with continuous finite mass. No global uniform
kernel bound is imposed. -/
import UnifiedTheory.Audit.KFCausalFiniteKernelInterval

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalFiniteKernelSpacetime
noncomputable section
open MeasureTheory ProbabilityTheory Set Classical BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalFiniteKernelInterval

def truncated (κ : Kernel ℝ ℝ) (b c : ℝ) : Kernel ℝ ℝ :=
  Kernel.piecewise (s := Icc b c) measurableSet_Icc κ 0

theorem truncated_eq (κ : Kernel ℝ ℝ) (b c t : ℝ) (ht : t ∈ Icc b c) :
    truncated κ b c t = κ t := by simp [truncated,Kernel.piecewise_apply,ht]

variable (κ : Kernel ℝ ℝ) [∀ t, IsFiniteMeasure (κ t)]
  (hm : Continuous (fun t => (κ t).real univ)) (b c : ℝ)

include hm in
theorem truncated_finite : IsFiniteKernel (truncated κ b c) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hm.continuousOn
  refine ⟨⟨ENNReal.ofReal C,ENNReal.ofReal_lt_top,fun t => ?_⟩⟩
  by_cases ht : t ∈ Icc b c
  · rw [truncated_eq κ b c t ht]
    calc κ t univ = ENNReal.ofReal ((κ t).real univ) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hC ⟨t,ht,rfl⟩)
  · simp [truncated,Kernel.piecewise_apply,ht]

def spacetime : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc b c)).compProd (truncated κ b c)

include hm in
theorem spacetime_finite : IsFiniteMeasure (spacetime κ b c) := by
  letI := truncated_finite κ hm b c
  unfold spacetime
  infer_instance

include hm in
theorem spacetime_rectangle (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    spacetime κ b c (A ×ˢ B) = ∫⁻ t in A, κ t B ∂volume.restrict (Icc b c) := by
  letI := truncated_finite κ hm b c
  rw [spacetime,Measure.compProd_apply_prod hA hB]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (ae_restrict_mem measurableSet_Icc)] with t ht
  rw [truncated_eq κ b c t ht]

include hm in
theorem spacetime_mass : spacetime κ b c univ = integrated κ b c univ := by
  rw [← univ_prod_univ,spacetime_rectangle κ hm b c univ univ .univ .univ]
  simp only [Measure.restrict_univ]
  exact (Measure.bind_apply MeasurableSet.univ κ.aemeasurable).symm

include hm in
theorem spacetime_test (q : (ℝ × ℝ) →ᵇ ℂ) :
    (∫ z, q z ∂spacetime κ b c) = ∫ t in Icc b c, ∫ p, q (t,p) ∂κ t := by
  letI := truncated_finite κ hm b c
  letI := spacetime_finite κ hm b c
  rw [spacetime,Measure.integral_compProd (q.integrable _)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [truncated_eq κ b c t ht]

include hm in
theorem spacetime_slice (u v : ℝ) (hu : b ≤ u) (hv : v ≤ c) :
    ((spacetime κ b c).restrict (Icc u v ×ˢ univ)).map Prod.snd = integrated κ u v := by
  ext A hA
  rw [Measure.map_apply measurable_snd hA,Measure.restrict_apply (hA.preimage measurable_snd)]
  have hi : Prod.snd ⁻¹' A ∩ (Icc u v ×ˢ (univ : Set ℝ)) = Icc u v ×ˢ A := by
    ext z
    simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,and_true]
    exact and_comm
  rw [hi,spacetime_rectangle κ hm b c (Icc u v) A measurableSet_Icc hA,
    Measure.restrict_restrict measurableSet_Icc]
  have hs : Icc u v ∩ Icc b c = Icc u v :=
    inter_eq_left.mpr (Icc_subset_Icc hu hv)
  rw [hs]
  exact (Measure.bind_apply hA κ.aemeasurable).symm

include hm in
theorem spacetime_time_bound (C : ℝ)
    (hb : ∀ t ∈ Icc b c, (κ t).real univ ≤ C)
    (A : Set ℝ) (hA : MeasurableSet A) :
    spacetime κ b c (A ×ˢ univ) ≤ ENNReal.ofReal C * volume (A ∩ Icc b c) := by
  rw [spacetime_rectangle κ hm b c A univ hA .univ]
  calc
    _ ≤ ∫⁻ _t in A, ENNReal.ofReal C ∂volume.restrict (Icc b c) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae (ae_restrict_mem measurableSet_Icc)] with t ht
      calc κ t univ = ENNReal.ofReal ((κ t).real univ) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hb t ht)
    _ = _ := by simp [Measure.restrict_apply,hA]

include hm in
theorem spacetime_time_sum_bound (η : Kernel ℝ ℝ) [∀ t, IsFiniteMeasure (η t)]
    (hn : Continuous (fun t => (η t).real univ)) (C : ℝ)
    (hb : ∀ t ∈ Icc b c, (κ t).real univ+(η t).real univ ≤ C)
    (A : Set ℝ) (hA : MeasurableSet A) :
    spacetime κ b c (A ×ˢ univ)+spacetime η b c (A ×ˢ univ) ≤
      ENNReal.ofReal C * volume (A ∩ Icc b c) := by
  rw [spacetime_rectangle κ hm b c A univ hA .univ,
    spacetime_rectangle η hn b c A univ hA .univ,
    ← lintegral_add_left (κ.measurable_coe MeasurableSet.univ)]
  calc
    _ ≤ ∫⁻ _t in A, ENNReal.ofReal C ∂volume.restrict (Icc b c) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae (ae_restrict_mem measurableSet_Icc)] with t ht
      calc
        κ t univ+η t univ = ENNReal.ofReal ((κ t).real univ+(η t).real univ) := by
          rw [ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg]
          simp only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hb t ht)
    _ = _ := by simp [Measure.restrict_apply,hA]

#print axioms truncated_finite
#print axioms spacetime_finite
#print axioms spacetime_rectangle
#print axioms spacetime_mass
#print axioms spacetime_test
#print axioms spacetime_slice
#print axioms spacetime_time_bound
#print axioms spacetime_time_sum_bound
end
end UnifiedTheory.Audit.KFCausalFiniteKernelSpacetime
