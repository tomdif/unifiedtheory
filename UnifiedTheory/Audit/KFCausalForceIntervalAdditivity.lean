/- Actual integrated positive force measures are additive on adjacent
ordered time intervals. Shared endpoints have zero Lebesgue measure. -/
import UnifiedTheory.Audit.KFCausalNeutralIntegratedForce

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalForceIntervalAdditivity
noncomputable section
open MeasureTheory ProbabilityTheory Set
open UnifiedTheory.Audit.KFCausalFiniteKernelInterval
open UnifiedTheory.Audit.KFCausalNeutralOutputTimeKernel
open UnifiedTheory.Audit.KFCausalNeutralIntegratedForce
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

theorem integrated_add (κ : Kernel ℝ ℝ) (b c d : ℝ) (hbc : b ≤ c) (hcd : c ≤ d) :
    integrated κ b d = integrated κ b c + integrated κ c d := by
  have hi : Ioc b d = Ioc b c ∪ Ioc c d := by
    ext t
    simp only [mem_Ioc,mem_union]
    constructor
    · intro ht
      by_cases htc : t ≤ c
      · exact Or.inl ⟨ht.1,htc⟩
      · exact Or.inr ⟨lt_of_not_ge htc,ht.2⟩
    · rintro (ht | ht)
      · exact ⟨ht.1,ht.2.trans hcd⟩
      · exact ⟨hbc.trans_lt ht.1,ht.2⟩
  have hd : Disjoint (Ioc b c) (Ioc c d) := by
    apply Set.disjoint_left.mpr
    intro t ht hu
    exact (not_lt_of_ge ht.2) hu.1
  have hm : volume.restrict (Icc b d) =
      volume.restrict (Icc b c) + volume.restrict (Icc c d) := by
    simp only [← restrict_Ioc_eq_restrict_Icc]
    rw [hi,Measure.restrict_union hd measurableSet_Ioc]
  unfold integrated
  rw [hm]
  ext A hA
  simp only [Measure.add_apply,Measure.bind_apply hA κ.aemeasurable,lintegral_add_measure]

theorem integrated_self (κ : Kernel ℝ ℝ) (b : ℝ) : integrated κ b b = 0 := by
  unfold integrated
  rw [← restrict_Ioc_eq_restrict_Icc]
  simp

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h : ℝ) (w : Fin 8 → ℂ)
  (y : ℝ → Lp KFCausalNeutralTranslationOutput.Outputs 2 μ) (hy : Continuous y)

theorem intervalPair_add (b c d : ℝ) (hbc : b ≤ c) (hcd : c ≤ d) :
    (intervalPair μ h w y hy b d).positive =
      (intervalPair μ h w y hy b c).positive + (intervalPair μ h w y hy c d).positive ∧
    (intervalPair μ h w y hy b d).negative =
      (intervalPair μ h w y hy b c).negative + (intervalPair μ h w y hy c d).negative :=
  ⟨integrated_add _ b c d hbc hcd,integrated_add _ b c d hbc hcd⟩

theorem intervalPair_self (b : ℝ) :
    (intervalPair μ h w y hy b b).positive = 0 ∧
    (intervalPair μ h w y hy b b).negative = 0 :=
  ⟨integrated_self _ b,integrated_self _ b⟩

variable (ε a h₀ : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h₀ ≠ 0)
  (hh : |h₀| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)
  (r : ℝ) (hr : 0 < r)

local notation "F" => forceInterval ε a h₀ hε ha hne hh m g k s p r hr

theorem forceInterval_add (b c d : ℝ) (hbc : b ≤ c) (hcd : c ≤ d) :
    (F b d).positive = (F b c).positive + (F c d).positive ∧
    (F b d).negative = (F b c).negative + (F c d).negative :=
  intervalPair_add _ _ _ _ _ b c d hbc hcd

theorem forceInterval_self (b : ℝ) : (F b b).positive = 0 ∧ (F b b).negative = 0 :=
  intervalPair_self _ _ _ _ _ b

#print axioms integrated_add
#print axioms integrated_self
#print axioms intervalPair_add
#print axioms intervalPair_self
#print axioms forceInterval_add
#print axioms forceInterval_self
end
end UnifiedTheory.Audit.KFCausalForceIntervalAdditivity
