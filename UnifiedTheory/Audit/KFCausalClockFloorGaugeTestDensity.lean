/- The finite-energy tests with an actual chart-coordinate output are
total in the physical Hilbert space. Explicit coherent states supply the
dense family, so the transformed weak equation has separating tests. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaugeDerivative
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
import UnifiedTheory.Audit.KFCausalClockFloorAveragedDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaugeTestDensity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorGaugeDerivative (chartOperator)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chart_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan coherentSpan_dense hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (state_configuration_coe)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative (physicalProfile physicalProfile_memLp clockMultiplier)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentClockMomentum (sourceProfile_eq)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry

theorem gaussian_chart_absorption (x : ℝ) : |x| * Real.exp (-x^2) ≤ Real.exp (-(1/2:ℝ)*x^2) := by
  have hb : |x| ≤ Real.exp (x^2/2) := by
    nlinarith [Real.add_one_le_exp (x^2/2),sq_nonneg (|x|-1),sq_abs x]
  have he : Real.exp (x^2/2)*Real.exp (-x^2) = Real.exp (-(1/2:ℝ)*x^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  exact (mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le).trans_eq he

theorem chart_clock_memLp (ε : ℝ) (hε : 0 < ε) :
    MemLp (fun s => (chart ε s:ℂ)*clockFunction ε 1 s) 2 volume := by
  have hc : Continuous (fun s => (chart ε s:ℂ)*clockFunction ε 1 s) :=
    (Complex.continuous_ofReal.comp (chart_continuous ε)).mul (clockFunction_continuous ε 1)
  apply (clockFunction_memLp ε (1/2) hε (by norm_num)).of_le hc.aestronglyMeasurable
  filter_upwards [] with s
  simp only [norm_mul,clockFunction,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (realClock_positive ε 1 s hε.le),abs_of_pos (realClock_positive ε (1/2) s hε.le)]
  unfold realClock
  simpa only [neg_mul,one_mul,mul_left_comm] using
    mul_le_mul_of_nonneg_left (gaussian_chart_absorption (chart ε s))
      (by positivity : 0 ≤ 1+ε*Real.exp (-s))

theorem state_chart_domain (ε h : ℝ) (hε : 0 < ε) (hne : h ≠ 0) (p : Joint 2 4) :
    state ε 1 h hε zero_lt_one hne p ∈ (chartOperator ε).domain := by
  apply (KFCausalUnitaryRealMultiplier.realPullback_domain (LinearIsometryEquiv.refl ℂ Hilbert) _ _ _).mpr
  have hm := physicalProfile_memLp (amplitudeConstant h p) (clockFrequency p)
    (groundWidth h) (neutralWidth h) (groundWidth_positive h hne)
    (neutralWidth_positive h hne) (neutralWidth_bound h) (sourceCoefficients h p)
    (fun s => (chart ε s:ℂ)*clockFunction ε 1 s) (chart_clock_memLp ε hε)
  apply hm.ae_eq
  filter_upwards [state_configuration_coe ε 1 h hε zero_lt_one hne p] with x hx
  change _ = (chart ε x.1:ℂ)*state ε 1 h hε zero_lt_one hne p x
  rw [hx,sourceProfile_eq]
  simp only [physicalProfile,clockMultiplier,amplitudeConstant,clockFrequency,sourceCoefficients]
  ring

theorem coherentSpan_le_chart_domain (ε h : ℝ) (hε : 0 < ε) (hne : h ≠ 0) :
    coherentSpan ε 1 h hε zero_lt_one hne ≤ (chartOperator ε).domain := by
  apply Submodule.span_le.mpr
  rintro f ⟨p,rfl⟩
  exact state_chart_domain ε h hε hne p

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m q k : ℝ)

def testDomain : Submodule ℂ Hilbert :=
  (KFCausalClockFloorAveragedEnergy.energyOperator ε hε h (hamiltonian_bound ε h hh) hne m q k 0).domain ⊓
    (chartOperator ε).domain

theorem testDomain_dense : Dense (testDomain ε hε h hne hh m q k : Set Hilbert) := by
  have hd : Dense (coherentSpan ε 1 h hε zero_lt_one hne : Set Hilbert) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (coherentSpan_dense ε 1 h hε zero_lt_one hne)
  apply hd.mono
  intro f hf
  exact ⟨KFCausalClockFloorAveragedDensity.coherentSpan_le_energy_domain
    ε 1 h hε zero_lt_one hne hh m q k 0 hf,coherentSpan_le_chart_domain ε h hε hne hf⟩

theorem physical_test_dense : Dense {f : Hilbert |
    ∃ v : KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hne hh m q k 0,
      ∃ g : Hilbert, KFCausalClockFloorAveragedFormTransport.embedding ε hε h hne hh m q k 0 v = f ∧
        (f,g) ∈ (chartOperator ε).graph} := by
  apply (testDomain_dense ε hε h hne hh m q k).mono
  intro f hf
  obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf.2
  exact ⟨KFCausalClosedGraphForm.graphVector
    (KFCausalClockFloorAveragedHamiltonian.formData ε hε h hne hh m q k 0) ⟨f,hf.1⟩,g,rfl,hg⟩

#print axioms gaussian_chart_absorption
#print axioms chart_clock_memLp
#print axioms state_chart_domain
#print axioms coherentSpan_le_chart_domain
#print axioms testDomain_dense
#print axioms physical_test_dense
end
end UnifiedTheory.Audit.KFCausalClockFloorGaugeTestDensity
