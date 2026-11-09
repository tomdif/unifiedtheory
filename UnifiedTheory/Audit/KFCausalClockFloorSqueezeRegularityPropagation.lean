/- Actual propagation of integrated squeeze-orbit regularity. The
initial class is constructed and dense. The exponent-one endpoint and
full generator-domain propagation are not consequences of this bound. -/
import UnifiedTheory.Audit.KFCausalSqueezeOrbitRegularity
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeTestDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSqueezeRegularityPropagation
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator (squeezeMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeOrbitEstimate
open UnifiedTheory.Audit.KFCausalSqueezeOrbitRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution evolution_embedding)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow_initial)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyBalance (energy)
open UnifiedTheory.Audit.KFCausalClockFloorCombinedDynamics (transformedState)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "U" => evolution ε hε h hne hh m g k
local notation "E" => energy ε hε h hne hh m g k

theorem integrated_regularity_propagation (p : ℝ) (hp : p < 1) (s r t : ℝ)
    (hrt : r ≤ t) (w : V) (hf : IntegrableOn (density p (U s r (J w))) (Ioo (0:ℝ) 1)) :
    IntegrableOn (density p (U s t (J w))) (Ioo (0:ℝ) 1) ∧
      regularity p (U s t (J w)) ≤ regularity p (U s r (J w))+budget h (t-r) (E s r w)/(1-p) := by
  have hb (a : ℝ) (ha : a ∈ Ioo (0:ℝ) 1) :
      orbitGap a (U s t (J w)) ≤ orbitGap a (U s r (J w))+budget h (t-r) (E s r w)*a := by
    have hab : |a| ≤ 1 := by rw [abs_of_pos ha.1]; exact ha.2.le
    simpa only [abs_of_pos ha.1] using orbitGap_propagation ε hε h hne hh m g k a s r t hab hrt w
  exact ⟨integrable_of_gap_comparison p hp _ _ _ hf hb,regularity_comparison p hp _ _ _ hf hb⟩

theorem generator_initial_gap (a s t : ℝ) (ha : |a| ≤ 1) (hst : s ≤ t) (w : V) (z : Hilbert)
    (hw : (J w,z) ∈ (squeezeMomentum h).graph) :
    orbitGap a (U s t (J w)) ≤ (‖z‖/|h|)^2*a^2+budget h (t-s) (E s s w)*|a| := by
  have hi : U s s (J w) = J w := by rw [evolution_embedding,formFlow_initial]
  have hb : orbitGap a (U s s (J w)) ≤ (‖z‖/|h|)^2*a^2 := by
    simpa only [hi] using generator_gap_bound h hne (J w) z hw a
  exact (orbitGap_propagation ε hε h hne hh m g k a s s t ha hst w).trans
    (add_le_add hb le_rfl)

theorem generator_initial_regularity (p : ℝ) (hp : p < 1) (s t : ℝ) (hst : s ≤ t)
    (w : V) (z : Hilbert) (hw : (J w,z) ∈ (squeezeMomentum h).graph) :
    IntegrableOn (density p (U s t (J w))) (Ioo (0:ℝ) 1) ∧
      regularity p (U s t (J w)) ≤ ((‖z‖/|h|)^2+budget h (t-s) (E s s w))/(1-p) := by
  have hb (a : ℝ) (ha : a ∈ Ioo (0:ℝ) 1) :
      orbitGap a (U s t (J w)) ≤ ((‖z‖/|h|)^2+budget h (t-s) (E s s w))*a := by
    have hab : |a| ≤ 1 := by rw [abs_of_pos ha.1]; exact ha.2.le
    have he := generator_initial_gap ε hε h hne hh m g k a s t hab hst w z hw
    rw [abs_of_pos ha.1] at he
    have hs : (‖z‖/|h|)^2*a^2 ≤ (‖z‖/|h|)^2*a :=
      mul_le_mul_of_nonneg_left (by nlinarith [ha.1,ha.2] : a^2 ≤ a) (sq_nonneg _)
    nlinarith only [he,hs]
  exact ⟨density_integrable p hp _ _ hb,regularity_bound p hp _ _ hb⟩

theorem regular_initial_dense : Dense {f : Hilbert | ∃ w : V, J w = f ∧
    ∀ p : ℝ, p < 1 → IntegrableOn (density p f) (Ioo (0:ℝ) 1)} := by
  apply (KFCausalClockFloorSqueezeTestDensity.physical_test_dense ε hε h hne hh m g k 0).mono
  rintro f ⟨w,z,hw,hz⟩
  refine ⟨w,hw,fun p hp => density_integrable p hp ((‖z‖/|h|)^2) f ?_⟩
  intro a ha
  have hab : |a| ≤ 1 := by rw [abs_of_pos ha.1]; exact ha.2.le
  simpa only [abs_of_pos ha.1] using generator_small_gap h hne f z hz a hab

theorem combined_regularity_propagation (p : ℝ) (hp : p < 1) (v s r t : ℝ)
    (hrt : r ≤ t) (w : V)
    (hf : IntegrableOn (density p (transformedState ε hε h hne hh m g k v s r (J w))) (Ioo (0:ℝ) 1)) :
    IntegrableOn (density p (transformedState ε hε h hne hh m g k v s t (J w))) (Ioo (0:ℝ) 1) ∧
      regularity p (transformedState ε hε h hne hh m g k v s t (J w)) ≤
        regularity p (transformedState ε hε h hne hh m g k v s r (J w))+
          budget h (t-r) (E s r w)/(1-p) := by
  have hf' : IntegrableOn (density p (U s r (J w))) (Ioo (0:ℝ) 1) := by
    simpa only [transformedState,density_combined] using hf
  simpa only [transformedState,density_combined,regularity_combined] using
    integrated_regularity_propagation ε hε h hne hh m g k p hp s r t hrt w hf'

theorem integrability_iff (p : ℝ) (hp : p < 1) (s r t : ℝ) (hrt : r ≤ t) (w : V) :
    IntegrableOn (density p (U s r (J w))) (Ioo (0:ℝ) 1) ↔
      IntegrableOn (density p (U s t (J w))) (Ioo (0:ℝ) 1) := by
  constructor
  · intro hf
    exact (integrated_regularity_propagation ε hε h hne hh m g k p hp s r t hrt w hf).1
  · intro hf
    apply integrable_of_gap_comparison p hp (budget h (t-r) (E s r w)) _ _ hf
    intro a ha
    have hab : |a| ≤ 1 := by rw [abs_of_pos ha.1]; exact ha.2.le
    have hb := (abs_le.mp (orbitGap_increment_bound ε hε h hne hh m g k a s r t hab hrt w)).1
    rw [abs_of_pos ha.1] at hb
    linarith only [hb]

theorem regularity_increment_bound (p : ℝ) (hp : p < 1) (s r t : ℝ) (hrt : r ≤ t)
    (w : V) (hf : IntegrableOn (density p (U s r (J w))) (Ioo (0:ℝ) 1)) :
    |regularity p (U s t (J w))-regularity p (U s r (J w))| ≤ budget h (t-r) (E s r w)/(1-p) := by
  obtain ⟨ht,hu⟩ := integrated_regularity_propagation ε hε h hne hh m g k p hp s r t hrt w hf
  have hb (a : ℝ) (ha : a ∈ Ioo (0:ℝ) 1) :
      orbitGap a (U s r (J w)) ≤ orbitGap a (U s t (J w))+budget h (t-r) (E s r w)*a := by
    have hab : |a| ≤ 1 := by rw [abs_of_pos ha.1]; exact ha.2.le
    have he := (abs_le.mp (orbitGap_increment_bound ε hε h hne hh m g k a s r t hab hrt w)).1
    rw [abs_of_pos ha.1] at he
    linarith only [he]
  have hl := regularity_comparison p hp _ _ _ ht hb
  apply abs_le.mpr
  constructor <;> linarith only [hl,hu]

#print axioms integrated_regularity_propagation
#print axioms generator_initial_gap
#print axioms generator_initial_regularity
#print axioms regular_initial_dense
#print axioms combined_regularity_propagation
#print axioms integrability_iff
#print axioms regularity_increment_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorSqueezeRegularityPropagation
