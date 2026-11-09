/- Exact extraction of canonical momentum from its charge-orbit graph,
and sufficient tail/tightness estimates from actual operator outputs.
These results do not supply the missing estimates along full evolution. -/
import UnifiedTheory.Audit.KFCausalCanonicalClockTails
import UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction
import Mathlib.MeasureTheory.Measure.Tight

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalCanonicalClockControl
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action action_reverse group)
open UnifiedTheory.Audit.KFCausalCanonicalClockChargeGraph (graph_charge graph_output_norm)
open UnifiedTheory.Audit.KFCausalCanonicalClockProbability (law)
open UnifiedTheory.Audit.KFCausalCanonicalClockTails (tail graph_tail_bound law_outside_bound)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure orbitState orbitState_coe)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction

theorem averaged_graph_norm (h : ℝ) (hh : h ≠ 0) (f : Hilbert)
    (q : Lp Hilbert 2 angleMeasure)
    (hq : ∀ᵐ θ ∂angleMeasure, (action h hh (2*Real.pi*θ) f,q θ) ∈ (clockMomentum h).graph) :
    ∃ g : Hilbert, (f,g) ∈ (clockMomentum h).graph ∧ ‖g‖^2 = ‖q‖^2 := by
  obtain ⟨θ,hθ⟩ := hq.exists
  let g := action h hh (-(2*Real.pi*θ)) (q θ)
  have hg : (f,g) ∈ (clockMomentum h).graph := by
    simpa only [action_reverse] using graph_charge h hh (-(2*Real.pi*θ)) _ _ hθ
  refine ⟨g,hg,?_⟩
  rw [l2_norm_square angleMeasure q]
  have he : (fun θ => ‖q θ‖^2) =ᵐ[angleMeasure] fun _ => ‖g‖^2 := by
    filter_upwards [hq] with φ hφ
    rw [graph_output_norm h hh (2*Real.pi*φ) f g (q φ) hg hφ]
  rw [integral_congr_ae he]
  simp

theorem domain_iff_orbit_graph (h : ℝ) (hh : h ≠ 0) (f : Hilbert) :
    f ∈ (clockMomentum h).domain ↔ ∃ q : Lp Hilbert 2 angleMeasure,
      ∀ᵐ θ ∂angleMeasure, (action h hh (2*Real.pi*θ) f,q θ) ∈ (clockMomentum h).graph := by
  constructor
  · intro hf
    obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
    refine ⟨orbitState (group h hh) (2*Real.pi) g,?_⟩
    filter_upwards [orbitState_coe (group h hh) (2*Real.pi) g] with θ hθ
    rw [hθ]
    exact graph_charge h hh (2*Real.pi*θ) f g hg
  · rintro ⟨q,hq⟩
    obtain ⟨g,hg,_⟩ := averaged_graph_norm h hh f q hq
    exact LinearPMap.mem_domain_of_mem_graph hg

theorem averaged_graph_tail_bound (h : ℝ) (hh : h ≠ 0) (R : ℝ) (f : Hilbert)
    (q : Lp Hilbert 2 angleMeasure)
    (hq : ∀ᵐ θ ∂angleMeasure, (action h hh (2*Real.pi*θ) f,q θ) ∈ (clockMomentum h).graph) :
    R^2*tail h R f ≤ ‖q‖^2 := by
  obtain ⟨g,hg,he⟩ := averaged_graph_norm h hh f q hq
  exact (graph_tail_bound h hh R f g hg).trans_eq he

theorem reconstruction_tail_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (R : ℝ)
    (f : Configuration → ℂ) (hf : MemLp f 2 (volume : Measure Configuration))
    (hw : MemLp (weightedDifferential ε f) 2 (volume : Measure Configuration))
    (hs : MemLp (shearDerivative f) 2 (volume : Measure Configuration)) (hd : Differentiable ℝ f) :
    R^2*tail h R (hf.toLp f) ≤
      (‖(-Complex.I*(h:ℂ)) • hw.toLp (weightedDifferential ε f)‖+
        ‖(-Complex.I*(h:ℂ)) • hs.toLp (shearDerivative f)‖+|h|/2*‖hf.toLp f‖)^2 := by
  have hg := clock_graph_controls ε hε h hh f hf hw hs hd
  exact (graph_tail_bound h hh R _ _ hg).trans
    (pow_le_pow_left₀ (norm_nonneg _) (canonical_norm_bound ε hε h hh f hf hw hs hd _ hg) 2)

theorem bounded_graph_family_tight {I : Type*} (h : I → ℝ) (hh : ∀ i, h i ≠ 0)
    (f g : I → Hilbert) (hg : ∀ i, (f i,g i) ∈ (clockMomentum (h i)).graph)
    (B : ℝ) (hB : ∀ i, ‖g i‖^2 ≤ B) :
    IsTightMeasureSet (Set.range (fun i => law (h i) (f i))) := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro η hη
  by_cases htop : η = ⊤
  · subst η
    exact ⟨∅,isCompact_empty,fun _ _ => le_top⟩
  have hp : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
  obtain ⟨R,hR⟩ := exists_gt (max (1:ℝ) (B/η.toReal))
  have hR1 : 1 < R := (le_max_left _ _).trans_lt hR
  have hR0 : 0 < R := by linarith
  have hBR : B < R*η.toReal :=
    (div_lt_iff₀ hp).mp ((le_max_right _ _).trans_lt hR)
  refine ⟨Set.Icc (-R) R,isCompact_Icc,?_⟩
  rintro μ ⟨i,rfl⟩
  apply (law_outside_bound (h i) (hh i) R hR0 (f i) (g i) (hg i)).trans
  rw [← ENNReal.ofReal_toReal htop]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
  have hs : R ≤ R^2 := by nlinarith
  simpa only [mul_comm] using (hB i).trans (hBR.le.trans (mul_le_mul_of_nonneg_right hs hp.le))

#print axioms averaged_graph_norm
#print axioms domain_iff_orbit_graph
#print axioms averaged_graph_tail_bound
#print axioms reconstruction_tail_bound
#print axioms bounded_graph_family_tight

end
end UnifiedTheory.Audit.KFCausalCanonicalClockControl
