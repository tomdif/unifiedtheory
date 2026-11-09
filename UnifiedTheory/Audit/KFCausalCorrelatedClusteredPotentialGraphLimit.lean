/- Actual physical Hilbert limits of the three ordered potential
outputs. Closed field and field-square graphs survive confluence.
This does not assert convergence of the input state or kinetic/Hamiltonian
graphs, nor a relative estimate uniform over all finite families. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalCauchy
import UnifiedTheory.Audit.KFCausalSquaredErrorCompleteness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialGraphLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredPhysicalCauchy
open KFCausalCorrelatedClusteredPhysicalClockLimit (amplitudes amplitudes_continuous amplitudes_memLp shift_bound lift)
open KFCausalCorrelatedClusteredL2Error (errorMass errorMass_tendsto)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalPhysicalField (physicalField physicalField_closed)
open KFCausalTransverseFieldSquare (fieldSquare fieldSquare_selfAdjoint)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalOrderedOperatorComposition (composition_graph)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (ha : ∀ i, 0 < a i)
local notation "U" => finiteOutput f ε h a p hε hh hb ha

theorem output_exists_limit (k : Fin 3) :
    ∃ v : Hilbert, Tendsto (fun δ => U δ (potentialIndex k)) (𝓝[>] 0) (𝓝 v) := by
  have hy := shift_bound ε h hb
  have hg := errorMass_tendsto f (amplitudes ε (-h/2) a p) (groundWidth h) (neutralWidth h) ε (-h/2)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy
    (amplitudes_continuous ε (-h/2) a p hε hy) (amplitudes_memLp ε (-h/2) a p hε hy ha)
  apply KFCausalSquaredErrorCompleteness.exists_limit (fun δ => U δ (potentialIndex k))
    (fun δ => 8*errorMass f (amplitudes ε (-h/2) a p) (groundWidth h) (neutralWidth h) ε (-h/2) δ)
  · simpa only [mul_zero] using hg.const_mul 8
  · intro δ η hδ hη
    simpa only [mul_add] using output_distance_bound f ε h a p hε hh hb ha δ η hδ hη k

def limitingOutput (k : Fin 3) : Hilbert := Classical.choose (output_exists_limit f ε h a p hε hh hb ha k)

theorem output_tendsto (k : Fin 3) :
    Tendsto (fun δ => U δ (potentialIndex k)) (𝓝[>] 0) (𝓝 (limitingOutput f ε h a p hε hh hb ha k)) :=
  Classical.choose_spec (output_exists_limit f ε h a p hε hh hb ha k)

theorem finite_field_graph (δ : ℝ) (hδ : 0 < δ) : (U δ 7,U δ 5) ∈ (physicalField pointField).graph := by
  have hg (j : Fin 8) := KFCausalReciprocalNeutralSuperposition.output_graph (count f) ε h
    (lift f a) (widths f δ) (lift f p) (coefficients f δ) (sources f) (polynomials f)
    hε (fun i => ha (index f i).1) hh (widths_admissible f δ hδ.le) hb j
  obtain ⟨Y,hY,hL⟩ := (composition_graph _ _ _ _).mp (hg 5)
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hY (hg 7) rfl
  dsimp only at he
  simpa only [finiteOutput,dif_pos hδ] using he ▸ hL

theorem finite_square_graph (δ : ℝ) (hδ : 0 < δ) : (U δ 7,U δ 6) ∈ (fieldSquare pointField).graph := by
  have hg (j : Fin 8) := KFCausalReciprocalNeutralSuperposition.output_graph (count f) ε h
    (lift f a) (widths f δ) (lift f p) (coefficients f δ) (sources f) (polynomials f)
    hε (fun i => ha (index f i).1) hh (widths_admissible f δ hδ.le) hb j
  obtain ⟨Y,hY,hQ⟩ := (composition_graph _ _ _ _).mp (hg 6)
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hY (hg 7) rfl
  dsimp only at he
  simpa only [finiteOutput,dif_pos hδ] using he ▸ hQ

local notation "V" => limitingOutput f ε h a p hε hh hb ha

theorem limit_field_graph : (V 0,V 1) ∈ (physicalField pointField).graph := by
  have h0 : Tendsto (fun δ => U δ 7) (𝓝[>] 0) (𝓝 (V 0)) := output_tendsto f ε h a p hε hh hb ha 0
  have h1 : Tendsto (fun δ => U δ 5) (𝓝[>] 0) (𝓝 (V 1)) := output_tendsto f ε h a p hε hh hb ha 1
  apply (physicalField_closed pointField).mem_of_tendsto (h0.prodMk_nhds h1)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_field_graph f ε h a p hε hh hb ha δ hδ

theorem limit_square_graph : (V 0,V 2) ∈ (fieldSquare pointField).graph := by
  have h0 : Tendsto (fun δ => U δ 7) (𝓝[>] 0) (𝓝 (V 0)) := output_tendsto f ε h a p hε hh hb ha 0
  have h2 : Tendsto (fun δ => U δ 6) (𝓝[>] 0) (𝓝 (V 2)) := output_tendsto f ε h a p hε hh hb ha 2
  apply (fieldSquare_selfAdjoint pointField).isClosed.mem_of_tendsto (h0.prodMk_nhds h2)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_square_graph f ε h a p hε hh hb ha δ hδ

theorem limit_domains : V 0 ∈ (physicalField pointField).domain ∧ V 0 ∈ (fieldSquare pointField).domain :=
  ⟨LinearPMap.mem_domain_of_mem_graph (limit_field_graph f ε h a p hε hh hb ha),
   LinearPMap.mem_domain_of_mem_graph (limit_square_graph f ε h a p hε hh hb ha)⟩

theorem limiting_energy_identity :
    KFCausalCorrelatedClusteredPhysicalClockLimit.limitingEnergy f ε h a p = ‖V 0‖^2+‖V 1‖^2/2+‖V 2‖^2/4 := by
  have hk (k : Fin 3) := (output_tendsto f ε h a p hε hh hb ha k).norm.pow 2
  have hn := ((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4)
  have he : Tendsto (KFCausalCorrelatedClusteredPhysicalClockLimit.finiteEnergy f ε h a p hε hh hb ha)
      (𝓝[>] 0) (𝓝 (‖V 0‖^2+‖V 1‖^2/2+‖V 2‖^2/4)) := by
    apply Tendsto.congr' _ hn
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0 < δ at hδ
    simp only [KFCausalCorrelatedClusteredPhysicalClockLimit.finiteEnergy,finiteOutput,dif_pos hδ,
      KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy]
    rfl
  exact tendsto_nhds_unique (KFCausalCorrelatedClusteredPhysicalClockLimit.potentialEnergy_tendsto
    f ε h a p hε hh hb ha) he

#print axioms output_exists_limit
#print axioms output_tendsto
#print axioms finite_field_graph
#print axioms finite_square_graph
#print axioms limit_field_graph
#print axioms limit_square_graph
#print axioms limit_domains
#print axioms limiting_energy_identity
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialGraphLimit
