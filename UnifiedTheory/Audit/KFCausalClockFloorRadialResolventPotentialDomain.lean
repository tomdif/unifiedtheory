/- Orbit-factor graph transport, shifted adjoint pairing on completed
potential outputs, and operator-level domain invariance and strong convergence
for the potential Hamiltonian under the radial resolvent regularizer. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventShiftedOrderedTransport
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotentialForm

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotentialDomain
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorOrbitVacuumGraph (OrbitSpace physicalOrbit)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open KFCausalClockFloorOrbitFactorGraphs (factorOperator growingWeight)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorMatterClosure (energyFactor_closable)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorRadialResolventRegularizer (action sequence_tendsto)
open KFCausalClockFloorRadialResolventShifted (shifted_sequence_tendsto)
open KFCausalClockFloorRadialResolventSections (outputAction outputActionLp)
open KFCausalClockFloorRadialYosidaOrderedTransport (shift_bound)
open KFCausalClockFloorRadialResolventPotential (formAction formAction_embedding formAction_output)
open KFCausalClockFloorRadialResolventShiftedPairing (neg_shift_bound half_shift_bound
  shiftedMultiplier_pairing shiftedResolvent_pairing)
open KFCausalClockFloorRadialResolventShiftedOrderedTransport
  (shiftedMultiplier shiftedResolvent narrow_half_shift_bound
    ordered_graph_shiftedResolvent linear_matter_graph_shiftedResolvent
    quadratic_matter_graph_shiftedResolvent)
open KFCausalClockFloorChartPhasePairing (orderedOutput orderedOutputLp)

private theorem submodule_closure_transport {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (S : Submodule ℂ X) (T : Submodule ℂ Y)
    (L : X →L[ℂ] Y) (hT : IsClosed (T : Set Y))
    (hS : ∀ z ∈ S, L z ∈ T) (z : X) (hz : z ∈ S.topologicalClosure) :
    L z ∈ T := by
  have hs : S ≤ T.comap L.toLinearMap := hS
  exact S.topologicalClosure_minimal hs (hT.preimage L.continuous) hz

private theorem closure_graph_transport (E : Hilbert →ₗ.[ℂ] Hilbert) (hE : E.IsClosable)
    (S₀ S₁ : Hilbert →L[ℂ] Hilbert)
    (hS : ∀ f g, (f, g) ∈ E.graph → (S₀ f, S₁ g) ∈ E.graph)
    (f g : Hilbert) (hfg : (f, g) ∈ E.closure.graph) :
    (S₀ f, S₁ g) ∈ E.closure.graph := by
  let P := S₀.prodMap S₁
  have hsub : E.graph ≤ E.closure.graph.comap P.toLinearMap := by
    rintro ⟨u, v⟩ huv
    exact LinearPMap.le_graph_of_le E.le_closure (hS u v huv)
  have hc : IsClosed (E.closure.graph.comap P.toLinearMap : Set (Hilbert × Hilbert)) :=
    hE.closure_isClosed.preimage P.continuous
  rw [← hE.graph_closure_eq_closure_graph] at hfg
  exact E.graph.topologicalClosure_minimal hsub hc hfg

private theorem lp_operator_graph_transport (E : Hilbert →ₗ.[ℂ] Hilbert)
    (S₀ S₁ : Hilbert →L[ℂ] Hilbert)
    (hS : ∀ f g, (f, g) ∈ E.graph → (S₀ f, S₁ g) ∈ E.graph)
    (φ ψ : OrbitSpace) (hφψ : (φ, ψ) ∈ (KFCausalLpClosedOperator.operator angleMeasure E).graph) :
    (S₀.compLpL 2 angleMeasure φ, S₁.compLpL 2 angleMeasure ψ) ∈
      (KFCausalLpClosedOperator.operator angleMeasure E).graph := by
  rw [KFCausalLpClosedOperator.operator_graph] at hφψ ⊢
  filter_upwards [hφψ, S₀.coeFn_compLp φ, S₁.coeFn_compLp ψ] with θ hθ h0 h1
  change (S₀.compLp φ θ, S₁.compLp ψ θ) ∈ E.graph
  rw [h0, h1]
  exact hS (φ θ) (ψ θ) hθ

private theorem coordinate_ordered (i : Fin 8) (y : EnergyOutputSpace) :
    coordinateLp i (orderedOutputLp y) = if i.val < 5 then 0 else coordinateLp i y := by
  apply Lp.ext
  filter_upwards [(coordinate i).coeFn_compLp (orderedOutputLp y),
    orderedOutput.coeFn_compLp y, (coordinate i).coeFn_compLp y,
    Lp.coeFn_zero (E := Hilbert) (p := 2) (μ := angleMeasure)] with θ h1 h2 h3 h0
  change (coordinate i).compLp (orderedOutputLp y) θ = _
  rw [h1]
  change orderedOutput.compLp y θ i = _
  rw [h2]
  by_cases hi : i.val < 5
  · simp only [orderedOutput, KFCausalFiniteOutputRescaling.selected_apply, hi,
      not_true_eq_false, if_false, if_true, h0, Pi.zero_apply]
  · simpa only [orderedOutput, KFCausalFiniteOutputRescaling.selected_apply, hi,
      not_false_eq_true, if_true, if_false] using h3.symm

theorem ordered_energyFactor_shiftedResolvent (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₀ y₁ : ℝ) (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (hy₀₁ : y₁ = y₀ - h / 2) (i : Fin 8) (hi : ¬ i.val < 5)
    (f g : Hilbert) (hfg : (f, g) ∈ (energyFactor ε hε h modelDirections pointField i).graph) :
    (shiftedResolvent ε hε h N hN y₀ hy₀ f,
      shiftedResolvent ε hε h N hN y₁ hy₁ g) ∈
      (energyFactor ε hε h modelDirections pointField i).graph := by
  fin_cases i
  · exact False.elim (hi (by decide))
  · exact False.elim (hi (by decide))
  · exact False.elim (hi (by decide))
  · exact False.elim (hi (by decide))
  · exact False.elim (hi (by decide))
  · exact linear_matter_graph_shiftedResolvent ε hε h N hN y₀ y₁ hy₀ hy₁ hy₀₁ f g hfg
  · exact quadratic_matter_graph_shiftedResolvent ε hε h N hN y₀ y₁ hy₀ hy₁ hy₀₁ f g hfg
  · exact ordered_graph_shiftedResolvent ε hε h N hN y₀ y₁ hy₀ hy₁ hy₀₁ f g hfg

theorem ordered_factorOperator_shiftedResolvent (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hb : |h| ≤ Real.pi * ε / 3) (y₀ y₁ : ℝ)
    (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (hy₀₁ : y₁ = y₀ - h / 2) (i : Fin 8) (hi : ¬ i.val < 5)
    (φ ψ : OrbitSpace) (hφψ : (φ, ψ) ∈ (factorOperator ε hε h i).graph) :
    ((shiftedResolvent ε hε h N hN y₀ hy₀).compLpL 2 angleMeasure φ,
      (shiftedResolvent ε hε h N hN y₁ hy₁).compLpL 2 angleMeasure ψ) ∈
      (factorOperator ε hε h i).graph := by
  have hpi : |h| ≤ Real.pi * ε := hamiltonian_bound ε h (wide_bound ε hε h hb)
  exact lp_operator_graph_transport
    (energyFactor ε hε h modelDirections pointField i).closure
    (shiftedResolvent ε hε h N hN y₀ hy₀)
    (shiftedResolvent ε hε h N hN y₁ hy₁)
    (closure_graph_transport (energyFactor ε hε h modelDirections pointField i)
      (energyFactor_closable ε h hε hpi modelDirections pointField i)
      (shiftedResolvent ε hε h N hN y₀ hy₀)
      (shiftedResolvent ε hε h N hN y₁ hy₁)
      (ordered_energyFactor_shiftedResolvent ε hε h N hN y₀ y₁ hy₀ hy₁ hy₀₁ i hi))
    φ ψ hφψ

theorem coordinateLp_outputActionLp (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi * ε / 6) (i : Fin 8) (z : EnergyOutputSpace) :
    coordinateLp i (outputActionLp ε hε h N hN y hy z) =
      (shiftedResolvent ε hε h N hN y hy).compLpL 2 angleMeasure (coordinateLp i z) := by
  apply Lp.ext
  filter_upwards [(coordinate i).coeFn_compLp (outputActionLp ε hε h N hN y hy z),
    (outputAction ε hε h N hN y hy).coeFn_compLp z,
    (shiftedResolvent ε hε h N hN y hy).coeFn_compLp (coordinateLp i z),
    (coordinate i).coeFn_compLp z] with θ h1 h2 h3 h4
  change (coordinate i).compLp (outputActionLp ε hε h N hN y hy z) θ =
    (shiftedResolvent ε hε h N hN y hy).compLp (coordinateLp i z) θ
  rw [h1, h3]
  change (outputAction ε hε h N hN y hy).compLp z θ i =
    shiftedResolvent ε hε h N hN y hy ((coordinate i).compLp z θ)
  rw [h2, h4]
  rfl

theorem orbit_shiftedResolvent_pairing (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi * ε / 6) (φ ψ : OrbitSpace) :
    inner ℂ ((shiftedResolvent ε hε h N hN y hy).compLpL 2 angleMeasure φ) ψ =
      inner ℂ φ ((shiftedResolvent ε hε h N hN (-y) (neg_shift_bound ε y hy)).compLpL 2 angleMeasure ψ) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(shiftedResolvent ε hε h N hN y hy).coeFn_compLp φ,
    (shiftedResolvent ε hε h N hN (-y) (neg_shift_bound ε y hy)).coeFn_compLp ψ] with θ hφ hψ
  change inner ℂ ((shiftedResolvent ε hε h N hN y hy).compLp φ θ) (ψ θ) =
    inner ℂ (φ θ) ((shiftedResolvent ε hε h N hN (-y) (neg_shift_bound ε y hy)).compLp ψ θ)
  rw [hφ, hψ]
  exact shiftedResolvent_pairing ε hε h N hN y hy (φ θ) (ψ θ)

theorem inner_components (f g : EnergyOutputSpace) :
    inner ℂ f g = ∑ i : Fin 8, inner ℂ (coordinateLp i f) (coordinateLp i g) := by
  have he : (fun θ => inner ℂ (f θ) (g θ)) =ᵐ[angleMeasure]
      fun θ => ∑ i : Fin 8, inner ℂ (coordinateLp i f θ) (coordinateLp i g θ) := by
    filter_upwards [ae_all_iff.mpr (fun i : Fin 8 => (coordinate i).coeFn_compLp f),
      ae_all_iff.mpr (fun i : Fin 8 => (coordinate i).coeFn_compLp g)] with θ hf hg
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg₂ (inner ℂ) (hf i).symm (hg i).symm
  rw [L2.inner_def, integral_congr_ae he, integral_finset_sum Finset.univ]
  · rfl
  · intro i _
    exact L2.integrable_inner (𝕜 := ℂ) (coordinateLp i f) (coordinateLp i g)

theorem outputActionLp_pairing (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi * ε / 6) (z₁ z₂ : EnergyOutputSpace) :
    inner ℂ (outputActionLp ε hε h N hN y hy z₁) z₂ =
      inner ℂ z₁ (outputActionLp ε hε h N hN (-y) (neg_shift_bound ε y hy) z₂) := by
  rw [inner_components, inner_components]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateLp_outputActionLp, coordinateLp_outputActionLp,
    orbit_shiftedResolvent_pairing]

private theorem outputActionLp_congr (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₁ y₂ : ℝ) (hy₁ : |y₁| ≤ Real.pi * ε / 6) (hy₂ : |y₂| ≤ Real.pi * ε / 6)
    (hy : y₁ = y₂) (z : EnergyOutputSpace) :
    outputActionLp ε hε h N hN y₁ hy₁ z = outputActionLp ε hε h N hN y₂ hy₂ z := by
  subst hy
  rfl

private theorem shiftedResolvent_congr (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₁ y₂ : ℝ) (hy₁ : |y₁| ≤ Real.pi * ε / 6) (hy₂ : |y₂| ≤ Real.pi * ε / 6)
    (hy : y₁ = y₂) (f : Hilbert) :
    shiftedResolvent ε hε h N hN y₁ hy₁ f = shiftedResolvent ε hε h N hN y₂ hy₂ f := by
  subst hy
  rfl

theorem outputActionLp_neg_half_pairing (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hb : |h| ≤ Real.pi * ε / 3) (z₁ z₂ : EnergyOutputSpace) :
    inner ℂ (outputActionLp ε hε h N hN (-h / 2) (shift_bound ε h hb) z₁) z₂ =
      inner ℂ z₁ (outputActionLp ε hε h N hN (h / 2) (half_shift_bound ε h hb) z₂) := by
  rw [outputActionLp_pairing, outputActionLp_congr ε hε h N hN (-(-h / 2)) (h / 2)
    (neg_shift_bound ε (-h / 2) (shift_bound ε h hb)) (half_shift_bound ε h hb) (by ring) z₂]

theorem shiftedResolvent_neg_pairing (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hbn : |h| ≤ Real.pi * ε / 6) (f g : Hilbert) :
    inner ℂ f (shiftedResolvent ε hε h N hN h hbn g) =
      inner ℂ (shiftedResolvent ε hε h N hN (-h) (neg_shift_bound ε h hbn) f) g := by
  have hpair := shiftedResolvent_pairing ε hε h N hN (-h) (neg_shift_bound ε h hbn) f g
  rw [shiftedResolvent_congr ε hε h N hN (-(-h)) h
    (neg_shift_bound ε (-h) (neg_shift_bound ε h hbn)) hbn (neg_neg h) g] at hpair
  exact hpair.symm

private theorem ordered_slice_factor_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (m g k : ℝ) (f : Hilbert) (y : EnergyOutputSpace) (i : Fin 8)
    (hg : (physicalOrbit h hh (growingWeight m g k i • f), coordinateLp i y) ∈
      (factorOperator ε hε h i).graph) :
    (physicalOrbit h hh ((if i.val < 5 then 0 else growingWeight m g k i) • f),
      coordinateLp i (orderedOutputLp y)) ∈ (factorOperator ε hε h i).graph := by
  rw [coordinate_ordered]
  by_cases hi : i.val < 5
  · simpa only [hi, if_true, zero_smul, map_zero] using
      (factorOperator ε hε h i).graph.zero_mem
  · simpa only [hi, if_false] using hg

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi * ε / 3) (hh : h ≠ 0) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k

theorem potential_closure_component (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f, z) ∈ (Tpot).graph) (i : Fin 8) :
    (physicalOrbit h hh ((if i.val < 5 then 0 else growingWeight m g k i) • f),
      coordinateLp i z) ∈ (factorOperator ε hε h i).graph := by
  let L : Hilbert × EnergyOutputSpace →L[ℂ] OrbitSpace × OrbitSpace :=
    ((physicalOrbit h hh).toContinuousLinearMap.comp
      ((if i.val < 5 then 0 else growingWeight m g k i) •
        ContinuousLinearMap.fst ℂ Hilbert EnergyOutputSpace)).prod
      ((coordinateLp i).comp (ContinuousLinearMap.snd ℂ Hilbert EnergyOutputSpace))
  have hz' : (f, z) ∈
      (KFCausalClockFloorPotentialOutputClosure.initialGraph ε hε h hh hw m g k).topologicalClosure :=
    (congrArg (fun G : Submodule ℂ (Hilbert × EnergyOutputSpace) => (f, z) ∈ G)
      (KFCausalClockFloorPotentialOutputClosure.operator_graph ε hε h hh hw m g k)).mp hz
  have hinit : ∀ w ∈ KFCausalClockFloorPotentialOutputClosure.initialGraph ε hε h hh hw m g k,
      L w ∈ (factorOperator ε hε h i).graph := by
    rintro w ⟨u, rfl⟩
    exact ordered_slice_factor_graph ε hε h hh m g k
      (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k 0 u)
      (KFCausalClockFloorAveragedRegularity.growingMap ε hε h hh hw m g k u) i
      (KFCausalClockFloorOrbitFactorGraphs.growing_factor_graph ε hε h hh hw m g k u i)
  exact submodule_closure_transport
    (KFCausalClockFloorPotentialOutputClosure.initialGraph ε hε h hh hw m g k)
    (factorOperator ε hε h i).graph L
    (KFCausalClockFloorOrbitFactorGraphs.factorOperator_closed ε hε h (hamiltonian_bound ε h hw) i)
    hinit (f, z) hz'

theorem potential_closure_orbit_shiftedResolvent (y₀ y₁ : ℝ)
    (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (hy₀₁ : y₁ = y₀ - h / 2) (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f, z) ∈ (Tpot).graph) (i : Fin 8) :
    ((shiftedResolvent ε hε h N hN y₀ hy₀).compLpL 2 angleMeasure
        (physicalOrbit h hh ((if i.val < 5 then 0 else growingWeight m g k i) • f)),
      coordinateLp i (outputActionLp ε hε h N hN y₁ hy₁ z)) ∈
      (factorOperator ε hε h i).graph := by
  have hc := potential_closure_component ε hε h hb hh m g k f z hz i
  rw [coordinateLp_outputActionLp]
  by_cases hi : i.val < 5
  · have hzero : coordinateLp i z = 0 :=
      (factorOperator ε hε h i).graph_fst_eq_zero_snd hc
        (by simp only [hi, if_true, zero_smul, map_zero])
    simpa only [hi, if_true, zero_smul, map_zero, hzero] using
      (factorOperator ε hε h i).graph.zero_mem
  · exact ordered_factorOperator_shiftedResolvent ε hε h N hN hb y₀ y₁ hy₀ hy₁ hy₀₁ i hi _ _ hc

theorem potentialForm_output_shifted_pairing (u v : PV) :
    inner ℂ (PB (formAction ε hε h N hN hb hh m g k u)) (PB v) =
      inner ℂ (PB u) (outputActionLp ε hε h N hN (h / 2) (half_shift_bound ε h hb) (PB v)) :=
  (congrArg (fun z : EnergyOutputSpace => inner ℂ z (PB v))
    (formAction_output ε hε h N hN hb hh m g k u)).trans
    (outputActionLp_neg_half_pairing ε hε h N hN hb (PB u) (PB v))

theorem potentialForm_variational_shifted_pairing
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshift : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v))
    (u : PV) (y : Hilbert)
    (hy : ∀ w : PV, inner ℂ (PB u) (PB w) = inner ℂ y (PJ w)) (v : PV) :
    inner ℂ (PB (formAction ε hε h N hN hb hh m g k u)) (PB v) =
      inner ℂ (shiftedResolvent ε hε h N hN (-h) (neg_shift_bound ε h hbn) y) (PJ v) := by
  let w := Classical.choose (hshift v)
  have hws : PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v) :=
    Classical.choose_spec (hshift v)
  have h1 : inner ℂ (PB (formAction ε hε h N hN hb hh m g k u)) (PB v) =
      inner ℂ (PB u) (PB w) :=
    (potentialForm_output_shifted_pairing ε hε h N hN hb hh m g k u v).trans
      (congrArg (inner ℂ (PB u)) hws.2.symm)
  have h2 : inner ℂ (PB u) (PB w) =
      inner ℂ y (shiftedResolvent ε hε h N hN h hbn (PJ v)) :=
    (hy w).trans (congrArg (inner ℂ y) hws.1)
  exact (h1.trans h2).trans (shiftedResolvent_neg_pairing ε hε h N hN hbn y (PJ v))

theorem formAction_potentialHamiltonian_graph
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshift : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v))
    (u : PV) (y : Hilbert)
    (hy : ∀ w : PV, inner ℂ (PB u) (PB w) = inner ℂ y (PJ w)) :
    (action ε hε h N hN (PJ u),
      shiftedResolvent ε hε h N hN (-h) (neg_shift_bound ε h hbn) y) ∈ (P).graph := by
  have hchar := (KFCausalClosedGraphForm.hamiltonian_domain_characterization PD
    (formAction ε hε h N hN hb hh m g k u)
    (shiftedResolvent ε hε h N hN (-h) (neg_shift_bound ε h hbn) y)).mpr
      (potentialForm_variational_shifted_pairing ε hε h N hN hb hh m g k hbn hshift u y hy)
  obtain ⟨hd, he⟩ := hchar
  have hg : (PJ (formAction ε hε h N hN hb hh m g k u),
      shiftedResolvent ε hε h N hN (-h) (neg_shift_bound ε h hbn) y) ∈ (P).graph :=
    (LinearPMap.mem_graph_iff _).mpr ⟨⟨_, hd⟩, rfl, he⟩
  exact (congrArg (fun f : Hilbert =>
    (f, shiftedResolvent ε hε h N hN (-h) (neg_shift_bound ε h hbn) y) ∈ (P).graph)
    (formAction_embedding ε hε h N hN hb hh m g k u)).mp hg

def domainFormLift (x : (P).domain) : PV :=
  KFCausalClosedGraphForm.formLift PD x

theorem domainFormLift_embedding (x : (P).domain) :
    PJ (domainFormLift ε hε h hb hh m g k x) = (x : Hilbert) :=
  KFCausalClosedGraphForm.embedding_formLift PD x

theorem domainFormLift_represents (x : (P).domain) (w : PV) :
    inner ℂ (PB (domainFormLift ε hε h hb hh m g k x)) (PB w) =
      inner ℂ (P x) (PJ w) :=
  KFCausalClosedGraphForm.hamiltonian_represents_form PD x w

theorem potentialHamiltonian_resolvent_graph
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshift : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v))
    (x : (P).domain) :
    (action ε hε h N hN (x : Hilbert),
      shiftedResolvent ε hε h N hN (-h) (neg_shift_bound ε h hbn) (P x)) ∈ (P).graph := by
  have hg := formAction_potentialHamiltonian_graph ε hε h N hN hb hh m g k hbn hshift
    (domainFormLift ε hε h hb hh m g k x) (P x)
    (domainFormLift_represents ε hε h hb hh m g k x)
  exact (congrArg (fun f : Hilbert =>
    (action ε hε h N hN f,
      shiftedResolvent ε hε h N hN (-h) (neg_shift_bound ε h hbn) (P x)) ∈ (P).graph)
    (domainFormLift_embedding ε hε h hb hh m g k x)).mp hg

theorem potentialHamiltonian_resolvent_domain
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshift : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v))
    (f : Hilbert) (hf : f ∈ (P).domain) :
    action ε hε h N hN f ∈ (P).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (potentialHamiltonian_resolvent_graph ε hε h N hN hb hh m g k hbn hshift ⟨f, hf⟩)

theorem potentialHamiltonian_yosida_domain
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshift : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v))
    (f : Hilbert) (hf : f ∈ (P).domain) :
    KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f ∈ (P).domain := by
  have hj := potentialHamiltonian_resolvent_domain ε hε h N hN hb hh m g k hbn hshift f hf
  have hsub := (P).domain.sub_mem hf hj
  have hsmul := (P).domain.smul_mem (N : ℂ) hsub
  have heq : (N : ℂ) • (f - action ε hε h N hN f) =
      KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f := by
    change (N : ℂ) • (f - (f - (N⁻¹ : ℂ) •
      KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f)) = _
    rw [sub_sub_cancel, smul_smul]
    have hNne : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
    rw [mul_inv_cancel₀ hNne, one_smul]
  exact (congrArg (fun z : Hilbert => z ∈ (P).domain) heq).mp hsmul

theorem potentialHamiltonian_resolvent_commutator_tendsto
    (hbn : |h| ≤ Real.pi * ε / 6) (f : Hilbert) :
    Tendsto (fun n : ℕ =>
      shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h) (neg_shift_bound ε h hbn) f -
        action ε hε h ((n : ℝ) + 1) (by positivity) f) atTop (𝓝 0) := by
  have h1 := shifted_sequence_tendsto ε hε h (-h) (neg_shift_bound ε h hbn) f
  have h2 := sequence_tendsto ε hε h f
  simpa only [sub_self] using h1.sub h2

#print axioms ordered_energyFactor_shiftedResolvent
#print axioms ordered_factorOperator_shiftedResolvent
#print axioms coordinateLp_outputActionLp
#print axioms orbit_shiftedResolvent_pairing
#print axioms inner_components
#print axioms outputActionLp_pairing
#print axioms outputActionLp_neg_half_pairing
#print axioms shiftedResolvent_neg_pairing
#print axioms potential_closure_component
#print axioms potential_closure_orbit_shiftedResolvent
#print axioms potentialForm_output_shifted_pairing
#print axioms potentialForm_variational_shifted_pairing
#print axioms formAction_potentialHamiltonian_graph
#print axioms domainFormLift_embedding
#print axioms domainFormLift_represents
#print axioms potentialHamiltonian_resolvent_graph
#print axioms potentialHamiltonian_resolvent_domain
#print axioms potentialHamiltonian_yosida_domain
#print axioms potentialHamiltonian_resolvent_commutator_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotentialDomain
