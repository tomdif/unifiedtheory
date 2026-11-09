/- Unconditional operator-level decomposition of the growing Hamiltonian into
the maximal radial operator plus the potential Hamiltonian:
  Dom(G) = Dom(K_rad) ∩ Dom(P)  and  G x = K_rad x + P x  for all x ∈ Dom(G),
together with exact root-radial and growing-form shifted pairings, unconditional
reduction of Dom(G) resolvent invariance to Dom(P) resolvent invariance, and
strong commutator convergence. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotentialDomain
import UnifiedTheory.Audit.KFCausalClockFloorGrowingFormReconstruction

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventGrowingDomain
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorChartPhasePairing (orderedOutput orderedOutputLp)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaSymbol (radial radial_nonnegative symbol)
open KFCausalClockFloorRadialResolventRegularizer (multiplier action action_coe
  radial_graph sequence_tendsto)
open KFCausalClockFloorRadialYosidaDomain (operator)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootSymbol rootOperator
  rootOutput rootOutput_graph rootOutput_inner)
open KFCausalClockFloorGrowingRadialDomination (radial_domain)
open KFCausalClockFloorPotentialHamiltonian (growingLift growingLift_embedding
  growingLift_output)
open KFCausalClockFloorRadialResolventGrowing (formAction formAction_embedding
  rootOutput_formAction growingLift_formAction)
open KFCausalClockFloorGrowingFormReconstruction (reconstruct_growing_form)
open KFCausalClockFloorRadialResolventSections (outputActionLp)
open KFCausalClockFloorRadialResolventShiftedPairing (neg_shift_bound half_shift_bound)
open KFCausalClockFloorRadialResolventShiftedOrderedTransport (shiftedResolvent
  narrow_half_shift_bound)
open KFCausalClockFloorRadialResolventPotentialDomain (inner_components
  potentialForm_output_shifted_pairing potentialHamiltonian_resolvent_graph)
open KFCausalClockFloorRotatedAntiSymbol (chargedWeight_continuous)
open KFCausalUnitaryRealMultiplier (realPullback_domain realPullback_graph)
open KFCausalUnitIntervalOrbit (angleMeasure)

private theorem radial_continuous (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    Continuous (radial ε h) :=
  ((chargedWeight_continuous ε hε h 0).add (chargedWeight_continuous ε hε h 1)).div_const 2

private theorem root_square (ε : ℝ) (hε : 0 < ε) (h : ℝ) (x : Joint 2 4) :
    rootSymbol ε h x ^ 2 = radial ε h x :=
  Real.sq_sqrt (radial_nonnegative ε hε h x)

private theorem multiplier_mul_radial (ε h N : ℝ) (x : Joint 2 4) :
    multiplier ε h N x * radial ε h x = symbol ε h N x := by
  unfold multiplier symbol
  exact div_mul_eq_mul_div N (N + radial ε h x) (radial ε h x)

private theorem real_mul_inner (a b : ℝ) (u v : ℂ) :
    inner ℂ ((a : ℂ) * ((b : ℂ) * u)) ((b : ℂ) * v) =
      inner ℂ (((a * b ^ 2 : ℝ) : ℂ) * u) v := by
  change inner ℂ ((a : ℂ) • ((b : ℂ) • u)) ((b : ℂ) • v) =
    inner ℂ (((a * b ^ 2 : ℝ) : ℂ) • u) v
  rw [inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_left]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

private theorem real_sq_inner (b : ℝ) (u v : ℂ) :
    inner ℂ ((b : ℂ) * u) ((b : ℂ) * v) =
      inner ℂ (((b ^ 2 : ℝ) : ℂ) * u) v := by
  simpa only [Complex.ofReal_one, one_mul] using real_mul_inner 1 b u v

theorem root_yosida_pairing (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f g r s : Hilbert)
    (hfr : (f, r) ∈ (rootOperator ε hε h).graph)
    (hgs : (g, s) ∈ (rootOperator ε hε h).graph) :
    inner ℂ (action ε hε h N hN r) s =
      inner ℂ (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f) g := by
  have hr := (realPullback_graph chargeCoordinates (rootSymbol ε h)
    (radial_continuous ε hε h).sqrt.measurable f r).mp hfr
  have hs := (realPullback_graph chargeCoordinates (rootSymbol ε h)
    (radial_continuous ε hε h).sqrt.measurable g s).mp hgs
  rw [← chargeCoordinates.inner_map_map (action ε hε h N hN r) s,
    ← chargeCoordinates.inner_map_map
      (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f) g,
    L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [action_coe ε hε h N hN r, hr, hs,
    KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN f] with x ha hrx hsx hm
  change inner ℂ ((chargeCoordinates (action ε hε h N hN r)) x) ((chargeCoordinates s) x) =
    inner ℂ ((chargeCoordinates (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f)) x)
      ((chargeCoordinates g) x)
  rw [ha, hrx, hsx, hm, real_mul_inner, root_square ε hε h x, multiplier_mul_radial]

theorem root_radial_pairing (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (f g r s k_f : Hilbert)
    (hfr : (f, r) ∈ (rootOperator ε hε h).graph)
    (hgs : (g, s) ∈ (rootOperator ε hε h).graph)
    (hkf : (f, k_f) ∈ (operator ε hε h).graph) :
    inner ℂ r s = inner ℂ k_f g := by
  have hr := (realPullback_graph chargeCoordinates (rootSymbol ε h)
    (radial_continuous ε hε h).sqrt.measurable f r).mp hfr
  have hs := (realPullback_graph chargeCoordinates (rootSymbol ε h)
    (radial_continuous ε hε h).sqrt.measurable g s).mp hgs
  have hk := (realPullback_graph chargeCoordinates (radial ε h)
    (radial_continuous ε hε h).measurable f k_f).mp hkf
  rw [← chargeCoordinates.inner_map_map r s,
    ← chargeCoordinates.inner_map_map k_f g,
    L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hr, hs, hk] with x hrx hsx hkx
  change inner ℂ ((chargeCoordinates r) x) ((chargeCoordinates s) x) =
    inner ℂ ((chargeCoordinates k_f) x) ((chargeCoordinates g) x)
  rw [hrx, hsx, hkx, real_sq_inner, root_square ε hε h x]

theorem radial_action_commute (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f k_f : Hilbert) (hkf : (f, k_f) ∈ (operator ε hε h).graph) :
    KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f =
      action ε hε h N hN k_f := by
  have hk := (realPullback_graph chargeCoordinates (radial ε h)
    (radial_continuous ε hε h).measurable f k_f).mp hkf
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN f,
    action_coe ε hε h N hN k_f, hk] with x hm ha hkx
  rw [hm, ha, hkx, ← mul_assoc, ← Complex.ofReal_mul, multiplier_mul_radial]

theorem radial_domain_le_root_domain (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (f : Hilbert) (hf : f ∈ (operator ε hε h).domain) :
    f ∈ (rootOperator ε hε h).domain := by
  let k_f : Hilbert := operator ε hε h ⟨f, hf⟩
  have hkf : (f, k_f) ∈ (operator ε hε h).graph := (operator ε hε h).mem_graph ⟨f, hf⟩
  have hk := (realPullback_graph chargeCoordinates (radial ε h)
    (radial_continuous ε hε h).measurable f k_f).mp hkf
  apply (realPullback_domain chargeCoordinates (rootSymbol ε h)
    (radial_continuous ε hε h).sqrt.measurable f).mpr
  have hae : AEStronglyMeasurable
      (fun x : Joint 2 4 => (rootSymbol ε h x : ℂ) * (chargeCoordinates f) x) volume :=
    (Complex.continuous_ofReal.comp (radial_continuous ε hε h).sqrt).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (chargeCoordinates f))
  apply ((Lp.memLp (chargeCoordinates f)).norm.add
    (Lp.memLp (chargeCoordinates k_f)).norm).of_le hae
  filter_upwards [hk] with x hkx
  change ‖(rootSymbol ε h x : ℂ) * (chargeCoordinates f) x‖ ≤
    ‖‖(chargeCoordinates f) x‖ + ‖(chargeCoordinates k_f) x‖‖
  rw [Real.norm_eq_abs]
  apply le_trans _ (le_abs_self _)
  have hr0 : 0 ≤ rootSymbol ε h x := Real.sqrt_nonneg _
  have hrad0 : 0 ≤ radial ε h x := radial_nonnegative ε hε h x
  have hle : rootSymbol ε h x ≤ 1 + radial ε h x := by
    have hsq : 0 ≤ (rootSymbol ε h x - 1) ^ 2 := sq_nonneg _
    nlinarith [root_square ε hε h x]
  rw [hkx, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr0, abs_of_nonneg hrad0]
  nlinarith [norm_nonneg ((chargeCoordinates f) x)]

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

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi * ε / 3) (hh : h ≠ 0) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k 0
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "GV" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hw m g k
local notation "GJ" => KFCausalClosedGraphForm.embedding GD
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "R" => rootOutput ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "Kr" => operator ε hε h

private theorem static_coordinate_zero (u : GV) (i : Fin 8) (hi : i.val < 3) :
    coordinateLp i (GB u) = 0 := by
  have hg : (GJ u, GB u) ∈ (KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k).graph :=
    u.property
  have hg' : (GJ u, GB u) ∈
      (KFCausalClockFloorGrowingOutputClosure.initialGraph ε hε h hh hw m g k).topologicalClosure :=
    (congrArg (fun S : Submodule ℂ (Hilbert × EnergyOutputSpace) => (GJ u, GB u) ∈ S)
      (KFCausalClockFloorGrowingOutputClosure.operator_graph ε hε h hh hw m g k)).mp hg
  have hc := KFCausalClockFloorGrowingOutputClosure.closure_component ε hε h hh hw m g k
    (GJ u, GB u) hg' i
  exact (KFCausalClockFloorOrbitFactorGraphs.factorOperator ε hε h i).graph_fst_eq_zero_snd hc
    (by simp only [KFCausalClockFloorOrbitFactorGraphs.growingWeight, hi, if_true, zero_smul, map_zero])

theorem growingForm_split_inner (u v : GV) :
    inner ℂ (GB u) (GB v) =
      inner ℂ (R u) (R v) +
        inner ℂ (PB (growingLift ε hε h hh hw m g k u))
          (PB (growingLift ε hε h hh hw m g k v)) := by
  have h0 := static_coordinate_zero ε hε h hb hh m g k u 0 (by decide)
  have h1 := static_coordinate_zero ε hε h hb hh m g k u 1 (by decide)
  have h2 := static_coordinate_zero ε hε h hb hh m g k u 2 (by decide)
  have hr := rootOutput_inner ε hε h hh hw m g k u v
  have e1 := inner_components (GB u) (GB v)
  have e2 := inner_components (orderedOutputLp (GB u)) (orderedOutputLp (GB v))
  have hs : (∑ i : Fin 8, inner ℂ (coordinateLp i (GB u)) (coordinateLp i (GB v))) =
      (inner ℂ (coordinateLp 3 (GB u)) (coordinateLp 3 (GB v)) +
        inner ℂ (coordinateLp 4 (GB u)) (coordinateLp 4 (GB v))) +
      (∑ i : Fin 8, inner ℂ (coordinateLp i (orderedOutputLp (GB u)))
        (coordinateLp i (orderedOutputLp (GB v)))) := by
    simp [Fin.sum_univ_succ, coordinate_ordered, h0, h1, h2]
    abel
  have he := e1.trans (hs.trans (congrArg (fun z : ℂ =>
    (inner ℂ (coordinateLp 3 (GB u)) (coordinateLp 3 (GB v)) +
      inner ℂ (coordinateLp 4 (GB u)) (coordinateLp 4 (GB v))) + z) e2.symm))
  have ho : inner ℂ (orderedOutputLp (GB u)) (orderedOutputLp (GB v)) =
      inner ℂ (PB (growingLift ε hε h hh hw m g k u))
        (PB (growingLift ε hε h hh hw m g k v)) :=
    congrArg₂ (inner ℂ)
      (growingLift_output ε hε h hh hw m g k u).symm
      (growingLift_output ε hε h hh hw m g k v).symm
  exact (he.trans (congrArg (fun z : ℂ => z +
    inner ℂ (orderedOutputLp (GB u)) (orderedOutputLp (GB v))) hr.symm)).trans
    (congrArg (fun z : ℂ => inner ℂ (R u) (R v) + z) ho)

theorem growingForm_formAction_root_pairing (u v : GV) :
    inner ℂ (R (formAction ε hε h N hN hb hh m g k u)) (R v) =
      inner ℂ (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (GJ u)) (GJ v) :=
  (congrArg (fun z : Hilbert => inner ℂ z (R v))
    (rootOutput_formAction ε hε h N hN hb hh m g k u)).trans
    (root_yosida_pairing ε hε h N hN (GJ u) (GJ v) (R u) (R v)
      (rootOutput_graph ε hε h hh hw m g k u)
      (rootOutput_graph ε hε h hh hw m g k v))

theorem growingForm_formAction_output_pairing (u v : GV) :
    inner ℂ (GB (formAction ε hε h N hN hb hh m g k u)) (GB v) =
      inner ℂ (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (GJ u)) (GJ v) +
        inner ℂ (PB (growingLift ε hε h hh hw m g k u))
          (outputActionLp ε hε h N hN (h / 2) (half_shift_bound ε h hb)
            (PB (growingLift ε hε h hh hw m g k v))) := by
  have h1 := growingForm_split_inner ε hε h hb hh m g k
    (formAction ε hε h N hN hb hh m g k u) v
  have h2 := growingForm_formAction_root_pairing ε hε h N hN hb hh m g k u v
  have h3 : inner ℂ (PB (growingLift ε hε h hh hw m g k (formAction ε hε h N hN hb hh m g k u)))
      (PB (growingLift ε hε h hh hw m g k v)) =
      inner ℂ (PB (growingLift ε hε h hh hw m g k u))
        (outputActionLp ε hε h N hN (h / 2) (half_shift_bound ε h hb)
          (PB (growingLift ε hε h hh hw m g k v))) :=
    (congrArg (fun w : PV => inner ℂ (PB w) (PB (growingLift ε hε h hh hw m g k v)))
      (growingLift_formAction ε hε h N hN hb hh m g k u)).trans
      (potentialForm_output_shifted_pairing ε hε h N hN hb hh m g k
        (growingLift ε hε h hh hw m g k u) (growingLift ε hε h hh hw m g k v))
  exact h1.trans (congrArg₂ (· + ·) h2 h3)

theorem growingForm_radial_potential_pairing (u v : GV) (k_u : Hilbert)
    (hku : (GJ u, k_u) ∈ (Kr).graph) :
    inner ℂ (GB u) (GB v) =
      inner ℂ k_u (GJ v) +
        inner ℂ (PB (growingLift ε hε h hh hw m g k u))
          (PB (growingLift ε hε h hh hw m g k v)) :=
  (growingForm_split_inner ε hε h hb hh m g k u v).trans
    (congrArg (fun z : ℂ => z +
      inner ℂ (PB (growingLift ε hε h hh hw m g k u))
        (PB (growingLift ε hε h hh hw m g k v)))
      (root_radial_pairing ε hε h (GJ u) (GJ v) (R u) (R v) k_u
        (rootOutput_graph ε hε h hh hw m g k u)
        (rootOutput_graph ε hε h hh hw m g k v) hku))

private theorem reference_growingLift_eq (v : RV) :
    growingLift ε hε h hh hw m g k
      (KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k v) =
      KFCausalClockFloorPotentialHamiltonian.referenceLift ε hε h hh hw m g k v := by
  apply KFCausalClosedGraphForm.embedding_injective PD
  exact (growingLift_embedding ε hε h hh hw m g k
    (KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k v)).trans
    ((KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding ε hε h hh hw m g k v).trans
      (KFCausalClockFloorPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k v).symm)

theorem growingHamiltonian_to_potentialHamiltonian_graph
    (f y k_f : Hilbert) (hfy : (f, y) ∈ (G).graph) (hkf : (f, k_f) ∈ (Kr).graph) :
    (f, y - k_f) ∈ (P).graph := by
  let x : (G).domain := ⟨f, LinearPMap.mem_domain_of_mem_graph hfy⟩
  have hx : G x = y := (G).mem_graph_snd_inj' ((G).mem_graph x) hfy rfl
  let u : GV := KFCausalClosedGraphForm.formLift GD x
  have huJ : GJ u = f := KFCausalClosedGraphForm.embedding_formLift GD x
  have hku : (GJ u, k_f) ∈ (Kr).graph :=
    (congrArg (fun z : Hilbert => (z, k_f) ∈ (Kr).graph) huJ.symm).mp hkf
  have hrep (w : GV) :
      inner ℂ (PB (growingLift ε hε h hh hw m g k u))
        (PB (growingLift ε hε h hh hw m g k w)) =
        inner ℂ (y - k_f) (PJ (growingLift ε hε h hh hw m g k w)) := by
    have h1 : inner ℂ (GB u) (GB w) = inner ℂ y (GJ w) :=
      (KFCausalClosedGraphForm.hamiltonian_represents_form GD x w).trans
        (congrArg (fun z : Hilbert => inner ℂ z (GJ w)) hx)
    have h2 := growingForm_radial_potential_pairing ε hε h hb hh m g k u w k_f hku
    have hsub : inner ℂ (PB (growingLift ε hε h hh hw m g k u))
        (PB (growingLift ε hε h hh hw m g k w)) =
        inner ℂ y (GJ w) - inner ℂ k_f (GJ w) :=
      eq_sub_of_add_eq' (h2.symm.trans h1)
    have h3 : inner ℂ y (GJ w) - inner ℂ k_f (GJ w) =
        inner ℂ (y - k_f) (PJ (growingLift ε hε h hh hw m g k w)) :=
      (inner_sub_left y k_f (GJ w)).symm.trans
        (congrArg (inner ℂ (y - k_f)) (growingLift_embedding ε hε h hh hw m g k w).symm)
    exact hsub.trans h3
  have href (v : RV) :
      inner ℂ (PB (growingLift ε hε h hh hw m g k u))
        (PB (KFCausalClockFloorPotentialHamiltonian.referenceLift ε hε h hh hw m g k v)) =
        inner ℂ (y - k_f)
          (PJ (KFCausalClockFloorPotentialHamiltonian.referenceLift ε hε h hh hw m g k v)) := by
    have heq := reference_growingLift_eq ε hε h hb hh m g k v
    exact (congrArg (fun z : PV => inner ℂ (PB (growingLift ε hε h hh hw m g k u)) (PB z))
      heq.symm).trans
      ((hrep (KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k v)).trans
        (congrArg (fun z : PV => inner ℂ (y - k_f) (PJ z)) heq))
  have hall (z : PV) :
      inner ℂ (PB (growingLift ε hε h hh hw m g k u)) (PB z) =
        inner ℂ (y - k_f) (PJ z) :=
    congrFun ((KFCausalClockFloorPotentialHamiltonian.referenceLift_dense ε hε h hh hw m g k).equalizer
      (continuous_const.inner (𝕜 := ℂ) (PB).continuous)
      (continuous_const.inner (𝕜 := ℂ) (PJ).continuous)
      (funext href)) z
  have hchar := (KFCausalClosedGraphForm.hamiltonian_domain_characterization PD
    (growingLift ε hε h hh hw m g k u) (y - k_f)).mpr hall
  obtain ⟨hd, he⟩ := hchar
  have hg : (PJ (growingLift ε hε h hh hw m g k u), y - k_f) ∈ (P).graph :=
    (LinearPMap.mem_graph_iff _).mpr ⟨⟨_, hd⟩, rfl, he⟩
  have hPJ : PJ (growingLift ε hε h hh hw m g k u) = f :=
    (growingLift_embedding ε hε h hh hw m g k u).trans huJ
  exact (congrArg (fun z : Hilbert => (z, y - k_f) ∈ (P).graph) hPJ).mp hg

theorem growingHamiltonian_in_potentialHamiltonian_domain
    (f : Hilbert) (hf : f ∈ (G).domain) : f ∈ (P).domain := by
  let x : (G).domain := ⟨f, hf⟩
  have hkr : f ∈ (Kr).domain := radial_domain ε hε h hh hb m g k x
  exact LinearPMap.mem_domain_of_mem_graph
    (growingHamiltonian_to_potentialHamiltonian_graph ε hε h hb hh m g k
      f (G x) (Kr ⟨f, hkr⟩) ((G).mem_graph x) ((Kr).mem_graph ⟨f, hkr⟩))

theorem potentialHamiltonian_and_radial_to_growingHamiltonian_graph
    (f k_f p_f : Hilbert) (hkf : (f, k_f) ∈ (Kr).graph) (hfp : (f, p_f) ∈ (P).graph) :
    (f, k_f + p_f) ∈ (G).graph := by
  let xp : (P).domain := ⟨f, LinearPMap.mem_domain_of_mem_graph hfp⟩
  have hxp : P xp = p_f := (P).mem_graph_snd_inj' ((P).mem_graph xp) hfp rfl
  let z : PV := KFCausalClosedGraphForm.formLift PD xp
  have hzJ : PJ z = f := KFCausalClosedGraphForm.embedding_formLift PD xp
  have hkr : f ∈ (Kr).domain := LinearPMap.mem_domain_of_mem_graph hkf
  have hroot : f ∈ (rootOperator ε hε h).domain :=
    radial_domain_le_root_domain ε hε h f hkr
  let r : Hilbert := rootOperator ε hε h ⟨f, hroot⟩
  have hrg : (PJ z, r) ∈ (rootOperator ε hε h).graph :=
    (congrArg (fun w : Hilbert => (w, r) ∈ (rootOperator ε hε h).graph) hzJ.symm).mp
      ((rootOperator ε hε h).mem_graph ⟨f, hroot⟩)
  have hex := reconstruct_growing_form ε hε h hh hb m g k z r hrg
  let u : GV := Classical.choose hex
  have hu : GJ u = PJ z ∧ R u = r ∧ growingLift ε hε h hh hw m g k u = z :=
    Classical.choose_spec hex
  have huJ : GJ u = f := hu.1.trans hzJ
  have hku : (GJ u, k_f) ∈ (Kr).graph :=
    (congrArg (fun w : Hilbert => (w, k_f) ∈ (Kr).graph) huJ.symm).mp hkf
  have hall (w : GV) :
      inner ℂ (GB u) (GB w) = inner ℂ (k_f + p_f) (GJ w) := by
    have h1 := growingForm_radial_potential_pairing ε hε h hb hh m g k u w k_f hku
    have h2 : inner ℂ (PB (growingLift ε hε h hh hw m g k u))
        (PB (growingLift ε hε h hh hw m g k w)) = inner ℂ p_f (GJ w) :=
      (congrArg (fun v : PV => inner ℂ (PB v) (PB (growingLift ε hε h hh hw m g k w)))
        hu.2.2).trans
        ((KFCausalClosedGraphForm.hamiltonian_represents_form PD xp
          (growingLift ε hε h hh hw m g k w)).trans
          ((congrArg₂ (inner ℂ) hxp (growingLift_embedding ε hε h hh hw m g k w))))
    exact (h1.trans (congrArg (fun s : ℂ => inner ℂ k_f (GJ w) + s) h2)).trans
      (inner_add_left k_f p_f (GJ w)).symm
  have hchar := (KFCausalClosedGraphForm.hamiltonian_domain_characterization GD
    u (k_f + p_f)).mpr hall
  obtain ⟨hd, he⟩ := hchar
  have hg : (GJ u, k_f + p_f) ∈ (G).graph :=
    (LinearPMap.mem_graph_iff _).mpr ⟨⟨_, hd⟩, rfl, he⟩
  exact (congrArg (fun w : Hilbert => (w, k_f + p_f) ∈ (G).graph) huJ).mp hg

theorem growingHamiltonian_domain_iff (f : Hilbert) :
    f ∈ (G).domain ↔ f ∈ (Kr).domain ∧ f ∈ (P).domain := by
  constructor
  · intro hf
    exact ⟨radial_domain ε hε h hh hb m g k ⟨f, hf⟩,
      growingHamiltonian_in_potentialHamiltonian_domain ε hε h hb hh m g k f hf⟩
  · rintro ⟨hk, hp⟩
    exact LinearPMap.mem_domain_of_mem_graph
      (potentialHamiltonian_and_radial_to_growingHamiltonian_graph ε hε h hb hh m g k
        f (Kr ⟨f, hk⟩) (P ⟨f, hp⟩) ((Kr).mem_graph ⟨f, hk⟩) ((P).mem_graph ⟨f, hp⟩))

theorem growingHamiltonian_eq_radial_add_potential (x : (G).domain) :
    G x =
      Kr ⟨(x : Hilbert), radial_domain ε hε h hh hb m g k x⟩ +
        P ⟨(x : Hilbert),
          growingHamiltonian_in_potentialHamiltonian_domain ε hε h hb hh m g k
            (x : Hilbert) x.property⟩ := by
  let hk := radial_domain ε hε h hh hb m g k x
  let hp := growingHamiltonian_in_potentialHamiltonian_domain ε hε h hb hh m g k
    (x : Hilbert) x.property
  have hg := potentialHamiltonian_and_radial_to_growingHamiltonian_graph ε hε h hb hh m g k
    (x : Hilbert) (Kr ⟨(x : Hilbert), hk⟩) (P ⟨(x : Hilbert), hp⟩)
    ((Kr).mem_graph ⟨(x : Hilbert), hk⟩) ((P).mem_graph ⟨(x : Hilbert), hp⟩)
  exact (G).mem_graph_snd_inj' ((G).mem_graph x) hg rfl

theorem growingHamiltonian_resolvent_domain_iff_potential (f : Hilbert) :
    action ε hε h N hN f ∈ (G).domain ↔ action ε hε h N hN f ∈ (P).domain :=
  (growingHamiltonian_domain_iff ε hε h hb hh m g k (action ε hε h N hN f)).trans
    ⟨And.right, fun hp =>
      ⟨KFCausalClockFloorRadialResolventRegularizer.radial_domain ε hε h N hN f, hp⟩⟩

theorem growingHamiltonian_resolvent_graph_of_potential
    (f k_f w : Hilbert) (hkf : (f, k_f) ∈ (Kr).graph)
    (hpw : (action ε hε h N hN f, w) ∈ (P).graph) :
    (action ε hε h N hN f, action ε hε h N hN k_f + w) ∈ (G).graph := by
  have hrg : (action ε hε h N hN f, action ε hε h N hN k_f) ∈ (Kr).graph := by
    rw [← radial_action_commute ε hε h N hN f k_f hkf]
    exact radial_graph ε hε h N hN f
  exact potentialHamiltonian_and_radial_to_growingHamiltonian_graph ε hε h hb hh m g k
    (action ε hε h N hN f) (action ε hε h N hN k_f) w hrg hpw

theorem growingHamiltonian_resolvent_graph
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshift : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v))
    (x : (G).domain) :
    let hk := radial_domain ε hε h hh hb m g k x
    let hp := growingHamiltonian_in_potentialHamiltonian_domain ε hε h hb hh m g k
      (x : Hilbert) x.property
    (action ε hε h N hN (x : Hilbert),
      action ε hε h N hN (Kr ⟨(x : Hilbert), hk⟩) +
        shiftedResolvent ε hε h N hN (-h) (neg_shift_bound ε h hbn)
          (P ⟨(x : Hilbert), hp⟩)) ∈ (G).graph := by
  let hk := radial_domain ε hε h hh hb m g k x
  let hp := growingHamiltonian_in_potentialHamiltonian_domain ε hε h hb hh m g k
    (x : Hilbert) x.property
  exact growingHamiltonian_resolvent_graph_of_potential ε hε h N hN hb hh m g k
    (x : Hilbert) (Kr ⟨(x : Hilbert), hk⟩)
    (shiftedResolvent ε hε h N hN (-h) (neg_shift_bound ε h hbn) (P ⟨(x : Hilbert), hp⟩))
    ((Kr).mem_graph ⟨(x : Hilbert), hk⟩)
    (potentialHamiltonian_resolvent_graph ε hε h N hN hb hh m g k hbn hshift ⟨(x : Hilbert), hp⟩)

theorem growingHamiltonian_resolvent_domain
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshift : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v))
    (f : Hilbert) (hf : f ∈ (G).domain) :
    action ε hε h N hN f ∈ (G).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (growingHamiltonian_resolvent_graph ε hε h N hN hb hh m g k hbn hshift ⟨f, hf⟩)

theorem growingHamiltonian_yosida_domain
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshift : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v))
    (f : Hilbert) (hf : f ∈ (G).domain) :
    KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f ∈ (G).domain := by
  have hj := growingHamiltonian_resolvent_domain ε hε h N hN hb hh m g k hbn hshift f hf
  have hsub := (G).domain.sub_mem hf hj
  have hsmul := (G).domain.smul_mem (N : ℂ) hsub
  have heq : (N : ℂ) • (f - action ε hε h N hN f) =
      KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f := by
    change (N : ℂ) • (f - (f - (N⁻¹ : ℂ) •
      KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f)) = _
    rw [sub_sub_cancel, smul_smul]
    have hNne : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
    rw [mul_inv_cancel₀ hNne, one_smul]
  exact (congrArg (fun z : Hilbert => z ∈ (G).domain) heq).mp hsmul

theorem growingHamiltonian_resolvent_output_tendsto
    (hbn : |h| ≤ Real.pi * ε / 6) (x : (G).domain) :
    let hk := radial_domain ε hε h hh hb m g k x
    let hp := growingHamiltonian_in_potentialHamiltonian_domain ε hε h hb hh m g k
      (x : Hilbert) x.property
    Tendsto (fun n : ℕ =>
      action ε hε h ((n : ℝ) + 1) (by positivity) (Kr ⟨(x : Hilbert), hk⟩) +
        shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h) (neg_shift_bound ε h hbn)
          (P ⟨(x : Hilbert), hp⟩))
      atTop (𝓝 (G x)) := by
  let hk := radial_domain ε hε h hh hb m g k x
  let hp := growingHamiltonian_in_potentialHamiltonian_domain ε hε h hb hh m g k
    (x : Hilbert) x.property
  have h1 := sequence_tendsto ε hε h (Kr ⟨(x : Hilbert), hk⟩)
  have h2 := KFCausalClockFloorRadialResolventShifted.shifted_sequence_tendsto
    ε hε h (-h) (neg_shift_bound ε h hbn) (P ⟨(x : Hilbert), hp⟩)
  exact (congrArg (fun y : Hilbert =>
    Tendsto (fun n : ℕ =>
      action ε hε h ((n : ℝ) + 1) (by positivity) (Kr ⟨(x : Hilbert), hk⟩) +
        shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h) (neg_shift_bound ε h hbn)
          (P ⟨(x : Hilbert), hp⟩)) atTop (𝓝 y))
    (growingHamiltonian_eq_radial_add_potential ε hε h hb hh m g k x).symm).mp (h1.add h2)

#print axioms root_yosida_pairing
#print axioms root_radial_pairing
#print axioms radial_action_commute
#print axioms radial_domain_le_root_domain
#print axioms growingForm_split_inner
#print axioms growingForm_formAction_root_pairing
#print axioms growingForm_formAction_output_pairing
#print axioms growingForm_radial_potential_pairing
#print axioms growingHamiltonian_to_potentialHamiltonian_graph
#print axioms growingHamiltonian_in_potentialHamiltonian_domain
#print axioms potentialHamiltonian_and_radial_to_growingHamiltonian_graph
#print axioms growingHamiltonian_domain_iff
#print axioms growingHamiltonian_eq_radial_add_potential
#print axioms growingHamiltonian_resolvent_domain_iff_potential
#print axioms growingHamiltonian_resolvent_graph_of_potential
#print axioms growingHamiltonian_resolvent_graph
#print axioms growingHamiltonian_resolvent_domain
#print axioms growingHamiltonian_yosida_domain
#print axioms growingHamiltonian_resolvent_output_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventGrowingDomain
