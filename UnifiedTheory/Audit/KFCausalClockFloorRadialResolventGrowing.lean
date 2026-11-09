/- The radial resolvent regularizer lifts to a bounded operator on the
completed growing form, intertwined with the Hilbert regularizer on both
the form embedding and the radial square-root output, compatible with the
potential-form projection, and converging strongly to the identity in the
completed growing-form norm. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotentialForm
import UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialDomination

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventGrowing
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorChartPhasePairing (orderedOutput orderedOutputLp)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer (action sequence_tendsto)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOutput rootOutput_inner)
open KFCausalClockFloorGrowingRadialDomination (root_intertwining)
open KFCausalClockFloorPotentialHamiltonian (growingLift growingLift_embedding growingLift_output)
open KFCausalUnitIntervalOrbit (angleMeasure)

private theorem coordinate_ordered (i : Fin 8) (y : EnergyOutputSpace) :
    coordinateLp i (orderedOutputLp y)=if i.val<5 then 0 else coordinateLp i y := by
  apply Lp.ext
  filter_upwards [(coordinate i).coeFn_compLp (orderedOutputLp y),
    orderedOutput.coeFn_compLp y,(coordinate i).coeFn_compLp y,
    Lp.coeFn_zero (E := Hilbert) (p := 2) (μ := angleMeasure)] with θ h1 h2 h3 h0
  change (coordinate i).compLp (orderedOutputLp y) θ=_
  rw [h1]
  change orderedOutput.compLp y θ i=_
  rw [h2]
  by_cases hi : i.val<5
  · simp only [orderedOutput,KFCausalFiniteOutputRescaling.selected_apply,hi,
      not_true_eq_false,if_false,if_true,h0,Pi.zero_apply]
  · simpa only [orderedOutput,KFCausalFiniteOutputRescaling.selected_apply,hi,
      not_false_eq_true,if_true,if_false] using h3.symm

private theorem inner_components (f g : EnergyOutputSpace) :
    inner ℂ f g=∑ i : Fin 8, inner ℂ (coordinateLp i f) (coordinateLp i g) := by
  have he : (fun θ => inner ℂ (f θ) (g θ)) =ᵐ[angleMeasure]
      fun θ => ∑ i : Fin 8, inner ℂ (coordinateLp i f θ) (coordinateLp i g θ) := by
    filter_upwards [ae_all_iff.mpr (fun i : Fin 8 => (coordinate i).coeFn_compLp f),
      ae_all_iff.mpr (fun i : Fin 8 => (coordinate i).coeFn_compLp g)] with θ hf hg
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg₂ (inner ℂ) (hf i).symm (hg i).symm
  rw [L2.inner_def,integral_congr_ae he,integral_finset_sum Finset.univ]
  · rfl
  · intro i _
    exact L2.integrable_inner (𝕜 := ℂ) (coordinateLp i f) (coordinateLp i g)

private theorem norm_tendsto_of_three_sq {X : Type*} [SeminormedAddCommGroup X]
    (u : ℕ → X) (a b c : ℕ → ℝ)
    (heq : ∀ n, ‖u n‖^2=a n^2+(b n^2+c n^2))
    (ha : Tendsto a atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => ‖u n‖^2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => a n^2+(b n^2+c n^2)) atTop (𝓝 (0^2+(0^2+0^2))) :=
      (ha.pow 2).add ((hb.pow 2).add (hc.pow 2))
    have h0' : Tendsto (fun n => a n^2+(b n^2+c n^2)) atTop (𝓝 0) := by
      simpa only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,add_zero] using h0
    exact h0'.congr' (Eventually.of_forall (fun n => (heq n).symm))
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi*ε/3) (hh : h ≠ 0) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "GV" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hw m g k
local notation "GJ" => KFCausalClosedGraphForm.embedding GD
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "R" => rootOutput ε hε h hh hw m g k

private theorem static_coordinate_zero (u : GV) (i : Fin 8) (hi : i.val<3) :
    coordinateLp i (GB u)=0 := by
  have hg := u.property
  change (GJ u,GB u) ∈ (KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k).graph at hg
  rw [KFCausalClockFloorGrowingOutputClosure.operator_graph] at hg
  have hc := KFCausalClockFloorGrowingOutputClosure.closure_component ε hε h hh hw m g k
    (GJ u,GB u) hg i
  exact (KFCausalClockFloorOrbitFactorGraphs.factorOperator ε hε h i).graph_fst_eq_zero_snd hc
    (by simp only [KFCausalClockFloorOrbitFactorGraphs.growingWeight,hi,if_true,zero_smul,map_zero])

private theorem form_split (u v : GV) :
    inner ℂ (GB u) (GB v)=inner ℂ (R u) (R v)+
      inner ℂ (orderedOutputLp (GB u)) (orderedOutputLp (GB v)) := by
  have h0 := static_coordinate_zero ε hε h hb hh m g k u 0 (by decide)
  have h1 := static_coordinate_zero ε hε h hb hh m g k u 1 (by decide)
  have h2 := static_coordinate_zero ε hε h hb hh m g k u 2 (by decide)
  have hr := rootOutput_inner ε hε h hh hw m g k u v
  have e1 := inner_components (GB u) (GB v)
  have e2 := inner_components (orderedOutputLp (GB u)) (orderedOutputLp (GB v))
  have hs : (∑ i : Fin 8, inner ℂ (coordinateLp i (GB u)) (coordinateLp i (GB v)))=
      (inner ℂ (coordinateLp 3 (GB u)) (coordinateLp 3 (GB v))+
        inner ℂ (coordinateLp 4 (GB u)) (coordinateLp 4 (GB v)))+
      (∑ i : Fin 8, inner ℂ (coordinateLp i (orderedOutputLp (GB u)))
        (coordinateLp i (orderedOutputLp (GB v)))) := by
    simp [Fin.sum_univ_succ,coordinate_ordered,h0,h1,h2]
    abel
  have he := e1.trans (hs.trans (congrArg (fun z : ℂ =>
    (inner ℂ (coordinateLp 3 (GB u)) (coordinateLp 3 (GB v))+
      inner ℂ (coordinateLp 4 (GB u)) (coordinateLp 4 (GB v)))+z) e2.symm))
  exact he.trans (congrArg (fun z : ℂ => z+
    inner ℂ (orderedOutputLp (GB u)) (orderedOutputLp (GB v))) hr.symm)

private theorem norm_sq_of_inner_sum {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (x z : X) (y : Y)
    (h : inner ℂ x x=inner ℂ y y+inner ℂ z z) :
    ‖x‖^2=‖y‖^2+‖z‖^2 := by
  have hi := congrArg Complex.re h
  rw [Complex.add_re] at hi
  exact ((inner_self_eq_norm_sq (𝕜 := ℂ) x).symm.trans hi).trans
    (congrArg₂ (·+·) (inner_self_eq_norm_sq (𝕜 := ℂ) y) (inner_self_eq_norm_sq (𝕜 := ℂ) z))

theorem growing_output_norm_sq (u : GV) :
    ‖GB u‖^2=‖R u‖^2+‖PB (growingLift ε hε h hh hw m g k u)‖^2 := by
  have hi := norm_sq_of_inner_sum (GB u) (orderedOutputLp (GB u)) (R u)
    (form_split ε hε h hb hh m g k u u)
  have ho : ‖orderedOutputLp (GB u)‖^2=‖PB (growingLift ε hε h hh hw m g k u)‖^2 :=
    congrArg (fun y : EnergyOutputSpace => ‖y‖^2)
      (growingLift_output ε hε h hh hw m g k u).symm
  exact hi.trans (congrArg (fun s : ℝ => ‖R u‖^2+s) ho)

theorem growing_form_norm_sq (u : GV) :
    ‖u‖^2=‖GJ u‖^2+(‖R u‖^2+‖PB (growingLift ε hε h hh hw m g k u)‖^2) :=
  (KFCausalClosedGraphForm.form_norm_identity GD u).trans
    (congrArg (fun s : ℝ => ‖GJ u‖^2+s)
      (growing_output_norm_sq ε hε h hb hh m g k u))

def formAction : GV →L[ℂ] GV :=
  ContinuousLinearMap.id ℂ GV-
    (N⁻¹:ℂ) • KFCausalClockFloorRadialYosidaGrowing.formAction ε hε h N hN hb hh m g k

theorem formAction_embedding (u : GV) :
    GJ (formAction ε hε h N hN hb hh m g k u)=action ε hε h N hN (GJ u) := by
  let y := KFCausalClockFloorRadialYosidaGrowing.formAction ε hε h N hN hb hh m g k u
  have h1 : GJ (u-(N⁻¹:ℂ) • y)=GJ u-(N⁻¹:ℂ) • GJ y :=
    ((GJ).map_sub u ((N⁻¹:ℂ) • y)).trans
      (congrArg (fun z : Hilbert => GJ u-z) ((GJ).map_smul (N⁻¹:ℂ) y))
  exact h1.trans (congrArg (fun z : Hilbert => GJ u-(N⁻¹:ℂ) • z)
    (KFCausalClockFloorRadialYosidaGrowing.formAction_embedding ε hε h N hN hb hh m g k u))

theorem rootOutput_formAction (u : GV) :
    R (formAction ε hε h N hN hb hh m g k u)=action ε hε h N hN (R u) := by
  let y := KFCausalClockFloorRadialYosidaGrowing.formAction ε hε h N hN hb hh m g k u
  have h1 : R (u-(N⁻¹:ℂ) • y)=R u-(N⁻¹:ℂ) • R y :=
    ((R).map_sub u ((N⁻¹:ℂ) • y)).trans
      (congrArg (fun z : Hilbert => R u-z) ((R).map_smul (N⁻¹:ℂ) y))
  have h2 : R y=KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (R u) :=
    root_intertwining ε hε h hh hb m g k N hN u
  exact h1.trans (congrArg (fun z : Hilbert => R u-(N⁻¹:ℂ) • z) h2)

theorem growingLift_formAction (u : GV) :
    growingLift ε hε h hh hw m g k (formAction ε hε h N hN hb hh m g k u)=
      KFCausalClockFloorRadialResolventPotential.formAction ε hε h N hN hb hh m g k
        (growingLift ε hε h hh hw m g k u) := by
  apply KFCausalClosedGraphForm.embedding_injective PD
  exact (growingLift_embedding ε hε h hh hw m g k
    (formAction ε hε h N hN hb hh m g k u)).trans
    ((formAction_embedding ε hε h N hN hb hh m g k u).trans
      ((congrArg (action ε hε h N hN)
        (growingLift_embedding ε hε h hh hw m g k u).symm).trans
        (KFCausalClockFloorRadialResolventPotential.formAction_embedding
          ε hε h N hN hb hh m g k (growingLift ε hε h hh hw m g k u)).symm))

private theorem growingLift_sub (u v : GV) :
    growingLift ε hε h hh hw m g k (u-v)=
      growingLift ε hε h hh hw m g k u-growingLift ε hε h hh hw m g k v := by
  apply KFCausalClosedGraphForm.embedding_injective PD
  exact (growingLift_embedding ε hε h hh hw m g k (u-v)).trans
    (((GJ).map_sub u v).trans
      ((congrArg₂ (·-·)
        (growingLift_embedding ε hε h hh hw m g k u).symm
        (growingLift_embedding ε hε h hh hw m g k v).symm).trans
        ((PJ).map_sub (growingLift ε hε h hh hw m g k u)
          (growingLift ε hε h hh hw m g k v)).symm))

theorem form_sequence_tendsto (u : GV) :
    Tendsto (fun n : ℕ =>
      formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k u) atTop (𝓝 u) := by
  let uSeq : ℕ → GV := fun n => formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k u
  let pu := growingLift ε hε h hh hw m g k u
  let pSeq : ℕ → PV := fun n =>
    KFCausalClockFloorRadialResolventPotential.formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k pu
  have hJ := tendsto_iff_norm_sub_tendsto_zero.mp (sequence_tendsto ε hε h (GJ u))
  have hR := tendsto_iff_norm_sub_tendsto_zero.mp (sequence_tendsto ε hε h (R u))
  have hP := tendsto_iff_norm_sub_tendsto_zero.mp
    (((PB).continuous.tendsto pu).comp
      (KFCausalClockFloorRadialResolventPotentialForm.form_sequence_tendsto ε hε h hb hh m g k pu))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine norm_tendsto_of_three_sq (fun n => uSeq n-u)
    (fun n => ‖action ε hε h ((n:ℝ)+1) (by positivity) (GJ u)-GJ u‖)
    (fun n => ‖action ε hε h ((n:ℝ)+1) (by positivity) (R u)-R u‖)
    (fun n => ‖PB (pSeq n)-PB pu‖) ?_ hJ hR hP
  intro n
  have he := growing_form_norm_sq ε hε h hb hh m g k (uSeq n-u)
  have h1 : ‖GJ (uSeq n-u)‖^2=‖action ε hε h ((n:ℝ)+1) (by positivity) (GJ u)-GJ u‖^2 := by
    refine congrArg (fun z : Hilbert => ‖z‖^2) ?_
    exact ((GJ).map_sub (uSeq n) u).trans
      (congrArg (fun z : Hilbert => z-GJ u)
        (formAction_embedding ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k u))
  have h2 : ‖R (uSeq n-u)‖^2=‖action ε hε h ((n:ℝ)+1) (by positivity) (R u)-R u‖^2 := by
    refine congrArg (fun z : Hilbert => ‖z‖^2) ?_
    exact ((R).map_sub (uSeq n) u).trans
      (congrArg (fun z : Hilbert => z-R u)
        (rootOutput_formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k u))
  have h3 : ‖PB (growingLift ε hε h hh hw m g k (uSeq n-u))‖^2=‖PB (pSeq n)-PB pu‖^2 := by
    refine congrArg (fun y : EnergyOutputSpace => ‖y‖^2) ?_
    have hl : growingLift ε hε h hh hw m g k (uSeq n-u)=pSeq n-pu :=
      (growingLift_sub ε hε h hb hh m g k (uSeq n) u).trans
        (congrArg (fun w : PV => w-pu)
          (growingLift_formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k u))
    exact (congrArg PB hl).trans ((PB).map_sub (pSeq n) pu)
  exact he.trans (congrArg₂ (·+·) h1 (congrArg₂ (·+·) h2 h3))

theorem energy_sequence_tendsto (u : GV) :
    Tendsto (fun n : ℕ =>
      ‖GB (formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k u)‖^2)
      atTop (𝓝 (‖GB u‖^2)) :=
  (((GB).continuous.tendsto u).comp
    (form_sequence_tendsto ε hε h hb hh m g k u)).norm.pow 2

#print axioms growing_output_norm_sq
#print axioms growing_form_norm_sq
#print axioms formAction_embedding
#print axioms rootOutput_formAction
#print axioms growingLift_formAction
#print axioms form_sequence_tendsto
#print axioms energy_sequence_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventGrowing
