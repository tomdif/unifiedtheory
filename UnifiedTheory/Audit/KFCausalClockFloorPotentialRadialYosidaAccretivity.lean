/- Unconditional linear and quadratic radial-Yosida and radial-resolvent
accretivity on the completed potential form and on the entire potential
Hamiltonian domain `Dom(P)`:
- For `|h| ≤ π * ε / 3`: `0 ≤ Re ⟨P x, M_N x⟩` and `0 ≤ Re ⟨P x, J_N x⟩`.
- For `|h| ≤ π * ε / 4` (and `|h| ≤ π * ε / 6`):
  `0 ≤ Re ⟨P x, M_N (M_N x)⟩` and `0 ≤ Re ⟨P x, J_N (J_N x)⟩`. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaQuarterStripSector
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotential
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotentialForm

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPotentialRadialYosidaAccretivity
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalJointGraphBoundedCorrection (outputMap)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaOrderedTransport (shift_bound shifted_accretive)
open KFCausalClockFloorRadialResolventRegularizer (action)
open KFCausalClockFloorRadialResolventSections (outputAction outputActionLp)
open KFCausalClockFloorRadialResolventPotential
  (yosidaOutputLp graph_action formAction formAction_embedding formAction_output)
open KFCausalClockFloorRadialYosidaQuarterStripSector
  (quarter_shift_bound quarter_le_third sixth_le_quarter
    shifted_sq_accretive resolvent_shifted_accretive resolvent_shifted_sq_accretive)

private theorem outputMap_accretive (S : Hilbert →L[ℂ] Hilbert)
    (hS : ∀ f : Hilbert, 0 ≤ (inner ℂ f (S f)).re)
    (w : Output (Fin 8) Hilbert) :
    0 ≤ (inner ℂ w (outputMap (fun _ : Fin 8 => S) w)).re := by
  rw [PiLp.inner_apply, Complex.re_sum]
  exact Finset.sum_nonneg (fun i _ => hS (w i))

private theorem outputMap_sq_accretive (S : Hilbert →L[ℂ] Hilbert)
    (hS : ∀ f : Hilbert, 0 ≤ (inner ℂ f (S (S f))).re)
    (w : Output (Fin 8) Hilbert) :
    0 ≤ (inner ℂ w
      (outputMap (fun _ : Fin 8 => S) (outputMap (fun _ : Fin 8 => S) w))).re := by
  rw [PiLp.inner_apply, Complex.re_sum]
  exact Finset.sum_nonneg (fun i _ => hS (w i))

private theorem outputLp_accretive_of_hilbert (S : Hilbert →L[ℂ] Hilbert)
    (hS : ∀ f : Hilbert, 0 ≤ (inner ℂ f (S f)).re)
    (z : EnergyOutputSpace) :
    0 ≤ (inner ℂ z
      ((outputMap (fun _ : Fin 8 => S)).compLpL 2 angleMeasure z)).re := by
  let R := outputMap (fun _ : Fin 8 => S)
  let L := R.compLpL 2 angleMeasure
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) z (L z))
  change (∫ θ, (inner ℂ (z θ) (L z θ)).re ∂angleMeasure) =
    (∫ θ, inner ℂ (z θ) (L z θ) ∂angleMeasure).re at he
  rw [L2.inner_def, ← he]
  apply integral_nonneg_of_ae
  filter_upwards [R.coeFn_compLp z] with θ hθ
  change R.compLp z θ = R (z θ) at hθ
  change 0 ≤ (inner ℂ (z θ) (R.compLp z θ)).re
  rw [hθ]
  exact outputMap_accretive S hS (z θ)

private theorem outputLp_sq_accretive_of_hilbert (S : Hilbert →L[ℂ] Hilbert)
    (hS : ∀ f : Hilbert, 0 ≤ (inner ℂ f (S (S f))).re)
    (z : EnergyOutputSpace) :
    0 ≤ (inner ℂ z
      ((outputMap (fun _ : Fin 8 => S)).compLpL 2 angleMeasure
        ((outputMap (fun _ : Fin 8 => S)).compLpL 2 angleMeasure z))).re := by
  let R := outputMap (fun _ : Fin 8 => S)
  let L := R.compLpL 2 angleMeasure
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) z (L (L z)))
  change (∫ θ, (inner ℂ (z θ) (L (L z) θ)).re ∂angleMeasure) =
    (∫ θ, inner ℂ (z θ) (L (L z) θ) ∂angleMeasure).re at he
  rw [L2.inner_def, ← he]
  apply integral_nonneg_of_ae
  filter_upwards [R.coeFn_compLp z, R.coeFn_compLp (L z)] with θ h1 h2
  change R.compLp z θ = R (z θ) at h1
  change R.compLp (L z) θ = R (L z θ) at h2
  change 0 ≤ (inner ℂ (z θ) (R.compLp (L z) θ)).re
  rw [h2]
  change 0 ≤ (inner ℂ (z θ) (R (R.compLp z θ))).re
  rw [h1]
  exact outputMap_sq_accretive S hS (z θ)

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi * ε / 3) (hh : h ≠ 0) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN
local notation "J" => action ε hε h N hN
local notation "A" => KFCausalClockFloorRadialYosidaOrderedTransport.shifted
  ε hε h N hN (-h / 2) (shift_bound ε h hb)
local notation "R" => outputMap (fun _ : Fin 8 => A)
local notation "L" => yosidaOutputLp ε hε h N hN hb
local notation "O" => outputActionLp ε hε h N hN (-h / 2) (shift_bound ε h hb)
local notation "T" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k

theorem output_complement (z : EnergyOutputSpace) :
    z - (N⁻¹ : ℂ) • L z = O z := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub z ((N⁻¹ : ℂ) • L z), Lp.coeFn_smul (N⁻¹ : ℂ) (L z),
    (R).coeFn_compLp z,
    (outputAction ε hε h N hN (-h / 2) (shift_bound ε h hb)).coeFn_compLp z]
      with θ hs hc hR hJ
  change (z - (N⁻¹ : ℂ) • L z) θ =
    (outputAction ε hε h N hN (-h / 2) (shift_bound ε h hb)).compLp z θ
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hc]
  simp only [Pi.smul_apply]
  change z θ - (N⁻¹ : ℂ) • (R).compLp z θ =
    (outputAction ε hε h N hN (-h / 2) (shift_bound ε h hb)).compLp z θ
  rw [hR, hJ]
  apply PiLp.ext
  intro i
  rfl

theorem yosida_from_resolvent_action (f : Hilbert) :
    (N : ℂ) • (f - J f) = M f := by
  change (N : ℂ) • (f - (f - (N⁻¹ : ℂ) • M f)) = M f
  rw [sub_sub_cancel, smul_smul]
  have hNne : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  rw [mul_inv_cancel₀ hNne, one_smul]

theorem yosidaOutputLp_from_outputActionLp (z : EnergyOutputSpace) :
    (N : ℂ) • (z - O z) = L z := by
  rw [← output_complement ε hε h N hN hb z, sub_sub_cancel, smul_smul]
  have hNne : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  rw [mul_inv_cancel₀ hNne, one_smul]

theorem yosida_graph (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f, z) ∈ (T).graph) : (M f, L z) ∈ (T).graph := by
  have hj := graph_action ε hε h N hN hb hh m g k f z hz
  have hsub := (T).graph.sub_mem hz hj
  have hsmul := (T).graph.smul_mem (N : ℂ) hsub
  change ((N : ℂ) • (f - J f), (N : ℂ) • (z - O z)) ∈ (T).graph at hsmul
  rwa [yosida_from_resolvent_action ε hε h N hN f,
    yosidaOutputLp_from_outputActionLp ε hε h N hN hb z] at hsmul

def yosidaFormAction : PV →L[ℂ] PV :=
  KFCausalClosedGraphDiagonalAction.action PD M L
    (yosida_graph ε hε h N hN hb hh m g k)

theorem yosidaFormAction_embedding (u : PV) :
    PJ (yosidaFormAction ε hε h N hN hb hh m g k u) = M (PJ u) := rfl

theorem yosidaFormAction_output (u : PV) :
    PB (yosidaFormAction ε hε h N hN hb hh m g k u) = L (PB u) := rfl

theorem yosidaOutputLp_accretive (z : EnergyOutputSpace) :
    0 ≤ (inner ℂ z (L z)).re :=
  outputLp_accretive_of_hilbert A
    (shifted_accretive ε hε h N hN (-h / 2) (shift_bound ε h hb)) z

theorem outputActionLp_accretive (z : EnergyOutputSpace) :
    0 ≤ (inner ℂ z (O z)).re :=
  outputLp_accretive_of_hilbert
    (KFCausalClockFloorRadialResolventShifted.shifted ε hε h N hN (-h / 2) (shift_bound ε h hb))
    (resolvent_shifted_accretive ε hε h N hN (-h / 2) (shift_bound ε h hb)) z

private theorem form_pairing
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (D : KFCausalClosedGraphForm.Data X Y) (dMap : X →L[ℂ] X) (lMap : Y →L[ℂ] Y)
    (F : KFCausalClosedGraphForm.FormSpace D →L[ℂ] KFCausalClosedGraphForm.FormSpace D)
    (hj : ∀ u, KFCausalClosedGraphForm.embedding D (F u) = dMap (KFCausalClosedGraphForm.embedding D u))
    (he : ∀ u, KFCausalClosedGraphForm.energyOutput D (F u) = lMap (KFCausalClosedGraphForm.energyOutput D u))
    (x : (KFCausalClosedGraphForm.hamiltonian D).domain) :
    inner ℂ (KFCausalClosedGraphForm.hamiltonian D x) (dMap (x : X)) =
      inner ℂ (KFCausalClosedGraphForm.energyOutput D (KFCausalClosedGraphForm.formLift D x))
        (lMap (KFCausalClosedGraphForm.energyOutput D (KFCausalClosedGraphForm.formLift D x))) := by
  have hpair := KFCausalClosedGraphForm.hamiltonian_represents_form D x
    (F (KFCausalClosedGraphForm.formLift D x))
  rw [hj, he, KFCausalClosedGraphForm.embedding_formLift] at hpair
  exact hpair.symm

private theorem form_sq_pairing
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (D : KFCausalClosedGraphForm.Data X Y) (dMap : X →L[ℂ] X) (lMap : Y →L[ℂ] Y)
    (F : KFCausalClosedGraphForm.FormSpace D →L[ℂ] KFCausalClosedGraphForm.FormSpace D)
    (hj : ∀ u, KFCausalClosedGraphForm.embedding D (F u) = dMap (KFCausalClosedGraphForm.embedding D u))
    (he : ∀ u, KFCausalClosedGraphForm.energyOutput D (F u) = lMap (KFCausalClosedGraphForm.energyOutput D u))
    (x : (KFCausalClosedGraphForm.hamiltonian D).domain) :
    inner ℂ (KFCausalClosedGraphForm.hamiltonian D x) (dMap (dMap (x : X))) =
      inner ℂ (KFCausalClosedGraphForm.energyOutput D (KFCausalClosedGraphForm.formLift D x))
        (lMap (lMap (KFCausalClosedGraphForm.energyOutput D (KFCausalClosedGraphForm.formLift D x)))) := by
  have hpair := KFCausalClosedGraphForm.hamiltonian_represents_form D x
    (F (F (KFCausalClosedGraphForm.formLift D x)))
  rw [hj, hj, he, he, KFCausalClosedGraphForm.embedding_formLift] at hpair
  exact hpair.symm

private theorem form_accretive
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (D : KFCausalClosedGraphForm.Data X Y) (dMap : X →L[ℂ] X) (lMap : Y →L[ℂ] Y)
    (F : KFCausalClosedGraphForm.FormSpace D →L[ℂ] KFCausalClosedGraphForm.FormSpace D)
    (hj : ∀ u, KFCausalClosedGraphForm.embedding D (F u) = dMap (KFCausalClosedGraphForm.embedding D u))
    (he : ∀ u, KFCausalClosedGraphForm.energyOutput D (F u) = lMap (KFCausalClosedGraphForm.energyOutput D u))
    (hp : ∀ y, 0 ≤ (inner ℂ y (lMap y)).re)
    (x : (KFCausalClosedGraphForm.hamiltonian D).domain) :
    0 ≤ (inner ℂ (KFCausalClosedGraphForm.hamiltonian D x) (dMap (x : X))).re := by
  rw [form_pairing D dMap lMap F hj he x]
  exact hp _

private theorem form_sq_accretive
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (D : KFCausalClosedGraphForm.Data X Y) (dMap : X →L[ℂ] X) (lMap : Y →L[ℂ] Y)
    (F : KFCausalClosedGraphForm.FormSpace D →L[ℂ] KFCausalClosedGraphForm.FormSpace D)
    (hj : ∀ u, KFCausalClosedGraphForm.embedding D (F u) = dMap (KFCausalClosedGraphForm.embedding D u))
    (he : ∀ u, KFCausalClosedGraphForm.energyOutput D (F u) = lMap (KFCausalClosedGraphForm.energyOutput D u))
    (hp : ∀ y, 0 ≤ (inner ℂ y (lMap (lMap y))).re)
    (x : (KFCausalClosedGraphForm.hamiltonian D).domain) :
    0 ≤ (inner ℂ (KFCausalClosedGraphForm.hamiltonian D x) (dMap (dMap (x : X)))).re := by
  rw [form_sq_pairing D dMap lMap F hj he x]
  exact hp _

theorem potential_form_yosida_pairing (x : (P).domain) :
    inner ℂ (P x) (M (x : Hilbert)) =
      inner ℂ (PB (KFCausalClosedGraphForm.formLift PD x))
        (L (PB (KFCausalClosedGraphForm.formLift PD x))) :=
  form_pairing PD M L (yosidaFormAction ε hε h N hN hb hh m g k)
    (yosidaFormAction_embedding ε hε h N hN hb hh m g k)
    (yosidaFormAction_output ε hε h N hN hb hh m g k) x

theorem potential_form_resolvent_pairing (x : (P).domain) :
    inner ℂ (P x) (J (x : Hilbert)) =
      inner ℂ (PB (KFCausalClosedGraphForm.formLift PD x))
        (O (PB (KFCausalClosedGraphForm.formLift PD x))) :=
  form_pairing PD J O (formAction ε hε h N hN hb hh m g k)
    (formAction_embedding ε hε h N hN hb hh m g k)
    (formAction_output ε hε h N hN hb hh m g k) x

theorem potential_form_yosida_sq_pairing (x : (P).domain) :
    inner ℂ (P x) (M (M (x : Hilbert))) =
      inner ℂ (PB (KFCausalClosedGraphForm.formLift PD x))
        (L (L (PB (KFCausalClosedGraphForm.formLift PD x)))) :=
  form_sq_pairing PD M L (yosidaFormAction ε hε h N hN hb hh m g k)
    (yosidaFormAction_embedding ε hε h N hN hb hh m g k)
    (yosidaFormAction_output ε hε h N hN hb hh m g k) x

theorem potential_form_resolvent_sq_pairing (x : (P).domain) :
    inner ℂ (P x) (J (J (x : Hilbert))) =
      inner ℂ (PB (KFCausalClosedGraphForm.formLift PD x))
        (O (O (PB (KFCausalClosedGraphForm.formLift PD x)))) :=
  form_sq_pairing PD J O (formAction ε hε h N hN hb hh m g k)
    (formAction_embedding ε hε h N hN hb hh m g k)
    (formAction_output ε hε h N hN hb hh m g k) x

theorem potential_yosida_accretive (x : (P).domain) :
    0 ≤ (inner ℂ (P x) (M (x : Hilbert))).re :=
  form_accretive PD M L (yosidaFormAction ε hε h N hN hb hh m g k)
    (yosidaFormAction_embedding ε hε h N hN hb hh m g k)
    (yosidaFormAction_output ε hε h N hN hb hh m g k)
    (yosidaOutputLp_accretive ε hε h N hN hb) x

theorem potential_resolvent_accretive (x : (P).domain) :
    0 ≤ (inner ℂ (P x) (J (x : Hilbert))).re :=
  form_accretive PD J O (formAction ε hε h N hN hb hh m g k)
    (formAction_embedding ε hε h N hN hb hh m g k)
    (formAction_output ε hε h N hN hb hh m g k)
    (outputActionLp_accretive ε hε h N hN hb) x

theorem yosidaOutputLp_sq_accretive (hq : |h| ≤ Real.pi * ε / 4) (z : EnergyOutputSpace) :
    0 ≤ (inner ℂ z (L (L z))).re :=
  outputLp_sq_accretive_of_hilbert A
    (shifted_sq_accretive ε hε h N hN (-h / 2)
      (shift_bound ε h hb) (quarter_shift_bound ε h hq)) z

theorem outputActionLp_sq_accretive (hq : |h| ≤ Real.pi * ε / 4) (z : EnergyOutputSpace) :
    0 ≤ (inner ℂ z (O (O z))).re :=
  outputLp_sq_accretive_of_hilbert
    (KFCausalClockFloorRadialResolventShifted.shifted ε hε h N hN (-h / 2) (shift_bound ε h hb))
    (resolvent_shifted_sq_accretive ε hε h N hN (-h / 2)
      (shift_bound ε h hb) (quarter_shift_bound ε h hq)) z

theorem potential_yosida_sq_accretive (hq : |h| ≤ Real.pi * ε / 4) (x : (P).domain) :
    0 ≤ (inner ℂ (P x) (M (M (x : Hilbert)))).re :=
  form_sq_accretive PD M L (yosidaFormAction ε hε h N hN hb hh m g k)
    (yosidaFormAction_embedding ε hε h N hN hb hh m g k)
    (yosidaFormAction_output ε hε h N hN hb hh m g k)
    (yosidaOutputLp_sq_accretive ε hε h N hN hb hq) x

theorem potential_resolvent_sq_accretive (hq : |h| ≤ Real.pi * ε / 4) (x : (P).domain) :
    0 ≤ (inner ℂ (P x) (J (J (x : Hilbert)))).re :=
  form_sq_accretive PD J O (formAction ε hε h N hN hb hh m g k)
    (formAction_embedding ε hε h N hN hb hh m g k)
    (formAction_output ε hε h N hN hb hh m g k)
    (outputActionLp_sq_accretive ε hε h N hN hb hq) x

theorem potential_yosida_sq_accretive_sixth (hs : |h| ≤ Real.pi * ε / 6) (x : (P).domain) :
    0 ≤ (inner ℂ (P x) (M (M (x : Hilbert)))).re :=
  potential_yosida_sq_accretive ε hε h N hN hb hh m g k (sixth_le_quarter ε hε h hs) x

theorem potential_resolvent_sq_accretive_sixth (hs : |h| ≤ Real.pi * ε / 6) (x : (P).domain) :
    0 ≤ (inner ℂ (P x) (J (J (x : Hilbert)))).re :=
  potential_resolvent_sq_accretive ε hε h N hN hb hh m g k (sixth_le_quarter ε hε h hs) x

#print axioms output_complement
#print axioms yosida_from_resolvent_action
#print axioms yosidaOutputLp_from_outputActionLp
#print axioms yosida_graph
#print axioms yosidaFormAction_embedding
#print axioms yosidaFormAction_output
#print axioms yosidaOutputLp_accretive
#print axioms outputActionLp_accretive
#print axioms potential_form_yosida_pairing
#print axioms potential_form_resolvent_pairing
#print axioms potential_form_yosida_sq_pairing
#print axioms potential_form_resolvent_sq_pairing
#print axioms potential_yosida_accretive
#print axioms potential_resolvent_accretive
#print axioms yosidaOutputLp_sq_accretive
#print axioms outputActionLp_sq_accretive
#print axioms potential_yosida_sq_accretive
#print axioms potential_resolvent_sq_accretive
#print axioms potential_yosida_sq_accretive_sixth
#print axioms potential_resolvent_sq_accretive_sixth
end
end UnifiedTheory.Audit.KFCausalClockFloorPotentialRadialYosidaAccretivity
