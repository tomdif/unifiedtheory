/- Unconditional Two-Time Form and Resolvent Pairing Comparison for all real
couplings: exact sesquilinear two-time form difference identities on the
completed full and residual form spaces, exact two-time operator-domain pairing
identities for H(t) against H(s) and S(t) against S(s), and exact two-time
resolvent matrix-element difference identities for R_{H(t)}(a) against
R_{H(s)}(a) and R_{S(t)}(a) against R_{S(s)}(a). -/
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormTransfer
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialSum
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianClockCore
import UnifiedTheory.Audit.KFCausalClockFloorResidualClockCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormResolventComparison
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp growingOutputLp
  timeOutputLp_inner)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorChartPhasePairing (orderedOutput orderedOutputLp)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOutput rootOutput_inner)
open KFCausalClockFloorPotentialHamiltonian (growingLift growingLift_embedding growingLift_output)
open KFCausalClockFloorResidualFormSplit (potentialLift potentialLift_embedding)
open KFCausalClockFloorTwoTimeFormTransfer (residualFormTransfer
  residualFormTransfer_embedding residualFormTransfer_inverse
  potentialLift_residualFormTransfer two_time_residual_inner_difference
  growingProject residualProject growingProject_formTransfer residualProject_formTransfer)
open KFCausalPositiveResolventBounds (point point_value)
open KFCausalUnitIntervalOrbit (angleMeasure)

private theorem complex_split_diff (a b c d : ℂ) (t s : ℝ)
    (ht : a=c+(Real.exp (2*t):ℂ)*d) (hs : b=c+(Real.exp (2*s):ℂ)*d) :
    a-b=((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*d := by
  rw [ht,hs,Complex.ofReal_sub]
  ring

private theorem exp_sub_zero_complex_mul (t : ℝ) (z : ℂ) :
    (Real.exp (2*(t-0)):ℂ)*z=(Real.exp (2*t):ℂ)*z := by
  rw [sub_zero]

private theorem inner_right_of_represents {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (x hy : Hilbert) (v1 v2 : K)
    (hrep : inner ℂ v2 v1=inner ℂ hy x) :
    inner ℂ x hy=inner ℂ v1 v2 := by
  rw [← inner_conj_symm x hy,← hrep,inner_conj_symm v1 v2]

private theorem sub_of_eq_pair (a b c d r : ℂ)
    (h1 : a=c) (h2 : b=d) (hdiff : c-d=r) : a-b=r := by
  rw [h1,h2,hdiff]

private theorem resolvent_pairing_diff_eq (f1 f2 rx ry hx hy : Hilbert) (a : ℝ)
    (ht : hx=f1-a • rx) (hs : hy=f2-a • ry) :
    inner ℂ f1 ry-inner ℂ rx f2=inner ℂ hx ry-inner ℂ rx hy := by
  rw [ht,hs,inner_sub_left,inner_sub_right,
    inner_smul_left_eq_smul,inner_smul_right_eq_smul]
  abel

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

private theorem inner_components (f1 f2 : EnergyOutputSpace) :
    inner ℂ f1 f2=∑ i : Fin 8, inner ℂ (coordinateLp i f1) (coordinateLp i f2) := by
  have he : (fun θ => inner ℂ (f1 θ) (f2 θ)) =ᵐ[angleMeasure]
      fun θ => ∑ i : Fin 8, inner ℂ (coordinateLp i f1 θ) (coordinateLp i f2 θ) := by
    filter_upwards [Filter.eventually_all.mpr (fun i : Fin 8 => (coordinate i).coeFn_compLp f1),
      Filter.eventually_all.mpr (fun i : Fin 8 => (coordinate i).coeFn_compLp f2)] with θ hf1 hf2
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg₂ (inner ℂ) (hf1 i).symm (hf2 i).symm
  rw [L2.inner_def,integral_congr_ae he,integral_finset_sum Finset.univ]
  · rfl
  · intro i _
    exact L2.integrable_inner (𝕜 := ℂ) (coordinateLp i f1) (coordinateLp i f2)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "AD" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hw m g k
local notation "VT" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k
local notation "AJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k
local notation "AT" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k
local notation "FT" => KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hw m g k
local notation "SJ" => fun t => KFCausalClosedGraphForm.embedding (SD t)
local notation "SB" => fun t => KFCausalClosedGraphForm.energyOutput (SD t)
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "GV" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hw m g k
local notation "GJ" => KFCausalClosedGraphForm.embedding GD
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD
local notation "R" => rootOutput ε hε h hh hw m g k
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD

private theorem static_coordinate_zero (u : GV) (i : Fin 8) (hi : i.val<3) :
    coordinateLp i (GB u)=0 := by
  have hg := u.property
  change (GJ u,GB u) ∈ (KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k).graph at hg
  rw [KFCausalClockFloorGrowingOutputClosure.operator_graph] at hg
  have hc := KFCausalClockFloorGrowingOutputClosure.closure_component ε hε h hh hw m g k
    (GJ u,GB u) hg i
  exact (KFCausalClockFloorOrbitFactorGraphs.factorOperator ε hε h i).graph_fst_eq_zero_snd hc
    (by simp only [KFCausalClockFloorOrbitFactorGraphs.growingWeight,hi,if_true,zero_smul,map_zero])

theorem growing_output_inner_split (u v : GV) :
    inner ℂ (GB u) (GB v)=inner ℂ (R u) (R v)+
      inner ℂ (PB (growingLift ε hε h hh hw m g k u))
        (PB (growingLift ε hε h hh hw m g k v)) := by
  have h0 := static_coordinate_zero ε hε h hh hb m g k u 0 (by decide)
  have h1 := static_coordinate_zero ε hε h hh hb m g k u 1 (by decide)
  have h2 := static_coordinate_zero ε hε h hh hb m g k u 2 (by decide)
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
  have ho : inner ℂ (orderedOutputLp (GB u)) (orderedOutputLp (GB v))=
      inner ℂ (PB (growingLift ε hε h hh hw m g k u))
        (PB (growingLift ε hε h hh hw m g k v)) :=
    congrArg₂ (inner ℂ) (growingLift_output ε hε h hh hw m g k u).symm
      (growingLift_output ε hε h hh hw m g k v).symm
  exact (he.trans (congrArg (fun z : ℂ => z+
    inner ℂ (orderedOutputLp (GB u)) (orderedOutputLp (GB v))) hr.symm)).trans
    (congrArg (fun z : ℂ => inner ℂ (R u) (R v)+z) ho)

private theorem growingLift_growingProject_eq (s : ℝ) (u : VT s) :
    growingLift ε hε h hh hw m g k (growingProject ε hε h hh hb m g k s u)=
      potentialLift ε hε h hh hw m g k s (residualProject ε hε h hh hb m g k s u) := by
  apply KFCausalClosedGraphForm.embedding_injective PD
  exact (growingLift_embedding ε hε h hh hw m g k
    (growingProject ε hε h hh hb m g k s u)).trans
    ((KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding
      ε hε h hh hw m g k (FT s 0 u)).trans
      ((KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding
        ε hε h hh hw m g k s (FT s 0 u)).symm.trans
        (potentialLift_embedding ε hε h hh hw m g k s
          (residualProject ε hε h hh hb m g k s u)).symm))

theorem growingProject_inner_split (t s : ℝ) (ut : VT t) (us : VT s) :
    inner ℂ (GB (growingProject ε hε h hh hb m g k t ut))
      (GB (growingProject ε hε h hh hb m g k s us))=
      inner ℂ (R (growingProject ε hε h hh hb m g k t ut))
        (R (growingProject ε hε h hh hb m g k s us))+
      inner ℂ (PB (potentialLift ε hε h hh hw m g k t
        (residualProject ε hε h hh hb m g k t ut)))
        (PB (potentialLift ε hε h hh hw m g k s
          (residualProject ε hε h hh hb m g k s us))) := by
  have h1 := growing_output_inner_split ε hε h hh hb m g k
    (growingProject ε hε h hh hb m g k t ut)
    (growingProject ε hε h hh hb m g k s us)
  have hp : inner ℂ (PB (growingLift ε hε h hh hw m g k
      (growingProject ε hε h hh hb m g k t ut)))
      (PB (growingLift ε hε h hh hw m g k
        (growingProject ε hε h hh hb m g k s us)))=
      inner ℂ (PB (potentialLift ε hε h hh hw m g k t
        (residualProject ε hε h hh hb m g k t ut)))
        (PB (potentialLift ε hε h hh hw m g k s
          (residualProject ε hε h hh hb m g k s us))) :=
    congrArg₂ (inner ℂ)
      (congrArg PB (growingLift_growingProject_eq ε hε h hh hb m g k t ut))
      (congrArg PB (growingLift_growingProject_eq ε hε h hh hb m g k s us))
  exact h1.trans (congrArg (fun z : ℂ =>
    inner ℂ (R (growingProject ε hε h hh hb m g k t ut))
      (R (growingProject ε hε h hh hb m g k s us))+z) hp)

private theorem averaged_output_inner_at_time (t s : ℝ) (u1 u2 : VT s) :
    inner ℂ (AT t (FT s t u1)) (AT t (FT s t u2))=
      inner ℂ (staticOutputLp (AT 0 (FT s 0 u1))) (staticOutputLp (AT 0 (FT s 0 u2)))+
        (Real.exp (2*t):ℂ)*inner ℂ (GB (growingProject ε hε h hh hb m g k s u1))
          (GB (growingProject ε hε h hh hb m g k s u2)) := by
  let u10 := FT s 0 u1
  let u20 := FT s 0 u2
  have hft1 : FT s t u1=FT 0 t u10 :=
    (KFCausalClockFloorAveragedFormTransport.transfer_comp ε hε h hh hw m g k s 0 t u1).symm
  have hft2 : FT s t u2=FT 0 t u20 :=
    (KFCausalClockFloorAveragedFormTransport.transfer_comp ε hε h hh hw m g k s 0 t u2).symm
  have hat1 : AT t (FT s t u1)=timeOutputLp 0 t (AT 0 u10) :=
    (congrArg (AT t) hft1).trans
      (KFCausalClockFloorAveragedFormTransport.transfer_energyOutput ε hε h hh hw m g k 0 t u10)
  have hat2 : AT t (FT s t u2)=timeOutputLp 0 t (AT 0 u20) :=
    (congrArg (AT t) hft2).trans
      (KFCausalClockFloorAveragedFormTransport.transfer_energyOutput ε hε h hh hw m g k 0 t u20)
  have hinner : inner ℂ (AT t (FT s t u1)) (AT t (FT s t u2))=
      inner ℂ (timeOutputLp 0 t (AT 0 u10)) (timeOutputLp 0 t (AT 0 u20)) :=
    congrArg₂ (inner ℂ) hat1 hat2
  have hgb1 : GB (growingProject ε hε h hh hb m g k s u1)=growingOutputLp (AT 0 u10) :=
    (KFCausalClockFloorGrowingHamiltonian.referenceLift_output ε hε h hh hw m g k u10).trans
      (ContinuousLinearMap.comp_apply growingOutputLp (AT 0) u10)
  have hgb2 : GB (growingProject ε hε h hh hb m g k s u2)=growingOutputLp (AT 0 u20) :=
    (KFCausalClockFloorGrowingHamiltonian.referenceLift_output ε hε h hh hw m g k u20).trans
      (ContinuousLinearMap.comp_apply growingOutputLp (AT 0) u20)
  have hg_inner : inner ℂ (growingOutputLp (AT 0 u10)) (growingOutputLp (AT 0 u20))=
      inner ℂ (GB (growingProject ε hε h hh hb m g k s u1))
        (GB (growingProject ε hε h hh hb m g k s u2)) :=
    congrArg₂ (inner ℂ) hgb1.symm hgb2.symm
  exact (hinner.trans (timeOutputLp_inner 0 t (AT 0 u10) (AT 0 u20))).trans
    (congrArg (fun z : ℂ =>
      inner ℂ (staticOutputLp (AT 0 u10)) (staticOutputLp (AT 0 u20))+z)
      ((exp_sub_zero_complex_mul t
        (inner ℂ (growingOutputLp (AT 0 u10)) (growingOutputLp (AT 0 u20)))).trans
        (congrArg ((Real.exp (2*t):ℂ)*·) hg_inner)))

theorem two_time_averaged_growing_inner_difference (t s : ℝ) (u1 u2 : VT s) :
    inner ℂ (AT t (FT s t u1)) (AT t (FT s t u2))-inner ℂ (AT s u1) (AT s u2)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*
        inner ℂ (GB (growingProject ε hε h hh hb m g k s u1))
          (GB (growingProject ε hε h hh hb m g k s u2)) := by
  have ht := averaged_output_inner_at_time ε hε h hh hb m g k t s u1 u2
  have hs0 := averaged_output_inner_at_time ε hε h hh hb m g k s s u1 u2
  have hself : inner ℂ (AT s (FT s s u1)) (AT s (FT s s u2))=inner ℂ (AT s u1) (AT s u2) :=
    congrArg₂ (inner ℂ)
      (congrArg (AT s) (KFCausalClockFloorAveragedFormTransport.transfer_self ε hε h hh hw m g k s u1))
      (congrArg (AT s) (KFCausalClockFloorAveragedFormTransport.transfer_self ε hε h hh hw m g k s u2))
  have hs := hself.symm.trans hs0
  exact complex_split_diff _ _ _ _ t s ht hs

theorem two_time_averaged_inner_difference (t s : ℝ) (u1 u2 : VT s) :
    inner ℂ (AT t (FT s t u1)) (AT t (FT s t u2))-inner ℂ (AT s u1) (AT s u2)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*
        (inner ℂ (R (growingProject ε hε h hh hb m g k s u1))
          (R (growingProject ε hε h hh hb m g k s u2))+
        inner ℂ (PB (potentialLift ε hε h hh hw m g k s
          (residualProject ε hε h hh hb m g k s u1)))
          (PB (potentialLift ε hε h hh hw m g k s
            (residualProject ε hε h hh hb m g k s u2)))) :=
  (two_time_averaged_growing_inner_difference ε hε h hh hb m g k t s u1 u2).trans
    (congrArg (((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*·)
      (growingProject_inner_split ε hε h hh hb m g k s s u1 u2))

theorem residual_two_time_form_pairing (t s : ℝ) (x : (S t).domain)
    (wt : SV t) (ws : SV s) (hwt : SJ t wt=(x:Hilbert)) :
    inner ℂ (S t x) (SJ s ws)=
      inner ℂ (SB t wt) (SB t (residualFormTransfer ε hε h hh hb m g k s t ws)) := by
  let ws_t := residualFormTransfer ε hε h hh hb m g k s t ws
  have hlx : KFCausalClosedGraphForm.formLift (SD t) x=wt :=
    KFCausalClosedGraphForm.embedding_injective (SD t)
      ((KFCausalClosedGraphForm.embedding_formLift (SD t) x).trans hwt.symm)
  have hrep := KFCausalClosedGraphForm.hamiltonian_represents_form (SD t) x ws_t
  have h1 : inner ℂ (SB t (KFCausalClosedGraphForm.formLift (SD t) x)) (SB t ws_t)=
      inner ℂ (SB t wt) (SB t ws_t) :=
    congrArg (fun z => inner ℂ (SB t z) (SB t ws_t)) hlx
  have h2 : inner ℂ (S t x) (SJ t ws_t)=inner ℂ (S t x) (SJ s ws) :=
    congrArg (inner ℂ (S t x)) (residualFormTransfer_embedding ε hε h hh hb m g k s t ws)
  exact h2.symm.trans (hrep.symm.trans h1)

theorem residual_two_time_domain_pairing_difference (t s : ℝ)
    (x : (S t).domain) (y : (S s).domain) (wt : SV t) (ws : SV s)
    (hwt : SJ t wt=(x:Hilbert)) (hws : SJ s ws=(y:Hilbert)) :
    inner ℂ (S t x) (y:Hilbert)-inner ℂ (x:Hilbert) (S s y)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*
        inner ℂ (PB (potentialLift ε hε h hh hw m g k t wt))
          (PB (potentialLift ε hε h hh hw m g k s ws)) := by
  let wt_s := residualFormTransfer ε hε h hh hb m g k t s wt
  let ws_t := residualFormTransfer ε hε h hh hb m g k s t ws
  have h1_0 := residual_two_time_form_pairing ε hε h hh hb m g k t s x wt ws hwt
  have h1_y : inner ℂ (S t x) (y:Hilbert)=inner ℂ (S t x) (SJ s ws) :=
    congrArg (inner ℂ (S t x)) hws.symm
  have h1_inv : inner ℂ (SB t wt) (SB t ws_t)=
      inner ℂ (SB t (residualFormTransfer ε hε h hh hb m g k s t wt_s)) (SB t ws_t) :=
    congrArg (fun z => inner ℂ (SB t z) (SB t ws_t))
      (residualFormTransfer_inverse ε hε h hh hb m g k t s wt).symm
  have h1 := h1_y.trans (h1_0.trans h1_inv)
  have h2_0 := residual_two_time_form_pairing ε hε h hh hb m g k s t y ws wt hws
  have h2_x : inner ℂ (S s y) (SJ t wt)=inner ℂ (S s y) (x:Hilbert) :=
    congrArg (inner ℂ (S s y)) hwt
  have h2 := inner_right_of_represents (x:Hilbert) (S s y) (SB s wt_s) (SB s ws)
    (h2_0.symm.trans h2_x)
  have hdiff := two_time_residual_inner_difference ε hε h hh hb m g k t s wt_s ws
  have hpot : inner ℂ (PB (potentialLift ε hε h hh hw m g k s wt_s))
      (PB (potentialLift ε hε h hh hw m g k s ws))=
      inner ℂ (PB (potentialLift ε hε h hh hw m g k t wt))
        (PB (potentialLift ε hε h hh hw m g k s ws)) :=
    congrArg (fun z => inner ℂ (PB z) (PB (potentialLift ε hε h hh hw m g k s ws)))
      (potentialLift_residualFormTransfer ε hε h hh hb m g k t s wt)
  exact sub_of_eq_pair _ _ _ _ _ h1 h2
    (hdiff.trans (congrArg (((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*·) hpot))

theorem residual_two_time_formLift_pairing_difference (t s : ℝ)
    (x : (S t).domain) (y : (S s).domain) :
    inner ℂ (S t x) (y:Hilbert)-inner ℂ (x:Hilbert) (S s y)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*
        inner ℂ (PB (potentialLift ε hε h hh hw m g k t
          (KFCausalClosedGraphForm.formLift (SD t) x)))
          (PB (potentialLift ε hε h hh hw m g k s
            (KFCausalClosedGraphForm.formLift (SD s) y))) :=
  residual_two_time_domain_pairing_difference ε hε h hh hb m g k t s x y
    (KFCausalClosedGraphForm.formLift (SD t) x)
    (KFCausalClosedGraphForm.formLift (SD s) y)
    (KFCausalClosedGraphForm.embedding_formLift (SD t) x)
    (KFCausalClosedGraphForm.embedding_formLift (SD s) y)

theorem residual_resolvent_two_time_pairing_difference (t s a : ℝ) (ha : 0 < a)
    (f1 f2 : Hilbert) (wt : SV t) (ws : SV s)
    (hwt : SJ t wt=RS t a f1) (hws : SJ s ws=RS s a f2) :
    inner ℂ f1 (RS s a f2)-inner ℂ (RS t a f1) f2=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*
        inner ℂ (PB (potentialLift ε hε h hh hw m g k t wt))
          (PB (potentialLift ε hε h hh hw m g k s ws)) := by
  let hrt := KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha
  let hrs := KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k s a ha
  let x := point (S t) (RS t a) a hrt f1
  let y := point (S s) (RS s a) a hrs f2
  have h1 := resolvent_pairing_diff_eq f1 f2 (RS t a f1) (RS s a f2) (S t x) (S s y) a
    (point_value (S t) (RS t a) a hrt f1) (point_value (S s) (RS s a) a hrs f2)
  exact h1.trans
    (residual_two_time_domain_pairing_difference ε hε h hh hb m g k t s x y wt ws hwt hws)

theorem residual_resolvent_two_time_formLift_pairing_difference (t s a : ℝ) (ha : 0 < a)
    (f1 f2 : Hilbert) :
    inner ℂ f1 (RS s a f2)-inner ℂ (RS t a f1) f2=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*
        inner ℂ (PB (potentialLift ε hε h hh hw m g k t
          (KFCausalClosedGraphForm.formLift (SD t)
            (point (S t) (RS t a) a
              (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha) f1))))
          (PB (potentialLift ε hε h hh hw m g k s
            (KFCausalClosedGraphForm.formLift (SD s)
              (point (S s) (RS s a) a
                (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k s a ha) f2)))) :=
  let hrt := KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha
  let hrs := KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k s a ha
  let x := point (S t) (RS t a) a hrt f1
  let y := point (S s) (RS s a) a hrs f2
  residual_resolvent_two_time_pairing_difference ε hε h hh hb m g k t s a ha f1 f2
    (KFCausalClosedGraphForm.formLift (SD t) x)
    (KFCausalClosedGraphForm.formLift (SD s) y)
    (KFCausalClosedGraphForm.embedding_formLift (SD t) x)
    (KFCausalClosedGraphForm.embedding_formLift (SD s) y)

theorem hamiltonian_two_time_form_pairing (t s : ℝ) (x : (H t).domain)
    (ut : VT t) (us : VT s) (hut : AJ t ut=(x:Hilbert)) :
    inner ℂ (H t x) (AJ s us)=
      inner ℂ (AT t ut) (AT t (FT s t us)) := by
  let us_t := FT s t us
  have hlx : KFCausalClosedGraphForm.formLift (AD t) x=ut :=
    KFCausalClosedGraphForm.embedding_injective (AD t)
      ((KFCausalClosedGraphForm.embedding_formLift (AD t) x).trans hut.symm)
  have hrep := KFCausalClosedGraphForm.hamiltonian_represents_form (AD t) x us_t
  have h1 : inner ℂ (AT t (KFCausalClosedGraphForm.formLift (AD t) x)) (AT t us_t)=
      inner ℂ (AT t ut) (AT t us_t) :=
    congrArg (fun z => inner ℂ (AT t z) (AT t us_t)) hlx
  have h2 : inner ℂ (H t x) (AJ t us_t)=inner ℂ (H t x) (AJ s us) :=
    congrArg (inner ℂ (H t x))
      (KFCausalClockFloorAveragedFormTransport.transfer_embedding ε hε h hh hw m g k s t us)
  exact h2.symm.trans (hrep.symm.trans h1)

theorem hamiltonian_two_time_growing_domain_pairing_difference (t s : ℝ)
    (x : (H t).domain) (y : (H s).domain) (ut : VT t) (us : VT s)
    (hut : AJ t ut=(x:Hilbert)) (hus : AJ s us=(y:Hilbert)) :
    inner ℂ (H t x) (y:Hilbert)-inner ℂ (x:Hilbert) (H s y)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*
        inner ℂ (GB (growingProject ε hε h hh hb m g k t ut))
          (GB (growingProject ε hε h hh hb m g k s us)) := by
  let ut_s := FT t s ut
  let us_t := FT s t us
  have h1_0 := hamiltonian_two_time_form_pairing ε hε h hh hb m g k t s x ut us hut
  have h1_y : inner ℂ (H t x) (y:Hilbert)=inner ℂ (H t x) (AJ s us) :=
    congrArg (inner ℂ (H t x)) hus.symm
  have h1_inv : inner ℂ (AT t ut) (AT t us_t)=
      inner ℂ (AT t (FT s t ut_s)) (AT t us_t) :=
    congrArg (fun z => inner ℂ (AT t z) (AT t us_t))
      (KFCausalClockFloorAveragedFormTransport.transfer_inverse ε hε h hh hw m g k t s ut).symm
  have h1 := h1_y.trans (h1_0.trans h1_inv)
  have h2_0 := hamiltonian_two_time_form_pairing ε hε h hh hb m g k s t y us ut hus
  have h2_x : inner ℂ (H s y) (AJ t ut)=inner ℂ (H s y) (x:Hilbert) :=
    congrArg (inner ℂ (H s y)) hut
  have h2 := inner_right_of_represents (x:Hilbert) (H s y) (AT s ut_s) (AT s us)
    (h2_0.symm.trans h2_x)
  have hdiff := two_time_averaged_growing_inner_difference ε hε h hh hb m g k t s ut_s us
  have hgp : inner ℂ (GB (growingProject ε hε h hh hb m g k s ut_s))
      (GB (growingProject ε hε h hh hb m g k s us))=
      inner ℂ (GB (growingProject ε hε h hh hb m g k t ut))
        (GB (growingProject ε hε h hh hb m g k s us)) :=
    congrArg (fun z => inner ℂ (GB z) (GB (growingProject ε hε h hh hb m g k s us)))
      (growingProject_formTransfer ε hε h hh hb m g k t s ut)
  exact sub_of_eq_pair _ _ _ _ _ h1 h2
    (hdiff.trans (congrArg (((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*·) hgp))

theorem hamiltonian_two_time_domain_pairing_difference (t s : ℝ)
    (x : (H t).domain) (y : (H s).domain) (ut : VT t) (us : VT s)
    (hut : AJ t ut=(x:Hilbert)) (hus : AJ s us=(y:Hilbert)) :
    inner ℂ (H t x) (y:Hilbert)-inner ℂ (x:Hilbert) (H s y)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*
        (inner ℂ (R (growingProject ε hε h hh hb m g k t ut))
          (R (growingProject ε hε h hh hb m g k s us))+
        inner ℂ (PB (potentialLift ε hε h hh hw m g k t
          (residualProject ε hε h hh hb m g k t ut)))
          (PB (potentialLift ε hε h hh hw m g k s
            (residualProject ε hε h hh hb m g k s us)))) :=
  (hamiltonian_two_time_growing_domain_pairing_difference ε hε h hh hb m g k t s x y ut us hut hus).trans
    (congrArg (((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*·)
      (growingProject_inner_split ε hε h hh hb m g k t s ut us))

theorem hamiltonian_two_time_formLift_pairing_difference (t s : ℝ)
    (x : (H t).domain) (y : (H s).domain) :
    inner ℂ (H t x) (y:Hilbert)-inner ℂ (x:Hilbert) (H s y)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*
        (inner ℂ (R (growingProject ε hε h hh hb m g k t
          (KFCausalClosedGraphForm.formLift (AD t) x)))
          (R (growingProject ε hε h hh hb m g k s
            (KFCausalClosedGraphForm.formLift (AD s) y)))+
        inner ℂ (PB (potentialLift ε hε h hh hw m g k t
          (residualProject ε hε h hh hb m g k t
            (KFCausalClosedGraphForm.formLift (AD t) x))))
          (PB (potentialLift ε hε h hh hw m g k s
            (residualProject ε hε h hh hb m g k s
              (KFCausalClosedGraphForm.formLift (AD s) y))))) :=
  hamiltonian_two_time_domain_pairing_difference ε hε h hh hb m g k t s x y
    (KFCausalClosedGraphForm.formLift (AD t) x)
    (KFCausalClosedGraphForm.formLift (AD s) y)
    (KFCausalClosedGraphForm.embedding_formLift (AD t) x)
    (KFCausalClosedGraphForm.embedding_formLift (AD s) y)

theorem hamiltonian_resolvent_two_time_growing_pairing_difference (t s a : ℝ) (ha : 0 < a)
    (f1 f2 : Hilbert) (ut : VT t) (us : VT s)
    (hut : AJ t ut=RH t a f1) (hus : AJ s us=RH s a f2) :
    inner ℂ f1 (RH s a f2)-inner ℂ (RH t a f1) f2=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*
        inner ℂ (GB (growingProject ε hε h hh hb m g k t ut))
          (GB (growingProject ε hε h hh hb m g k s us)) := by
  let hrt := KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha
  let hrs := KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k s a ha
  let x := point (H t) (RH t a) a hrt f1
  let y := point (H s) (RH s a) a hrs f2
  have h1 := resolvent_pairing_diff_eq f1 f2 (RH t a f1) (RH s a f2) (H t x) (H s y) a
    (point_value (H t) (RH t a) a hrt f1) (point_value (H s) (RH s a) a hrs f2)
  exact h1.trans
    (hamiltonian_two_time_growing_domain_pairing_difference ε hε h hh hb m g k t s x y ut us hut hus)

theorem hamiltonian_resolvent_two_time_pairing_difference (t s a : ℝ) (ha : 0 < a)
    (f1 f2 : Hilbert) (ut : VT t) (us : VT s)
    (hut : AJ t ut=RH t a f1) (hus : AJ s us=RH s a f2) :
    inner ℂ f1 (RH s a f2)-inner ℂ (RH t a f1) f2=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*
        (inner ℂ (R (growingProject ε hε h hh hb m g k t ut))
          (R (growingProject ε hε h hh hb m g k s us))+
        inner ℂ (PB (potentialLift ε hε h hh hw m g k t
          (residualProject ε hε h hh hb m g k t ut)))
          (PB (potentialLift ε hε h hh hw m g k s
            (residualProject ε hε h hh hb m g k s us)))) :=
  (hamiltonian_resolvent_two_time_growing_pairing_difference ε hε h hh hb m g k t s a ha f1 f2 ut us hut hus).trans
    (congrArg (((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*·)
      (growingProject_inner_split ε hε h hh hb m g k t s ut us))

theorem hamiltonian_resolvent_two_time_formLift_pairing_difference (t s a : ℝ) (ha : 0 < a)
    (f1 f2 : Hilbert) :
    inner ℂ f1 (RH s a f2)-inner ℂ (RH t a f1) f2=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*
        (inner ℂ (R (growingProject ε hε h hh hb m g k t
          (KFCausalClosedGraphForm.formLift (AD t)
            (point (H t) (RH t a) a
              (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) f1))))
          (R (growingProject ε hε h hh hb m g k s
            (KFCausalClosedGraphForm.formLift (AD s)
              (point (H s) (RH s a) a
                (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k s a ha) f2))))+
        inner ℂ (PB (potentialLift ε hε h hh hw m g k t
          (residualProject ε hε h hh hb m g k t
            (KFCausalClosedGraphForm.formLift (AD t)
              (point (H t) (RH t a) a
                (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) f1)))))
          (PB (potentialLift ε hε h hh hw m g k s
            (residualProject ε hε h hh hb m g k s
              (KFCausalClosedGraphForm.formLift (AD s)
                (point (H s) (RH s a) a
                  (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k s a ha) f2)))))) :=
  let hrt := KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha
  let hrs := KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k s a ha
  let x := point (H t) (RH t a) a hrt f1
  let y := point (H s) (RH s a) a hrs f2
  hamiltonian_resolvent_two_time_pairing_difference ε hε h hh hb m g k t s a ha f1 f2
    (KFCausalClosedGraphForm.formLift (AD t) x)
    (KFCausalClosedGraphForm.formLift (AD s) y)
    (KFCausalClosedGraphForm.embedding_formLift (AD t) x)
    (KFCausalClosedGraphForm.embedding_formLift (AD s) y)

#print axioms growing_output_inner_split
#print axioms growingProject_inner_split
#print axioms two_time_averaged_growing_inner_difference
#print axioms two_time_averaged_inner_difference
#print axioms residual_two_time_form_pairing
#print axioms residual_two_time_domain_pairing_difference
#print axioms residual_two_time_formLift_pairing_difference
#print axioms residual_resolvent_two_time_pairing_difference
#print axioms residual_resolvent_two_time_formLift_pairing_difference
#print axioms hamiltonian_two_time_form_pairing
#print axioms hamiltonian_two_time_growing_domain_pairing_difference
#print axioms hamiltonian_two_time_domain_pairing_difference
#print axioms hamiltonian_two_time_formLift_pairing_difference
#print axioms hamiltonian_resolvent_two_time_growing_pairing_difference
#print axioms hamiltonian_resolvent_two_time_pairing_difference
#print axioms hamiltonian_resolvent_two_time_formLift_pairing_difference
end
end UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormResolventComparison
