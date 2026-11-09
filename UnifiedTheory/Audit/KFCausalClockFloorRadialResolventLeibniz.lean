/- The static symmetric-momentum Leibniz correction of the radial Yosida
action lifts to an L² circle-orbit section operator on the physical reference
form, is invariant under time rescaling and residual row selection, and its
resolvent-scaled 1/N contribution converges strongly to zero as N → ∞. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaReference
import UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumGraph
import UnifiedTheory.Audit.KFCausalClockFloorStaticPotentialOutputClosure

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventLeibniz
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalFiniteOutputRescaling (selected_apply)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp)
open KFCausalPhysicalEnergyTransport (staticOutput timeOutput timeOutput_apply)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorStaticPotentialOutputClosure (retained selectedOutput selectedOutputLp)
open KFCausalClockFloorOrbitVacuumGraph (OrbitSpace physicalOrbit physicalOrbit_coe)
open KFCausalClockFloorRadialYosidaKinetics (symmetricCorrection symmetricCorrection_norm correction)
open KFCausalClockFloorRadialYosidaEnergy (energy_bound factorCorrection)
open KFCausalClockFloorRadialYosidaForm (outputAction extra)
open KFCausalClockFloorRadialYosidaReference (wide_bound averagedAction averagedAction_embedding)
open KFCausalJointGraphBoundedCorrection (correctionMap)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalAveragedEnergyGraph (l2_norm_square)

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi*ε/3) (hne : h ≠ 0) (m g k t : ℝ)

theorem extra_time_zero (f : Hilbert) :
    extra ε hε h N hN m g k t f=extra ε hε h N hN m g k 0 f := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [extra,correctionMap,factorCorrection,correction,energyWeight]

theorem point_time_extra (f : Hilbert) :
    timeOutput 0 t (extra ε hε h N hN m g k 0 f)=extra ε hε h N hN m g k 0 f := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [timeOutput_apply,extra,correctionMap,factorCorrection,correction]

theorem point_selected_extra (f : Hilbert) :
    selectedOutput (extra ε hε h N hN m g k 0 f)=extra ε hε h N hN m g k 0 f := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [selectedOutput,selected_apply,retained,extra,
    correctionMap,factorCorrection,correction]

theorem point_static_extra (f : Hilbert) :
    staticOutput (extra ε hε h N hN m g k 0 f)=extra ε hε h N hN m g k 0 f := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [staticOutput,selected_apply,extra,
    correctionMap,factorCorrection,correction]

private theorem extra_apply (f : Hilbert) (i : Fin 8) :
    extra ε hε h N hN m g k t f i=
      energyWeight m g k t i • factorCorrection ε hε h N hN i f := rfl

theorem extra_norm_sq (f : Hilbert) :
    ‖extra ε hε h N hN m g k t f‖^2=
      (1/2)*‖symmetricCorrection ε hε h N hN 0 f‖^2+
      (1/2)*‖symmetricCorrection ε hε h N hN 1 f‖^2 := by
  have hs : ‖(Real.sqrt (1/2):ℂ)‖^2=1/2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_eight]
  simp only [extra_apply]
  change ‖energyWeight m g k t 0 • (0:Hilbert)‖^2+
    ‖(Real.sqrt (1/2):ℂ) • symmetricCorrection ε hε h N hN 0 f‖^2+
    ‖(Real.sqrt (1/2):ℂ) • symmetricCorrection ε hε h N hN 1 f‖^2+
    ‖energyWeight m g k t 3 • (0:Hilbert)‖^2+
    ‖energyWeight m g k t 4 • (0:Hilbert)‖^2+
    ‖energyWeight m g k t 5 • (0:Hilbert)‖^2+
    ‖energyWeight m g k t 6 • (0:Hilbert)‖^2+
    ‖energyWeight m g k t 7 • (0:Hilbert)‖^2=_
  simp only [smul_zero,norm_zero,norm_smul,mul_pow,hs]
  ring

theorem extra_norm (f : Hilbert) :
    ‖extra ε hε h N hN m g k t f‖ ≤
      (|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹)*‖f‖ := by
  let C := |h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹
  have hC : 0 ≤ C*‖f‖ := by positivity
  have h0 := symmetricCorrection_norm ε hε h N hN 0 f
  have h1 := symmetricCorrection_norm ε hε h N hN 1 f
  have h0s : ‖symmetricCorrection ε hε h N hN 0 f‖^2 ≤ (C*‖f‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) h0 2
  have h1s : ‖symmetricCorrection ε hε h N hN 1 f‖^2 ≤ (C*‖f‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hsq : ‖extra ε hε h N hN m g k t f‖^2 ≤ (C*‖f‖)^2 := by
    rw [extra_norm_sq]
    linarith
  exact ( abs_le_of_sq_le_sq' hsq hC ).2

def extraSection : OrbitSpace →L[ℂ] EnergyOutputSpace :=
  (extra ε hε h N hN m g k 0).compLpL 2 angleMeasure

def orbitExtra : Hilbert →L[ℂ] EnergyOutputSpace :=
  (extraSection ε hε h N hN m g k).comp (physicalOrbit h hne).toContinuousLinearMap

def scaledOrbitExtra : Hilbert →L[ℂ] EnergyOutputSpace :=
  (N⁻¹:ℂ) • orbitExtra ε hε h N hN hne m g k

def referenceOutputActionLp : EnergyOutputSpace →L[ℂ] EnergyOutputSpace :=
  (outputAction ε hε h N hN hb).compLpL 2 angleMeasure

theorem extraSection_norm (φ : OrbitSpace) :
    ‖extraSection ε hε h N hN m g k φ‖ ≤
      (|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹)*‖φ‖ := by
  let C := |h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹
  have hC : 0 ≤ C*‖φ‖ := by positivity
  have hφ : Integrable (fun θ => ‖φ θ‖^2) angleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable φ)).mp (Lp.memLp φ)
  have he : ∀ᵐ θ ∂angleMeasure,
      ‖extraSection ε hε h N hN m g k φ θ‖^2 ≤ C^2*‖φ θ‖^2 := by
    filter_upwards [(extra ε hε h N hN m g k 0).coeFn_compLp φ] with θ hθ
    change ‖(extra ε hε h N hN m g k 0).compLp φ θ‖^2 ≤ C^2*‖φ θ‖^2
    rw [hθ]
    exact (pow_le_pow_left₀ (norm_nonneg _) (extra_norm ε hε h N hN m g k 0 (φ θ)) 2).trans_eq
      (by ring)
  have hint : Integrable (fun θ => ‖extraSection ε hε h N hN m g k φ θ‖^2) angleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hsq : ‖extraSection ε hε h N hN m g k φ‖^2 ≤ (C*‖φ‖)^2 := by
    rw [l2_norm_square angleMeasure (extraSection ε hε h N hN m g k φ),
      mul_pow,l2_norm_square angleMeasure φ,← integral_const_mul]
    exact integral_mono_ae hint (hφ.const_mul (C^2)) he
  exact (abs_le_of_sq_le_sq' hsq hC).2

theorem orbitExtra_norm (f : Hilbert) :
    ‖orbitExtra ε hε h N hN hne m g k f‖ ≤
      (|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹)*‖f‖ := by
  simpa only [orbitExtra,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,LinearIsometry.norm_map] using
      extraSection_norm ε hε h N hN m g k (physicalOrbit h hne f)

theorem scaledOrbitExtra_norm (f : Hilbert) :
    ‖scaledOrbitExtra ε hε h N hN hne m g k f‖ ≤
      (N⁻¹*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹))*‖f‖ := by
  change ‖(N⁻¹:ℂ) • orbitExtra ε hε h N hN hne m g k f‖ ≤ _
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN,mul_assoc]
  exact mul_le_mul_of_nonneg_left (orbitExtra_norm ε hε h N hN hne m g k f) (inv_nonneg.mpr hN.le)

theorem scaledOrbitExtra_norm_sq (f : Hilbert) :
    ‖scaledOrbitExtra ε hε h N hN hne m g k f‖^2 ≤
      (h^2*‖f‖^2/ε^2)*N⁻¹ := by
  have hb0 := scaledOrbitExtra_norm ε hε h N hN hne m g k f
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb0 2
  have heq : ((N⁻¹*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹))*‖f‖)^2=
      (h^2*‖f‖^2/ε^2)*N⁻¹ := by
    simp only [mul_pow,inv_pow,sq_abs,
      Real.sq_sqrt (div_nonneg hN.le hε.le),Real.sq_sqrt hε.le]
    field_simp [hN.ne',hε.ne']
  exact hsq.trans_eq heq

theorem scaledOrbitExtra_tendsto (f : Hilbert) :
    Tendsto (fun n : ℕ =>
      scaledOrbitExtra ε hε h ((n:ℝ)+1) (by positivity) hne m g k f) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (((n:ℝ)+1)⁻¹:ℝ)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hbound : Tendsto (fun n : ℕ => (h^2*‖f‖^2/ε^2)*(((n:ℝ)+1)⁻¹:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hinv.const_mul (h^2*‖f‖^2/ε^2)
  have hsq : Tendsto (fun n : ℕ =>
      ‖scaledOrbitExtra ε hε h ((n:ℝ)+1) (by positivity) hne m g k f‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _)
      (fun n => scaledOrbitExtra_norm_sq ε hε h ((n:ℝ)+1) (by positivity) hne m g k f) hbound
  have hn : Tendsto (fun n : ℕ =>
      ‖scaledOrbitExtra ε hε h ((n:ℝ)+1) (by positivity) hne m g k f‖) atTop (𝓝 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using hn)

theorem timeOutputLp_orbitExtra (f : Hilbert) :
    timeOutputLp 0 t (orbitExtra ε hε h N hN hne m g k f)=
      orbitExtra ε hε h N hN hne m g k f := by
  let φ := physicalOrbit h hne f
  let z := extraSection ε hε h N hN m g k φ
  apply Lp.ext
  filter_upwards [(timeOutput 0 t).coeFn_compLp z,
    (extra ε hε h N hN m g k 0).coeFn_compLp φ] with θ h1 h2
  change (timeOutput 0 t).compLp z θ=z θ
  rw [h1]
  change timeOutput 0 t ((extra ε hε h N hN m g k 0).compLp φ θ)=
    (extra ε hε h N hN m g k 0).compLp φ θ
  rw [h2,point_time_extra]

theorem selectedOutputLp_orbitExtra (f : Hilbert) :
    selectedOutputLp (orbitExtra ε hε h N hN hne m g k f)=
      orbitExtra ε hε h N hN hne m g k f := by
  let φ := physicalOrbit h hne f
  let z := extraSection ε hε h N hN m g k φ
  apply Lp.ext
  filter_upwards [selectedOutput.coeFn_compLp z,
    (extra ε hε h N hN m g k 0).coeFn_compLp φ] with θ h1 h2
  change selectedOutput.compLp z θ=z θ
  rw [h1]
  change selectedOutput ((extra ε hε h N hN m g k 0).compLp φ θ)=
    (extra ε hε h N hN m g k 0).compLp φ θ
  rw [h2,point_selected_extra]

theorem staticOutputLp_orbitExtra (f : Hilbert) :
    staticOutputLp (orbitExtra ε hε h N hN hne m g k f)=
      orbitExtra ε hε h N hN hne m g k f := by
  let φ := physicalOrbit h hne f
  let z := extraSection ε hε h N hN m g k φ
  apply Lp.ext
  filter_upwards [staticOutput.coeFn_compLp z,
    (extra ε hε h N hN m g k 0).coeFn_compLp φ] with θ h1 h2
  change staticOutput.compLp z θ=z θ
  rw [h1]
  change staticOutput ((extra ε hε h N hN m g k 0).compLp φ θ)=
    (extra ε hε h N hN m g k 0).compLp φ θ
  rw [h2,point_static_extra]

local notation "hs" => energy_bound ε hε h hb
local notation "hw" => wide_bound ε hε h hb
local notation "BD" => KFCausalClockFloorFormHamiltonian.formData ε hε h hs m g k 0
local notation "BJ" => KFCausalClosedGraphForm.embedding BD
local notation "BA" => KFCausalClosedGraphForm.energyOutput BD
local notation "BF" => KFCausalClockFloorRadialYosidaForm.formAction ε hε h N hN hb hne m g k 0
local notation "AV" => KFCausalClockFloorAveragedEnergy.AveragedSpace ε hε h hs hne m g k 0
local notation "AJ" => KFCausalClockFloorAveragedEnergy.embedding ε hε h hs hne m g k 0
local notation "AA" => KFCausalClockFloorAveragedEnergy.energyOutput ε hε h hs hne m g k 0
local notation "AS" => KFCausalClockFloorAveragedEnergy.sectionMap ε hε h hs hne m g k 0
local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hne hw m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hne hw m g k 0
local notation "RA" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hne hw m g k 0

theorem averagedAction_output (a : AV) :
    AA (averagedAction ε hε h N hN hb hne m g k a)=
      referenceOutputActionLp ε hε h N hN hb (AA a)+
      orbitExtra ε hε h N hN hne m g k (AJ a) := by
  let v := AS a
  let φ := physicalOrbit h hne (AJ a)
  let w1 := referenceOutputActionLp ε hε h N hN hb (AA a)
  let w2 := orbitExtra ε hε h N hN hne m g k (AJ a)
  change (BA).compLp ((BF).compLp v)=w1+w2
  apply Lp.ext
  filter_upwards [(BA).coeFn_compLp ((BF).compLp v),(BF).coeFn_compLp v,
    Lp.coeFn_add w1 w2,(outputAction ε hε h N hN hb).coeFn_compLp (AA a),
    (BA).coeFn_compLp v,(extra ε hε h N hN m g k 0).coeFn_compLp φ,
    KFCausalClockFloorAveragedEnergy.orbit_lift_ae ε hε h hs hne m g k 0 a,
    physicalOrbit_coe h hne (AJ a)]
    with θ h1 h2 hadd h3 h4 h5 horb hpo
  have hlhs : ((BA).compLp ((BF).compLp v)) θ=
      outputAction ε hε h N hN hb (BA (v θ))+
        extra ε hε h N hN m g k 0 (BJ (v θ)) :=
    h1.trans ((congrArg BA h2).trans
      (KFCausalClockFloorRadialYosidaForm.formAction_output ε hε h N hN hb hne m g k 0 (v θ)))
  have hw1 : w1 θ=outputAction ε hε h N hN hb (BA (v θ)) :=
    h3.trans (congrArg (outputAction ε hε h N hN hb) h4)
  have hw2 : w2 θ=extra ε hε h N hN m g k 0 (BJ (v θ)) :=
    h5.trans (congrArg (extra ε hε h N hN m g k 0) (hpo.trans horb.symm))
  have hrhs : (w1+w2) θ=
      outputAction ε hε h N hN hb (BA (v θ))+
        extra ε hε h N hN m g k 0 (BJ (v θ)) :=
    hadd.trans (congrArg₂ (·+·) hw1 hw2)
  exact hlhs.trans hrhs.symm

theorem reference_full_stability (u : RV) :
    ∃ v : RV, RJ v=KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (RJ u) ∧
      RA v=referenceOutputActionLp ε hε h N hN hb (RA u)+
        orbitExtra ε hε h N hN hne m g k (RJ u) := by
  let lift := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hne hw m g k 0
  have hl : Function.Surjective lift :=
    KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hne hw m g k 0
  let a := Classical.choose (hl u)
  have ha : lift a=u := Classical.choose_spec (hl u)
  refine ⟨lift (averagedAction ε hε h N hN hb hne m g k a),?_,?_⟩
  · have hj : AJ a=RJ u :=
      (KFCausalClockFloorAveragedHamiltonian.graphFormVector_embedding
        ε hε h hne hw m g k 0 a).symm.trans (congrArg RJ ha)
    exact (KFCausalClockFloorAveragedHamiltonian.graphFormVector_embedding
      ε hε h hne hw m g k 0 (averagedAction ε hε h N hN hb hne m g k a)).trans
      ((averagedAction_embedding ε hε h N hN hb hne m g k a).trans
        (congrArg (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN) hj))
  · have hj : AJ a=RJ u :=
      (KFCausalClockFloorAveragedHamiltonian.graphFormVector_embedding
        ε hε h hne hw m g k 0 a).symm.trans (congrArg RJ ha)
    have he : AA a=RA u :=
      (KFCausalClockFloorAveragedHamiltonian.graphFormVector_output
        ε hε h hne hw m g k 0 a).symm.trans (congrArg RA ha)
    exact (KFCausalClockFloorAveragedHamiltonian.graphFormVector_output
      ε hε h hne hw m g k 0 (averagedAction ε hε h N hN hb hne m g k a)).trans
      ((averagedAction_output ε hε h N hN hb hne m g k a).trans
        (congrArg₂ (·+·)
          (congrArg (referenceOutputActionLp ε hε h N hN hb) he)
          (congrArg (orbitExtra ε hε h N hN hne m g k) hj)))

#print axioms extra_time_zero
#print axioms point_time_extra
#print axioms point_selected_extra
#print axioms point_static_extra
#print axioms extra_norm_sq
#print axioms extra_norm
#print axioms extraSection_norm
#print axioms orbitExtra_norm
#print axioms scaledOrbitExtra_norm
#print axioms scaledOrbitExtra_norm_sq
#print axioms scaledOrbitExtra_tendsto
#print axioms timeOutputLp_orbitExtra
#print axioms selectedOutputLp_orbitExtra
#print axioms staticOutputLp_orbitExtra
#print axioms averagedAction_output
#print axioms reference_full_stability
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventLeibniz
