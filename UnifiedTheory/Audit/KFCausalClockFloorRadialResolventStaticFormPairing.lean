/- Integration by parts of the symmetric-momentum Leibniz defect on the
completed static form. The pairing of the orbit Leibniz correction against any
completed static energy output is represented by an explicit bounded orbit
section depending on the first state's form norm and pairs directly against the
second state's physical orbit embedding. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaSecondDerivative
import UnifiedTheory.Audit.KFCausalClockFloorSymmetricOrbitGraph
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticForm

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticFormPairing
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalFiniteJointGraph (Output)
open KFCausalFiniteOutputRescaling (selected_apply)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp)
open KFCausalPhysicalEnergyTransport (staticOutput)
open KFCausalClockFloorOrbitVacuumGraph (OrbitSpace physicalOrbit physicalOrbit_coe)
open KFCausalClockFloorRadialYosidaSymbol (symbol action_coe)
open KFCausalClockFloorRadialYosidaKinetics
  (symmetricCorrection symmetricCorrection_norm correction)
open KFCausalClockFloorRadialYosidaSecondDerivative
  (symmetricSecondCorrection symmetricSecondCorrection_norm
    symmetricCorrection_clockMomentum_pairing)
open KFCausalClockFloorSymmetricOrbitGraph
  (symmetricEnergyIndex form_symmetric_graph)
open KFCausalClockFloorRadialYosidaEnergy (energy_bound factorOutput factorCorrection)
open KFCausalClockFloorRadialYosidaForm (outputAction extra)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventLeibniz
  (orbitExtra scaledOrbitExtra referenceOutputActionLp)
open KFCausalClockFloorRadialResolventResidual (referenceOutputResolventLp)
open KFCausalClockFloorRadialResolventStaticForm (formAction formAction_output)
open KFCausalJointGraphBoundedCorrection (outputMap correctionMap)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalAveragedEnergyGraph (l2_norm_square)
open KFCausalSymmetricMomentumCoordinates (symmetricDirection)
open KFCausalClockFloorTrialMomentum (clockMomentum)

private theorem staticOutput_apply (z : Output (Fin 8) Hilbert) (i : Fin 8) :
    staticOutput z i = if i.val < 3 then z i else 0 :=
  selected_apply (fun j : Fin 8 => j.val < 3) z i

private theorem inner_ofReal_smul_right (r : ℝ) (x y : Hilbert) :
    inner ℂ x ((r:ℂ) • y) = inner ℂ ((r:ℂ) • x) y := by
  rw [inner_smul_right,inner_smul_left,Complex.conj_ofReal]

def outputProj (j : Fin 8) : Output (Fin 8) Hilbert →L[ℂ] Hilbert where
  toFun y := y j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := PiLp.continuous_apply 2 (fun _ : Fin 8 => Hilbert) j

theorem outputProj_norm (j : Fin 8) (y : Output (Fin 8) Hilbert) :
    ‖outputProj j y‖ ≤ ‖y‖ := by
  have hsq : ‖y j‖^2 ≤ ‖y‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.single_le_sum (fun i _ => sq_nonneg ‖y i‖) (Finset.mem_univ j)
  exact (abs_le_of_sq_le_sq' hsq (norm_nonneg y)).2

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)

def extraFirstDual : Output (Fin 8) Hilbert →L[ℂ] Hilbert :=
  (Real.sqrt (1/2) : ℂ) •
    ((symmetricCorrection ε hε h N hN 0).comp (outputProj 1)+
      (symmetricCorrection ε hε h N hN 1).comp (outputProj 2))

def extraSecondDual : Hilbert →L[ℂ] Hilbert :=
  ((1/2:ℝ):ℂ) •
    (symmetricSecondCorrection ε hε h N hN 0+
      symmetricSecondCorrection ε hε h N hN 1)

theorem extraFirstDual_staticOutput (y : Output (Fin 8) Hilbert) :
    extraFirstDual ε hε h N hN (staticOutput y) = extraFirstDual ε hε h N hN y := by
  have h1 : staticOutput y 1 = y 1 := by
    rw [staticOutput_apply]
    rfl
  have h2 : staticOutput y 2 = y 2 := by
    rw [staticOutput_apply]
    rfl
  change (Real.sqrt (1/2) : ℂ) •
      (symmetricCorrection ε hε h N hN 0 (staticOutput y 1)+
        symmetricCorrection ε hε h N hN 1 (staticOutput y 2)) =
    (Real.sqrt (1/2) : ℂ) •
      (symmetricCorrection ε hε h N hN 0 (y 1)+
        symmetricCorrection ε hε h N hN 1 (y 2))
  rw [h1,h2]

theorem extraFirstDual_norm (y : Output (Fin 8) Hilbert) :
    ‖extraFirstDual ε hε h N hN y‖ ≤
      (2*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹))*‖y‖ := by
  let C := |h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹
  have hC : 0 ≤ C := by positivity
  change ‖(Real.sqrt (1/2) : ℂ) •
    (symmetricCorrection ε hε h N hN 0 (outputProj 1 y)+
      symmetricCorrection ε hε h N hN 1 (outputProj 2 y))‖ ≤ (2*C)*‖y‖
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 : ‖symmetricCorrection ε hε h N hN 0 (outputProj 1 y)‖ ≤ C*‖y‖ :=
    (symmetricCorrection_norm ε hε h N hN 0 (outputProj 1 y)).trans
      (mul_le_mul_of_nonneg_left (outputProj_norm 1 y) hC)
  have h2 : ‖symmetricCorrection ε hε h N hN 1 (outputProj 2 y)‖ ≤ C*‖y‖ :=
    (symmetricCorrection_norm ε hε h N hN 1 (outputProj 2 y)).trans
      (mul_le_mul_of_nonneg_left (outputProj_norm 2 y) hC)
  have hsum : ‖symmetricCorrection ε hε h N hN 0 (outputProj 1 y)+
      symmetricCorrection ε hε h N hN 1 (outputProj 2 y)‖ ≤ (2*C)*‖y‖ := by
    have ha := (norm_add_le _ _).trans (add_le_add h1 h2)
    linarith
  have hs1 : Real.sqrt (1/2) ≤ 1 := Real.sqrt_le_one.mpr (by norm_num)
  nlinarith [norm_nonneg (symmetricCorrection ε hε h N hN 0 (outputProj 1 y)+
    symmetricCorrection ε hε h N hN 1 (outputProj 2 y)),mul_nonneg hC (norm_nonneg y)]

theorem extraSecondDual_norm (f : Hilbert) :
    ‖extraSecondDual ε hε h N hN f‖ ≤ (6*h^2/ε^2)*‖f‖ := by
  change ‖((1/2:ℝ):ℂ) •
    (symmetricSecondCorrection ε hε h N hN 0 f+
      symmetricSecondCorrection ε hε h N hN 1 f)‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have h0 := symmetricSecondCorrection_norm ε hε h N hN 0 f
  have h1 := symmetricSecondCorrection_norm ε hε h N hN 1 f
  have hsum := (norm_add_le _ _).trans (add_le_add h0 h1)
  linarith

variable (hb : |h| ≤ Real.pi*ε/3) (hh : h ≠ 0) (m g k : ℝ)

include hh in
private theorem scaled_symmetric_pairing (i : Fin 2) (f₁ g₁ f₂ g₂ : Hilbert)
    (hu : ((Real.sqrt (1/2) : ℂ) • f₁,g₁) ∈ (clockMomentum ε h (symmetricDirection i)).graph)
    (hv : ((Real.sqrt (1/2) : ℂ) • f₂,g₂) ∈ (clockMomentum ε h (symmetricDirection i)).graph) :
    inner ℂ ((Real.sqrt (1/2) : ℂ) • symmetricCorrection ε hε h N hN i f₁) g₂ =
      inner ℂ ((Real.sqrt (1/2) : ℂ) • symmetricCorrection ε hε h N hN i g₁+
        ((1/2:ℝ):ℂ) • symmetricSecondCorrection ε hε h N hN i f₁) f₂ := by
  have hp := symmetricCorrection_clockMomentum_pairing ε hε h N hN hh i
    ((Real.sqrt (1/2) : ℂ) • f₁) g₁ ((Real.sqrt (1/2) : ℂ) • f₂) g₂ hu hv
  rw [← map_smul,hp,inner_ofReal_smul_right,map_smul,smul_add,smul_smul]
  have hsq : (Real.sqrt (1/2) : ℂ)*(Real.sqrt (1/2) : ℂ) = ((1/2:ℝ):ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [hsq]

private theorem point_extra_pairing (f₁ f₂ : Hilbert) (y₁ y₂ : Output (Fin 8) Hilbert)
    (h0 : inner ℂ ((Real.sqrt (1/2) : ℂ) • symmetricCorrection ε hε h N hN 0 f₁)
      (y₂ (symmetricEnergyIndex 0)) =
      inner ℂ ((Real.sqrt (1/2) : ℂ) • symmetricCorrection ε hε h N hN 0
        (y₁ (symmetricEnergyIndex 0))+
        ((1/2:ℝ):ℂ) • symmetricSecondCorrection ε hε h N hN 0 f₁) f₂)
    (h1 : inner ℂ ((Real.sqrt (1/2) : ℂ) • symmetricCorrection ε hε h N hN 1 f₁)
      (y₂ (symmetricEnergyIndex 1)) =
      inner ℂ ((Real.sqrt (1/2) : ℂ) • symmetricCorrection ε hε h N hN 1
        (y₁ (symmetricEnergyIndex 1))+
        ((1/2:ℝ):ℂ) • symmetricSecondCorrection ε hε h N hN 1 f₁) f₂) :
    inner ℂ (extra ε hε h N hN m g k 0 f₁) (staticOutput y₂) =
      inner ℂ (extraFirstDual ε hε h N hN (staticOutput y₁)+
        extraSecondDual ε hε h N hN f₁) f₂ := by
  have hs1 : staticOutput y₂ 1 = y₂ (symmetricEnergyIndex 0) := by
    rw [staticOutput_apply]
    rfl
  have hs2 : staticOutput y₂ 2 = y₂ (symmetricEnergyIndex 1) := by
    rw [staticOutput_apply]
    rfl
  have hj0 : extra ε hε h N hN m g k 0 f₁ 0 = 0 := by
    simp [extra,correctionMap,factorCorrection]
  have hj1 : extra ε hε h N hN m g k 0 f₁ 1 =
      (Real.sqrt (1/2) : ℂ) • symmetricCorrection ε hε h N hN 0 f₁ := by
    simp [extra,correctionMap,factorCorrection,correction,energyWeight]
  have hj2 : extra ε hε h N hN m g k 0 f₁ 2 =
      (Real.sqrt (1/2) : ℂ) • symmetricCorrection ε hε h N hN 1 f₁ := by
    simp [extra,correctionMap,factorCorrection,correction,energyWeight]
  have hj3 : extra ε hε h N hN m g k 0 f₁ 3 = 0 := by
    simp [extra,correctionMap,factorCorrection,correction]
  have hj4 : extra ε hε h N hN m g k 0 f₁ 4 = 0 := by
    simp [extra,correctionMap,factorCorrection,correction]
  have hj5 : extra ε hε h N hN m g k 0 f₁ 5 = 0 := by
    simp [extra,correctionMap,factorCorrection]
  have hj6 : extra ε hε h N hN m g k 0 f₁ 6 = 0 := by
    simp [extra,correctionMap,factorCorrection]
  have hj7 : extra ε hε h N hN m g k 0 f₁ 7 = 0 := by
    simp [extra,correctionMap,factorCorrection]
  rw [extraFirstDual_staticOutput,PiLp.inner_apply,Fin.sum_univ_eight]
  change inner ℂ (extra ε hε h N hN m g k 0 f₁ 0) (staticOutput y₂ 0)+
    inner ℂ (extra ε hε h N hN m g k 0 f₁ 1) (staticOutput y₂ 1)+
    inner ℂ (extra ε hε h N hN m g k 0 f₁ 2) (staticOutput y₂ 2)+
    inner ℂ (extra ε hε h N hN m g k 0 f₁ 3) (staticOutput y₂ 3)+
    inner ℂ (extra ε hε h N hN m g k 0 f₁ 4) (staticOutput y₂ 4)+
    inner ℂ (extra ε hε h N hN m g k 0 f₁ 5) (staticOutput y₂ 5)+
    inner ℂ (extra ε hε h N hN m g k 0 f₁ 6) (staticOutput y₂ 6)+
    inner ℂ (extra ε hε h N hN m g k 0 f₁ 7) (staticOutput y₂ 7) = _
  rw [hj0,hj1,hj2,hj3,hj4,hj5,hj6,hj7,hs1,hs2]
  simp only [inner_zero_left,zero_add,add_zero]
  rw [h0,h1,← inner_add_left]
  congr 1
  change ((Real.sqrt (1/2) : ℂ) • symmetricCorrection ε hε h N hN 0 (y₁ 1)+
      ((1/2:ℝ):ℂ) • symmetricSecondCorrection ε hε h N hN 0 f₁)+
    ((Real.sqrt (1/2) : ℂ) • symmetricCorrection ε hε h N hN 1 (y₁ 2)+
      ((1/2:ℝ):ℂ) • symmetricSecondCorrection ε hε h N hN 1 f₁) =
    (Real.sqrt (1/2) : ℂ) •
      (symmetricCorrection ε hε h N hN 0 (y₁ 1)+
        symmetricCorrection ε hε h N hN 1 (y₁ 2))+
    ((1/2:ℝ):ℂ) •
      (symmetricSecondCorrection ε hε h N hN 0 f₁+
        symmetricSecondCorrection ε hε h N hN 1 f₁)
  simp only [smul_add]
  abel

local notation "hs" => energy_bound ε hε h hb
local notation "hw" => wide_bound ε hε h hb
local notation "BD" => KFCausalClockFloorFormHamiltonian.formData ε hε h hs m g k 0
local notation "BJ" => KFCausalClosedGraphForm.embedding BD
local notation "BA" => KFCausalClosedGraphForm.energyOutput BD
local notation "AV" => KFCausalClockFloorAveragedEnergy.AveragedSpace ε hε h hs hh m g k 0
local notation "AJ" => KFCausalClockFloorAveragedEnergy.embedding ε hε h hs hh m g k 0
local notation "AA" => KFCausalClockFloorAveragedEnergy.energyOutput ε hε h hs hh m g k 0
local notation "AS" => KFCausalClockFloorAveragedEnergy.sectionMap ε hε h hs hh m g k 0
local notation "AS0" => KFCausalClockFloorStaticRootSource.staticOutput ε hε h hh hw m g k 0
local notation "Tstat" => KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hw m g k 0
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw m g k 0
local notation "TV" => KFCausalClockFloorStaticHamiltonian.StaticForm ε hε h hh hw m g k 0
local notation "TJ" => KFCausalClosedGraphForm.embedding TD
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD

include hh in
theorem base_extra_pairing (u v : KFCausalClosedGraphForm.FormSpace BD) :
    inner ℂ (extra ε hε h N hN m g k 0 (BJ u)) (staticOutput (BA v)) =
      inner ℂ (extraFirstDual ε hε h N hN (staticOutput (BA u))+
        extraSecondDual ε hε h N hN (BJ u)) (BJ v) :=
  point_extra_pairing ε hε h N hN m g k (BJ u) (BJ v) (BA u) (BA v)
    (scaled_symmetric_pairing ε hε h N hN hh 0 (BJ u) (BA u (symmetricEnergyIndex 0))
      (BJ v) (BA v (symmetricEnergyIndex 0))
      (form_symmetric_graph ε hε h hs m g k 0 0 u)
      (form_symmetric_graph ε hε h hs m g k 0 0 v))
    (scaled_symmetric_pairing ε hε h N hN hh 1 (BJ u) (BA u (symmetricEnergyIndex 1))
      (BJ v) (BA v (symmetricEnergyIndex 1))
      (form_symmetric_graph ε hε h hs m g k 0 1 u)
      (form_symmetric_graph ε hε h hs m g k 0 1 v))

def sectionFirstDual : EnergyOutputSpace →L[ℂ] OrbitSpace :=
  (extraFirstDual ε hε h N hN).compLpL 2 angleMeasure

def orbitSecondDual : Hilbert →L[ℂ] OrbitSpace :=
  ((extraSecondDual ε hε h N hN).compLpL 2 angleMeasure).comp
    (physicalOrbit h hh).toContinuousLinearMap

def scaledSectionFirstDual : EnergyOutputSpace →L[ℂ] OrbitSpace :=
  (N⁻¹:ℂ) • sectionFirstDual ε hε h N hN

def scaledOrbitSecondDual : Hilbert →L[ℂ] OrbitSpace :=
  (N⁻¹:ℂ) • orbitSecondDual ε hε h N hN hh

theorem sectionFirstDual_norm (z : EnergyOutputSpace) :
    ‖sectionFirstDual ε hε h N hN z‖ ≤
      (2*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹))*‖z‖ := by
  let C := 2*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹)
  have hC : 0 ≤ C*‖z‖ := by positivity
  have hz : Integrable (fun θ => ‖z θ‖^2) angleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable z)).mp (Lp.memLp z)
  have he : ∀ᵐ θ ∂angleMeasure,
      ‖sectionFirstDual ε hε h N hN z θ‖^2 ≤ C^2*‖z θ‖^2 := by
    filter_upwards [(extraFirstDual ε hε h N hN).coeFn_compLp z] with θ hθ
    change ‖(extraFirstDual ε hε h N hN).compLp z θ‖^2 ≤ C^2*‖z θ‖^2
    rw [hθ]
    exact (pow_le_pow_left₀ (norm_nonneg _)
      (extraFirstDual_norm ε hε h N hN (z θ)) 2).trans_eq (by ring)
  have hint : Integrable (fun θ => ‖sectionFirstDual ε hε h N hN z θ‖^2) angleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hsq : ‖sectionFirstDual ε hε h N hN z‖^2 ≤ (C*‖z‖)^2 := by
    rw [l2_norm_square angleMeasure (sectionFirstDual ε hε h N hN z),
      mul_pow,l2_norm_square angleMeasure z,← integral_const_mul]
    exact integral_mono_ae hint (hz.const_mul (C^2)) he
  exact (abs_le_of_sq_le_sq' hsq hC).2

theorem orbitSecondDual_norm (f : Hilbert) :
    ‖orbitSecondDual ε hε h N hN hh f‖ ≤ (6*h^2/ε^2)*‖f‖ := by
  let φ := physicalOrbit h hh f
  let C := 6*h^2/ε^2
  have hC : 0 ≤ C*‖φ‖ := by positivity
  have hφ : Integrable (fun θ => ‖φ θ‖^2) angleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable φ)).mp (Lp.memLp φ)
  have he : ∀ᵐ θ ∂angleMeasure,
      ‖((extraSecondDual ε hε h N hN).compLpL 2 angleMeasure φ) θ‖^2 ≤ C^2*‖φ θ‖^2 := by
    filter_upwards [(extraSecondDual ε hε h N hN).coeFn_compLp φ] with θ hθ
    change ‖(extraSecondDual ε hε h N hN).compLp φ θ‖^2 ≤ C^2*‖φ θ‖^2
    rw [hθ]
    exact (pow_le_pow_left₀ (norm_nonneg _)
      (extraSecondDual_norm ε hε h N hN (φ θ)) 2).trans_eq (by ring)
  have hint : Integrable
      (fun θ => ‖((extraSecondDual ε hε h N hN).compLpL 2 angleMeasure φ) θ‖^2) angleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hsq : ‖(extraSecondDual ε hε h N hN).compLpL 2 angleMeasure φ‖^2 ≤ (C*‖φ‖)^2 := by
    rw [l2_norm_square angleMeasure ((extraSecondDual ε hε h N hN).compLpL 2 angleMeasure φ),
      mul_pow,l2_norm_square angleMeasure φ,← integral_const_mul]
    exact integral_mono_ae hint (hφ.const_mul (C^2)) he
  have hb0 := (abs_le_of_sq_le_sq' hsq hC).2
  simpa only [orbitSecondDual,φ,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,LinearIsometry.norm_map] using hb0

theorem scaledSectionFirstDual_norm (z : EnergyOutputSpace) :
    ‖scaledSectionFirstDual ε hε h N hN z‖ ≤
      (N⁻¹*(2*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹)))*‖z‖ := by
  change ‖(N⁻¹:ℂ) • sectionFirstDual ε hε h N hN z‖ ≤ _
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN,mul_assoc]
  exact mul_le_mul_of_nonneg_left (sectionFirstDual_norm ε hε h N hN z) (inv_nonneg.mpr hN.le)

theorem scaledOrbitSecondDual_norm (f : Hilbert) :
    ‖scaledOrbitSecondDual ε hε h N hN hh f‖ ≤ (N⁻¹*(6*h^2/ε^2))*‖f‖ := by
  change ‖(N⁻¹:ℂ) • orbitSecondDual ε hε h N hN hh f‖ ≤ _
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN,mul_assoc]
  exact mul_le_mul_of_nonneg_left (orbitSecondDual_norm ε hε h N hN hh f) (inv_nonneg.mpr hN.le)

private theorem l2_pairing_of_ae (z₁ z₂ : EnergyOutputSpace) (φ₁ φ₂ : OrbitSpace)
    (hae : ∀ᵐ θ ∂angleMeasure, inner ℂ (z₁ θ) (z₂ θ) = inner ℂ (φ₁ θ) (φ₂ θ)) :
    inner ℂ z₁ z₂ = inner ℂ φ₁ φ₂ := by
  rw [L2.inner_def,L2.inner_def]
  exact integral_congr_ae hae

theorem averaged_orbitExtra_pairing (a b : AV) :
    inner ℂ (orbitExtra ε hε h N hN hh m g k (AJ a)) (AS0 b) =
      inner ℂ (sectionFirstDual ε hε h N hN (AS0 a)+
        orbitSecondDual ε hε h N hN hh (AJ a)) (physicalOrbit h hh (AJ b)) := by
  apply l2_pairing_of_ae
  let sa := AS a
  let sb := AS b
  let φa := physicalOrbit h hh (AJ a)
  let φb := physicalOrbit h hh (AJ b)
  filter_upwards [(extra ε hε h N hN m g k 0).coeFn_compLp φa,
    staticOutput.coeFn_compLp (AA b),
    (BA).coeFn_compLp sb,
    Lp.coeFn_add (sectionFirstDual ε hε h N hN (AS0 a)) (orbitSecondDual ε hε h N hN hh (AJ a)),
    (extraFirstDual ε hε h N hN).coeFn_compLp (AS0 a),
    staticOutput.coeFn_compLp (AA a),
    (BA).coeFn_compLp sa,
    (extraSecondDual ε hε h N hN).coeFn_compLp φa,
    KFCausalClockFloorAveragedEnergy.orbit_lift_ae ε hε h hs hh m g k 0 a,
    KFCausalClockFloorAveragedEnergy.orbit_lift_ae ε hε h hs hh m g k 0 b,
    physicalOrbit_coe h hh (AJ a),
    physicalOrbit_coe h hh (AJ b)]
    with θ hex hsb hbab hadd hd1 hsa hbaa hd2 horba horbb hpoa hpob
  have hl1 : orbitExtra ε hε h N hN hh m g k (AJ a) θ =
      extra ε hε h N hN m g k 0 (BJ (sa θ)) :=
    hex.trans (congrArg (extra ε hε h N hN m g k 0) (hpoa.trans horba.symm))
  have hl2 : AS0 b θ = staticOutput (BA (sb θ)) :=
    hsb.trans (congrArg staticOutput hbab)
  have ha1 : sectionFirstDual ε hε h N hN (AS0 a) θ =
      extraFirstDual ε hε h N hN (staticOutput (BA (sa θ))) :=
    hd1.trans (congrArg (extraFirstDual ε hε h N hN) (hsa.trans (congrArg staticOutput hbaa)))
  have ha2 : orbitSecondDual ε hε h N hN hh (AJ a) θ =
      extraSecondDual ε hε h N hN (BJ (sa θ)) :=
    hd2.trans (congrArg (extraSecondDual ε hε h N hN) (hpoa.trans horba.symm))
  have hr1 : (sectionFirstDual ε hε h N hN (AS0 a)+orbitSecondDual ε hε h N hN hh (AJ a)) θ =
      extraFirstDual ε hε h N hN (staticOutput (BA (sa θ)))+
        extraSecondDual ε hε h N hN (BJ (sa θ)) :=
    hadd.trans (congrArg₂ (·+·) ha1 ha2)
  have hr2 : physicalOrbit h hh (AJ b) θ = BJ (sb θ) := hpob.trans horbb.symm
  exact (congrArg₂ (inner ℂ) hl1 hl2).trans
    ((base_extra_pairing ε hε h N hN hb hh m g k (sa θ) (sb θ)).trans
      (congrArg₂ (inner ℂ) hr1 hr2).symm)

private theorem closure_bilinear_eq
    {V X Y Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (j : V →L[ℂ] X) (s : V →L[ℂ] Y)
    (L : X →L[ℂ] Y) (D₁ : Y →L[ℂ] Z) (D₂ : X →L[ℂ] Z) (P : X →L[ℂ] Z)
    (h0 : ∀ a b : V, inner ℂ (L (j a)) (s b) = inner ℂ (D₁ (s a)+D₂ (j a)) (P (j b)))
    (p₁ p₂ : X × Y)
    (hp₁ : p₁ ∈ (j.prod s).toLinearMap.range.topologicalClosure)
    (hp₂ : p₂ ∈ (j.prod s).toLinearMap.range.topologicalClosure) :
    inner ℂ (L p₁.1) p₂.2 = inner ℂ (D₁ p₁.2+D₂ p₁.1) (P p₂.1) := by
  let S := (j.prod s).toLinearMap.range
  have step1 (a : V) : ∀ q : X × Y, q ∈ S.topologicalClosure →
      inner ℂ (L (j a)) q.2 = inner ℂ (D₁ (s a)+D₂ (j a)) (P q.1) := by
    intro q hq
    have hc : IsClosed {q : X × Y | inner ℂ (L (j a)) q.2 = inner ℂ (D₁ (s a)+D₂ (j a)) (P q.1)} :=
      isClosed_eq (continuous_const.inner continuous_snd)
        (continuous_const.inner (P.continuous.comp continuous_fst))
    refine closure_minimal ?_ hc (by simpa only [Submodule.topologicalClosure_coe] using hq)
    rintro _ ⟨b,rfl⟩
    exact h0 a b
  have hc2 : IsClosed {p : X × Y | inner ℂ (L p.1) p₂.2 = inner ℂ (D₁ p.2+D₂ p.1) (P p₂.1)} :=
    isClosed_eq
      ((L.continuous.comp continuous_fst).inner continuous_const)
      (((D₁.continuous.comp continuous_snd).add
        (D₂.continuous.comp continuous_fst)).inner continuous_const)
  refine closure_minimal ?_ hc2 (by simpa only [Submodule.topologicalClosure_coe] using hp₁)
  rintro _ ⟨a,rfl⟩
  exact step1 a p₂ hp₂

theorem orbitExtra_graph_pairing (f₁ f₂ : Hilbert) (z₁ z₂ : EnergyOutputSpace)
    (h1 : (f₁,z₁) ∈ (Tstat).graph) (h2 : (f₂,z₂) ∈ (Tstat).graph) :
    inner ℂ (orbitExtra ε hε h N hN hh m g k f₁) z₂ =
      inner ℂ (sectionFirstDual ε hε h N hN z₁+
        orbitSecondDual ε hε h N hN hh f₁) (physicalOrbit h hh f₂) := by
  have heq := KFCausalClockFloorStaticOutputClosure.operator_graph ε hε h hh hw m g k 0
  have hu : (f₁,z₁) ∈ (KFCausalClockFloorStaticOutputClosure.initialGraph
      ε hε h hh hw m g k 0).topologicalClosure :=
    (Eq.subset (congrArg SetLike.coe heq)) h1
  have hv : (f₂,z₂) ∈ (KFCausalClockFloorStaticOutputClosure.initialGraph
      ε hε h hh hw m g k 0).topologicalClosure :=
    (Eq.subset (congrArg SetLike.coe heq)) h2
  exact closure_bilinear_eq AJ AS0
    (orbitExtra ε hε h N hN hh m g k)
    (sectionFirstDual ε hε h N hN)
    (orbitSecondDual ε hε h N hN hh)
    (physicalOrbit h hh).toContinuousLinearMap
    (averaged_orbitExtra_pairing ε hε h N hN hb hh m g k)
    (f₁,z₁) (f₂,z₂) hu hv

theorem orbitExtra_staticForm_pairing (u v : TV) :
    inner ℂ (orbitExtra ε hε h N hN hh m g k (TJ u)) (TB v) =
      inner ℂ (sectionFirstDual ε hε h N hN (TB u)+
        orbitSecondDual ε hε h N hN hh (TJ u)) (physicalOrbit h hh (TJ v)) :=
  orbitExtra_graph_pairing ε hε h N hN hb hh m g k (TJ u) (TJ v) (TB u) (TB v)
    u.property v.property

private theorem scaledOrbitExtra_apply (f : Hilbert) :
    scaledOrbitExtra ε hε h N hN hh m g k f =
      (N⁻¹:ℂ) • orbitExtra ε hε h N hN hh m g k f := rfl

private theorem scaledSectionFirstDual_apply (z : EnergyOutputSpace) :
    scaledSectionFirstDual ε hε h N hN z =
      (N⁻¹:ℂ) • sectionFirstDual ε hε h N hN z := rfl

private theorem scaledOrbitSecondDual_apply (f : Hilbert) :
    scaledOrbitSecondDual ε hε h N hN hh f =
      (N⁻¹:ℂ) • orbitSecondDual ε hε h N hN hh f := rfl

private theorem scaled_pairing_of_unscaled (f₁ f₂ : Hilbert) (z₁ z₂ : EnergyOutputSpace)
    (hp : inner ℂ (orbitExtra ε hε h N hN hh m g k f₁) z₂ =
      inner ℂ (sectionFirstDual ε hε h N hN z₁+
        orbitSecondDual ε hε h N hN hh f₁) (physicalOrbit h hh f₂)) :
    inner ℂ (scaledOrbitExtra ε hε h N hN hh m g k f₁) z₂ =
      inner ℂ (scaledSectionFirstDual ε hε h N hN z₁+
        scaledOrbitSecondDual ε hε h N hN hh f₁) (physicalOrbit h hh f₂) := by
  rw [scaledOrbitExtra_apply,scaledSectionFirstDual_apply,scaledOrbitSecondDual_apply,
    ← smul_add,inner_smul_left,inner_smul_left,hp]

theorem scaledOrbitExtra_staticForm_pairing (u v : TV) :
    inner ℂ (scaledOrbitExtra ε hε h N hN hh m g k (TJ u)) (TB v) =
      inner ℂ (scaledSectionFirstDual ε hε h N hN (TB u)+
        scaledOrbitSecondDual ε hε h N hN hh (TJ u)) (physicalOrbit h hh (TJ v)) :=
  scaled_pairing_of_unscaled ε hε h N hN hh m g k (TJ u) (TJ v) (TB u) (TB v)
    (orbitExtra_staticForm_pairing ε hε h N hN hb hh m g k u v)

private theorem bound_of_pairing (f₁ f₂ : Hilbert) (z₁ z₂ : EnergyOutputSpace)
    (hp : inner ℂ (orbitExtra ε hε h N hN hh m g k f₁) z₂ =
      inner ℂ (sectionFirstDual ε hε h N hN z₁+
        orbitSecondDual ε hε h N hN hh f₁) (physicalOrbit h hh f₂)) :
    ‖inner ℂ (orbitExtra ε hε h N hN hh m g k f₁) z₂‖ ≤
      ((2*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹))*‖z₁‖+(6*h^2/ε^2)*‖f₁‖)*‖f₂‖ := by
  rw [hp]
  apply (norm_inner_le_norm _ _).trans
  rw [(physicalOrbit h hh).norm_map f₂]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (norm_add_le _ _).trans (add_le_add
    (sectionFirstDual_norm ε hε h N hN z₁)
    (orbitSecondDual_norm ε hε h N hN hh f₁))

theorem orbitExtra_staticForm_bound (u v : TV) :
    ‖inner ℂ (orbitExtra ε hε h N hN hh m g k (TJ u)) (TB v)‖ ≤
      ((2*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹))*‖TB u‖+(6*h^2/ε^2)*‖TJ u‖)*‖TJ v‖ :=
  bound_of_pairing ε hε h N hN hh m g k (TJ u) (TJ v) (TB u) (TB v)
    (orbitExtra_staticForm_pairing ε hε h N hN hb hh m g k u v)

private theorem scaled_bound_of_pairing (f₁ f₂ : Hilbert) (z₁ z₂ : EnergyOutputSpace)
    (hp : inner ℂ (scaledOrbitExtra ε hε h N hN hh m g k f₁) z₂ =
      inner ℂ (scaledSectionFirstDual ε hε h N hN z₁+
        scaledOrbitSecondDual ε hε h N hN hh f₁) (physicalOrbit h hh f₂)) :
    ‖inner ℂ (scaledOrbitExtra ε hε h N hN hh m g k f₁) z₂‖ ≤
      (N⁻¹*(2*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹))*‖z₁‖+
        N⁻¹*(6*h^2/ε^2)*‖f₁‖)*‖f₂‖ := by
  rw [hp]
  apply (norm_inner_le_norm _ _).trans
  rw [(physicalOrbit h hh).norm_map f₂]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (norm_add_le _ _).trans (add_le_add
    (scaledSectionFirstDual_norm ε hε h N hN z₁)
    (scaledOrbitSecondDual_norm ε hε h N hN hh f₁))

theorem scaledOrbitExtra_staticForm_bound (u v : TV) :
    ‖inner ℂ (scaledOrbitExtra ε hε h N hN hh m g k (TJ u)) (TB v)‖ ≤
      (N⁻¹*(2*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹))*‖TB u‖+
        N⁻¹*(6*h^2/ε^2)*‖TJ u‖)*‖TJ v‖ :=
  scaled_bound_of_pairing ε hε h N hN hh m g k (TJ u) (TJ v) (TB u) (TB v)
    (scaledOrbitExtra_staticForm_pairing ε hε h N hN hb hh m g k u v)

private theorem point_staticOutput_idem (y : Output (Fin 8) Hilbert) :
    staticOutput (staticOutput y) = staticOutput y := by
  apply PiLp.ext
  intro i
  rw [staticOutput_apply,staticOutput_apply]
  split_ifs <;> rfl

theorem staticOutputLp_idem (z : EnergyOutputSpace) :
    staticOutputLp (staticOutputLp z) = staticOutputLp z := by
  apply Lp.ext
  filter_upwards [staticOutput.coeFn_compLp (staticOutputLp z),
    staticOutput.coeFn_compLp z] with θ h1 h2
  have h2' : staticOutputLp z θ = staticOutput (z θ) := h2
  change staticOutput.compLp (staticOutputLp z) θ = staticOutput.compLp z θ
  rw [h1,h2,h2',point_staticOutput_idem]

theorem staticGraph_output_fixed (f : Hilbert) (z : EnergyOutputSpace)
    (hfz : (f,z) ∈ (Tstat).graph) :
    staticOutputLp z = z := by
  let S := KFCausalClockFloorStaticOutputClosure.initialGraph ε hε h hh hw m g k 0
  have heq := KFCausalClockFloorStaticOutputClosure.operator_graph ε hε h hh hw m g k 0
  have hu : (f,z) ∈ S.topologicalClosure :=
    (Eq.subset (congrArg SetLike.coe heq)) hfz
  have hc : IsClosed {p : Hilbert × EnergyOutputSpace | staticOutputLp p.2 = p.2} :=
    isClosed_eq (staticOutputLp.continuous.comp continuous_snd) continuous_snd
  refine closure_minimal ?_ hc (by simpa only [Submodule.topologicalClosure_coe] using hu)
  rintro _ ⟨a,rfl⟩
  exact staticOutputLp_idem (AA a)

theorem staticForm_output_fixed (u : TV) :
    staticOutputLp (TB u) = TB u :=
  staticGraph_output_fixed ε hε h hb hh m g k (TJ u) (TB u) u.property

theorem yosidaAction_selfAdjoint_pairing (f₁ f₂ : Hilbert) :
    inner ℂ (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f₁) f₂ =
      inner ℂ f₁ (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f₂) := by
  rw [← chargeCoordinates.inner_map_map
      (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f₁) f₂,
    ← chargeCoordinates.inner_map_map f₁
      (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f₂),
    L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [action_coe ε hε h N hN f₁,action_coe ε hε h N hN f₂] with x h1 h2
  rw [h1,h2]
  change inner ℂ ((symbol ε h N x:ℂ) • (chargeCoordinates f₁) x) ((chargeCoordinates f₂) x) =
    inner ℂ ((chargeCoordinates f₁) x) ((symbol ε h N x:ℂ) • (chargeCoordinates f₂) x)
  rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal]

private theorem point_outputAction_static_pairing (y₁ y₂ : Output (Fin 8) Hilbert) :
    inner ℂ (outputAction ε hε h N hN hb y₁) (staticOutput y₂) =
      inner ℂ y₁ (outputAction ε hε h N hN hb (staticOutput y₂)) := by
  rw [PiLp.inner_apply,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ (factorOutput ε hε h N hN hb i (y₁ i)) (staticOutput y₂ i) =
    inner ℂ (y₁ i) (factorOutput ε hε h N hN hb i (staticOutput y₂ i))
  rw [staticOutput_apply]
  fin_cases i <;>
    simp [factorOutput,yosidaAction_selfAdjoint_pairing ε hε h N hN]

theorem referenceOutputActionLp_static_pairing (z₁ z₂ : EnergyOutputSpace) :
    inner ℂ (referenceOutputActionLp ε hε h N hN hb z₁) (staticOutputLp z₂) =
      inner ℂ z₁ (referenceOutputActionLp ε hε h N hN hb (staticOutputLp z₂)) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(outputAction ε hε h N hN hb).coeFn_compLp z₁,
    staticOutput.coeFn_compLp z₂,
    (outputAction ε hε h N hN hb).coeFn_compLp (staticOutputLp z₂)] with θ h1 h2 h3
  have h2' : staticOutputLp z₂ θ = staticOutput (z₂ θ) := h2
  change inner ℂ ((outputAction ε hε h N hN hb).compLp z₁ θ) (staticOutput.compLp z₂ θ) =
    inner ℂ (z₁ θ) ((outputAction ε hε h N hN hb).compLp (staticOutputLp z₂) θ)
  rw [h1,h2,h3,h2']
  exact point_outputAction_static_pairing ε hε h N hN hb (z₁ θ) (z₂ θ)

private theorem referenceOutputResolventLp_apply (z : EnergyOutputSpace) :
    referenceOutputResolventLp ε hε h N hN hb z =
      z-(N⁻¹:ℂ) • referenceOutputActionLp ε hε h N hN hb z := rfl

private theorem resolvent_pairing_of_fixed (z₁ z₂ : EnergyOutputSpace)
    (hz₂ : staticOutputLp z₂ = z₂) :
    inner ℂ (referenceOutputResolventLp ε hε h N hN hb z₁) z₂ =
      inner ℂ z₁ (referenceOutputResolventLp ε hε h N hN hb z₂) := by
  have ha : inner ℂ (referenceOutputActionLp ε hε h N hN hb z₁) z₂ =
      inner ℂ z₁ (referenceOutputActionLp ε hε h N hN hb z₂) := by
    have h0 := referenceOutputActionLp_static_pairing ε hε h N hN hb z₁ z₂
    rwa [hz₂] at h0
  rw [referenceOutputResolventLp_apply,referenceOutputResolventLp_apply,
    inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    ← Complex.ofReal_inv,Complex.conj_ofReal,ha]

theorem referenceOutputResolventLp_staticForm_pairing (u v : TV) :
    inner ℂ (referenceOutputResolventLp ε hε h N hN hb (TB u)) (TB v) =
      inner ℂ (TB u) (referenceOutputResolventLp ε hε h N hN hb (TB v)) :=
  resolvent_pairing_of_fixed ε hε h N hN hb (TB u) (TB v)
    (staticForm_output_fixed ε hε h hb hh m g k v)

private theorem output_pairing_algebra (z₁ z₂ w₁ s₁ : EnergyOutputSpace)
    (hw₁ : w₁ = referenceOutputResolventLp ε hε h N hN hb z₁+(-s₁))
    (hres : inner ℂ (referenceOutputResolventLp ε hε h N hN hb z₁) z₂ =
      inner ℂ z₁ (referenceOutputResolventLp ε hε h N hN hb z₂)) :
    inner ℂ w₁ z₂ =
      inner ℂ z₁ (referenceOutputResolventLp ε hε h N hN hb z₂)-inner ℂ s₁ z₂ := by
  rw [hw₁,← sub_eq_add_neg,inner_sub_left,hres]

theorem formAction_output_pairing (u v : TV) :
    inner ℂ (TB (formAction ε hε h N hN hb hh m g k u)) (TB v) =
      inner ℂ (TB u) (referenceOutputResolventLp ε hε h N hN hb (TB v))-
        inner ℂ (scaledOrbitExtra ε hε h N hN hh m g k (TJ u)) (TB v) :=
  output_pairing_algebra ε hε h N hN hb (TB u) (TB v)
    (TB (formAction ε hε h N hN hb hh m g k u))
    (scaledOrbitExtra ε hε h N hN hh m g k (TJ u))
    (formAction_output ε hε h N hN hb hh m g k u)
    (referenceOutputResolventLp_staticForm_pairing ε hε h N hN hb hh m g k u v)

private theorem commutator_pairing_algebra (z₁ z₂ w₁ w₂ s₁ s₂ : EnergyOutputSpace)
    (φ₁ φ₂ : OrbitSpace)
    (hp : inner ℂ w₁ z₂ = inner ℂ z₁ (referenceOutputResolventLp ε hε h N hN hb z₂)-inner ℂ s₁ z₂)
    (hw₂ : w₂ = referenceOutputResolventLp ε hε h N hN hb z₂+(-s₂))
    (hs₁ : inner ℂ s₁ z₂ = inner ℂ φ₁ φ₂) :
    inner ℂ w₁ z₂ = inner ℂ z₁ w₂+inner ℂ z₁ s₂-inner ℂ φ₁ φ₂ := by
  have hres : referenceOutputResolventLp ε hε h N hN hb z₂ = w₂+s₂ := by
    rw [hw₂,neg_add_cancel_right]
  rw [hp,hres,inner_add_right,hs₁]

theorem formAction_output_commutator_pairing (u v : TV) :
    inner ℂ (TB (formAction ε hε h N hN hb hh m g k u)) (TB v) =
      inner ℂ (TB u) (TB (formAction ε hε h N hN hb hh m g k v))+
        inner ℂ (TB u) (scaledOrbitExtra ε hε h N hN hh m g k (TJ v))-
        inner ℂ (scaledSectionFirstDual ε hε h N hN (TB u)+
          scaledOrbitSecondDual ε hε h N hN hh (TJ u)) (physicalOrbit h hh (TJ v)) :=
  commutator_pairing_algebra ε hε h N hN hb
    (TB u) (TB v)
    (TB (formAction ε hε h N hN hb hh m g k u))
    (TB (formAction ε hε h N hN hb hh m g k v))
    (scaledOrbitExtra ε hε h N hN hh m g k (TJ u))
    (scaledOrbitExtra ε hε h N hN hh m g k (TJ v))
    (scaledSectionFirstDual ε hε h N hN (TB u)+
      scaledOrbitSecondDual ε hε h N hN hh (TJ u))
    (physicalOrbit h hh (TJ v))
    (formAction_output_pairing ε hε h N hN hb hh m g k u v)
    (formAction_output ε hε h N hN hb hh m g k v)
    (scaledOrbitExtra_staticForm_pairing ε hε h N hN hb hh m g k u v)

#print axioms outputProj_norm
#print axioms extraFirstDual_staticOutput
#print axioms extraFirstDual_norm
#print axioms extraSecondDual_norm
#print axioms base_extra_pairing
#print axioms sectionFirstDual_norm
#print axioms orbitSecondDual_norm
#print axioms scaledSectionFirstDual_norm
#print axioms scaledOrbitSecondDual_norm
#print axioms averaged_orbitExtra_pairing
#print axioms orbitExtra_graph_pairing
#print axioms orbitExtra_staticForm_pairing
#print axioms scaledOrbitExtra_staticForm_pairing
#print axioms orbitExtra_staticForm_bound
#print axioms scaledOrbitExtra_staticForm_bound
#print axioms staticOutputLp_idem
#print axioms staticGraph_output_fixed
#print axioms staticForm_output_fixed
#print axioms yosidaAction_selfAdjoint_pairing
#print axioms referenceOutputActionLp_static_pairing
#print axioms referenceOutputResolventLp_staticForm_pairing
#print axioms formAction_output_pairing
#print axioms formAction_output_commutator_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticFormPairing
