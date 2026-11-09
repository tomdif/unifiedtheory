/- Exact signed shear response as a weighted shear momentum expectation.
Real clock terms cancel on the actual shear domain. No sign or Hamiltonian
energy bound for the remaining expectation is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorShearWeight
import UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorSignedShearResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shiftedDefect)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockShearRealMultiplier
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse (response response_split)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (shearCorrection)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hbound : |h| ≤ 2*Real.pi*ε/3)
local notation "Z" => shiftedDefect ε hε h hbound
local notation "D" => defectOperator ε hε
local notation "J" => shearMomentum h
local notation "responseL" => KFCausalClockFloorVacuumMomentumResponse.response ε hε h hbound

def realContraction : Hilbert →L[ℂ] Hilbert :=
  multiplyL (fun x => ((physicalSymbol ε h x).re/2:ℝ))
    (by exact (Complex.continuous_ofReal.comp
      ((Complex.continuous_re.comp (physicalSymbol_continuous ε hε h hbound)).div_const 2)).measurable)
    (fun x => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_div]
      norm_num
      linarith [(Complex.abs_re_le_norm _).trans (physicalSymbol_bound ε hε h hbound x)])

def realPart : Hilbert →L[ℂ] Hilbert := (2:ℂ) • realContraction ε hε h hbound

theorem realPart_coe (f : Hilbert) :
    realPart ε hε h hbound f =ᵐ[volume] fun x => ((physicalSymbol ε h x).re:ℂ)*f x := by
  let M := realContraction ε hε h hbound
  have hm : M f =ᵐ[volume] fun x => (((physicalSymbol ε h x).re/2:ℝ):ℂ)*f x :=
    multiplyL_coe _ _ _ f
  filter_upwards [Lp.coeFn_smul (2:ℂ) (M f),hm] with x hs hm
  change ((2:ℂ) • M f) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  change 2*(M f x) = _
  change M f x = _ at hm
  rw [hm]
  push_cast
  ring

theorem realPart_shear_pairing (hne : h ≠ 0) (g j : Hilbert) (hj : (g,j) ∈ (J).graph) :
    (inner ℂ g (realPart ε hε h hbound j)).im = 0 :=
  real_shear_pairing _ (fun s => (physicalSymbol ε h (s,0)).re)
    (realPart_coe ε hε h hbound) h hne g j hj

variable (hne : h ≠ 0)
local notation "Q" => root ε hε h hbound hne
include hε hbound hne

theorem root_symmetric (f g : Hilbert) : inner ℂ (Q f) g = inner ℂ f (Q g) :=
  real_symmetric _ (rootValue ε h) (root_coe ε hε h hbound hne) f g

theorem root_shear_graph (g j : Hilbert) (hj : (g,j) ∈ (J).graph) :
    (Q g,Q j) ∈ (J).graph :=
  clock_graph _ (fun s => (rootValue ε h s:ℂ)) (root_coe ε hε h hbound hne) h hne g j hj

theorem symbol_split (s : ℝ) : physicalSymbol ε h (s,0) =
    ((physicalSymbol ε h (s,0)).re:ℂ)+(((2*h/ε:ℝ):ℂ)*Complex.I)*((rootValue ε h s:ℂ)^2) := by
  have hs := rootValue_square ε hε h hbound hne s
  rw [← Complex.ofReal_pow]
  apply Complex.ext
  · simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,
      sub_zero,add_zero]
  · simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.mul_re,
      Complex.ofReal_re,Complex.I_re,Complex.I_im,mul_zero,mul_one,
      sub_zero,add_zero,zero_add]
    rw [hs]
    unfold coefficient
    field_simp [hne,hε.ne']

theorem shifted_split (f : Hilbert) :
    Z f = realPart ε hε h hbound f+(((2*h/ε:ℝ):ℂ)*Complex.I) • Q (Q f) := by
  let c : ℂ := ((2*h/ε:ℝ):ℂ)*Complex.I
  apply Lp.ext
  filter_upwards [shiftedDefect_physical_coe ε hε h hbound f,realPart_coe ε hε h hbound f,
    root_coe ε hε h hbound hne (Q f),root_coe ε hε h hbound hne f,
    Lp.coeFn_add (realPart ε hε h hbound f) (c • Q (Q f)),
    Lp.coeFn_smul c (Q (Q f))] with x hz ha hqq hq hs hc
  change Z f x = (realPart ε hε h hbound f+c • Q (Q f)) x
  rw [hz,hs]
  simp only [Pi.add_apply]
  rw [ha,hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hqq,hq]
  have he := symbol_split ε hε h hbound hne x.1
  change physicalSymbol ε h x = ((physicalSymbol ε h x).re:ℂ)+
    (((2*h/ε:ℝ):ℂ)*Complex.I)*((rootValue ε h x.1:ℂ)^2) at he
  conv_lhs => rw [he]
  dsimp only [c]
  ring

theorem shear_pairing (g j : Hilbert) (hj : (g,j) ∈ (J).graph) :
    (inner ℂ g (shearCorrection ε hε h hbound j)).im =
      -(2*h/ε^2)*(inner ℂ (Q g) (Q j)).re := by
  change (inner ℂ g ((1/(ε:ℂ)) • (D j-Z j))).im = _
  have hc : (1/(ε:ℂ)) = ((1/ε:ℝ):ℂ) := by push_cast; rfl
  rw [inner_smul_right,hc,inner_sub_right,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,add_zero,Complex.sub_im,
    defect_shear_pairing ε hε h hne g j hj,shifted_split ε hε h hbound hne j,
    inner_add_right,Complex.add_im,realPart_shear_pairing ε hε h hbound hne g j hj,
    zero_add,inner_smul_right,← root_symmetric ε hε h hbound hne g (Q j)]
  simp only [Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add]
  ring

theorem response_weighted_shear (g j : Hilbert) (hj : (g,j) ∈ (J).graph) :
    response ε hε h hbound g j = responseL g+(4/ε^2)*(inner ℂ (Q g) (Q j)).re := by
  rw [response_split ε hε h hbound hne g j,shear_pairing ε hε h hbound hne g j hj]
  field_simp [hne,hε.ne']
  ring

theorem response_weighted_bound (g j : Hilbert) (hj : (g,j) ∈ (J).graph) :
    |response ε hε h hbound g j-responseL g| ≤ (4/ε^2)*‖Q g‖*‖Q j‖ := by
  rw [response_weighted_shear ε hε h hbound hne g j hj,add_sub_cancel_left,
    abs_mul,abs_of_nonneg (by positivity : 0 ≤ 4/ε^2)]
  exact (mul_le_mul_of_nonneg_left
    ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _))
    (by positivity : 0 ≤ 4/ε^2)).trans_eq (by ring)

theorem response_balanced_bound (g j : Hilbert) (hj : (g,j) ∈ (J).graph) :
    |response ε hε h hbound g j-responseL g| ≤ (4/ε^2)*‖D g‖*‖D j‖ := by
  apply (response_weighted_bound ε hε h hbound hne g j hj).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (root_norm_le_defect ε hε h hbound hne g)
      (by positivity)) (root_norm_le_defect ε hε h hbound hne j) (norm_nonneg _) (by positivity)

theorem core_weighted_response (f g : Hilbert)
    (hfg : (f,g) ∈ KFCausalClockFloorJointMomentumCore.regularGraph ε hε h) :
    ∃ b tb j : Hilbert,
      (f,b) ∈ (KFCausalClockFloorPureClockMomentum.pureMomentum ε hε h).graph ∧
      (b,tb) ∈ (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph ∧
      (g,j) ∈ (J).graph ∧
      (-2/h)*(inner ℂ g tb).im = responseL g+(4/ε^2)*(inner ℂ (Q g) (Q j)).re := by
  obtain ⟨b,tb,j,hb,ht,hj,hr⟩ :=
    KFCausalClockFloorPureClockVacuumResponse.core_response ε hε h hbound hne f g hfg
  exact ⟨b,tb,j,hb,ht,hj,hr.trans (response_weighted_shear ε hε h hbound hne g j hj)⟩

#print axioms realPart_coe
#print axioms realPart_shear_pairing
#print axioms root_symmetric
#print axioms root_shear_graph
#print axioms symbol_split
#print axioms shifted_split
#print axioms shear_pairing
#print axioms response_weighted_shear
#print axioms response_weighted_bound
#print axioms response_balanced_bound
#print axioms core_weighted_response
end
end UnifiedTheory.Audit.KFCausalClockFloorSignedShearResponse
