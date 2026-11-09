/- Comparison of the actual time-dependent full flow with its full
frozen flow in exponential time. Every static factor is retained. -/
import UnifiedTheory.Audit.KFCausalClockFloorFrozenFastEvolution
import UnifiedTheory.Audit.KFCausalClockFloorSmoothedFullDerivative
import UnifiedTheory.Audit.KFCausalSplitFormComparison

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFrozenComparison
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorAveragedRegularity (staticMap growingMap referenceFormOperator)
open KFCausalClockFloorAveragedFormFlow (formFlow formFlow_initial formFlow_physical_norm)
open KFCausalClockFloorFastTimeEnergy (physicalTime physicalTime_derivative physicalTime_continuous exp_physicalTime exp_neg_physicalTime)
open KFCausalBoundedFormCurve (gram formOperator)
open KFCausalSplitFormComparison (splitOperator)

private theorem rescale {V K : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A B : V →L[ℂ] K) (h u r : ℝ) (hne : h ≠ 0) (hu : 0 < u)
    (hr : Real.exp (2*r)=u) (v : V) :
    (-Complex.I*((1/(2*h*u):ℝ):ℂ)) • formOperator A B r v=
      (-Complex.I*((1/(2*h):ℝ):ℂ)) • splitOperator A B (1/u) v := by
  have hc : (-Complex.I*((1/(2*h*u):ℝ):ℂ))=
      (-Complex.I*((1/(2*h):ℝ):ℂ))*((1/u:ℝ):ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hne,Complex.ofReal_ne_zero.mpr hu.ne']
  rw [hc,mul_smul]
  congr 1
  rw [Complex.coe_smul]
  simp only [formOperator,splitOperator,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_add,smul_smul,hr,one_div,inv_mul_cancel₀ hu.ne',one_smul]
  module

private theorem time_rescale {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module ℝ V] [IsScalarTower ℝ ℂ V] (h u : ℝ) (hne : h ≠ 0) (hu : 0 < u) (v : V) :
    (1/(2*u):ℝ) • ((-Complex.I*((1/h:ℝ):ℂ)) • v)=
      (-Complex.I*((1/(2*h*u):ℝ):ℂ)) • v := by
  rw [← smul_assoc]
  congr 1
  rw [Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hne,Complex.ofReal_ne_zero.mpr hu.ne']

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "A" => staticMap ε hε h hne hb m g k
local notation "B" => growingMap ε hε h hne hb m g k
local notation "Q" => referenceFormOperator ε hε h hne hb m g k
local notation "F" => formFlow ε hε h hne hb m g k
local notation "E" => KFCausalClockFloorFrozenFastEvolution.evolution ε hε h hne hb m g k
local notation "q" => KFCausalClockFloorFrozenFastEvolution.energy ε hε h hne hb m g k
local notation "c" => (-Complex.I*((1/(2*h):ℝ):ℂ))

def actual (U u : ℝ) (v : V) : V := F (physicalTime U) (physicalTime u) v
def frozen (U u : ℝ) (v : V) : V := E U (u-U) v
local notation "a" => actual ε hε h hne hb m g k
local notation "b" => frozen ε hε h hne hb m g k

def massSlope (u : ℝ) (v : V) : V :=
  c • KFCausalClockFloorFrozenFastEvolution.fastForm ε hε h hne hb m g k u v
local notation "s" => massSlope ε hε h hne hb m g k

def discrepancy (U u : ℝ) (v : V) : ℝ := ‖J (a U u v)-J (b U u v)‖^2
def slope (U u : ℝ) (v : V) : ℝ :=
  (1/h)*(1/u-1/U)*(inner ℂ (A (a U u v)) (A (b U u v))).im
local notation "d" => discrepancy ε hε h hne hb m g k
local notation "slopeAt" => slope ε hε h hne hb m g k

theorem actual_mass_derivative (U u : ℝ) (hu : 0 < u) (v : V) :
    HasDerivAt (fun r => gram J (a U r v)) (s u (a U u v)) u := by
  have hd := (KFCausalClockFloorSmoothedFullDerivative.mass_derivative ε hε h hne hb m g k
    (physicalTime U) (physicalTime u) v).scomp u (physicalTime_derivative u hu)
  change HasDerivAt (fun r => gram J (a U r v))
    ((1/(2*u):ℝ) • ((-Complex.I*((1/h:ℝ):ℂ)) • Q (physicalTime u) (a U u v))) u at hd
  exact hd.congr_deriv ((time_rescale h u hne hu (Q (physicalTime u) (a U u v))).trans
    (rescale A B h u (physicalTime u) hne hu (exp_physicalTime u hu) (a U u v)))

theorem frozen_mass_derivative (U u : ℝ) (hU : 0 < U) (v : V) :
    HasDerivAt (fun r => gram J (b U r v)) (s U (b U u v)) u := by
  have hd := (KFCausalClockFloorFrozenReferenceEvolution.mass_derivative ε hε h hne hb m g k
    (physicalTime U) (1/(2*h*U)) v (u-U)).scomp u ((hasDerivAt_id u).sub_const U)
  simp only [one_smul] at hd
  exact hd.congr_deriv (rescale A B h U (physicalTime U) hne hU (exp_physicalTime U hU) (b U u v))

theorem frozen_continuous (U : ℝ) (v : V) : Continuous (fun u => b U u v) :=
  (KFCausalClockFloorFrozenFastEvolution.evolution_continuous ε hε h hne hb m g k U v).comp
    (continuous_id.sub continuous_const)

theorem discrepancy_derivative (U u : ℝ) (hU : 0 < U) (hu : 0 < u) (v : V) :
    HasDerivAt (fun r => d U r v) (slopeAt U u v) u := by
  apply KFCausalSplitFormComparison.distance_square_derivative J A B
    (fun r => a U r v) (fun r => b U r v) h (1/u) (1/U) u hne
    (frozen_continuous ε hε h hne hb m g k U v).continuousAt
    (actual_mass_derivative ε hε h hne hb m g k U u hu v)
    (frozen_mass_derivative ε hε h hne hb m g k U u hU v)
  · intro r
    exact (formFlow_physical_norm ε hε h hne hb m g k (physicalTime U) (physicalTime r) v).trans
      (formFlow_physical_norm ε hε h hne hb m g k (physicalTime U) (physicalTime u) v).symm
  · intro r
    exact (KFCausalClockFloorFrozenReferenceEvolution.physical_norm ε hε h hne hb m g k
      (physicalTime U) (1/(2*h*U)) (r-U) v).trans
        (KFCausalClockFloorFrozenReferenceEvolution.physical_norm ε hε h hne hb m g k
          (physicalTime U) (1/(2*h*U)) (u-U) v).symm

theorem discrepancy_initial (U : ℝ) (v : V) : d U U v=0 := by
  have ha : a U U v=v := formFlow_initial ε hε h hne hb m g k (physicalTime U) v
  have hb' : b U U v=v := by
    change E U (U-U) v=v
    rw [sub_self]
    exact KFCausalClockFloorFrozenFastEvolution.evolution_initial ε hε h hne hb m g k U v
  exact (congrArg₂ (fun x y : V => ‖J x-J y‖^2) ha hb').trans (by simp only [sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0)])

#print axioms actual_mass_derivative
#print axioms frozen_mass_derivative
#print axioms frozen_continuous
#print axioms discrepancy_derivative
#print axioms discrepancy_initial
end
end UnifiedTheory.Audit.KFCausalClockFloorFrozenComparison
