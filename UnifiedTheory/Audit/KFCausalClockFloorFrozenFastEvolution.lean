/- Frozen full dynamics in exponential time. The exact conserved form
is ||Bv||^2+||Av||^2/u, with the static contribution retained for u>0. -/
import UnifiedTheory.Audit.KFCausalClockFloorFrozenReferenceEvolution
import UnifiedTheory.Audit.KFCausalClockFloorFastTimeEnergy
import UnifiedTheory.Audit.KFCausalSplitFormComparison

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFrozenFastEvolution
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorAveragedRegularity (staticMap growingMap)
open KFCausalClockFloorFastTimeEnergy (physicalTime exp_physicalTime)

private theorem energy_rescale (a b a' b' u r : ℝ) (hu : 0 < u)
    (hr : Real.exp (2*r)=u) (he : a+Real.exp (2*r)*b=a'+Real.exp (2*r)*b') :
    b+a/u=b'+a'/u := by
  rw [hr] at he
  apply (mul_right_cancel₀ hu.ne')
  field_simp
  nlinarith only [he]

private theorem slope_rescale {V K : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A B : V →L[ℂ] K) (h u r : ℝ) (hne : h ≠ 0) (hu : 0 < u)
    (hr : Real.exp (2*r)=u) (v z : V) :
    (Complex.I*((1/(2*h*u):ℝ):ℂ))*inner ℂ v (KFCausalBoundedFormCurve.formOperator A B r z)=
    (Complex.I*((1/(2*h):ℝ):ℂ))*inner ℂ v (KFCausalSplitFormComparison.splitOperator A B (1/u) z) := by
  rw [KFCausalBoundedFormCurve.formOperator_pairing,hr]
  simp only [KFCausalSplitFormComparison.splitOperator,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,inner_add_right,inner_smul_right_eq_smul,
    KFCausalMassGram.gram_right_pairing,Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hu.ne',Complex.ofReal_ne_zero.mpr hne]
  ring

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "A" => staticMap ε hε h hne hb m g k
local notation "B" => growingMap ε hε h hne hb m g k

def evolution (u t : ℝ) : V →L[ℂ] V :=
  KFCausalClockFloorFrozenReferenceEvolution.evolution ε hε h hne hb m g k (physicalTime u) (1/(2*h*u)) t

def physical (u t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  KFCausalClockFloorFrozenEvolution.evolution ε hε h hne hb m g k (physicalTime u) (1/(2*h*u)) t

def fastForm (u : ℝ) : V →L[ℂ] V := KFCausalSplitFormComparison.splitOperator A B (1/u)

def energy (u : ℝ) (v : V) : ℝ := ‖B v‖^2+‖A v‖^2/u
local notation "E" => evolution ε hε h hne hb m g k
local notation "U" => physical ε hε h hne hb m g k
local notation "q" => energy ε hε h hne hb m g k

theorem evolution_embedding (u t : ℝ) (v : V) : J (E u t v)=U u t (J v) :=
  KFCausalClockFloorFrozenReferenceEvolution.evolution_embedding ε hε h hne hb m g k (physicalTime u) (1/(2*h*u)) t v

theorem evolution_initial (u : ℝ) (v : V) : E u 0 v=v :=
  KFCausalClockFloorFrozenReferenceEvolution.evolution_initial ε hε h hne hb m g k (physicalTime u) (1/(2*h*u)) v

theorem evolution_continuous (u : ℝ) (v : V) : Continuous (fun t => E u t v) :=
  KFCausalClockFloorFrozenReferenceEvolution.evolution_continuous ε hε h hne hb m g k (physicalTime u) (1/(2*h*u)) v

theorem energy_preserved (u t : ℝ) (hu : 0 < u) (v : V) : q u (E u t v)=q u v := by
  have he := KFCausalClockFloorFrozenReferenceEvolution.energy_preserved ε hε h hne hb m g k (physicalTime u) (1/(2*h*u)) t v
  exact energy_rescale (‖A (E u t v)‖^2) (‖B (E u t v)‖^2) (‖A v‖^2) (‖B v‖^2)
    u (physicalTime u) hu (exp_physicalTime u hu) he

theorem static_energy_bound (u t : ℝ) (hu : 0 < u) (v : V) : ‖A (E u t v)‖^2 ≤ u*q u v := by
  have he := energy_preserved ε hε h hne hb m g k u t hu v
  change ‖B (E u t v)‖^2+‖A (E u t v)‖^2/u=q u v at he
  have hp := sq_nonneg ‖B (E u t v)‖
  exact (div_le_iff₀ hu).mp (by linarith only [he,hp]) |>.trans_eq (mul_comm _ _)

theorem growing_energy_bound (u t : ℝ) (hu : 0 < u) (v : V) : ‖B (E u t v)‖^2 ≤ q u v := by
  have he := energy_preserved ε hε h hne hb m g k u t hu v
  change ‖B (E u t v)‖^2+‖A (E u t v)‖^2/u=q u v at he
  linarith only [he,div_nonneg (sq_nonneg ‖A (E u t v)‖) hu.le]

theorem weak_schrodinger (u t : ℝ) (hu : 0 < u) (v z : V) :
    HasDerivAt (fun a => inner ℂ (U u a (J v)) (J z))
      ((Complex.I*((1/(2*h):ℝ):ℂ))*inner ℂ (E u t v) (fastForm ε hε h hne hb m g k u z)) t := by
  have hd := KFCausalClockFloorFrozenReferenceEvolution.weak_schrodinger ε hε h hne hb m g k (physicalTime u) (1/(2*h*u)) v z t
  exact (slope_rescale A B h u (physicalTime u) hne hu (exp_physicalTime u hu) (E u t v) z) ▸ hd

#print axioms evolution_embedding
#print axioms evolution_initial
#print axioms evolution_continuous
#print axioms energy_preserved
#print axioms static_energy_bound
#print axioms growing_energy_bound
#print axioms weak_schrodinger
end
end UnifiedTheory.Audit.KFCausalClockFloorFrozenFastEvolution
