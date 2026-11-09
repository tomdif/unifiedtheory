/- The actual full frozen and growing groups satisfy the shifted-
resolvent derivative identities required by the strong-limit argument.
Every domain statement is discharged using the actual Hamiltonians. -/
import UnifiedTheory.Audit.KFCausalClockFloorFrozenFastEvolution
import UnifiedTheory.Audit.KFCausalClockFloorGrowingEvolution
import UnifiedTheory.Audit.KFCausalClockFloorGrowingResolventLimit
import UnifiedTheory.Audit.KFCausalResolventUnitaryResidual

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorResolventFlowData
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalUnitaryOrbitAverage (StrongUnitaryGroup)
open KFCausalClockFloorFastTimeEnergy (physicalTime)
open KFCausalClockFloorFastResolventIdentification

private theorem rate_rescale {H : Type*} [AddCommGroup H] [Module ℂ H]
    [Module ℝ H] [IsScalarTower ℝ ℂ H]
    (h u : ℝ) (hne : h ≠ 0) (hu : 0 < u) (x : H) :
    (-Complex.I*((1/(2*h*u):ℝ):ℂ)) • x=
      (-Complex.I*((1/(2*h):ℝ):ℂ)) • ((1/u:ℝ) • x) := by
  have hs : (1/u:ℝ) • x=((1/u:ℝ):ℂ) • x := (algebraMap_smul ℂ (1/u:ℝ) x).symm
  rw [hs,smul_smul]
  congr 1
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hne,Complex.ofReal_ne_zero.mpr hu.ne']

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "R" => KFCausalClockFloorFastResolvent.resolvent ε hε h hne hb m g k
local notation "S" => KFCausalClockFloorFastResolvent.limitResolvent ε hε h hne hb m g k
local notation "T" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hne hb m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hne hb m g k
local notation "c" => (-Complex.I*((1/(2*h):ℝ):ℂ))

def growingGroup : StrongUnitaryGroup Hilbert where
  action := KFCausalClockFloorGrowingEvolution.evolution ε hε h hne hb m g k
  initial := KFCausalClockFloorGrowingEvolution.evolution_initial ε hε h hne hb m g k
  compose := fun s t x => (KFCausalClockFloorGrowingEvolution.evolution_compose ε hε h hne hb m g k s t x).symm
  continuous_orbit := KFCausalClockFloorGrowingEvolution.evolution_continuous ε hε h hne hb m g k

def frozenGroup (u : ℝ) : StrongUnitaryGroup Hilbert where
  action := KFCausalClockFloorFrozenFastEvolution.physical ε hε h hne hb m g k u
  initial := KFCausalClockFloorFrozenEvolution.evolution_initial ε hε h hne hb m g k (physicalTime u) (1/(2*h*u))
  compose := fun s t x => (KFCausalClockFloorFrozenEvolution.evolution_compose ε hε h hne hb m g k (physicalTime u) (1/(2*h*u)) s t x).symm
  continuous_orbit := KFCausalClockFloorFrozenEvolution.evolution_continuous ε hε h hne hb m g k (physicalTime u) (1/(2*h*u))

local notation "V" => growingGroup ε hε h hne hb m g k
local notation "U" => frozenGroup ε hε h hne hb m g k

theorem limit_resolvent_contraction (x : Hilbert) : ‖S x‖ ≤ ‖x‖ := by
  let D := KFCausalClockFloorGrowingHamiltonian.formData ε hε h hne hb m g k
  let J := KFCausalClosedGraphForm.embedding D
  have hj : ‖J‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
    simpa only [one_mul] using KFCausalClosedGraphForm.embedding_contraction D v)
  exact ((S).le_opNorm x).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (KFCausalFormResolvent.resolvent_norm_le_one J hj) (norm_nonneg x))

theorem limit_resolvent_dense : DenseRange S :=
  KFCausalFormResolvent.resolvent_dense
    (KFCausalClosedGraphForm.embedding (KFCausalClockFloorGrowingHamiltonian.formData ε hε h hne hb m g k))
    (KFCausalClosedGraphForm.embedding_injective _)
    (KFCausalClosedGraphForm.embedding_dense _)

theorem growing_resolvent_derivative (f : Hilbert) (t : ℝ) :
    HasDerivAt (fun s => (V).action s (S f)) (c • (V).action t (f-S f)) t := by
  let x := limitPoint ε hε h hne hb m g k f
  have he : T x=f-S f := eq_sub_of_add_eq (limit_right_inverse ε hε h hne hb m g k f)
  have hd := KFCausalClockFloorGrowingEvolution.schrodinger ε hε h hne hb m g k x t
  exact hd.congr_deriv (congrArg (fun y : Hilbert => c • y)
    ((KFCausalClockFloorGrowingEvolution.hamiltonian_commutes ε hε h hne hb m g k t x).trans
      (congrArg ((V).action t) he)))

theorem frozen_resolvent_derivative (u : ℝ) (hu : 0 < u) (f : Hilbert) (t : ℝ) :
    HasDerivAt (fun s => (U u).action s (R u f)) (c • (U u).action t (f-R u f)) t := by
  let x := actualPoint ε hε h hne hb m g k u hu f
  have he : (1/u:ℝ) • H (physicalTime u) x=f-R u f :=
    eq_sub_of_add_eq (actual_right_inverse ε hε h hne hb m g k u hu f)
  have hd := KFCausalClockFloorFrozenEvolution.schrodinger ε hε h hne hb m g k
    (physicalTime u) (1/(2*h*u)) x t
  have hc := KFCausalClockFloorFrozenEvolution.hamiltonian_commutes ε hε h hne hb m g k
    (physicalTime u) (1/(2*h*u)) t x
  have hval : (x : Hilbert)=R u f := actualPoint_coe ε hε h hne hb m g k u hu f
  have hs := hd.congr_deriv ((congrArg (fun y : Hilbert => (-Complex.I*((1/(2*h*u):ℝ):ℂ)) • y) hc).trans
    ((rate_rescale h u hne hu ((U u).action t (H (physicalTime u) x))).trans
      (congrArg (fun y : Hilbert => c • y)
        (((((U u).action t : Hilbert →L[ℂ] Hilbert).map_smul_of_tower (1/u:ℝ) (H (physicalTime u) x)).symm).trans
          (congrArg ((U u).action t) he)))))
  have hf : (fun s => (U u).action s (x:Hilbert))=(fun s => (U u).action s (R u f)) :=
    funext (fun s => congrArg ((U u).action s) hval)
  exact (congrArg (fun w => HasDerivAt w (c • (U u).action t (f-R u f)) t) hf).mp hs

theorem resolvent_difference_bound (u : ℝ) (hu : 0 < u) (f : Hilbert) :
    ‖R u f-S f‖ ≤ 2*‖f‖ := by
  have h₁ := KFCausalClockFloorFastResolvent.resolvent_contraction ε hε h hne hb m g k u hu f
  have h₂ := limit_resolvent_contraction ε hε h hne hb m g k f
  exact (norm_sub_le _ _).trans (by linarith)

#print axioms limit_resolvent_contraction
#print axioms limit_resolvent_dense
#print axioms growing_resolvent_derivative
#print axioms frozen_resolvent_derivative
#print axioms resolvent_difference_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorResolventFlowData
