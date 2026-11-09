/- All positive shifted resolvents and Yosida approximants are constructed
for the actual growing Hamiltonian, with its original domain retained. -/
import UnifiedTheory.Audit.KFCausalShiftedResolventFromOne
import UnifiedTheory.Audit.KFCausalClockFloorGrowingResolventLimit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingYosida
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorGrowingHamiltonian (hamiltonian)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "D" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hne hb m g k
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "R" => KFCausalClockFloorFastResolvent.limitResolvent ε hε h hne hb m g k
local notation "T" => hamiltonian ε hε h hne hb m g k

private theorem r_injective : Function.Injective R :=
  KFCausalFormResolvent.resolvent_injective J
    (KFCausalClosedGraphForm.embedding_injective D) (KFCausalClosedGraphForm.embedding_dense D)

private theorem r_positive (x : Hilbert) : 0 ≤ (inner ℂ (R x) x).re :=
  (KFCausalFormResolvent.resolvent_positive J x).trans_eq
    (congrArg Complex.re (KFCausalFormResolvent.resolvent_symmetric J x x).symm)

private theorem r_contraction (x : Hilbert) : ‖R x‖ ≤ ‖x‖ := by
  have hj : ‖J‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
    simpa only [one_mul] using KFCausalClosedGraphForm.embedding_contraction D v)
  exact ((R).le_opNorm x).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (KFCausalFormResolvent.resolvent_norm_le_one J hj) (norm_nonneg x))

theorem shift_isUnit (a : ℝ) (ha : 0 < a) :
    IsUnit (KFCausalShiftedResolventFromOne.shift R a) :=
  KFCausalShiftedResolventFromOne.shift_isUnit R a ha (r_positive ε hε h hne hb m g k)
    (r_contraction ε hε h hne hb m g k) (KFCausalFormResolvent.resolvent_symmetric J)

def resolvent (a : ℝ) : Hilbert →L[ℂ] Hilbert := KFCausalShiftedResolventFromOne.resolvent R a

theorem resolves (a : ℝ) (ha : 0 < a) :
    KFCausalPositiveResolventBounds.Resolves T (resolvent ε hε h hne hb m g k a) a :=
  KFCausalShiftedResolventFromOne.resolves R (r_injective ε hε h hne hb m g k) a
    (shift_isUnit ε hε h hne hb m g k a ha)

theorem left_inverse (a : ℝ) (ha : 0 < a) (x : (T).domain) :
    resolvent ε hε h hne hb m g k a (T x+a • (x:Hilbert))=x :=
  KFCausalShiftedResolventFromOne.left_inverse R (r_injective ε hε h hne hb m g k) a
    (shift_isUnit ε hε h hne hb m g k a ha) x

theorem resolvent_commutes_one (a : ℝ) (ha : 0 < a) :
    resolvent ε hε h hne hb m g k a*R=R*resolvent ε hε h hne hb m g k a :=
  KFCausalShiftedResolventFromOne.resolvent_commutes_one R a (shift_isUnit ε hε h hne hb m g k a ha)

theorem resolvents_commute (a b : ℝ) (ha : 0 < a) (hb' : 0 < b) :
    resolvent ε hε h hne hb m g k a*resolvent ε hε h hne hb m g k b=
      resolvent ε hε h hne hb m g k b*resolvent ε hε h hne hb m g k a :=
  KFCausalShiftedResolventFromOne.resolvents_commute R a b
    (shift_isUnit ε hε h hne hb m g k a ha) (shift_isUnit ε hε h hne hb m g k b hb')

def yosida (a : ℝ) : Hilbert →L[ℂ] Hilbert :=
  KFCausalYosidaApproximation.yosida (resolvent ε hε h hne hb m g k a) a

theorem yosida_selfAdjoint (a : ℝ) (ha : 0 < a) : IsSelfAdjoint (yosida ε hε h hne hb m g k a) :=
  KFCausalYosidaApproximation.yosida_selfAdjoint T (resolvent ε hε h hne hb m g k a) a
    (resolves ε hε h hne hb m g k a ha) (KFCausalClockFloorGrowingHamiltonian.hamiltonian_selfAdjoint ε hε h hne hb m g k)

theorem yosida_limit (x : (T).domain) :
    Tendsto (fun a => yosida ε hε h hne hb m g k a (x:Hilbert)) atTop (𝓝 (T x)) :=
  KFCausalYosidaApproximation.yosida_strong_limit_on_domain T (resolvent ε hε h hne hb m g k)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_dense ε hε h hne hb m g k)
    (resolves ε hε h hne hb m g k)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hne hb m g k)
    (left_inverse ε hε h hne hb m g k) x

private theorem polynomial_commutes {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S Q : E →L[ℂ] E) (a b : ℝ) (hc : S*Q=Q*S) :
    KFCausalYosidaApproximation.yosida S a*KFCausalYosidaApproximation.yosida Q b=
      KFCausalYosidaApproximation.yosida Q b*KFCausalYosidaApproximation.yosida S a := by
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun L : E →L[ℂ] E => L x) hc
  simp only [ContinuousLinearMap.mul_apply] at he
  simp only [ContinuousLinearMap.mul_apply,KFCausalYosidaApproximation.yosida_apply,
    map_sub,ContinuousLinearMap.map_smul_of_tower,he]
  module

theorem yosida_commute (a b : ℝ) (ha : 0 < a) (hb' : 0 < b) :
    yosida ε hε h hne hb m g k a*yosida ε hε h hne hb m g k b=
      yosida ε hε h hne hb m g k b*yosida ε hε h hne hb m g k a :=
  polynomial_commutes _ _ a b (resolvents_commute ε hε h hne hb m g k a b ha hb')

theorem yosida_commutes_one (a : ℝ) (ha : 0 < a) :
    yosida ε hε h hne hb m g k a*R=R*yosida ε hε h hne hb m g k a := by
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun L : Hilbert →L[ℂ] Hilbert => L x)
    (resolvent_commutes_one ε hε h hne hb m g k a ha)
  simp only [ContinuousLinearMap.mul_apply] at he
  simp only [yosida,ContinuousLinearMap.mul_apply,KFCausalYosidaApproximation.yosida_apply,
    map_sub,ContinuousLinearMap.map_smul_of_tower,he]

#print axioms shift_isUnit
#print axioms resolves
#print axioms left_inverse
#print axioms resolvent_commutes_one
#print axioms resolvents_commute
#print axioms yosida_selfAdjoint
#print axioms yosida_limit
#print axioms yosida_commute
#print axioms yosida_commutes_one
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingYosida
