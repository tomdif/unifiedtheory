/- Actual potential and static graphs on the original finite sourced packets.
The radial output is identified through the genuine maximal multiplier graph;
subtracting it from the already constructed growing output identifies the
literal closed potential Hamiltonian. No common graph-core claim is made. -/
import UnifiedTheory.Audit.KFCausalOrderedStaticPotentialHilbertBound
import UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialSum

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFinitePotentialStaticGraph
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalFiniteSecondHamiltonianColumns (second)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalFiniteGrowingHamiltonianOutput (growingOutput)
open KFCausalFiniteHamiltonianTimeDerivative (coefficient coefficientDerivative outputDerivative)
open KFCausalOrderedStaticPotentialHilbertBound (weightedOutput)
open KFCausalIndependentRadialPacketMoments (momentState momentState_charge_coe)
open KFCausalIndependentRadialPacketDerivatives (momentProfile leftRadius rightRadius)
open KFCausalClockFloorRadialYosidaDomain (operator)

private theorem single_radial_graph (ε a h w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (hε : 0<ε) (ha : 0<a) (hh : h≠0) (hw : 1≤w) :
    (KFCausalIndependentRadialPackets.state ε a h w w C p b P hε ha hh hw hw,
      (1/2:ℂ) • inverseL ε hε (inverseL ε hε
        (momentState ε a h w w C p b P hε ha hh hw hw 1 0))+
      (1/2:ℂ) • inverseL ε hε (inverseL ε hε
        (momentState ε a h w w C p b P hε ha hh hw hw 0 1))) ∈
      (operator ε hε h).graph := by
  apply (KFCausalUnitaryRealMultiplier.realPullback_graph chargeCoordinates
    (KFCausalClockFloorRadialYosidaSymbol.radial ε h) _ _ _).mpr
  simp only [map_add,map_smul]
  filter_upwards [Lp.coeFn_add
      ((1/2:ℂ) • chargeCoordinates (inverseL ε hε (inverseL ε hε
        (momentState ε a h w w C p b P hε ha hh hw hw 1 0))))
      ((1/2:ℂ) • chargeCoordinates (inverseL ε hε (inverseL ε hε
        (momentState ε a h w w C p b P hε ha hh hw hw 0 1)))),
    Lp.coeFn_smul (1/2:ℂ) (chargeCoordinates (inverseL ε hε (inverseL ε hε
      (momentState ε a h w w C p b P hε ha hh hw hw 1 0)))),
    Lp.coeFn_smul (1/2:ℂ) (chargeCoordinates (inverseL ε hε (inverseL ε hε
      (momentState ε a h w w C p b P hε ha hh hw hw 0 1)))),
    KFCausalIndependentRadialMomentClock.inverseL_sq_charge_coe ε hε
      (momentState ε a h w w C p b P hε ha hh hw hw 1 0),
    KFCausalIndependentRadialMomentClock.inverseL_sq_charge_coe ε hε
      (momentState ε a h w w C p b P hε ha hh hw hw 0 1),
    momentState_charge_coe ε a h w w C p b P hε ha hh hw hw 1 0,
    momentState_charge_coe ε a h w w C p b P hε ha hh hw hw 0 1,
    KFCausalIndependentRadialPackets.state_charge_coe ε a h w w C p b P hε ha hh hw hw]
    with x hadd hsm1 hsm2 hD1 hD2 hM1 hM2 hS
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hsm1,hsm2]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hD1,hD2,hM1,hM2,hS,KFCausalClockFloorRadialYosidaSymbol.radial_coordinates]
  simp only [momentProfile,leftRadius,rightRadius,pow_one,pow_zero,mul_one,one_mul,
    KFCausalGaussianHolomorphicClockWeight.physicalPower,if_true,
    KFCausalClockFloorFlow.clock,Complex.ofReal_mul,Complex.ofReal_inv,
    Complex.ofReal_add,Complex.ofReal_pow,Complex.ofReal_ofNat,div_eq_mul_inv,mul_inv_rev]
  ring

private theorem coefficient_growing (m g k : ℝ) (hm : 0≤m) (hg : 0≤g) (hk : 0≤k)
    (j : Fin 8) : (1/2:ℂ)*coefficientDerivative m g k 0 j=
      (![0,0,0,1/2,1/2,m/2,g/4,k] : Fin 8→ℝ) j := by
  fin_cases j <;>
    simp only [coefficientDerivative,coefficient,KFCausalPhysicalEnergyFactors.energyWeight,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Complex.star_def,Complex.conj_ofReal,
      Real.exp_zero,one_mul] <;> norm_num only
  all_goals rw [←Complex.ofReal_mul,←sq,Real.sq_sqrt (by positivity)]
  all_goals push_cast
  all_goals ring

private theorem growing_sum (m g k : ℝ) (hm : 0≤m) (hg : 0≤g) (hk : 0≤k)
    (Z : Fin 8→Hilbert) :
    (2:ℝ)⁻¹ • (∑j,coefficientDerivative m g k 0 j • Z j)=
      ((1/2:ℂ) • Z 3+(1/2:ℂ) • Z 4)+
      ((k:ℂ) • Z 7+((m/2:ℝ):ℂ) • Z 5+((g/4:ℝ):ℂ) • Z 6) := by
  rw [←Complex.coe_smul]
  simp only [Complex.ofReal_inv,Complex.ofReal_ofNat,Finset.smul_sum,smul_smul,
    show (2:ℂ)⁻¹=1/2 by norm_num,coefficient_growing m g k hm hg hk]
  simp [Fin.sum_univ_succ]
  simp only [←Complex.coe_smul,Complex.ofReal_div,Complex.ofReal_inv,Complex.ofReal_ofNat]
  abel

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n→ℝ) (C b : Fin n→ℂ)
  (P : Fin n→Polynomial ℂ) (hε : 0<ε) (ha : ∀i,0<a i)
  (hh : h≠0) (hw : ∀i,1≤w i) (hb : |h|≤ε/10)
local notation "ψ" => KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw
local notation "Z" => fun j=>zeroProjection h hh (second n ε h a w p C b P hε ha hh hw hb j)

def radialOutput : Hilbert := (1/2:ℂ) • Z 3+(1/2:ℂ) • Z 4

theorem radial_graph :
    (ψ,radialOutput n ε h a w p C b P hε ha hh hw hb) ∈ (operator ε hε h).graph := by
  have hs := (operator ε hε h).graph.sum_mem
    (fun i (_ : i∈(Finset.univ:Finset (Fin n)))=>
      single_radial_graph ε (a i) h (w i) (C i) (p i) (b i) (P i) hε (ha i) hh (hw i))
  simp only [←prod_mk_sum,KFCausalIndependentRadialPackets.state_diagonal] at hs
  have h3 := KFCausalFiniteKineticHamiltonianColumns.projected_finite_eq
    n ε h a w p C b P hε ha hh hw hb 2
  have h4 := KFCausalFiniteKineticHamiltonianColumns.projected_finite_eq
    n ε h a w p C b P hε ha hh hw hb 3
  change Z 3=_ at h3
  change Z 4=_ at h4
  rw [radialOutput,h3,h4]
  simpa only [KFCausalReciprocalNeutralSuperposition.state,
    KFCausalIndependentRadialKineticOutputIdentity.kineticCombination,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Finset.sum_add_distrib,Finset.smul_sum] using hs

theorem growing_split (m g k : ℝ) (hm : 0≤m) (hg : 0≤g) (hk : 0≤k) :
    growingOutput n ε h a w p C b P hε ha hh hw hb m g k=
      radialOutput n ε h a w p C b P hε ha hh hw hb+
      weightedOutput n ε h a w p C b P hε ha hh hw hb m g k := by
  exact growing_sum m g k hm hg hk Z

theorem potential_graph (m g k : ℝ) (hm : 0≤m) (hg : 0≤g) (hk : 0≤k) :
    (ψ,weightedOutput n ε h a w p C b P hε ha hh hw hb m g k) ∈
      (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
        (hamiltonian_strip ε h hε hb) m g k).graph := by
  let G := KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh
    (hamiltonian_strip ε h hε hb) m g k
  let x : G.domain := ⟨ψ,KFCausalFiniteGrowingHamiltonianOutput.growing_domain
    n ε h a w p C b P hε ha hh hw hb m g k⟩
  have he : G x=growingOutput n ε h a w p C b P hε ha hh hw hb m g k :=
    G.mem_graph_snd_inj' (G.mem_graph x)
      (KFCausalFiniteGrowingHamiltonianOutput.growing_graph n ε h a w p C b P
        hε ha hh hw hb m g k) rfl
  have hb' := KFCausalSingleGaussianMixedSquare.original_strip ε h hε hb
  have hp := KFCausalClockFloorGrowingPotentialSum.potential_graph ε hε h hh hb' m g k x
  have hr : KFCausalClockFloorGaussianGrowingRadialPairing.radialOutput ε hε h hh hb' m g k x=
      radialOutput n ε h a w p C b P hε ha hh hw hb := by
    exact (operator ε hε h).mem_graph_snd_inj' ((operator ε hε h).mem_graph _)
      (radial_graph n ε h a w p C b P hε ha hh hw hb) rfl
  rw [he,hr,growing_split n ε h a w p C b P hε ha hh hw hb m g k hm hg hk,
    add_sub_cancel_left] at hp
  exact hp

theorem potential_domain (m g k : ℝ) (hm : 0≤m) (hg : 0≤g) (hk : 0≤k) :
    ψ ∈ (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
      (hamiltonian_strip ε h hε hb) m g k).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (potential_graph n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)

theorem static_graph :
    (ψ,KFCausalFiniteOrderedStaticOutput.staticOutput n ε h a w p C b P hε ha hh hw hb) ∈
      (KFCausalClockFloorStaticOperator.operator ε hε h).graph :=
  KFCausalFiniteOrderedStaticOutput.static_graph n ε h a w p C b P hε ha hh hw hb

#print axioms radial_graph
#print axioms growing_split
#print axioms potential_graph
#print axioms potential_domain
#print axioms static_graph
end
end UnifiedTheory.Audit.KFCausalFinitePotentialStaticGraph
