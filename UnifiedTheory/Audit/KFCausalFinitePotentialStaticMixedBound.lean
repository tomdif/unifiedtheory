/- The finite-packet estimate written in terms of the actual closed P and
maximal T operators. Ordered/reversed graphs identify the potential energy
with the actual half-output norms. No all-domain or common-core extension. -/
import UnifiedTheory.Audit.KFCausalFinitePotentialStaticGraph

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFinitePotentialStaticMixedBound
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalStandingChargeOperator (zeroProjection zeroProjection_fixes)
open KFCausalOrderedStaticPotentialPairing (halfOutput secondOutput index power field sourceProfile)
open KFCausalOrderedStaticPotentialHilbertBound (weightedOutput weightedEnergy)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalPhysicalFourierGeneralCoordinates (Product)

private theorem point_pairing (t : ℝ) (z : ℂ) (j : ℕ) :
    (inner ℂ ((t:ℂ)^(2*j)*z) z).re=t^(2*j)*‖z‖^2 := by
  rw [←Complex.ofReal_pow]
  change (inner ℂ (((t^(2*j):ℝ):ℂ) • z) z).re=_
  rw [inner_smul_left,Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  have hz : (inner ℂ z z).re = ‖z‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) z
  rw [hz]

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n→ℝ) (C b : Fin n→ℂ)
  (P : Fin n→Polynomial ℂ) (hε : 0<ε) (ha : ∀i,0<a i)
  (hh : h≠0) (hw : ∀i,1≤w i) (hb : |h|≤ε/10)
local notation "ψ" => KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw

theorem ordered_graph :
    (ψ,halfOutput n ε h a w p C b P hε ha hh hw hb 0) ∈
      (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph := by
  have hsingle (i:Fin n) :
      (KFCausalReciprocalNeutralPackets.state ε (a i) h (w i) hε (ha i) hh (hw i)
        (C i) (p i) (b i) (P i),
      KFCausalIndependentRadialMomentExponential.halfState ε h (a i) (w i) (w i) (w i)
        (C i) (p i) (b i) (P i) 0 0 hε hh (ha i) (hw i) (hw i) le_rfl hb 0) ∈
      (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph := by
    apply (KFCausalClockFloorBoundedInverse.ordered_graph_iff ε hε h _ _).mpr
    have hg := KFCausalIndependentRadialMomentExponential.actual_half_graph ε h (a i)
      (w i) (w i) (w i) (C i) (p i) (b i) (P i) 0 0 hε hh (ha i) (hw i) (hw i) le_rfl hb
    rwa [KFCausalIndependentRadialPacketMoments.momentState_zero,
      KFCausalIndependentRadialPackets.state_diagonal] at hg
  have hs := (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hsingle i)
  simpa only [←prod_mk_sum,KFCausalReciprocalNeutralSuperposition.state,halfOutput] using hs

theorem channel_energy (j : Fin 3) :
    (inner ℂ (zeroProjection h hh (KFCausalFiniteSecondHamiltonianColumns.second
      n ε h a w p C b P hε ha hh hw hb (index j))) ψ).re=
      ‖halfOutput n ε h a w p C b P hε ha hh hw hb j.val‖^2 := by
  have hz := KFCausalReciprocalNeutralSuperposition.state_zeroSector n ε h a w p C b P
    hε ha hh hw
  have hp := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (KFCausalStandingChargeOperator.zeroProjection_selfAdjoint h hh))
      (KFCausalFiniteSecondHamiltonianColumns.second n ε h a w p C b P hε ha hh hw hb (index j)) ψ
  change inner ℂ (zeroProjection h hh _) ψ=inner ℂ _ (zeroProjection h hh ψ) at hp
  rw [zeroProjection_fixes h hh ψ hz] at hp
  rw [hp,←KFCausalOrderedStaticPotentialPairing.original_second_eq n ε h a w p C b P
    hε ha hh hw hb j]
  have hpair := KFCausalClockFloorVacuumSquare.ordered_reversed_pairing ε hε h ψ
    (halfOutput n ε h a w p C b P hε ha hh hw hb 0)
    (halfOutput n ε h a w p C b P hε ha hh hw hb (power j))
    (secondOutput n ε h a w p C b P hε ha hh hw hb (power j))
    (ordered_graph n ε h a w p C b P hε ha hh hw hb)
    (KFCausalOrderedStaticPotentialPairing.reversed_graph n ε h a w p C b P
      hε ha hh hw hb (power j))
  rw [←hpair,←(clockMixed ε hε).inner_map_map,L2.inner_def]
  let u := halfOutput n ε h a w p C b P hε ha hh hw hb (power j)
  let v := halfOutput n ε h a w p C b P hε ha hh hw hb 0
  have hre : (∫ x : Product, inner ℂ ((clockMixed ε hε u) x) ((clockMixed ε hε v) x)).re =
      ∫ x : Product, (inner ℂ ((clockMixed ε hε u) x) ((clockMixed ε hε v) x)).re :=
    (integral_re (L2.integrable_inner (𝕜:=ℂ) (clockMixed ε hε u) (clockMixed ε hε v))).symm
  rw [hre]
  rw [(KFCausalOrderedStaticPotentialHilbertBound.channel_energy n ε h a w p C b P
    hε ha hh hw hb j.val).2]
  apply integral_congr_ae
  filter_upwards [KFCausalOrderedStaticPotentialPairing.halfOutput_coe n ε h a w p C b P
    hε ha hh hw hb (power j),KFCausalOrderedStaticPotentialPairing.halfOutput_coe
    n ε h a w p C b P hε ha hh hw hb 0] with x hx hy
  rw [hx,hy]
  simp only [pow_zero,one_mul]
  have hj : power j=2*j.val := by fin_cases j <;> rfl
  rw [hj,point_pairing]

theorem energy_pairing (m g k : ℝ) :
    (inner ℂ (weightedOutput n ε h a w p C b P hε ha hh hw hb m g k) ψ).re=
      weightedEnergy n ε h a w p C b P hε ha hh hw hb m g k := by
  unfold weightedOutput weightedEnergy
  simp only [inner_add_left,inner_smul_left,Complex.conj_ofReal,Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    channel_energy n ε h a w p C b P hε ha hh hw hb]
  rfl

def potentialPoint (m g k : ℝ) (hm : 0≤m) (hg : 0≤g) (hk : 0≤k) :
    (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
      (hamiltonian_strip ε h hε hb) m g k).domain :=
  ⟨ψ,KFCausalFinitePotentialStaticGraph.potential_domain n ε h a w p C b P
    hε ha hh hw hb m g k hm hg hk⟩

def staticPoint : (KFCausalClockFloorStaticOperator.operator ε hε h).domain :=
  ⟨ψ,LinearPMap.mem_domain_of_mem_graph
    (KFCausalFinitePotentialStaticGraph.static_graph n ε h a w p C b P hε ha hh hw hb)⟩

theorem actual_energy (m g k : ℝ) (hm : 0≤m) (hg : 0≤g) (hk : 0≤k) :
    (inner ℂ ψ (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
      (hamiltonian_strip ε h hε hb) m g k
        (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk))).re=
      weightedEnergy n ε h a w p C b P hε ha hh hw hb m g k := by
  have he : KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
      (hamiltonian_strip ε h hε hb) m g k
        (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk) =
      weightedOutput n ε h a w p C b P hε ha hh hw hb m g k :=
    (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
      (hamiltonian_strip ε h hε hb) m g k).mem_graph_snd_inj'
      ((KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
        (hamiltonian_strip ε h hε hb) m g k).mem_graph
          (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk))
      (KFCausalFinitePotentialStaticGraph.potential_graph n ε h a w p C b P
        hε ha hh hw hb m g k hm hg hk) rfl
  have hs : (inner ℂ ψ (weightedOutput n ε h a w p C b P hε ha hh hw hb m g k)).re =
      (inner ℂ (weightedOutput n ε h a w p C b P hε ha hh hw hb m g k) ψ).re :=
    inner_re_symm (𝕜:=ℂ) _ _
  rw [he,hs]
  exact energy_pairing n ε h a w p C b P hε ha hh hw hb m g k

theorem operator_mixed_lower (m g k : ℝ) (hm : 0≤m) (hg : 0≤g) (hk : 0<k) :
    -((2*h^2/ε)*(12+(m+3*g)/k))*
      (inner ℂ ψ (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
        (hamiltonian_strip ε h hε hb) m g k
          (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le))).re≤
    (inner ℂ (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
        (hamiltonian_strip ε h hε hb) m g k
          (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le))
      (KFCausalClockFloorStaticOperator.operator ε hε h
        (staticPoint n ε h a w p C b P hε ha hh hw hb))).re := by
  have hp : KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
      (hamiltonian_strip ε h hε hb) m g k
        (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le) =
      weightedOutput n ε h a w p C b P hε ha hh hw hb m g k :=
    (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
      (hamiltonian_strip ε h hε hb) m g k).mem_graph_snd_inj'
      ((KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
        (hamiltonian_strip ε h hε hb) m g k).mem_graph
          (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le))
      (KFCausalFinitePotentialStaticGraph.potential_graph n ε h a w p C b P
        hε ha hh hw hb m g k hm hg hk.le) rfl
  have ht : KFCausalClockFloorStaticOperator.operator ε hε h
      (staticPoint n ε h a w p C b P hε ha hh hw hb) =
      KFCausalFiniteOrderedStaticOutput.staticOutput n ε h a w p C b P hε ha hh hw hb :=
    (KFCausalClockFloorStaticOperator.operator ε hε h).mem_graph_snd_inj'
      ((KFCausalClockFloorStaticOperator.operator ε hε h).mem_graph
        (staticPoint n ε h a w p C b P hε ha hh hw hb))
      (KFCausalFinitePotentialStaticGraph.static_graph n ε h a w p C b P hε ha hh hw hb) rfl
  rw [actual_energy,hp,ht]
  exact KFCausalOrderedStaticPotentialHilbertBound.mixed_lower n ε h a w p C b P
    hε ha hh hw hb m g k hm hg hk

#print axioms ordered_graph
#print axioms channel_energy
#print axioms energy_pairing
#print axioms actual_energy
#print axioms operator_mixed_lower
end
end UnifiedTheory.Audit.KFCausalFinitePotentialStaticMixedBound
