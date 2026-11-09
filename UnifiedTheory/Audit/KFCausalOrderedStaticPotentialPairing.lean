/- Actual finite-packet potential/static pairings in one mixed chart.
Primitive reversed graphs justify moving Q, and actual L2 outputs supply
absolute integrability. No transverse integration by parts is assumed. -/
import UnifiedTheory.Audit.KFCausalOrderedStaticOutputRepresentative
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentMatterGraph

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalOrderedStaticPotentialPairing
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (split)
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorTrialSpectralDomain (reversedExponential)
open KFCausalStandingChargeOperator (zeroProjection zeroProjection_fixes)
open KFCausalIndependentRadialMomentExponential (halfState fullState second_half_graph)
open KFCausalIndependentRadialMomentInput (numerator)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalFiniteOrderedStaticOutput (staticOutput orderedOutput)

def index (j : Fin 3) : Fin 8 := ![7,5,6] j
def power (j : Fin 3) : ℕ := ![0,2,4] j
def field (ε : ℝ) (hε : 0<ε) (x : Product) : ℝ :=
  2*KFCausalPairedModeCoordinates.scale*(mixedMap ε hε x).2 2+(mixedMap ε hε x).2 3

private theorem mapped_sum_coe {N : ℕ}
    (T : Hilbert ≃ₗᵢ[ℂ] KFCausalEuclideanProductCoordinates.ProductHilbert 2 4)
    (f : Fin N→Hilbert) (F : Fin N→Product→ℂ) (m : Product→ℂ)
    (hf : ∀i,T (f i)=ᵐ[volume] fun x=>m x*F i x) :
    T (∑i,f i)=ᵐ[volume] fun x=>m x*∑i,F i x := by
  rw [map_sum]
  have ht := KFCausalFiniteLpRepresentatives.weighted_sum_coe volume (fun _ : Fin N => (1:ℂ))
    (fun i=>T (f i)) (fun i x=>m x*F i x) hf
  simpa only [one_smul,one_mul,Finset.mul_sum] using ht

private theorem factor_ae (f : KFCausalEuclideanProductCoordinates.ProductHilbert 2 4)
    (u v F : Product→ℂ) (k : ℕ) (hf : f=ᵐ[volume] fun x=>u x^k*F x)
    (hu : ∀x,u x=v x) : f=ᵐ[volume] fun x=>v x^k*F x := by
  filter_upwards [hf] with x hx
  rw [hx,hu]

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n→ℝ) (C b : Fin n→ℂ)
  (P : Fin n→Polynomial ℂ) (hε : 0<ε) (ha : ∀i,0<a i)
  (hh : h≠0) (hw : ∀i,1≤w i) (hb : |h|≤ε/10)

def halfOutput (k : ℕ) : Hilbert := ∑i,halfState ε h (a i) (w i) (w i) (w i)
  (C i) (p i) (b i) (P i) 0 0 hε hh (ha i) (hw i) (hw i) le_rfl hb k

def secondOutput (k : ℕ) : Hilbert := ∑i,inverseL ε hε
  (fullState ε h (a i) (w i) (w i) (w i) (C i) (p i) (b i) (P i) 0 0
    hε hh (ha i) (hw i) (hw i) le_rfl hb k)

def sourceProfile (x : Product) : ℂ := ∑i,
  numerator ε (a i) (groundWidth h) (w i) (w i) (momentumScale h)
    (C i) (p i) (b i) (P i) 0 0 (shift (h/2) (x.2 0:ℂ)) ((split 2 4).symm x)

def staticProfile (x : Product) : ℂ := ∑i,
  KFCausalOrderedStaticOutputRepresentative.profile ε (a i) h (w i) (w i)
    (C i) (p i) (b i) (P i) (shift (h/2) (x.2 0:ℂ)) ((split 2 4).symm x)

theorem reversed_graph (k : ℕ) :
    (halfOutput n ε h a w p C b P hε ha hh hw hb k,
      secondOutput n ε h a w p C b P hε ha hh hw hb k) ∈
      (reversedExponential ε hε h).graph := by
  have hg := (reversedExponential ε hε h).graph.sum_mem
    (fun i (_ : i∈(Finset.univ : Finset (Fin n))) =>
      KFCausalMatterHalfStepAssembly.reversed_exponential_graph ε hε h _ _
        (second_half_graph ε h (a i) (w i) (w i) (w i) (C i) (p i) (b i) (P i)
          0 0 hε hh (ha i) (hw i) (hw i) le_rfl hb k))
  simpa only [halfOutput,secondOutput,← prod_mk_sum] using hg

theorem original_second_eq (j : Fin 3) :
    secondOutput n ε h a w p C b P hε ha hh hw hb (power j)=
      KFCausalFiniteSecondHamiltonianColumns.second n ε h a w p C b P hε ha hh hw hb (index j) := by
  have hs (i : Fin n) :
      (KFCausalReciprocalNeutralPackets.state ε (a i) h (w i) hε (ha i) hh (hw i)
        (C i) (p i) (b i) (P i),
       inverseL ε hε (fullState ε h (a i) (w i) (w i) (w i) (C i) (p i) (b i) (P i)
         0 0 hε hh (ha i) (hw i) (hw i) le_rfl hb (power j))) ∈
      (KFCausalNaturalSecondHamiltonianGraph.component ε hε h (index j)).graph := by
    have he : KFCausalIndependentRadialPacketMoments.momentState ε (a i) h (w i) (w i)
        (C i) (p i) (b i) (P i) hε (ha i) hh (hw i) (hw i) 0 0=
        KFCausalReciprocalNeutralPackets.state ε (a i) h (w i) hε (ha i) hh (hw i)
          (C i) (p i) (b i) (P i) := by
      rw [KFCausalIndependentRadialPacketMoments.momentState_zero,
        KFCausalIndependentRadialPackets.state_diagonal]
    rw [← he]
    fin_cases j
    · exact KFCausalIndependentRadialMomentExponential.vacuum_graph ε h (a i) (w i) (w i) (w i)
        (C i) (p i) (b i) (P i) 0 0 hε hh (ha i) (hw i) (hw i) le_rfl hb
    · exact KFCausalIndependentRadialMomentMatterGraph.matter_graph ε h (a i) (w i) (w i) (w i)
        (C i) (p i) (b i) (P i) 0 0 hε hh (ha i) (hw i) (hw i) le_rfl hb 0
    · exact KFCausalIndependentRadialMomentMatterGraph.matter_graph ε h (a i) (w i) (w i) (w i)
        (C i) (p i) (b i) (P i) 0 0 hε hh (ha i) (hw i) (hw i) le_rfl hb 1
  have hg := (KFCausalNaturalSecondHamiltonianGraph.component ε hε h (index j)).graph.sum_mem
    (fun i (_ : i∈(Finset.univ : Finset (Fin n))) => hs i)
  have hg' : (KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw,
      secondOutput n ε h a w p C b P hε ha hh hw hb (power j)) ∈
      (KFCausalNaturalSecondHamiltonianGraph.component ε hε h (index j)).graph := by
    simpa only [KFCausalReciprocalNeutralSuperposition.state,secondOutput,← prod_mk_sum] using hg
  exact (KFCausalNaturalSecondHamiltonianGraph.component ε hε h (index j)).mem_graph_snd_inj'
    hg' (KFCausalFiniteSecondHamiltonianColumns.second_graph n ε h a w p C b P hε ha hh hw hb (index j)) rfl

theorem halfOutput_coe (k : ℕ) :
    clockMixed ε hε (halfOutput n ε h a w p C b P hε ha hh hw hb k) =ᵐ[volume]
      fun x : Product => (field ε hε x:ℂ)^k*sourceProfile n ε h a w p C b P x := by
  have hi (i : Fin n) : clockMixed ε hε
      (halfState ε h (a i) (w i) (w i) (w i) (C i) (p i) (b i) (P i) 0 0
        hε hh (ha i) (hw i) (hw i) le_rfl hb k) =ᵐ[volume]
      fun x : Product => (field ε hε x:ℂ)^k*
        numerator ε (a i) (groundWidth h) (w i) (w i) (momentumScale h)
          (C i) (p i) (b i) (P i) 0 0 (shift (h/2) (x.2 0:ℂ)) ((split 2 4).symm x) := by
    apply factor_ae _ _ _ _ k
      (KFCausalIndependentRadialMomentOutputRepresentative.half_coe ε h (a i)
        (w i) (w i) (w i) (C i) (p i) (b i) (P i) 0 0
        hε hh (ha i) (hw i) (hw i) le_rfl hb k)
    intro x
    rw [KFCausalIndependentRadialShiftedField.coefficient_half_line]
    exact KFCausalIndependentRadialShiftedField.point_real ε (groundWidth h) (w i) (w i)
      (momentumScale h) hε (groundWidth_positive h hh) (zero_lt_one.trans_le (hw i)) x
  exact mapped_sum_coe (clockMixed ε hε) _ _ _ hi

theorem unprojected_pairing (k : ℕ) :
    inner ℂ (secondOutput n ε h a w p C b P hε ha hh hw hb k)
      (staticOutput n ε h a w p C b P hε ha hh hw hb)=
    inner ℂ (halfOutput n ε h a w p C b P hε ha hh hw hb k)
      (orderedOutput n ε h a w p C b P hε ha hh hw hb) :=
  (KFCausalClockFloorVacuumSquare.ordered_reversed_pairing ε hε h _ _ _ _
    (KFCausalFiniteOrderedStaticOutput.ordered_graph n ε h a w p C b P hε ha hh hw hb)
    (reversed_graph n ε h a w p C b P hε ha hh hw hb k)).symm

theorem projected_pairing (j : Fin 3) :
    inner ℂ (zeroProjection h hh
      (KFCausalFiniteSecondHamiltonianColumns.second n ε h a w p C b P hε ha hh hw hb (index j)))
      (staticOutput n ε h a w p C b P hε ha hh hw hb)=
    inner ℂ (halfOutput n ε h a w p C b P hε ha hh hw hb (power j))
      (orderedOutput n ε h a w p C b P hε ha hh hw hb) := by
  rw [← original_second_eq n ε h a w p C b P hε ha hh hw hb j]
  have hp := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (KFCausalStandingChargeOperator.zeroProjection_selfAdjoint h hh))
      (secondOutput n ε h a w p C b P hε ha hh hw hb (power j))
      (staticOutput n ε h a w p C b P hε ha hh hw hb)
  change inner ℂ (zeroProjection h hh _) _=inner ℂ _ (zeroProjection h hh _) at hp
  rw [zeroProjection_fixes h hh _
    (KFCausalFiniteOrderedStaticOutput.static_zeroSector n ε h a w p C b P hε ha hh hw hb)] at hp
  exact hp.trans (unprojected_pairing n ε h a w p C b P hε ha hh hw hb (power j))

include ha hh hw hb in
theorem pairing_integrable (k : ℕ) : Integrable (fun x : Product =>
    conj ((field ε hε x:ℂ)^k*sourceProfile n ε h a w p C b P x)*
      staticProfile n ε h a w p C b P x) volume := by
  apply (L2.integrable_inner (𝕜 := ℂ)
    (clockMixed ε hε (halfOutput n ε h a w p C b P hε ha hh hw hb k))
    (clockMixed ε hε (orderedOutput n ε h a w p C b P hε ha hh hw hb))).congr
  filter_upwards [halfOutput_coe n ε h a w p C b P hε ha hh hw hb k,
    KFCausalOrderedStaticOutputRepresentative.finite_orderedOutput_clockMixed
      n ε h a w p C b P hε ha hh hw hb] with x hx hy
  rw [hx,hy]
  simp only [RCLike.inner_apply,starRingEnd_apply,staticProfile,mul_comm]

theorem projected_pairing_integral (j : Fin 3) :
    inner ℂ (zeroProjection h hh
      (KFCausalFiniteSecondHamiltonianColumns.second n ε h a w p C b P hε ha hh hw hb (index j)))
      (staticOutput n ε h a w p C b P hε ha hh hw hb)=
      ∫ x : Product,conj ((field ε hε x:ℂ)^power j*sourceProfile n ε h a w p C b P x)*
        staticProfile n ε h a w p C b P x := by
  rw [projected_pairing n ε h a w p C b P hε ha hh hw hb j,
    ← (clockMixed ε hε).inner_map_map,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [halfOutput_coe n ε h a w p C b P hε ha hh hw hb (power j),
    KFCausalOrderedStaticOutputRepresentative.finite_orderedOutput_clockMixed
      n ε h a w p C b P hε ha hh hw hb] with x hx hy
  rw [hx,hy]
  simp only [RCLike.inner_apply,starRingEnd_apply,staticProfile,mul_comm]

#print axioms reversed_graph
#print axioms original_second_eq
#print axioms halfOutput_coe
#print axioms unprojected_pairing
#print axioms projected_pairing
#print axioms pairing_integrable
#print axioms projected_pairing_integral
end
end UnifiedTheory.Audit.KFCausalOrderedStaticPotentialPairing
