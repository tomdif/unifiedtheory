/- The actual ordered matter rates split into nonnegative longitudinal
means and signed field-weighted shear means. Scalar shear pairings are
continuous by the proved composition identity and actual factor orbits;
no continuity of an unbounded field map is assumed. -/
import UnifiedTheory.Audit.KFCausalCoherentMatterWeakResponse
import UnifiedTheory.Audit.KFCausalCoherentFullResponseReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan action_coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeGraph (graph_charge)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (shearCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition (rate)

def matterIndex (i : Fin 2) : Fin 8 := ⟨i.val+5,by omega⟩

theorem factor_matter (ε h : ℝ) (hε : 0 < ε) (i : Fin 2) :
    energyFactor ε hε h modelDirections pointField (matterIndex i) =
      matterFactor ε hε h (fieldPower pointField i) := by fin_cases i <;> rfl

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3)

def shearRate (u j : Hilbert) : ℝ := (2/h)*(inner ℂ u (shearCorrection ε hε h hb j)).im

def longitudinalMean (g : Fin 8 → ℝ → Hilbert) (i : Fin 2) : ℝ :=
  ∫ θ, KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb (g (matterIndex i) θ) ∂angleMeasure

def shearMean (g : Fin 8 → ℝ → Hilbert) (j : Fin 2 → ℝ → Hilbert) (i : Fin 2) : ℝ :=
  ∫ θ, shearRate ε h hε hb (g (matterIndex i) θ) (j i θ) ∂angleMeasure

theorem actual_split (hh : h ≠ 0) (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ coherentSpan ε a h hε ha hh) (b : Hilbert) (hB : (f,b) ∈ (pureMomentum ε hε h).graph)
    (g k : Fin 8 → ℝ → Hilbert)
    (hOut : ∀ θ i,
      (action h hh (2*Real.pi*θ) f,g i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph ∧
      (action h hh (2*Real.pi*θ) b,k i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph)
    (hc : ∀ i, Continuous (g i) ∧ Continuous (k i)) :
    ∃ (q : ℝ → Hilbert) (j : Fin 2 → ℝ → Hilbert),
      (∀ θ, (g 7 θ,q θ) ∈ (shearMomentum h).graph) ∧
      (∀ θ i, (q θ,j i θ) ∈ (fieldPower pointField i).graph) ∧
      (∀ i, Continuous (fun θ => shearRate ε h hε hb (g (matterIndex i) θ) (j i θ))) ∧
      (∀ i, Integrable (fun θ => shearRate ε h hε hb (g (matterIndex i) θ) (j i θ)) angleMeasure) ∧
      (∀ θ i, (-2/h)*(inner ℂ (g (matterIndex i) θ) (k (matterIndex i) θ)).im =
        KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb (g (matterIndex i) θ)-
          shearRate ε h hε hb (g (matterIndex i) θ) (j i θ)) ∧
      (∀ i, rate h g k (matterIndex i) = longitudinalMean ε h hε hb g i-shearMean ε h hε hb g j i) ∧
      (∀ i, 0 ≤ longitudinalMean ε h hε hb g i) := by
  have hd (θ : ℝ) : g 7 θ ∈ (shearMomentum h).domain :=
    (KFCausalCoherentVacuumCommutator.span_regular ε a h hε ha hh hb _
      (action_coherentSpan ε a h hε ha hh _ f hf) _ (hOut θ 7).1).2.2
  let q : ℝ → Hilbert := fun θ => shearMomentum h ⟨g 7 θ,hd θ⟩
  have hq (θ : ℝ) : (g 7 θ,q θ) ∈ (shearMomentum h).graph := (shearMomentum h).mem_graph ⟨_,hd θ⟩
  have hM (θ : ℝ) (i : Fin 2) :
      (action h hh (2*Real.pi*θ) f,g (matterIndex i) θ) ∈ (matterFactor ε hε h (fieldPower pointField i)).graph ∧
      (action h hh (2*Real.pi*θ) b,k (matterIndex i) θ) ∈ (matterFactor ε hε h (fieldPower pointField i)).graph := by
    simpa only [factor_matter] using hOut θ (matterIndex i)
  have hx (i : Fin 2) (θ : ℝ) := KFCausalCoherentMatterWeakResponse.actual_composition ε a h hε ha hh hb pointField i
    (action h hh (2*Real.pi*θ) f) (action_coherentSpan ε a h hε ha hh _ f hf)
    (action h hh (2*Real.pi*θ) b) (g 7 θ) (q θ) (g (matterIndex i) θ) (k (matterIndex i) θ)
    (graph_charge ε hε h hh _ f b hB) (hOut θ 7).1 (hq θ) (hM θ i).1 (hM θ i).2
  choose j hj using hx
  have he (θ : ℝ) (i : Fin 2) :
      (-2/h)*(inner ℂ (g (matterIndex i) θ) (k (matterIndex i) θ)).im =
        KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb (g (matterIndex i) θ)-
          shearRate ε h hε hb (g (matterIndex i) θ) (j i θ) :=
    (KFCausalCoherentMatterWeakResponse.actual_weak_response ε a h hε ha hh hb pointField i
      (action h hh (2*Real.pi*θ) f) (action_coherentSpan ε a h hε ha hh _ f hf)
      (action h hh (2*Real.pi*θ) b) (g 7 θ) (q θ) (g (matterIndex i) θ) (k (matterIndex i) θ) (j i θ)
      (graph_charge ε hε h hh _ f b hB) (hOut θ 7).1 (hq θ) (hM θ i).1 (hM θ i).2 (hj i θ).1).trans
        (KFCausalClockFloorPureClockVacuumResponse.response_split ε hε h hb hh _ _)
  have hL (i : Fin 2) : Continuous (fun θ =>
      KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb (g (matterIndex i) θ)) :=
    (KFCausalClockFloorVacuumMomentumResponse.response_continuous ε hε h hb).comp (hc _).1
  have hS (i : Fin 2) : Continuous (fun θ => shearRate ε h hε hb (g (matterIndex i) θ) (j i θ)) := by
    have hs : (fun θ => shearRate ε h hε hb (g (matterIndex i) θ) (j i θ)) =
        fun θ => KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb (g (matterIndex i) θ)-
          (-2/h)*(inner ℂ (g (matterIndex i) θ) (k (matterIndex i) θ)).im :=
      funext (fun θ => by linarith [he θ i])
    rw [hs]
    exact (hL i).sub (continuous_const.mul
      (Complex.continuous_im.comp ((hc _).1.inner (hc _).2)))
  have hSi (i : Fin 2) := (continuous_angle_memLp _ (hS i)).integrable (by norm_num)
  refine ⟨q,j,hq,fun θ i => (hj i θ).1,hS,hSi,he,?_,?_⟩
  · intro i
    unfold rate
    simp_rw [he]
    exact integral_sub ((continuous_angle_memLp _ (hL i)).integrable (by norm_num)) (hSi i)
  · intro i
    exact integral_nonneg (fun θ => (KFCausalClockFloorVacuumMomentumResponse.response_bounds ε hε h hb _).1)

#print axioms factor_matter
#print axioms actual_split
end
end UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage
