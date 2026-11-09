/- Charge-averaged matter response with the exact field/shear correction.
The correction orbit is norm-continuous. The weighted shear scalar is
continuous by the exact response identity, so both separate integrals are
justified without asserting continuity of the unbounded shear output. -/
import UnifiedTheory.Audit.KFCausalCoherentFieldDerivativeOrbit
import UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalAveragedMatterShearCorrection
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan action_coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope)
open UnifiedTheory.Audit.KFCausalFieldShearResponseCorrection (derivativeCorrection corrected_response derivativeCorrection_bound)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (shearCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition (rate)
open UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (hh : h ≠ 0)
local notation "D" => defectOperator ε hε
local notation "W" => root ε hε h hb hh

def weightedRate (u j d : Hilbert) : ℝ :=
  (4/ε^2)*(inner ℂ (W u) (W (j+(-Complex.I*(h:ℂ)) • d))).re

def weightedMean (g : Fin 8 → ℝ → Hilbert) (j d : Fin 2 → ℝ → Hilbert) (i : Fin 2) : ℝ :=
  ∫ θ, weightedRate ε h hε hb hh (g (matterIndex i) θ) (j i θ) (d i θ) ∂angleMeasure

def correctionMean (g : Fin 8 → ℝ → Hilbert) (d : Fin 2 → ℝ → Hilbert) (i : Fin 2) : ℝ :=
  ∫ θ, derivativeCorrection ε hε h hb (g (matterIndex i) θ) (d i θ) ∂angleMeasure

theorem actual_average (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ coherentSpan ε a h hε ha hh) (b : Hilbert) (hB : (f,b) ∈ (pureMomentum ε hε h).graph)
    (g k : Fin 8 → ℝ → Hilbert)
    (hOut : ∀ θ i,
      (action h hh (2*Real.pi*θ) f,g i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph ∧
      (action h hh (2*Real.pi*θ) b,k i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph)
    (hc : ∀ i, Continuous (g i) ∧ Continuous (k i)) :
    ∃ (q : ℝ → Hilbert) (j d : Fin 2 → ℝ → Hilbert),
      (∀ θ, (g 7 θ,q θ) ∈ (shearMomentum h).graph) ∧
      (∀ θ i, (q θ,j i θ) ∈ (fieldPower pointField i).graph) ∧
      (∀ i, Continuous (d i)) ∧
      (∀ θ i, d i θ =ᵐ[volume] fun x => powerSlope pointField i x*g 7 θ x) ∧
      (∀ θ i, (g (matterIndex i) θ,j i θ+(-Complex.I*(h:ℂ)) • d i θ) ∈ (shearMomentum h).graph) ∧
      (∀ i, Continuous (fun θ => weightedRate ε h hε hb hh (g (matterIndex i) θ) (j i θ) (d i θ)) ∧
        Integrable (fun θ => weightedRate ε h hε hb hh (g (matterIndex i) θ) (j i θ) (d i θ)) angleMeasure) ∧
      (∀ i, Continuous (fun θ => derivativeCorrection ε hε h hb (g (matterIndex i) θ) (d i θ)) ∧
        Integrable (fun θ => derivativeCorrection ε hε h hb (g (matterIndex i) θ) (d i θ)) angleMeasure) ∧
      (∀ i, rate h g k (matterIndex i) = longitudinalMean ε h hε hb g i+
        weightedMean ε h hε hb hh g j d i-correctionMean ε h hε hb g d i) ∧
      (∀ i, |correctionMean ε h hε hb g d i| ≤
        ∫ θ, (4*|h|/ε^2)*‖g (matterIndex i) θ‖*‖D (D (d i θ))‖ ∂angleMeasure) := by
  obtain ⟨q,j,hq,hj,hS,hSi,_,hR,_⟩ := actual_split ε h hε hb hh a ha f hf b hB g k hOut hc
  have hg (θ : ℝ) : (action h hh (2*Real.pi*θ) f,g 7 θ) ∈ (orderedExponential ε hε h).graph :=
    (hOut θ 7).1
  have hx (i : Fin 2) := KFCausalCoherentFieldDerivativeOrbit.derivative_orbit
    ε a h hε ha hh hb f hf (g 7) hg pointField i
  choose d hd using hx
  have hk (θ : ℝ) (i : Fin 2) :
      (g (matterIndex i) θ,j i θ+(-Complex.I*(h:ℂ)) • d i θ) ∈ (shearMomentum h).graph := by
    have hM := (hOut θ (matterIndex i)).1
    rw [factor_matter] at hM
    obtain ⟨g',ht,hF⟩ := (KFCausalOrderedOperatorComposition.composition_graph _ _ _ _).mp hM
    have eg : g' = g 7 θ := (orderedExponential ε hε h).mem_graph_snd_inj' ht (hg θ) rfl
    have hF' : (g 7 θ,g (matterIndex i) θ) ∈ (fieldPower pointField i).graph := eg ▸ hF
    obtain ⟨d',hd',hk'⟩ := KFCausalCoherentFieldShearGraph.actual_power_graph
      ε a h hε ha hh hb pointField i _ (action_coherentSpan ε a h hε ha hh _ f hf)
      (g 7 θ) (q θ) (g (matterIndex i) θ) (j i θ) (hg θ) (hq θ) hF' (hj θ i)
    have ed : d' = d i θ := Lp.ext (hd'.trans ((hd i).2 θ).symm)
    simpa only [ed] using hk'
  have he (θ : ℝ) (i : Fin 2) : shearRate ε h hε hb (g (matterIndex i) θ) (j i θ) =
      derivativeCorrection ε hε h hb (g (matterIndex i) θ) (d i θ)-
        weightedRate ε h hε hb hh (g (matterIndex i) θ) (j i θ) (d i θ) := by
    have hr := corrected_response ε hε h hb hh _ _ _ (hk θ i)
    rw [KFCausalClockFloorPureClockVacuumResponse.response_split ε hε h hb hh] at hr
    unfold shearRate weightedRate
    linarith
  have hC (i : Fin 2) : Continuous (fun θ => derivativeCorrection ε hε h hb (g (matterIndex i) θ) (d i θ)) :=
    continuous_const.mul (Complex.continuous_re.comp
      ((hc _).1.inner ((shearCorrection ε hε h hb).continuous.comp (hd i).1)))
  have hCi (i : Fin 2) := (continuous_angle_memLp _ (hC i)).integrable (by norm_num)
  have hW (i : Fin 2) : Continuous
      (fun θ => weightedRate ε h hε hb hh (g (matterIndex i) θ) (j i θ) (d i θ)) := by
    have he' : (fun θ => weightedRate ε h hε hb hh (g (matterIndex i) θ) (j i θ) (d i θ)) =
        fun θ => derivativeCorrection ε hε h hb (g (matterIndex i) θ) (d i θ)-
          shearRate ε h hε hb (g (matterIndex i) θ) (j i θ) := funext (fun θ => by linarith [he θ i])
    rw [he']
    exact (hC i).sub (hS i)
  have hWi (i : Fin 2) := (continuous_angle_memLp _ (hW i)).integrable (by norm_num)
  refine ⟨q,j,d,hq,hj,fun i => (hd i).1,fun θ i => (hd i).2 θ,hk,
    fun i => ⟨hW i,hWi i⟩,fun i => ⟨hC i,hCi i⟩,?_,?_⟩
  · intro i
    have hMean : shearMean ε h hε hb g j i = correctionMean ε h hε hb g d i-
        weightedMean ε h hε hb hh g j d i := by
      unfold shearMean
      simp_rw [he]
      exact integral_sub (hCi i) (hWi i)
    rw [hR i,hMean]
    ring
  · intro i
    have hE : Continuous (fun θ => (4*|h|/ε^2)*‖g (matterIndex i) θ‖*‖D (D (d i θ))‖) :=
      (continuous_const.mul (hc _).1.norm).mul (((D).continuous.comp ((D).continuous.comp (hd i).1)).norm)
    exact abs_integral_le_integral_abs.trans (integral_mono (hCi i).abs
      ((continuous_angle_memLp _ hE).integrable (by norm_num))
      (fun θ => derivativeCorrection_bound ε hε h hb _ _))

#print axioms actual_average
end
end UnifiedTheory.Audit.KFCausalAveragedMatterShearCorrection
