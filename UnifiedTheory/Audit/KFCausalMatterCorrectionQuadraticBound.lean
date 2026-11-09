/- Quadratic-in-hbar bounds for the actual matter correction, including
its charge average. The averaged estimate separates the existing matter
factor moment from an explicitly retained cubic-defect derivative moment.
No energy control of that additional moment or of weighted shear is assumed. -/
import UnifiedTheory.Audit.KFCausalFieldCorrectionRealPairing
import UnifiedTheory.Audit.KFCausalAveragedMatterShearCorrection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalMatterCorrectionQuadraticBound
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope)
open UnifiedTheory.Audit.KFCausalFieldShearResponseCorrection (derivativeCorrection)
open UnifiedTheory.Audit.KFCausalFieldCorrectionRealPairing (field_correction_bound)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage (matterIndex factor_matter longitudinalMean)
open UnifiedTheory.Audit.KFCausalAveragedMatterShearCorrection (weightedMean correctionMean)
open UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition (rate)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "D" => defectOperator ε hε

theorem quadratic_average_bound (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (g u d : ℝ → Hilbert)
    (hu : ∀ θ, (g θ,u θ) ∈ (fieldPower l i).graph)
    (hd : ∀ θ, d θ =ᵐ[volume] fun x => powerSlope l i x*g θ x)
    (hc : Continuous u) (hcd : Continuous d) :
    |∫ θ, derivativeCorrection ε hε h hb (u θ) (d θ) ∂angleMeasure| ≤
      (10*h^2/ε^3)*((∫ θ, ‖u θ‖^2 ∂angleMeasure)+
        ∫ θ, ‖D (D (D (d θ)))‖^2 ∂angleMeasure) := by
  have hC : Continuous (fun θ => derivativeCorrection ε hε h hb (u θ) (d θ)) :=
    continuous_const.mul (Complex.continuous_re.comp (hc.inner
      ((KFCausalClockFloorPureClockVacuumCommutator.shearCorrection ε hε h hb).continuous.comp hcd)))
  have hU := (continuous_angle_memLp _ (hc.norm.pow 2)).integrable (by norm_num)
  have hD := (continuous_angle_memLp _
    (((D).continuous.comp ((D).continuous.comp ((D).continuous.comp hcd))).norm.pow 2)).integrable (by norm_num)
  have hE (θ : ℝ) : |derivativeCorrection ε hε h hb (u θ) (d θ)| ≤
      (10*h^2/ε^3)*(‖u θ‖^2+‖D (D (D (d θ)))‖^2) := by
    apply (field_correction_bound ε hε h hb l i (g θ) (u θ) (d θ) (hu θ) (hd θ)).trans
    have hy := mul_le_mul_of_nonneg_left
      (show 2*‖u θ‖*‖D (D (D (d θ)))‖ ≤ ‖u θ‖^2+‖D (D (D (d θ)))‖^2 by
        nlinarith [sq_nonneg (‖u θ‖-‖D (D (D (d θ)))‖)])
      (by positivity : 0 ≤ 10*h^2/ε^3)
    convert hy using 1
    ring
  have hi := abs_integral_le_integral_abs.trans
    (integral_mono ((continuous_angle_memLp _ hC).integrable (by norm_num)).abs
      ((hU.add hD).const_mul (10*h^2/ε^3)) hE)
  rw [integral_const_mul] at hi
  simp only [Pi.add_apply,Function.comp_apply] at hi hD
  rw [integral_add hU hD] at hi
  exact hi

variable (hh : h ≠ 0)
local notation "W" => root ε hε h hb hh
local notation "responseL" => KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb

theorem actual_weak_error (a : ℝ) (ha : 0 < a) (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
    (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) (b g jg u v : Hilbert)
    (hB : (f,b) ∈ (pureMomentum ε hε h).graph) (hg : (f,g) ∈ (orderedExponential ε hε h).graph)
    (hjg : (g,jg) ∈ (shearMomentum h).graph)
    (hu : (f,u) ∈ (matterFactor ε hε h (fieldPower l i)).graph)
    (hv : (b,v) ∈ (matterFactor ε hε h (fieldPower l i)).graph) :
    ∃ j d : Hilbert, (jg,j) ∈ (fieldPower l i).graph ∧
      d =ᵐ[volume] (fun x => powerSlope l i x*g x) ∧
      (u,j+(-Complex.I*(h:ℂ)) • d) ∈ (shearMomentum h).graph ∧
      (-2/h)*(inner ℂ u v).im = responseL u+
        (4/ε^2)*(inner ℂ (W u) (W (j+(-Complex.I*(h:ℂ)) • d))).re-
        derivativeCorrection ε hε h hb u d ∧
      |(-2/h)*(inner ℂ u v).im-(responseL u+
        (4/ε^2)*(inner ℂ (W u) (W (j+(-Complex.I*(h:ℂ)) • d))).re)| ≤
        (20*h^2/ε^3)*‖u‖*‖D (D (D d))‖ := by
  obtain ⟨j,d,hj,hd,hk,hr,_⟩ :=
    KFCausalCoherentMatterShearCorrection.actual_response_with_derivative
      ε a h hε ha hh hb l i f hf b g jg u v hB hg hjg hu hv
  obtain ⟨g',ht,hF⟩ := (composition_graph _ _ _ _).mp hu
  have eg : g' = g := (orderedExponential ε hε h).mem_graph_snd_inj' ht hg rfl
  have hF' : (g,u) ∈ (fieldPower l i).graph := eg ▸ hF
  refine ⟨j,d,hj,hd,hk,hr,?_⟩
  rw [hr,sub_sub_cancel_left,abs_neg]
  exact field_correction_bound ε hε h hb l i g u d hF' hd

theorem actual_average_lower (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ coherentSpan ε a h hε ha hh) (b : Hilbert)
    (hB : (f,b) ∈ (pureMomentum ε hε h).graph) (g k : Fin 8 → ℝ → Hilbert)
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
      (∀ i, rate h g k (matterIndex i) = longitudinalMean ε h hε hb g i+
        weightedMean ε h hε hb hh g j d i-correctionMean ε h hε hb g d i) ∧
      (∀ i, |correctionMean ε h hε hb g d i| ≤ (10*h^2/ε^3)*
        ((∫ θ, ‖g (matterIndex i) θ‖^2 ∂angleMeasure)+
          ∫ θ, ‖D (D (D (d i θ)))‖^2 ∂angleMeasure)) ∧
      (∀ i, weightedMean ε h hε hb hh g j d i-(10*h^2/ε^3)*
        ((∫ θ, ‖g (matterIndex i) θ‖^2 ∂angleMeasure)+
          ∫ θ, ‖D (D (D (d i θ)))‖^2 ∂angleMeasure) ≤ rate h g k (matterIndex i)) := by
  obtain ⟨q,j,d,hq,hj,hd,hrep,hk,_,_,hr,_⟩ :=
    KFCausalAveragedMatterShearCorrection.actual_average ε h hε hb hh a ha f hf b hB g k hOut hc
  have hF (θ : ℝ) (i : Fin 2) : (g 7 θ,g (matterIndex i) θ) ∈ (fieldPower pointField i).graph := by
    have hM := (hOut θ (matterIndex i)).1
    rw [factor_matter] at hM
    obtain ⟨g',ht,hF'⟩ := (composition_graph _ _ _ _).mp hM
    have eg : g' = g 7 θ := (orderedExponential ε hε h).mem_graph_snd_inj' ht (hOut θ 7).1 rfl
    exact eg ▸ hF'
  have hbound (i : Fin 2) := quadratic_average_bound ε hε h hb pointField i
    (g 7) (g (matterIndex i)) (d i) (fun θ => hF θ i) (fun θ => hrep θ i) (hc _).1 (hd i)
  refine ⟨q,j,d,hq,hj,hd,hrep,hk,hr,hbound,?_⟩
  intro i
  have hL : 0 ≤ longitudinalMean ε h hε hb g i :=
    integral_nonneg (fun θ => (KFCausalClockFloorVacuumMomentumResponse.response_bounds ε hε h hb _).1)
  have hE := (le_abs_self (correctionMean ε h hε hb g d i)).trans (hbound i)
  linarith [hr i]

#print axioms quadratic_average_bound
#print axioms actual_weak_error
#print axioms actual_average_lower
end
end UnifiedTheory.Audit.KFCausalMatterCorrectionQuadraticBound
