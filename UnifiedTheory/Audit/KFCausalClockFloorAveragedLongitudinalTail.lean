/- Positive longitudinal spectral tails of the inverse-clock-weighted charge
orbit are bounded by the actual completed averaged energy. No invariance of
the longitudinal generator under charge rotation is used. -/
import UnifiedTheory.Audit.KFCausalClockFloorLongitudinalTails
import UnifiedTheory.Audit.KFCausalClockFloorVacuumOutputFaithful
import UnifiedTheory.Audit.KFCausalClockFloorAveragedClockBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedLongitudinalTail
noncomputable section
open MeasureTheory
open scoped ENNReal
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalTails
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy (closedEnergy)
open UnifiedTheory.Audit.KFCausalClockFloorVacuumOutputFaithful (closedEnergy_vacuum_graph)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy

def orbitPositiveTail (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (R : ℝ) (f : Hilbert) : ℝ≥0∞ :=
  ∫⁻ θ, ENNReal.ofReal (positiveTail ε hε h R
    (inverseL ε hε (action h hh (2*Real.pi*θ) f))) ∂angleMeasure

theorem closed_energy_positive_tail (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hb : |h| ≤ Real.pi*ε) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (m g κ t R : ℝ) (hκ : 0 < κ) (f : Hilbert) (y : Output (Fin 8) Hilbert)
    (hfy : (f,y) ∈ (closedEnergy ε hε h v l m g κ t).graph) :
    positiveTail ε hε h R (inverseL ε hε f) ≤
      (Real.exp (-R)/(Real.exp (2*t)*κ))*‖y‖^2 := by
  let c := energyWeight m g κ t 7
  have hp : positiveTail ε hε h R (inverseL ε hε (c • f)) ≤ Real.exp (-R)*‖y 7‖^2 :=
    ordered_positive_tail_bound ε hε h R _ _
      (closedEnergy_vacuum_graph ε hε h hb v l m g κ t f y hfy)
  have hc : ‖c‖^2 = Real.exp (2*t)*κ := by
    change ‖((Real.exp t*Real.sqrt κ:ℝ):ℂ)‖^2 = _
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,Real.sq_sqrt hκ.le,
      show 2*t=t+t by ring,Real.exp_add,pow_two]
  have hs : positiveTail ε hε h R (inverseL ε hε (c • f)) =
      ‖c‖^2*positiveTail ε hε h R (inverseL ε hε f) :=
    (congrArg (positiveTail ε hε h R) ((inverseL ε hε).map_smul c f)).trans
      (positiveTail_smul ε hε h R c (inverseL ε hε f))
  have hy := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le y 7) 2) (Real.exp_pos (-R)).le
  have he : (Real.exp (2*t)*κ)*positiveTail ε hε h R (inverseL ε hε f) ≤
      Real.exp (-R)*‖y‖^2 :=
    (congrArg (fun r => r*positiveTail ε hε h R (inverseL ε hε f)) hc).symm.trans_le
      ((hs.symm.trans_le hp).trans hy)
  have hd : positiveTail ε hε h R (inverseL ε hε f) ≤
      (Real.exp (-R)*‖y‖^2)/(Real.exp (2*t)*κ) :=
    (le_div_iff₀ (mul_pos (Real.exp_pos (2*t)) hκ)).mpr (by nlinarith only [he])
  exact hd.trans_eq (by ring)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ Real.pi*ε) (hh : h ≠ 0)
  (m g κ t R : ℝ)
local notation "B" => KFCausalClockFloorFormHamiltonian.formData ε hε h hb m g κ t
local notation "V" => AveragedSpace ε hε h hb hh m g κ t
local notation "J" => embedding ε hε h hb hh m g κ t
local notation "A" => energyOutput ε hε h hb hh m g κ t
local notation "L" => sectionMap ε hε h hb hh m g κ t

theorem averaged_positive_tail (hκ : 0 < κ) (u : V) :
    orbitPositiveTail ε hε h hh R (J u) ≤
      ENNReal.ofReal ((Real.exp (-R)/(Real.exp (2*t)*κ))*‖A u‖^2) := by
  let c := Real.exp (-R)/(Real.exp (2*t)*κ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hi : Integrable (fun θ => ‖KFCausalClosedGraphForm.energyOutput B (L u θ)‖^2) angleMeasure := by
    have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (A u))).mp (Lp.memLp (A u))
    apply hi.congr
    filter_upwards [(KFCausalClosedGraphForm.energyOutput B).coeFn_compLp (L u)] with θ hθ
    change ‖(KFCausalClosedGraphForm.energyOutput B).compLp (L u) θ‖^2 = _
    exact congrArg (fun v => ‖v‖^2) hθ
  have hp : orbitPositiveTail ε hε h hh R (J u) ≤
      ∫⁻ θ, ENNReal.ofReal (c*‖KFCausalClosedGraphForm.energyOutput B (L u θ)‖^2) ∂angleMeasure := by
    apply lintegral_mono_ae
    filter_upwards [orbit_lift_ae ε hε h hb hh m g κ t u] with θ hθ
    have he := closed_energy_positive_tail ε hε h hb modelDirections pointField m g κ t R hκ
      _ _ (L u θ).property
    change positiveTail ε hε h R (inverseL ε hε (KFCausalClosedGraphForm.embedding B (L u θ))) ≤ _ at he
    have ht := congrArg (fun f : Hilbert => positiveTail ε hε h R (inverseL ε hε f)) hθ
    exact ENNReal.ofReal_le_ofReal (ht.symm.trans_le he)
  have he := (ofReal_integral_eq_lintegral_ofReal (hi.const_mul c)
    (Filter.Eventually.of_forall (fun _ => mul_nonneg hc (sq_nonneg _)))).symm
  have hv : (∫ θ, c*‖KFCausalClosedGraphForm.energyOutput B (L u θ)‖^2 ∂angleMeasure) =
      c*‖A u‖^2 := (integral_const_mul c _).trans
    (congrArg (fun r => c*r) (energy_integral ε hε h hb hh m g κ t u).symm)
  exact hp.trans_eq (he.trans (congrArg ENNReal.ofReal hv))

omit hb in
theorem form_positive_tail (hs : |h| ≤ 2*Real.pi*ε/3) (hκ : 0 < κ)
    (u : KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hs m g κ t) :
    orbitPositiveTail ε hε h hh R
      (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ t u) ≤
      ENNReal.ofReal ((Real.exp (-R)/(Real.exp (2*t)*κ))*
        ‖KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hs m g κ t u‖^2) := by
  let v := Classical.choose (KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective
    ε hε h hh hs m g κ t u)
  have hv := Classical.choose_spec (KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective
    ε hε h hh hs m g κ t u)
  change KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hs m g κ t v = u at hv
  have he := averaged_positive_tail ε hε h
    (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hs) hh m g κ t R hκ v
  have hJ := congrArg (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ t) hv
  have hA := congrArg (fun z => ‖KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hs m g κ t z‖^2) hv
  exact (congrArg (orbitPositiveTail ε hε h hh R) hJ).symm.trans_le
    (he.trans_eq (congrArg (fun E => ENNReal.ofReal ((Real.exp (-R)/(Real.exp (2*t)*κ))*E)) hA))

omit hb in
theorem reference_positive_tail (hs : |h| ≤ 2*Real.pi*ε/3) (hκ : 0 < κ)
    (u : KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hs m g κ 0) :
    orbitPositiveTail ε hε h hh R
      (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ 0 u) ≤
      ENNReal.ofReal ((Real.exp (-R)/(Real.exp (2*t)*κ))*
        KFCausalClockFloorAveragedTimeControl.timeEnergy ε hε h hh hs m g κ t u) := by
  have he := form_positive_tail ε hε h hh m g κ t R hs hκ
    (KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hs m g κ 0 t u)
  have hJ := KFCausalClockFloorAveragedFormTransport.transfer_embedding ε hε h hh hs m g κ 0 t u
  have hE := KFCausalClockFloorAveragedTimeControl.timeEnergy_actual ε hε h hh hs m g κ t u
  exact (congrArg (orbitPositiveTail ε hε h hh R) hJ).symm.trans_le
    (he.trans_eq (congrArg (fun E => ENNReal.ofReal ((Real.exp (-R)/(Real.exp (2*t)*κ))*E)) hE))

#print axioms closed_energy_positive_tail
#print axioms averaged_positive_tail
#print axioms form_positive_tail
#print axioms reference_positive_tail

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedLongitudinalTail
