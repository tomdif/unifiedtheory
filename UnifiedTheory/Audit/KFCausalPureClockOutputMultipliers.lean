/- Bounded clock operators in the original coherent pure-momentum output.
Their graph preservation supplies clock and kinetic domains of that output. -/
import UnifiedTheory.Audit.KFCausalBoundedClockFactorGraphs
import UnifiedTheory.Audit.KFCausalShiftedClockMomentOperator
import UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalPureClockOutputMultipliers
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockDerivative (rate)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain (clockInverse clockInverse_coe rate_bound)
open UnifiedTheory.Audit.KFCausalBoundedClockCharge (multiplier multiplier_coe)
open UnifiedTheory.Audit.KFCausalShiftedClockMomentOperator (momentOperator)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)

include hε in
theorem rate_continuous : Continuous (fun s => (rate ε s:ℂ)) := by
  unfold rate clock
  fun_prop (disch := intro s; positivity)

def rateOperator : Hilbert →L[ℂ] Hilbert :=
  multiplier (fun s => (rate ε s:ℂ)) (rate_continuous ε hε).measurable
    (1/(8*ε)) (by positivity) (fun s => by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using rate_bound ε hε s)

theorem rateOperator_coe (f : Hilbert) :
    rateOperator ε hε f =ᵐ[volume] fun x => (rate ε x.1:ℂ)*f x :=
  multiplier_coe _ _ _ _ _ f

def coefficient (p s : ℝ) : ℂ := ((p:ℂ)*Complex.I-1)*(clock ε s:ℂ)⁻¹-(rate ε s:ℂ)

def boundedPart (p : ℝ) : Hilbert →L[ℂ] Hilbert :=
  ((p:ℂ)*Complex.I-1) • clockInverse ε hε-rateOperator ε hε

theorem boundedPart_coe (p : ℝ) (f : Hilbert) :
    boundedPart ε hε p f =ᵐ[volume] fun x => coefficient ε p x.1*f x := by
  filter_upwards [Lp.coeFn_sub (((p:ℂ)*Complex.I-1) • clockInverse ε hε f) (rateOperator ε hε f),
    Lp.coeFn_smul ((p:ℂ)*Complex.I-1) (clockInverse ε hε f),
    clockInverse_coe ε hε f,rateOperator_coe ε hε f] with x hs hm hi hr
  change (((p:ℂ)*Complex.I-1) • clockInverse ε hε f-rateOperator ε hε f) x = _
  rw [hs]
  simp only [Pi.sub_apply,hm,Pi.smul_apply,smul_eq_mul,hi,hr,coefficient]
  ring

def outputMap (p : ℝ) (f g : Hilbert) : Hilbert :=
  (-Complex.I*(h:ℂ)) • (boundedPart ε hε p f-(2*(a:ℂ)) • momentOperator ε a 0 ha g)

theorem outputMap_continuous (p : ℝ) (f g : ℝ → Hilbert) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun θ => outputMap ε a h hε ha p (f θ) (g θ)) :=
  (((boundedPart ε hε p).continuous.comp hf).sub
    (((momentOperator ε a 0 ha).continuous.comp hg).const_smul (2*(a:ℂ)))).const_smul _

theorem outputMap_half_graph (p : ℝ) (f f' g g' : Hilbert)
    (hf : (f,f') ∈ (clockHalf ε).graph) (hg : (g,g') ∈ (clockHalf ε).graph) :
    (outputMap ε a h hε ha p f g,outputMap ε a h hε ha p f' g') ∈ (clockHalf ε).graph := by
  have hi : (clockInverse ε hε f,clockInverse ε hε f') ∈ (clockHalf ε).graph :=
    (clockHalf ε).graph.smul_mem (1/(ε:ℂ))
      (KFCausalClockFloorKineticDefect.clockHalf_graph_defect ε hε f f' hf)
  have hr : (rateOperator ε hε f,rateOperator ε hε f') ∈ (clockHalf ε).graph :=
    KFCausalBoundedClockFactorGraphs.half_graph _ _ _ _ _ ε f f' hf
  have hm : (momentOperator ε a 0 ha g,momentOperator ε a 0 ha g') ∈ (clockHalf ε).graph :=
    KFCausalBoundedClockFactorGraphs.half_graph _ _ _ _ _ ε g g' hg
  exact (clockHalf ε).graph.smul_mem _ ((clockHalf ε).graph.sub_mem
    ((clockHalf ε).graph.sub_mem ((clockHalf ε).graph.smul_mem _ hi) hr)
    ((clockHalf ε).graph.smul_mem _ hm))

theorem outputMap_kinetic_graph (hh : h ≠ 0) (v : Transverse) (p : ℝ) (f f' g g' : Hilbert)
    (hf : (f,f') ∈ (clockMomentum ε h v).graph) (hg : (g,g') ∈ (clockMomentum ε h v).graph) :
    (outputMap ε a h hε ha p f g,outputMap ε a h hε ha p f' g') ∈ (clockMomentum ε h v).graph := by
  have hi : (clockInverse ε hε f,clockInverse ε hε f') ∈ (clockMomentum ε h v).graph :=
    (clockMomentum ε h v).graph.smul_mem (1/(ε:ℂ))
      (KFCausalClockFloorKineticDefect.clockMomentum_graph_defect ε hε h v f f' hf)
  have hr : (rateOperator ε hε f,rateOperator ε hε f') ∈ (clockMomentum ε h v).graph :=
    KFCausalBoundedClockFactorGraphs.kinetic_graph _ _ _ _ _ ε h hh v f f' hf
  have hm : (momentOperator ε a 0 ha g,momentOperator ε a 0 ha g') ∈ (clockMomentum ε h v).graph :=
    KFCausalBoundedClockFactorGraphs.kinetic_graph _ _ _ _ _ ε h hh v g g' hg
  exact (clockMomentum ε h v).graph.smul_mem _ ((clockMomentum ε h v).graph.sub_mem
    ((clockMomentum ε h v).graph.sub_mem ((clockMomentum ε h v).graph.smul_mem _ hi) hr)
    ((clockMomentum ε h v).graph.smul_mem _ hm))

#print axioms rate_continuous
#print axioms rateOperator_coe
#print axioms boundedPart_coe
#print axioms outputMap_continuous
#print axioms outputMap_half_graph
#print axioms outputMap_kinetic_graph
end
end UnifiedTheory.Audit.KFCausalPureClockOutputMultipliers
