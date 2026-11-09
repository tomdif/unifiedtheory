/- Actual commutation of the paired squeeze and chart phases, including
preservation of the full maximal chart and squeeze-generator graphs. -/
import UnifiedTheory.Audit.KFCausalPairedSqueezeClockCommutation
import UnifiedTheory.Audit.KFCausalClockFloorGaugeDerivative
import UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator
import UnifiedTheory.Audit.KFCausalClockFloorReferenceChartModulation
import UnifiedTheory.Audit.KFCausalClockFloorReferenceSqueeze

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalSqueezeChartCommutation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport
open UnifiedTheory.Audit.KFCausalClockFloorGaugeDerivative (chartOperator chartOperator_graph gauge)
open UnifiedTheory.Audit.KFCausalClockFloorChartModulation (modulation modulation_coe phase)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart)
open UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator (squeezeMomentum bounded_commutation)

theorem chart_graph_squeeze (ε a : ℝ) (f z : Hilbert) (hfz : (f,z) ∈ (chartOperator ε).graph) :
    (transport a f,transport a z) ∈ (chartOperator ε).graph := by
  apply (chartOperator_graph ε _ _).mpr
  filter_upwards [transport_coe a z,transport_coe a f,
    (squeezeFlow_quasiMeasurePreserving a).ae ((chartOperator_graph ε f z).mp hfz)] with x hz hf hx
  rw [hz,hx,hf]
  change (Real.exp (-a/2):ℂ)*((chart ε x.1:ℂ)*f (squeezeFlow a x)) =
    (chart ε x.1:ℂ)*((Real.exp (-a/2):ℂ)*f (squeezeFlow a x))
  ring

theorem chart_domain_squeeze (ε a : ℝ) (f : Hilbert) :
    transport a f ∈ (chartOperator ε).domain ↔ f ∈ (chartOperator ε).domain := by
  have hf (b : ℝ) (v : Hilbert) (hv : v ∈ (chartOperator ε).domain) :
      transport b v ∈ (chartOperator ε).domain := by
    obtain ⟨z,hz⟩ := LinearPMap.mem_domain_iff.mp hv
    exact LinearPMap.mem_domain_of_mem_graph (chart_graph_squeeze ε b v z hz)
  constructor
  · intro hv
    simpa only [transport_reverse] using hf (-a) _ hv
  · exact hf a f

theorem modulation_commutes (ε a r : ℝ) (f : Hilbert) :
    transport a (modulation ε r f) = modulation ε r (transport a f) :=
  KFCausalPairedSqueezeClockCommutation.clock_multiplier (modulation ε r : Hilbert →L[ℂ] Hilbert)
    (fun s => Real.fourierChar (r*chart ε s)) (modulation_coe ε r) a f

theorem gauge_commutes (ε h a t : ℝ) (f : Hilbert) :
    transport a (gauge ε h t f) = gauge ε h t (transport a f) :=
  modulation_commutes ε a (KFCausalClockFloorGaugeEnergy.rate h t) f

theorem modulation_squeeze_graph (ε h : ℝ) (hne : h ≠ 0) (r : ℝ) (f z : Hilbert)
    (hfz : (f,z) ∈ (squeezeMomentum h).graph) :
    (modulation ε r f,modulation ε r z) ∈ (squeezeMomentum h).graph :=
  bounded_commutation h hne (modulation ε r) (fun a x => (modulation_commutes ε a r x).symm) f z hfz

theorem gauge_defect_commutes (ε : ℝ) (hε : 0 < ε) (h t : ℝ) (f : Hilbert) :
    gauge ε h t (KFCausalClockFloorDefectOperator.defectOperator ε hε f) =
      KFCausalClockFloorDefectOperator.defectOperator ε hε (gauge ε h t f) := by
  apply Lp.ext
  filter_upwards [modulation_coe ε (KFCausalClockFloorGaugeEnergy.rate h t)
      (KFCausalClockFloorDefectOperator.defectOperator ε hε f),
    KFCausalClockFloorDefectOperator.defectOperator_coe ε hε (gauge ε h t f),
    KFCausalClockFloorDefectOperator.defectOperator_coe ε hε f,
    modulation_coe ε (KFCausalClockFloorGaugeEnergy.rate h t) f] with x h1 h2 h3 h4
  change modulation ε (KFCausalClockFloorGaugeEnergy.rate h t) _ x = _
  rw [h1,h2,h3]
  change _ = _*modulation ε (KFCausalClockFloorGaugeEnergy.rate h t) f x
  rw [h4]
  ring

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m q k t : ℝ)

theorem form_actions_commute (a r : ℝ)
    (u : KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hne hh m q k t) :
    KFCausalClockFloorReferenceSqueeze.formAction ε hε h hne hh m q k a t
      (KFCausalClockFloorReferenceChartModulation.formAction ε hε h hne hh m q k r t u) =
    KFCausalClockFloorReferenceChartModulation.formAction ε hε h hne hh m q k r t
      (KFCausalClockFloorReferenceSqueeze.formAction ε hε h hne hh m q k a t u) := by
  apply KFCausalClockFloorAveragedFormTransport.embedding_injective ε hε h hne hh m q k t
  simp only [KFCausalClockFloorReferenceSqueeze.formAction_embedding,
    KFCausalClockFloorReferenceChartModulation.formAction_embedding,modulation_commutes]

#print axioms chart_graph_squeeze
#print axioms chart_domain_squeeze
#print axioms modulation_commutes
#print axioms gauge_commutes
#print axioms modulation_squeeze_graph
#print axioms gauge_defect_commutes
#print axioms form_actions_commute
end
end UnifiedTheory.Audit.KFCausalSqueezeChartCommutation
