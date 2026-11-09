/- Exact maximal physical-field graphs in the actual mixed Fourier chart.
The two symmetric charged positions remain position multipliers; the
equivalence includes their full weighted-L2 domains. -/
import UnifiedTheory.Audit.KFCausalUnboundedSpectatorFourier
import UnifiedTheory.Audit.KFCausalPhysicalFourierGeneralCoordinates
import UnifiedTheory.Audit.KFCausalPhysicalField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalPhysicalSpectatorGraph
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalPhysicalField (physicalField physicalField_graph)
open KFCausalPhysicalMixedCoordinates (pairedCoordinates mixedCoordinates)
open KFCausalPhysicalFourierGeneralCoordinates (Product pairedChart pairedChart_symm
  pairedChart_preserves_volume pairedCoordinates_coe)
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalPairedModeCoordinates (scale scale_square)

private theorem paired_chart_coe (f : Hilbert) :
    pairedCoordinates f =ᵐ[volume] fun z => f (pairedChart.symm z) := by
  simpa only [pairedChart_symm] using pairedCoordinates_coe f

theorem paired_field_graph_iff (l : Transverse →L[ℝ] ℝ) (v : Block 4 → ℝ)
    (hl : ∀ z : Product, l (pairedChart.symm z).2 = v z.2) (f g : Hilbert) :
    (f,g) ∈ (physicalField l).graph ↔
      pairedCoordinates g =ᵐ[volume] fun z => (v z.2 : ℂ)*(pairedCoordinates f) z := by
  rw [physicalField_graph]
  constructor
  · intro hg
    have hp := pairedChart_preserves_volume.symm.quasiMeasurePreserving.ae hg
    filter_upwards [hp,paired_chart_coe f,paired_chart_coe g] with z hz hf hg
    rw [hg,hf,hz,hl]
  · intro hg
    have hp : ∀ᵐ z : Product ∂volume,
        g (pairedChart.symm z) = (l (pairedChart.symm z).2 : ℂ)*f (pairedChart.symm z) := by
      filter_upwards [hg,paired_chart_coe f,paired_chart_coe g] with z hz hf hg
      rw [hg,hf,← hl] at hz
      exact hz
    have hq := pairedChart_preserves_volume.quasiMeasurePreserving.ae hp
    simpa only [pairedChart.symm_apply_apply] using hq

theorem mixed_field_graph_iff (l : Transverse →L[ℝ] ℝ) (v : Block 4 → ℝ)
    (hv : Measurable v) (hl : ∀ z : Product, l (pairedChart.symm z).2 = v z.2)
    (f g : Hilbert) :
    (f,g) ∈ (physicalField l).graph ↔
      mixedCoordinates g =ᵐ[volume] fun z => (v z.2 : ℂ)*(mixedCoordinates f) z := by
  rw [paired_field_graph_iff l v hl]
  exact (KFCausalUnboundedSpectatorFourier.leftFourier_relation_iff 2 4 v hv
    (pairedCoordinates f) (pairedCoordinates g)).symm

theorem mixed_field_domain_iff (l : Transverse →L[ℝ] ℝ) (v : Block 4 → ℝ)
    (hv : Measurable v) (hl : ∀ z : Product, l (pairedChart.symm z).2 = v z.2)
    (f : Hilbert) :
    f ∈ (physicalField l).domain ↔
      MemLp (fun z : Product => (v z.2 : ℂ)*(mixedCoordinates f) z) 2 := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨g,hg⟩
    exact (Lp.memLp (mixedCoordinates g)).ae_eq ((mixed_field_graph_iff l v hv hl f g).mp hg)
  · intro hm
    refine ⟨mixedCoordinates.symm (hm.toLp _), ?_⟩
    apply (mixed_field_graph_iff l v hv hl f _).mpr
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hm.coeFn_toLp

def symmetricPosition (i : Fin 2) : Transverse →L[ℝ] ℝ :=
  let c (j : Fin 5) : Transverse →L[ℝ] ℝ := ContinuousLinearMap.proj j
  ![scale • (c 0 + c 1),scale • (c 2 + c 3)] i

def symmetricIndex (i : Fin 2) : Fin 4 := ![1,2] i

theorem symmetric_position_chart (i : Fin 2) (z : Product) :
    symmetricPosition i (pairedChart.symm z).2 = z.2 (symmetricIndex i) := by
  rw [pairedChart_symm]
  fin_cases i
  · dsimp [symmetricPosition,symmetricIndex,KFCausalShiftedPhysicalFourierSlices.reconstruct]
    linear_combination 2*(z.2 1)*scale_square
  · dsimp [symmetricPosition,symmetricIndex,KFCausalShiftedPhysicalFourierSlices.reconstruct]
    linear_combination 2*(z.2 2)*scale_square

theorem symmetric_position_graph_iff (i : Fin 2) (f g : Hilbert) :
    (f,g) ∈ (physicalField (symmetricPosition i)).graph ↔
      mixedCoordinates g =ᵐ[volume]
        fun z : Product => (z.2 (symmetricIndex i) : ℂ)*(mixedCoordinates f) z :=
  mixed_field_graph_iff (symmetricPosition i) (fun v => v (symmetricIndex i))
    (by fun_prop) (symmetric_position_chart i) f g

theorem symmetric_position_domain_iff (i : Fin 2) (f : Hilbert) :
    f ∈ (physicalField (symmetricPosition i)).domain ↔
      MemLp (fun z : Product => (z.2 (symmetricIndex i) : ℂ)*(mixedCoordinates f) z) 2 :=
  mixed_field_domain_iff (symmetricPosition i) (fun v => v (symmetricIndex i))
    (by fun_prop) (symmetric_position_chart i) f

#print axioms paired_field_graph_iff
#print axioms mixed_field_graph_iff
#print axioms mixed_field_domain_iff
#print axioms symmetric_position_chart
#print axioms symmetric_position_graph_iff
#print axioms symmetric_position_domain_iff
end
end UnifiedTheory.Audit.KFCausalPhysicalSpectatorGraph
