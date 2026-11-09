/- All four actual physical transverse momenta survive the clustered
limit. Finite graph identities and strong output limits close the maximal
momentum graphs; no closedness of an arbitrary composition is assumed. -/
import UnifiedTheory.Audit.KFCausalNarrowBlockDerivativeLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredNarrowFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredTransverseGraphs
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredClockVectors (vector limitingVector vector_tendsto)
open KFCausalNarrowFourierCoordinates (mixedCoordinates)
open KFCausalNarrowPacketMomentumGraphs (differentialCoordinates)
open KFCausalNarrowBlockDerivativeLimit (blockVector blockVector_coe blockVector_exists_limit)
open KFCausalClusteredPacketDerivativeCoordinates (blockDifferential differential_sum)
open KFCausalPhysicalTransverseMomentum (transverseMomentum transverseMomentum_closed)
open KFCausalPhysicalEnergyFactors (modelDirections)

variable {m : ℕ} (f : Family m) (c : ℝ → Fin m → ℂ) (α β h : ℝ)

theorem differential_blocks (δ : ℝ) (hδ : 0 < δ) (j : Fin 4) (z : Block 2 × Block 4) :
    (∑ k, coefficients f δ k*differentialCoordinates α β (widths f δ k) (sources f k) (polynomials f k)
      (fun s => c s (index f k).1) j z) =
      ∑ i, f.amplitude i*blockDifferential (f.degree i) δ α β (f.source i) (f.polynomial i) (fun s => c s i) j z := by
  unfold coefficients widths sources polynomials
  rw [sum_index f (fun k => (f.amplitude k.1*KFCausalClusteredWidthProfiles.coefficients (f.degree k.1) δ k.2)*
    differentialCoordinates α β (KFCausalClusteredWidthProfiles.widths (f.degree k.1) δ k.2)
      (f.source k.1) (f.polynomial k.1) (fun s => c s k.1) j z)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← differential_sum (f.degree i) δ α β hδ (f.source i) (f.polynomial i) (fun s => c s i) j z,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hc : ∀ i, Continuous (fun s => c s i)) (hc2 : ∀ i, MemLp (fun s => c s i) 2 volume)

def finiteOutput (δ : ℝ) (j : Fin 4) : Hilbert := if hδ : 0 < δ then ∑ k, coefficients f δ k •
  KFCausalNarrowPacketMomentumGraphs.momentumOutput α β (widths f δ k) hα hβ
    (lt_of_lt_of_le zero_lt_one (widths_admissible f δ hδ.le k)) (sources f k) (polynomials f k)
    (fun s => c s (index f k).1) (hc _) (hc2 _) h j else 0

def coordinateOutput (δ : ℝ) (j : Fin 4) : ProductHilbert 2 4 :=
  (-Complex.I*(h:ℂ)) • ∑ i, f.amplitude i •
    blockVector α β hα hβ (f.source i) (f.polynomial i) (fun s => c s i) (hc i) (hc2 i) (f.degree i) j δ

theorem finite_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 4) :
    (vector f c α β hα hβ hw hc2 δ,finiteOutput f c α β h hα hβ hc hc2 δ j) ∈
      (transverseMomentum h (modelDirections j)).graph := by
  rw [KFCausalCorrelatedClusteredNarrowFourier.vector_sum f c α β hα hβ hw hc hc2 δ hδ,
    finiteOutput,dif_pos hδ]
  have hs := (transverseMomentum h (modelDirections j)).graph.sum_mem
    fun k (_ : k ∈ (Finset.univ : Finset (Fin (count f)))) =>
      (transverseMomentum h (modelDirections j)).graph.smul_mem (coefficients f δ k)
        (KFCausalNarrowPacketMomentumGraphs.momentum_graph α β (widths f δ k) hα hβ
          (lt_of_lt_of_le zero_lt_one (widths_admissible f δ hδ.le k)) (sources f k) (polynomials f k)
          (fun s => c s (index f k).1) (hc _) (hc2 _) h j)
  simpa only [Prod.smul_mk,← prod_mk_sum] using hs

theorem finite_coordinates_coe (δ : ℝ) (hδ : 0 < δ) (j : Fin 4) :
    mixedCoordinates (finiteOutput f c α β h hα hβ hc hc2 δ j) =ᵐ[volume]
      fun z => ∑ k, coefficients f δ k*((-Complex.I*(h:ℂ))*differentialCoordinates α β (widths f δ k)
        (sources f k) (polynomials f k) (fun s => c s (index f k).1) j z) := by
  rw [finiteOutput,dif_pos hδ,map_sum]
  simp only [map_smul]
  apply KFCausalFiniteLpRepresentatives.weighted_sum_coe
  intro k
  exact KFCausalNarrowPacketMomentumGraphs.momentum_coordinates_coe α β (widths f δ k) hα hβ
    (lt_of_lt_of_le zero_lt_one (widths_admissible f δ hδ.le k)) (sources f k) (polynomials f k)
    (fun s => c s (index f k).1) (hc _) (hc2 _) h j

theorem coordinateOutput_coe (δ : ℝ) (hδ : 0 < δ) (j : Fin 4) :
    coordinateOutput f c α β h hα hβ hc hc2 δ j =ᵐ[volume]
      fun z => (-Complex.I*(h:ℂ))*(∑ i, f.amplitude i*
        blockDifferential (f.degree i) δ α β (f.source i) (f.polynomial i) (fun s => c s i) j z) := by
  have hs := KFCausalFiniteLpRepresentatives.weighted_sum_coe volume f.amplitude
    (fun i => blockVector α β hα hβ (f.source i) (f.polynomial i) (fun s => c s i) (hc i) (hc2 i) (f.degree i) j δ)
    (fun i => blockDifferential (f.degree i) δ α β (f.source i) (f.polynomial i) (fun s => c s i) j)
    (fun i => blockVector_coe α β hα hβ (f.source i) (f.polynomial i) (fun s => c s i) (hc i) (hc2 i) (f.degree i) j δ hδ)
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ)) (∑ i, f.amplitude i •
    blockVector α β hα hβ (f.source i) (f.polynomial i) (fun s => c s i) (hc i) (hc2 i) (f.degree i) j δ),hs] with z hz hs
  simp only [coordinateOutput,hz,Pi.smul_apply,smul_eq_mul,hs]

theorem finite_coordinates_eq (δ : ℝ) (hδ : 0 < δ) (j : Fin 4) :
    mixedCoordinates (finiteOutput f c α β h hα hβ hc hc2 δ j) =
      coordinateOutput f c α β h hα hβ hc hc2 δ j := by
  apply Lp.ext
  filter_upwards [finite_coordinates_coe f c α β h hα hβ hc hc2 δ hδ j,
    coordinateOutput_coe f c α β h hα hβ hc hc2 δ hδ j] with z hf hg
  rw [hf,hg,← differential_blocks f c α β δ hδ j z,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem coordinateOutput_exists_limit (j : Fin 4) : ∃ v : ProductHilbert 2 4,
    Tendsto (fun δ => coordinateOutput f c α β h hα hβ hc hc2 δ j) (𝓝[>] 0) (𝓝 v) := by
  choose v hv using fun i => blockVector_exists_limit α β hα hβ (f.source i) (f.polynomial i)
    (fun s => c s i) (hc i) (hc2 i) (f.degree i) j
  exact ⟨_,(tendsto_finset_sum Finset.univ (fun i _ => (hv i).const_smul (f.amplitude i))).const_smul (-Complex.I*(h:ℂ))⟩

theorem output_exists_limit (j : Fin 4) : ∃ v : Hilbert,
    Tendsto (fun δ => finiteOutput f c α β h hα hβ hc hc2 δ j) (𝓝[>] 0) (𝓝 v) := by
  obtain ⟨v,hv⟩ := coordinateOutput_exists_limit f c α β h hα hβ hc hc2 j
  refine ⟨mixedCoordinates.symm v,?_⟩
  apply Tendsto.congr' _ ((mixedCoordinates.symm.continuous.tendsto v).comp hv)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  dsimp only [Function.comp_apply]
  rw [← finite_coordinates_eq f c α β h hα hβ hc hc2 δ hδ j,mixedCoordinates.symm_apply_apply]

def limitingOutput (j : Fin 4) : Hilbert := Classical.choose (output_exists_limit f c α β h hα hβ hc hc2 j)

theorem output_tendsto (j : Fin 4) :
    Tendsto (fun δ => finiteOutput f c α β h hα hβ hc hc2 δ j) (𝓝[>] 0)
      (𝓝 (limitingOutput f c α β h hα hβ hc hc2 j)) :=
  Classical.choose_spec (output_exists_limit f c α β h hα hβ hc hc2 j)

theorem limiting_graph (j : Fin 4) :
    (limitingVector f c α β hα hβ hw hc2 hc,limitingOutput f c α β h hα hβ hc hc2 j) ∈
      (transverseMomentum h (modelDirections j)).graph := by
  apply (transverseMomentum_closed h (modelDirections j)).mem_of_tendsto
    ((vector_tendsto f c α β hα hβ hw hc2 hc).prodMk_nhds (output_tendsto f c α β h hα hβ hc hc2 j))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_graph f c α β h hα hβ hw hc hc2 δ hδ j

theorem limiting_domain (j : Fin 4) : limitingVector f c α β hα hβ hw hc2 hc ∈
    (transverseMomentum h (modelDirections j)).domain :=
  LinearPMap.mem_domain_of_mem_graph (limiting_graph f c α β h hα hβ hw hc hc2 j)

theorem graph_tendsto (j : Fin 4) :
    Tendsto (fun δ => (vector f c α β hα hβ hw hc2 δ,finiteOutput f c α β h hα hβ hc hc2 δ j))
      (𝓝[>] 0) (𝓝 (limitingVector f c α β hα hβ hw hc2 hc,limitingOutput f c α β h hα hβ hc hc2 j)) :=
  (vector_tendsto f c α β hα hβ hw hc2 hc).prodMk_nhds (output_tendsto f c α β h hα hβ hc hc2 j)

#print axioms differential_blocks
#print axioms finite_graph
#print axioms finite_coordinates_coe
#print axioms coordinateOutput_coe
#print axioms finite_coordinates_eq
#print axioms coordinateOutput_exists_limit
#print axioms output_exists_limit
#print axioms output_tendsto
#print axioms limiting_graph
#print axioms limiting_domain
#print axioms graph_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredTransverseGraphs
