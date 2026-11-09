/- A concrete dense test space in the full six-coordinate configuration
Hilbert space. This supplies the domain for extending the coupled change
of variables; it does not assert a full Hamiltonian domain. -/
import UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalConfigurationTestSpace
noncomputable section
open MeasureTheory Set Filter
open scoped CompactlySupported ENNReal
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow

abbrev Test := C_c(Configuration, ℂ)
abbrev Hilbert := Lp ℂ 2 (volume : Measure Configuration)

theorem test_memLp (f : Test) : MemLp f 2 :=
  f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport

def embedding : Test →ₗ[ℂ] Hilbert where
  toFun f := (test_memLp f).toLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(test_memLp (f+g)).coeFn_toLp,(test_memLp f).coeFn_toLp,
      (test_memLp g).coeFn_toLp,Lp.coeFn_add ((test_memLp f).toLp f) ((test_memLp g).toLp g)]
      with x hfg hf hg hs
    rw [hfg,hs]
    simp only [Pi.add_apply,hf,hg,CompactlySupportedContinuousMap.add_apply]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(test_memLp (c • f)).coeFn_toLp,(test_memLp f).coeFn_toLp,
      Lp.coeFn_smul c ((test_memLp f).toLp f)] with x hcf hf hs
    simp only [RingHom.id_apply]
    rw [hcf,hs]
    simp only [Pi.smul_apply,hf,CompactlySupportedContinuousMap.smul_apply]

theorem embedding_coe (f : Test) : embedding f =ᵐ[volume] f := (test_memLp f).coeFn_toLp

theorem embedding_injective : Function.Injective embedding := by
  intro f g h
  apply DFunLike.ext'
  apply f.continuous.ae_eq_iff_eq volume g.continuous |>.mp
  exact (embedding_coe f).symm.trans (h ▸ embedding_coe g)

theorem embedding_dense : DenseRange embedding := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun δ hδ => ?_
  obtain ⟨g,hgs,hgn,hgc,hgm⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num : (2:ℝ≥0∞) ≠ ∞) hδ.ne'
  let G : Test := ⟨⟨g,hgc⟩,hgs⟩
  refine ⟨embedding G,⟨G,rfl⟩,?_⟩
  change embedding G ∈ Metric.closedEBall f δ
  rw [Metric.mem_closedEBall']
  change edist f ((test_memLp G).toLp G) ≤ δ
  rw [← Lp.toLp_coeFn f (Lp.memLp f),Lp.edist_toLp_toLp]
  exact hgn

theorem test_square_integrable (f : Test) : Integrable (fun x => ‖f x‖^2) :=
  (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).mp (test_memLp f)

theorem embedding_norm_square (f : Test) : ‖embedding f‖^2 = ∫ x, ‖f x‖^2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    _ = inner ℂ (embedding f) (embedding f) := by
      simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embedding f)).symm
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [embedding_coe f] with x hx
      rw [hx,inner_self_eq_norm_sq_to_K]
      norm_cast

#print axioms embedding
#print axioms embedding_injective
#print axioms embedding_dense
#print axioms test_square_integrable
#print axioms embedding_norm_square

end
end UnifiedTheory.Audit.KFCausalConfigurationTestSpace
