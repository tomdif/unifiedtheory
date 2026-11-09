/- A genuine L2 lift into the graph form of a closed operator. The
section is constructed by orthogonal projection of the L2 input/output
pair, and recovers the original averaged energy graph exactly. -/
import UnifiedTheory.Audit.KFCausalClosedGraphForm
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalLpClosedGraphFormLift
noncomputable section
open MeasureTheory Filter
open scoped Topology
variable {X H K : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

omit [InnerProductSpace ℂ H] [InnerProductSpace ℂ K] in
theorem ae_relation_closed (μ : Measure X) (S : Set (H × K)) (hS : IsClosed S) :
    IsClosed {z : Lp H 2 μ × Lp K 2 μ | ∀ᵐ x ∂μ, (z.1 x,z.2 x) ∈ S} := by
  apply IsSeqClosed.isClosed
  intro u z hu hz
  have hf := (continuous_fst.tendsto z).comp hz
  have hg := (continuous_snd.tendsto z).comp hz
  obtain ⟨a,ha,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  obtain ⟨b,hb,hbe⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hg.comp ha.tendsto_atTop)).exists_seq_tendsto_ae
  have hm : ∀ᵐ x ∂μ, ∀ n, ((u (a (b n))).1 x,(u (a (b n))).2 x) ∈ S :=
    ae_all_iff.mpr (fun n => hu (a (b n)))
  filter_upwards [hae,hbe,hm] with x hx hy hm
  exact hS.mem_of_tendsto ((hx.comp hb.tendsto_atTop).prodMk_nhds hy)
    (Eventually.of_forall hm)

variable [CompleteSpace H] [CompleteSpace K]
open KFCausalClosedGraphForm

theorem exists_section (μ : Measure X) (D : Data H K)
    (f : Lp H 2 μ) (z : Lp K 2 μ)
    (hz : ∀ᵐ x ∂μ, (f x,z x) ∈ D.operator.graph) :
    ∃ v : Lp (FormSpace D) 2 μ,
      (embedding D).compLp v = f ∧ (energyOutput D).compLp v = z := by
  let p : Lp (H × K) 2 μ := (ContinuousLinearMap.inl ℂ H K).compLp f +
    (ContinuousLinearMap.inr ℂ H K).compLp z
  let e := (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap
  let q := e.compLp p
  let v := (energyGraph D).orthogonalProjection.compLp q
  have hp : ∀ᵐ x ∂μ, p x = (f x,z x) := by
    filter_upwards [Lp.coeFn_add ((ContinuousLinearMap.inl ℂ H K).compLp f)
      ((ContinuousLinearMap.inr ℂ H K).compLp z),
      (ContinuousLinearMap.inl ℂ H K).coeFn_compLp f,
      (ContinuousLinearMap.inr ℂ H K).coeFn_compLp z] with x hx hf hg
    simpa only [p,Pi.add_apply,hf,hg,ContinuousLinearMap.inl_apply,ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk,add_zero,zero_add] using hx
  have hv : ∀ᵐ x ∂μ, embedding D (v x) = f x ∧ energyOutput D (v x) = z x := by
    filter_upwards [hz,hp,e.coeFn_compLp p,
      (energyGraph D).orthogonalProjection.coeFn_compLp q] with x hx hp hq hv
    have he : q x = WithLp.toLp 2 (f x,z x) := by
      exact hq.trans (congrArg e hp)
    let w : FormSpace D := ⟨WithLp.toLp 2 (f x,z x),hx⟩
    have hw : (v x) = w := by
      rw [hv,he]
      exact (energyGraph D).orthogonalProjection_mem_subspace_eq_self w
    rw [hw]
    exact ⟨rfl,rfl⟩
  refine ⟨v,?_,?_⟩
  · apply Lp.ext
    filter_upwards [hv,(embedding D).coeFn_compLp v] with x hx he
    exact he.trans hx.1
  · apply Lp.ext
    filter_upwards [hv,(energyOutput D).coeFn_compLp v] with x hx he
    exact he.trans hx.2

theorem averaged_graph_iff
    (U : KFCausalUnitaryOrbitAverage.StrongUnitaryGroup H) (T : ℝ) (D : Data H K)
    (f : H) (z : Lp K 2 KFCausalUnitIntervalOrbit.angleMeasure) :
    (f,z) ∈ (KFCausalAveragedEnergyGraph.averagedOperator U T
      (embedding D) (energyOutput D)).graph ↔
    ∀ᵐ θ ∂KFCausalUnitIntervalOrbit.angleMeasure,
      (KFCausalUnitIntervalOrbit.orbit U T f θ,z θ) ∈ D.operator.graph := by
  rw [KFCausalAveragedEnergyGraph.averagedOperator_graph U T _ _ (embedding_injective D)]
  constructor
  · rintro ⟨v,hv⟩
    have hf := congrArg Prod.fst hv
    have hz := congrArg Prod.snd hv
    let s := KFCausalAveragedFormSpace.sectionMap U T (embedding D) v
    have he : (embedding D).compLp s = KFCausalUnitIntervalOrbit.orbit U T f := by
      rw [KFCausalAveragedFormSpace.compatibility]
      exact congrArg (KFCausalUnitIntervalOrbit.orbit U T) hf
    have ho : (energyOutput D).compLp s = z := hz
    filter_upwards [(embedding D).coeFn_compLp s,(energyOutput D).coeFn_compLp s] with θ h1 h2
    rw [he] at h1
    rw [ho] at h2
    rw [h1,h2]
    exact (s θ).property
  · intro hz
    obtain ⟨s,hs,ho⟩ := exists_section KFCausalUnitIntervalOrbit.angleMeasure D
      (KFCausalUnitIntervalOrbit.orbit U T f) z hz
    let v : KFCausalAveragedFormSpace.FormSpace U T (embedding D) :=
      ⟨WithLp.toLp 2 (f,s),by
        change (embedding D).compLp s - KFCausalUnitIntervalOrbit.orbit U T f = 0
        exact sub_eq_zero.mpr hs⟩
    exact ⟨v,Prod.ext rfl ho⟩

#print axioms ae_relation_closed
#print axioms exists_section
#print axioms averaged_graph_iff
end
end UnifiedTheory.Audit.KFCausalLpClosedGraphFormLift
