/- Lift an actual closed operator graph to L2-valued functions by the
almost-everywhere graph relation. Closedness follows from almost-everywhere
subsequences of strong L2 limits; no domain invariance is assumed. -/
import UnifiedTheory.Audit.KFCausalGraphDetectionModulus
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalLpClosedOperator
noncomputable section
open MeasureTheory Filter
open scoped Topology
variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure X) (T : H →ₗ.[ℂ] H)
local notation "L" => Lp H 2 μ

def graph : Submodule ℂ (L × L) where
  carrier := {z | ∀ᵐ x ∂μ, (z.1 x,z.2 x) ∈ T.graph}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := H) (p := 2) (μ := μ)] with x hx
    change ((0:L) x,(0:L) x) ∈ T.graph
    rw [hx]
    exact T.graph.zero_mem
  add_mem' := by
    intro u v hu hv
    filter_upwards [hu,hv,Lp.coeFn_add u.1 v.1,Lp.coeFn_add u.2 v.2] with x hx hy h1 h2
    change ( (u.1+v.1) x,(u.2+v.2) x) ∈ T.graph
    rw [h1,h2]
    exact T.graph.add_mem hx hy
  smul_mem' := by
    intro c u hu
    filter_upwards [hu,Lp.coeFn_smul c u.1,Lp.coeFn_smul c u.2] with x hx h1 h2
    change ((c • u.1) x,(c • u.2) x) ∈ T.graph
    rw [h1,h2]
    exact T.graph.smul_mem c hx

theorem graph_vertical_zero (y : L) (hy : (0,y) ∈ graph μ T) : y = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hy,Lp.coeFn_zero (E := H) (p := 2) (μ := μ)] with x hx h0
  exact T.graph_fst_eq_zero_snd hx h0

def operator : L →ₗ.[ℂ] L := (graph μ T).toLinearPMap

theorem operator_graph : (operator μ T).graph = graph μ T := by
  apply Submodule.toLinearPMap_graph_eq
  intro z hz h0
  have he : z = (0,z.2) := Prod.ext h0 rfl
  rw [he] at hz
  exact graph_vertical_zero μ T z.2 hz

theorem graph_closed (hT : T.IsClosed) : IsClosed (graph μ T : Set (L × L)) := by
  apply IsSeqClosed.isClosed
  intro u z hu hz
  have hf : Tendsto (fun n => (u n).1) atTop (𝓝 z.1) := (continuous_fst.tendsto z).comp hz
  have hg : Tendsto (fun n => (u n).2) atTop (𝓝 z.2) := (continuous_snd.tendsto z).comp hz
  obtain ⟨a,ha,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  obtain ⟨b,hb,hbe⟩ := (tendstoInMeasure_of_tendsto_Lp (hg.comp ha.tendsto_atTop)).exists_seq_tendsto_ae
  have hmem : ∀ᵐ x ∂μ, ∀ n, ((u (a (b n))).1 x,(u (a (b n))).2 x) ∈ T.graph :=
    ae_all_iff.mpr (fun n => hu (a (b n)))
  filter_upwards [hae,hbe,hmem] with x hx hy hm
  exact hT.mem_of_tendsto ((hx.comp hb.tendsto_atTop).prodMk_nhds hy)
    (Eventually.of_forall hm)

theorem operator_closed (hT : T.IsClosed) : (operator μ T).IsClosed := by
  rw [LinearPMap.IsClosed,operator_graph]
  exact graph_closed μ T hT

theorem operator_graph_zero (hker : ∀ f, (f,0) ∈ T.graph → f = 0)
    (f : L) (hf : (f,0) ∈ (operator μ T).graph) : f = 0 := by
  rw [operator_graph] at hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hf,Lp.coeFn_zero (E := H) (p := 2) (μ := μ)] with x hx h0
  exact hker (f x) (by simpa only [h0] using hx)

theorem compLp_injective (B : H →L[ℂ] H) (hB : Function.Injective B) :
    Function.Injective (B.compLpL 2 μ) := by
  intro f g hfg
  apply Lp.ext
  filter_upwards [B.coeFn_compLp f,B.coeFn_compLp g] with x hf hg
  apply hB
  exact hf.symm.trans ((congrArg (fun z : L => z x) hfg).trans hg)

#print axioms graph_vertical_zero
#print axioms operator_graph
#print axioms graph_closed
#print axioms operator_closed
#print axioms operator_graph_zero
#print axioms compLp_injective
end
end UnifiedTheory.Audit.KFCausalLpClosedOperator
