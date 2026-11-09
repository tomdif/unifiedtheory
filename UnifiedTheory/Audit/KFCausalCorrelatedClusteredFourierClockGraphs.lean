/- Actual maximal pure-clock graphs for the joint Fourier representatives,
including strong convergence of both entries of the graph. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierPureClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierClockGraphs
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredJointFourierL2Limit
open KFCausalCorrelatedClusteredFourierPureClock
open KFCausalClockFloorPureClockDerivative (differential)
open KFCausalClockFloorPureClockMomentum (pureMomentum)

variable {m : ℕ} (f : Family m) (α β ε y z : ℝ) (a p : Fin m → ℝ) (k : ℕ)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε)
  (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3) (ha : ∀ i, 0 < a i)

include hα hβ hw hε hy hz ha in
theorem profile_differential_memLp (δ : ℝ) (hδ : 0 < δ) :
    MemLp (differential ε (profile α β ε y z f a p k δ)) 2 volume := by
  have he := funext (profile_differential α β ε y z hα hε hy hz f a p k δ hδ)
  rw [he]
  exact finiteClock_memLp f α β ε y z a p k hα hβ hw hε hy hz ha δ hδ

include hα hβ hw hε hy hz ha in
theorem limitProfile_differential_memLp :
    MemLp (differential ε (limitProfile α β ε y z f a p k)) 2 volume := by
  have he := funext (limitProfile_differential α β ε y z hα hε hy hz f a p k)
  rw [he]
  exact limitingClock_memLp f α β ε y z a p k hα hβ hw hε hy hz ha

def finiteDerivative (h δ : ℝ) : Hilbert :=
  (-Complex.I*(h:ℂ)) • finiteClock f α β ε y z a p k hα hβ hw hε hy hz ha δ

def limitingDerivative (h : ℝ) : Hilbert :=
  (-Complex.I*(h:ℂ)) • limitingClock f α β ε y z a p k hα hβ hw hε hy hz ha

theorem finite_graph (h : ℝ) (hh : h ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    (finiteInput f α β ε y z a p k hα hβ hw hε hy hz ha δ,
      finiteDerivative f α β ε y z a p k hα hβ hw hε hy hz ha h δ) ∈
      (pureMomentum ε hε h).graph := by
  have hf := finiteInput_memLp f α β ε y z a p k hα hβ hw hε hy hz ha δ hδ
  have hd := profile_differential_memLp f α β ε y z a p k hα hβ hw hε hy hz ha δ hδ
  have hi : hf.toLp (profile α β ε y z f a p k δ) =
      finiteInput f α β ε y z a p k hα hβ hw hε hy hz ha δ := by
    apply Lp.ext
    exact hf.coeFn_toLp.trans (finiteInput_coe f α β ε y z a p k hα hβ hw hε hy hz ha δ hδ).symm
  have ho : hd.toLp (differential ε (profile α β ε y z f a p k δ)) =
      finiteClock f α β ε y z a p k hα hβ hw hε hy hz ha δ := by
    apply Lp.ext
    filter_upwards [hd.coeFn_toLp,finiteClock_coe f α β ε y z a p k hα hβ hw hε hy hz ha δ hδ] with x hx hyx
    rw [hx,hyx,profile_differential α β ε y z hα hε hy hz f a p k δ hδ]
  have hg := KFCausalClockFloorPureClockDifferential.differential_graph ε hε h hh
    (profile α β ε y z f a p k δ) hf hd
    (profile_differentiable α β ε y z hα hε hy hz f a p k δ hδ)
  simpa only [hi,ho,finiteDerivative] using hg

theorem limiting_graph (h : ℝ) (hh : h ≠ 0) :
    (limitingInput f α β ε y z a p k hα hβ hw hε hy hz ha,
      limitingDerivative f α β ε y z a p k hα hβ hw hε hy hz ha h) ∈
      (pureMomentum ε hε h).graph := by
  have hf := limitingInput_memLp f α β ε y z a p k hα hβ hw hε hy hz ha
  have hd := limitProfile_differential_memLp f α β ε y z a p k hα hβ hw hε hy hz ha
  have hi : hf.toLp (limitProfile α β ε y z f a p k) =
      limitingInput f α β ε y z a p k hα hβ hw hε hy hz ha := by
    apply Lp.ext
    exact hf.coeFn_toLp.trans (limitingInput_coe f α β ε y z a p k hα hβ hw hε hy hz ha).symm
  have ho : hd.toLp (differential ε (limitProfile α β ε y z f a p k)) =
      limitingClock f α β ε y z a p k hα hβ hw hε hy hz ha := by
    apply Lp.ext
    filter_upwards [hd.coeFn_toLp,limitingClock_coe f α β ε y z a p k hα hβ hw hε hy hz ha] with x hx hyx
    rw [hx,hyx,limitProfile_differential α β ε y z hα hε hy hz f a p k]
  have hg := KFCausalClockFloorPureClockDifferential.differential_graph ε hε h hh
    (limitProfile α β ε y z f a p k) hf hd
    (limitProfile_differentiable α β ε y z hα hε hy hz f a p k)
  simpa only [hi,ho,limitingDerivative] using hg

theorem finite_domain (h : ℝ) (hh : h ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    finiteInput f α β ε y z a p k hα hβ hw hε hy hz ha δ ∈ (pureMomentum ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (finite_graph f α β ε y z a p k hα hβ hw hε hy hz ha h hh δ hδ)

theorem limiting_domain (h : ℝ) (hh : h ≠ 0) :
    limitingInput f α β ε y z a p k hα hβ hw hε hy hz ha ∈ (pureMomentum ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (limiting_graph f α β ε y z a p k hα hβ hw hε hy hz ha h hh)

theorem finiteDerivative_tendsto (h : ℝ) :
    Tendsto (finiteDerivative f α β ε y z a p k hα hβ hw hε hy hz ha h) (𝓝[>] 0)
      (𝓝 (limitingDerivative f α β ε y z a p k hα hβ hw hε hy hz ha h)) :=
  tendsto_const_nhds.smul (finiteClock_tendsto f α β ε y z a p k hα hβ hw hε hy hz ha)

theorem graph_pair_tendsto (h : ℝ) :
    Tendsto (fun δ => (finiteInput f α β ε y z a p k hα hβ hw hε hy hz ha δ,
      finiteDerivative f α β ε y z a p k hα hβ hw hε hy hz ha h δ)) (𝓝[>] 0)
      (𝓝 (limitingInput f α β ε y z a p k hα hβ hw hε hy hz ha,
        limitingDerivative f α β ε y z a p k hα hβ hw hε hy hz ha h)) :=
  (finiteInput_tendsto f α β ε y z a p k hα hβ hw hε hy hz ha).prodMk_nhds
    (finiteDerivative_tendsto f α β ε y z a p k hα hβ hw hε hy hz ha h)

#print axioms profile_differential_memLp
#print axioms limitProfile_differential_memLp
#print axioms finite_graph
#print axioms limiting_graph
#print axioms finite_domain
#print axioms limiting_domain
#print axioms finiteDerivative_tendsto
#print axioms graph_pair_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierClockGraphs
