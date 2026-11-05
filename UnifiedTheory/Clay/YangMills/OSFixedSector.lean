/-
The fixed sector of the actual OS semigroup is exactly the zero eigenspace of
its constructed maximal Hamiltonian, including full Schwartz transport.
Diagonal connected-kernel clustering implies uniqueness of the normalized
vacuum by the density of actual canonical states. The clustering estimate
remains an explicit physical hypothesis: this module does not establish a
spectral gap, a physical coupling trajectory, or continuum Yang--Mills existence.
-/

import UnifiedTheory.Clay.YangMills.FullSchwartzVacuum
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSFixedSector
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open KernelHilbertCompletion OSScalarDynamics OSLaplaceResolvent
open scoped NNReal Topology

variable {W : Hierarchy} {plane : Plane} {hp : Positive W plane}
  (D : Evolution W plane hp)

def laplaceDeficit (x : State (hp := hp)) (t : ℝ) : ℝ :=
  Real.exp (-t) * ‖x‖ ^ 2 - (inner ℂ x (integrand D x t)).re

theorem laplaceDeficit_nonneg (x : State (hp := hp)) (t : ℝ) :
    0 ≤ laplaceDeficit D x t := by
  unfold laplaceDeficit
  apply sub_nonneg.mpr
  calc
    _ ≤ ‖x‖ * ‖integrand D x t‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖x‖ * (Real.exp (-t) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (integrand_norm D x t) (norm_nonneg x)
    _ = _ := by ring

theorem laplaceDeficit_continuous (x : State (hp := hp)) :
    Continuous (laplaceDeficit D x) :=
  ((Real.continuous_exp.comp continuous_neg).mul continuous_const).sub
    (Complex.continuous_re.comp (continuous_const.inner (integrand_continuous D x)))

theorem laplaceDeficit_integrable (x : State (hp := hp)) :
    IntegrableOn (laplaceDeficit D x) (Set.Ioi 0) :=
  ((integrableOn_exp_neg_Ioi 0).mul_const (‖x‖ ^ 2)).sub
    (((integrand_integrable D x).const_inner (𝕜 := ℂ) x).re)

/-- An actual Laplace-resolvent fixed vector is fixed at every Euclidean time. -/
theorem fixed_of_resolvent_fixed (x : State (hp := hp)) (hx : resolvent D x = x)
    (s : ℝ≥0) : D.operator s x = x := by
  have hi := laplaceDeficit_integrable D x
  have hiq : Integrable (fun t : ℝ => (inner ℂ x (integrand D x t)).re)
      (volume.restrict (Set.Ioi 0)) := by
    simpa only [RCLike.re_to_complex] using
      (((integrand_integrable D x).const_inner (𝕜 := ℂ) x).re)
  have hz : (∫ t : ℝ in Set.Ioi 0, laplaceDeficit D x t) = 0 := by
    change (∫ t : ℝ in Set.Ioi 0,
      Real.exp (-t) * ‖x‖ ^ 2 - (inner ℂ x (integrand D x t)).re) = 0
    rw [integral_sub
      ((integrableOn_exp_neg_Ioi 0).mul_const (‖x‖ ^ 2))
      hiq,
      integral_mul_const, integral_exp_neg_Ioi_zero, one_mul, ← quadratic_pairing, hx,
      show (inner ℂ x x).re = ‖x‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) x]
    exact sub_self _
  have hae := (integral_eq_zero_iff_of_nonneg (laplaceDeficit_nonneg D x) hi).mp hz
  have he := MeasureTheory.Measure.eqOn_open_of_ae_eq hae isOpen_Ioi
    (laplaceDeficit_continuous D x).continuousOn continuous_zero.continuousOn
  by_cases hs : s = 0
  · simpa only [hs] using D.zero x
  have hpos : 0 < (s : ℝ) := by exact_mod_cast (lt_of_le_of_ne (zero_le s) (Ne.symm hs))
  have heq := he (show (s : ℝ) ∈ Set.Ioi 0 from hpos)
  simp only [laplaceDeficit, integrand, Real.toNNReal_coe, Pi.zero_apply] at heq
  rw [inner_smul_right_eq_smul (𝕜 := ℂ) x (D.operator s x) (Real.exp (-(s : ℝ)))] at heq
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at heq
  have hpair : (inner ℂ x (D.operator s x)).re = ‖x‖ ^ 2 := by
    nlinarith [Real.exp_pos (-(s : ℝ))]
  have hnorm := D.contraction s x
  have hsq : ‖x - D.operator s x‖ ^ 2 =
      ‖x‖ ^ 2 - 2 * (inner ℂ x (D.operator s x)).re + ‖D.operator s x‖ ^ 2 :=
    norm_sub_sq (𝕜 := ℂ) x (D.operator s x)
  have hzsub : ‖x - D.operator s x‖ = 0 := by
    nlinarith [norm_nonneg x, norm_nonneg (D.operator s x),
      sq_nonneg ‖x - D.operator s x‖, norm_nonneg (x - D.operator s x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzsub)).symm

theorem resolvent_fixed_of_fixed (x : State (hp := hp))
    (hx : ∀ s : ℝ≥0, D.operator s x = x) : resolvent D x = x := by
  rw [resolvent_apply]
  simp only [integrand, hx]
  rw [integral_smul_const, integral_exp_neg_Ioi_zero, one_smul]

/-- The exact maximal Hamiltonian kernel is precisely the actual semigroup's fixed sector. -/
theorem graph_zero_iff_fixed (x : State (hp := hp)) :
    (x, 0) ∈ (OSLaplaceHamiltonian.hamiltonian D).graph ↔
      ∀ s : ℝ≥0, D.operator s x = x := by
  rw [OSLaplaceHamiltonian.graph_iff, zero_add]
  exact ⟨fixed_of_resolvent_fixed D x, resolvent_fixed_of_fixed D x⟩

/-- The identification also holds on the full positive-time Schwartz completion. -/
theorem full_graph_zero_iff_fixed
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (x : FullSchwartzHamiltonian.State W plane hfull) :
    (x, 0) ∈ (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D).graph ↔
      ∀ s : ℝ≥0, FullSchwartzDynamics.operator W plane hp hfull D s x = x := by
  rw [FullSchwartzHamiltonian.graph_transport]
  simp only [map_zero]
  rw [graph_zero_iff_fixed]
  let e := FullSchwartzHilbert.equivalence W plane hp hfull
  constructor
  · intro hx t
    rw [FullSchwartzDynamics.operator_apply, hx, LinearIsometryEquiv.apply_symm_apply]
  · intro hx t
    have h := congrArg e.symm (hx t)
    change e.symm (e (D.operator t (e.symm x))) = e.symm x at h
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h

/-- Vanishing pairing with actual canonical states detects the zero vector. -/
theorem zero_of_canonical_pairings (x : State (hp := hp))
    (hx : ∀ i, inner ℂ x (canonical (positiveKernel W plane hp) i) = 0) : x = 0 := by
  have hspan : ∀ y ∈ Submodule.span ℂ (Set.range (canonical (positiveKernel W plane hp))),
      inner ℂ x y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hx i
    | zero => exact inner_zero_right _
    | add u v hu hv hiu hiv => simp only [inner_add_right, hiu, hiv, add_zero]
    | smul c v hv hi => simp only [inner_smul_right, hi, mul_zero]
  have hall (y : State (hp := hp)) : inner ℂ x y = 0 := by
    have hc : IsClosed {v : State (hp := hp) | inner ℂ x v = 0} :=
      isClosed_eq (innerSL ℂ x).continuous continuous_const
    have hcl := hc.closure_subset_iff.mpr hspan
    exact hcl (dense_canonical_span (positiveKernel W plane hp) y)
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp (hall x)

/-- Exact Pythagorean identity for the constructed vacuum subtraction. -/
theorem centered_norm_sq
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (x : State (hp := hp)) :
    ‖OSVacuumSector.centered W plane hp x‖ ^ 2 = ‖x‖ ^ 2 -
      ‖inner ℂ (OSVacuumSector.vacuum W plane hp) x‖ ^ 2 := by
  let Ω := OSVacuumSector.vacuum W plane hp
  let c := inner ℂ Ω x
  have ho : inner ℂ (OSVacuumSector.centered W plane hp x) (c • Ω) = 0 := by
    have hz : inner ℂ (OSVacuumSector.centered W plane hp x) Ω = 0 := by
      calc
        _ = star (inner ℂ Ω (OSVacuumSector.centered W plane hp x)) :=
          (inner_conj_symm (𝕜 := ℂ) (OSVacuumSector.centered W plane hp x) Ω).symm
        _ = 0 := by rw [OSVacuumSector.centered_orthogonal W plane hp hn, star_zero]
    calc
      _ = c * inner ℂ (OSVacuumSector.centered W plane hp x) Ω :=
        inner_smul_right (𝕜 := ℂ) (OSVacuumSector.centered W plane hp x) Ω c
      _ = 0 := by rw [hz, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (OSVacuumSector.centered W plane hp x) (c • Ω) ho
  have he : OSVacuumSector.centered W plane hp x + c • Ω = x := by
    exact sub_add_cancel _ _
  rw [he, norm_smul, OSVacuumSector.vacuum_norm W plane hp hn, mul_one] at h
  apply (eq_sub_iff_add_eq).mpr
  simpa only [pow_two] using h.symm

/-- The norm of an evolved centered canonical state is an actual connected reflected kernel. -/
theorem centered_canonical_norm_sq
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (i : Label) (t : ℝ≥0) :
    ‖D.operator t (OSVacuumSector.centered W plane hp
      (canonical (positiveKernel W plane hp) i))‖ ^ 2 =
      (kernel W plane (i, shift (t+t) i)).re -
        ‖inner ℂ (OSVacuumSector.vacuum W plane hp)
          (canonical (positiveKernel W plane hp) i)‖ ^ 2 := by
  rw [OSVacuumSector.evolution_centered, centered_norm_sq hn,
    OSVacuumSector.inner_vacuum_evolution]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), D.symmetric, D.add, D.canonical_action, canonical_inner]
  rfl

/-- Only diagonal connected Schwinger-kernel clustering is required here;
no Hamiltonian gap or uniqueness assertion occurs in this hypothesis. -/
def DiagonalClustering : Prop :=
  ∀ i : Label, Tendsto (fun t : ℝ≥0 => (kernel W plane (i, shift (t+t) i)).re) atTop
    (𝓝 (‖inner ℂ (OSVacuumSector.vacuum W plane hp)
      (canonical (positiveKernel W plane hp) i)‖ ^ 2))

theorem centered_canonical_tendsto_zero
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (hcluster : DiagonalClustering (W := W) (plane := plane) (hp := hp)) (i : Label) :
    Tendsto (fun t : ℝ≥0 => D.operator t (OSVacuumSector.centered W plane hp
      (canonical (positiveKernel W plane hp) i))) atTop (𝓝 0) := by
  have hsq : Tendsto (fun t : ℝ≥0 =>
      ‖D.operator t (OSVacuumSector.centered W plane hp
        (canonical (positiveKernel W plane hp) i))‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [centered_canonical_norm_sq D hn]
    have hc : Tendsto (fun _ : ℝ≥0 =>
        ‖inner ℂ (OSVacuumSector.vacuum W plane hp)
          (canonical (positiveKernel W plane hp) i)‖ ^ 2) atTop
        (𝓝 (‖inner ℂ (OSVacuumSector.vacuum W plane hp)
          (canonical (positiveKernel W plane hp) i)‖ ^ 2)) := tendsto_const_nhds
    simpa only [sub_self] using (hcluster i).sub hc
  have hnrm : Tendsto (fun t : ℝ≥0 => Real.sqrt
      (‖D.operator t (OSVacuumSector.centered W plane hp
        (canonical (positiveKernel W plane hp) i))‖ ^ 2)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply hnrm.congr'
  exact Eventually.of_forall (fun t => Real.sqrt_sq (norm_nonneg _))

/-- Clustering forces every actual fixed vector to be proportional to the normalized vacuum. -/
theorem fixed_unique_of_clustering
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (hcluster : DiagonalClustering (W := W) (plane := plane) (hp := hp))
    (x : State (hp := hp)) (hx : ∀ t : ℝ≥0, D.operator t x = x) :
    x = (inner ℂ (OSVacuumSector.vacuum W plane hp) x) • OSVacuumSector.vacuum W plane hp := by
  let y := OSVacuumSector.centered W plane hp x
  have hy (t : ℝ≥0) : D.operator t y = y := by
    dsimp only [y]
    rw [OSVacuumSector.evolution_centered, hx]
  have horth : inner ℂ y (OSVacuumSector.vacuum W plane hp) = 0 := by
    calc
      _ = star (inner ℂ (OSVacuumSector.vacuum W plane hp) y) :=
        (inner_conj_symm (𝕜 := ℂ) y (OSVacuumSector.vacuum W plane hp)).symm
      _ = 0 := by
        simp only [y, OSVacuumSector.centered_orthogonal W plane hp hn, star_zero]
  have hzero : y = 0 := by
    apply zero_of_canonical_pairings
    intro i
    have ht := ((innerSL ℂ y).continuous.tendsto 0).comp
      (centered_canonical_tendsto_zero D hn hcluster i)
    rw [map_zero] at ht
    change Tendsto (fun t : ℝ≥0 => inner ℂ y (D.operator t
      (OSVacuumSector.centered W plane hp (canonical (positiveKernel W plane hp) i))))
      atTop (𝓝 (0 : ℂ)) at ht
    have ht' : Tendsto (fun _t : ℝ≥0 => inner ℂ y (OSVacuumSector.centered W plane hp
        (canonical (positiveKernel W plane hp) i))) atTop (𝓝 (0 : ℂ)) := by
      apply ht.congr'
      exact Eventually.of_forall (fun t => by
        dsimp only
        rw [← D.symmetric, hy])
    have he := tendsto_nhds_unique tendsto_const_nhds ht'
    have hs := inner_smul_right (𝕜 := ℂ) y (OSVacuumSector.vacuum W plane hp)
      (inner ℂ (OSVacuumSector.vacuum W plane hp) (canonical (positiveKernel W plane hp) i))
    simp only [OSVacuumSector.centered, inner_sub_right, hs, horth, mul_zero, sub_zero] at he
    exact he
  exact sub_eq_zero.mp hzero

/-- The zero eigenspace of the actual maximal OS Hamiltonian is one-dimensional if
its actual reflected kernels cluster. The physical clustering estimate is still required. -/
theorem kernel_unique_of_clustering
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (hcluster : DiagonalClustering (W := W) (plane := plane) (hp := hp))
    (x : State (hp := hp)) (hx : (x, 0) ∈ (OSLaplaceHamiltonian.hamiltonian D).graph) :
    ∃ c : ℂ, x = c • OSVacuumSector.vacuum W plane hp :=
  ⟨_, fixed_unique_of_clustering D hn hcluster x ((graph_zero_iff_fixed D x).mp hx)⟩


/-- The same clustering criterion gives uniqueness on the full Schwartz Hilbert space,
with the already constructed full Hamiltonian and vacuum, by the proved unitary transport. -/
theorem full_kernel_unique_of_clustering
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (hcluster : DiagonalClustering (W := W) (plane := plane) (hp := hp))
    (x : FullSchwartzHamiltonian.State W plane hfull)
    (hx : (x, 0) ∈ (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D).graph) :
    ∃ c : ℂ, x = c • RenormalizedFullOSLimit.fullVacuum W plane hfull := by
  let e := FullSchwartzHilbert.equivalence W plane hp hfull
  have hg := (FullSchwartzHamiltonian.graph_transport W plane hp hfull D x 0).mp hx
  simp only [map_zero] at hg
  obtain ⟨c, hc⟩ := kernel_unique_of_clustering D hn hcluster (e.symm x) hg
  refine ⟨c, ?_⟩
  have he := congrArg e hc
  simpa only [e, LinearIsometryEquiv.apply_symm_apply, map_smul,
    FullSchwartzVacuum.equivalence_vacuum] using he


end
end UnifiedTheory.Clay.YangMills.OSFixedSector
